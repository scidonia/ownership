/-
A finite address map for the integrated multi-allocation state.

The integrated reconstruction model tracks logical allocations and their byte
heaps, but it says nothing about where an allocation lives in a flat address
space. This module adds the smallest such assignment: a finite map from live
`AllocId`s to concrete windows `(base, len)`. It does not connect to the LLVM
bridge. The bridge's `MemRep` and the emitted `store8` kernel are separate; this
file relates the logical state to windows, not to `LeanLLVM`'s byte memory.

What is modelled:

* `Window` is an address interval `[base, base + len)`. `Window.Disjoint` is
  interval separation, `Window.contains` is a logical offset inside the window,
  and `Window.addr` is the flat address `base + off`.
* `Map` is a finite list of `AllocId × Window` entries with a first-match
  lookup. `Map.WellFormed` requires distinct keys, pairwise disjoint live
  windows, and `base + len ≤ 2 ^ 64` for every window.
* `Covers` relates a map to `Integrated.State`: every live allocation has a
  window, every window has the allocation's recorded length, and every mapped
  key is live. Because lookup is a function, a live allocation has exactly one
  window. `Rel` is `WellFormed` together with `Covers`.
* `Map.within`, `Map.withinB` and `Map.addr?` are the offset lookup: an offset
  is inside an allocation when it is below that window's length, and the flat
  address is produced only for an in-window offset.
* `Map.addr?_lt` derives the pointer-width fact `base + off < 2 ^ 64` from
  `WellFormed` and a successful address lookup. No wraparound is assumed.

What is proved about the state transitions:

* `Map.alloc_wellFormed` — adding a fresh key whose window is disjoint from every
  existing window and within the address bound preserves `WellFormed`.
* `Map.free_wellFormed` — removing a key preserves `WellFormed`.
* `Rel.alloc` — an accepted `Integrated.State.alloc`, paired with adding the new
  allocation's window, preserves `Rel`.
* `Rel.free` — an accepted `Integrated.State.free`, paired with removing the
  window, preserves `Rel`.
* `Rel.write` — an accepted write preserves `Rel` and leaves every other
  allocation's `State.find?` and `State.snapshot` unchanged.
* `example_write_other` — the two-allocation fixture: writing allocation `⟨0⟩`
  leaves allocation `⟨3⟩`'s window and bytes unchanged.
* The refused controls are `alloc_refuses_overlap`, plus the fixture checks
  `overlapping_alloc_refused`, `missing_window_addr_none` and
  `out_of_window_addr_none`.

Persistent logical identity and reusable physical storage stay separate: the map
assigns windows to logical `AllocId`s, and nothing here claims that a loader
chooses them or that a freed window is physically reusable. That executable edge
belongs to a later bridge, not to this relation.
-/
import Cap.Integrated

namespace Cap
namespace AddressMap

open Integrated

/-! ### Windows -/

/-- A concrete address window `[base, base + len)`. -/
structure Window where
  base : Nat
  len : Nat
deriving Repr, DecidableEq, BEq

namespace Window

/-- The first address past the window. -/
def stop (w : Window) : Nat := w.base + w.len

/-- A logical offset inside the window. -/
def contains (w : Window) (off : Nat) : Prop := off < w.len

/-- The flat address of an offset in the window. -/
def addr (w : Window) (off : Nat) : Nat := w.base + off

/-- Two windows are disjoint when one stops at or before the other begins. -/
def Disjoint (w₁ w₂ : Window) : Prop :=
  w₁.stop ≤ w₂.base ∨ w₂.stop ≤ w₁.base

/-- Disjointness is symmetric. -/
theorem Disjoint.symm {w₁ w₂ : Window} (h : w₁.Disjoint w₂) : w₂.Disjoint w₁ := by
  rcases h with h | h
  · exact Or.inr h
  · exact Or.inl h

/-- The window's addresses stay inside the pointer width. -/
def inBounds (w : Window) : Prop := w.base + w.len ≤ 2 ^ 64

/-- The decidable form of `Window.inBounds`. -/
def inBoundsB (w : Window) : Bool := Nat.ble (w.base + w.len) (2 ^ 64)

theorem inBoundsB_eq_true {w : Window} : w.inBoundsB = true ↔ w.inBounds := by
  simp [inBoundsB, Window.inBounds]

/-- An in-window offset is a valid 64-bit address. -/
theorem addr_lt_of_contains {w : Window} {off : Nat}
    (hbound : w.inBounds) (h : w.contains off) : w.base + off < 2 ^ 64 := by
  unfold Window.inBounds at hbound
  unfold Window.contains at h
  omega

end Window

/-! ### The finite map -/

/-- A finite map from live allocation identifiers to concrete windows. -/
structure Map where
  entries : List (AllocId × Window)
deriving Repr, DecidableEq, BEq

namespace Map

/-- First-match lookup over the entry list. -/
def lookupList? : List (AllocId × Window) → AllocId → Option Window
  | [], _ => none
  | (k, v) :: rest, a => if k = a then some v else lookupList? rest a

/-- The window of an allocation, if one is mapped. -/
def lookup? (m : Map) (a : AllocId) : Option Window := lookupList? m.entries a

/-- The map with no windows. -/
def empty : Map := ⟨[]⟩

theorem lookupList?_cons_self (a : AllocId) (w : Window)
    (rest : List (AllocId × Window)) :
    lookupList? ((a, w) :: rest) a = some w := by
  simp [lookupList?]

theorem lookupList?_cons_other {a b : AllocId} (h : a ≠ b) (w : Window)
    (rest : List (AllocId × Window)) :
    lookupList? ((a, w) :: rest) b = lookupList? rest b := by
  simp [lookupList?, h]

/-- A successful lookup names an entry of the list. -/
theorem lookupList?_mem {l : List (AllocId × Window)} {a : AllocId} {w : Window}
    (h : lookupList? l a = some w) : (a, w) ∈ l := by
  induction l with
  | nil => simp [lookupList?] at h
  | cons p rest ih =>
      obtain ⟨k, v⟩ := p
      by_cases hk : k = a
      · simp only [lookupList?, hk, if_pos, Option.some.injEq] at h
        subst k
        subst w
        exact List.mem_cons_self
      · simp only [lookupList?, hk, if_false] at h
        exact List.mem_cons_of_mem _ (ih h)

/-- A key mentioned by an entry is found by lookup. -/
theorem lookupList?_isSome_of_mem_key {l : List (AllocId × Window)} {a : AllocId}
    (h : a ∈ l.map Prod.fst) : (lookupList? l a).isSome = true := by
  induction l with
  | nil => simp at h
  | cons p rest ih =>
      obtain ⟨k, v⟩ := p
      by_cases hk : k = a
      · simp [lookupList?, hk]
      · simp only [List.map_cons, List.mem_cons] at h
        rcases h with hhead | htail
        · exact absurd hhead.symm hk
        · simp only [lookupList?, hk, if_false]
          exact ih htail

/-- A key absent from the entry list has no window. -/
theorem lookupList?_eq_none_of_not_mem {l : List (AllocId × Window)} {a : AllocId}
    (h : a ∉ l.map Prod.fst) : lookupList? l a = none := by
  induction l with
  | nil => rfl
  | cons p rest ih =>
      obtain ⟨k, v⟩ := p
      by_cases hk : k = a
      · subst k
        exfalso
        exact h (by simp)
      · simp only [lookupList?, hk, if_false]
        apply ih
        intro hmem
        exact h (by simpa [List.map_cons] using List.mem_cons_of_mem k hmem)

/-- Distinct entry keys. -/
def KeysNodup (m : Map) : Prop := (m.entries.map Prod.fst).Nodup

/-- Any two distinct live windows are disjoint. -/
def NonOverlapping (m : Map) : Prop :=
  ∀ a w b v, m.lookup? a = some w → m.lookup? b = some v → a ≠ b → w.Disjoint v

/-- Every mapped window stays inside the pointer width. -/
def AddressBound (m : Map) : Prop :=
  ∀ a w, m.lookup? a = some w → w.inBounds

/-- The map invariant: distinct keys, disjoint live windows, bounded windows. -/
def WellFormed (m : Map) : Prop :=
  m.KeysNodup ∧ m.NonOverlapping ∧ m.AddressBound

theorem empty_wellFormed : empty.WellFormed := by
  refine ⟨?_, ?_, ?_⟩
  · simp [KeysNodup, empty]
  · intro a w b v ha hb hne
    simp [lookup?, empty, lookupList?] at ha
  · intro a w ha
    simp [lookup?, empty, lookupList?] at ha

/-- The decidable disjointness used by `alloc`. -/
def disjointB (w v : Window) : Bool :=
  Nat.ble w.stop v.base || Nat.ble v.stop w.base

/-- Check that `w` avoids every stored window. -/
def nonOverlappingB (m : Map) (w : Window) : Bool :=
  m.entries.all (fun p => disjointB w p.2)

theorem disjointB_eq_true {w v : Window} : disjointB w v = true ↔ w.Disjoint v := by
  simp [disjointB, Window.Disjoint]

/-- A successful `nonOverlappingB` check separates the new window from every
stored window. -/
theorem nonOverlappingB_sound {m : Map} {w : Window}
    (h : m.nonOverlappingB w = true) {b : AllocId} {v : Window}
    (hb : m.lookup? b = some v) : w.Disjoint v := by
  have hmem : (b, v) ∈ m.entries := lookupList?_mem hb
  have hall : ∀ p ∈ m.entries, disjointB w p.2 = true := by
    simpa [nonOverlappingB] using (List.all_eq_true.mp h)
  exact disjointB_eq_true.mp (hall (b, v) hmem)

/-- Add a fresh, disjoint, bounded window. A used key, an overlapping window or
an unbounded window is refused. -/
def alloc (m : Map) (a : AllocId) (w : Window) : Option Map :=
  if m.lookup? a = none ∧ m.nonOverlappingB w = true ∧ w.inBoundsB = true then
    some ⟨(a, w) :: m.entries⟩
  else none

theorem alloc_entries {m : Map} {a : AllocId} {w : Window} {m' : Map}
    (h : m.alloc a w = some m') : m'.entries = (a, w) :: m.entries := by
  unfold Map.alloc at h
  split at h
  · simp only [Option.some.injEq] at h
    subst m'
    rfl
  · simp at h

theorem alloc_lookup_none {m : Map} {a : AllocId} {w : Window} {m' : Map}
    (h : m.alloc a w = some m') : m.lookup? a = none := by
  unfold Map.alloc at h
  split at h
  · rename_i hc
    exact hc.1
  · simp at h

theorem alloc_nonOverlapping {m : Map} {a : AllocId} {w : Window} {m' : Map}
    (h : m.alloc a w = some m') : m.nonOverlappingB w = true := by
  unfold Map.alloc at h
  split at h
  · rename_i hc
    exact hc.2.1
  · simp at h

theorem alloc_bound {m : Map} {a : AllocId} {w : Window} {m' : Map}
    (h : m.alloc a w = some m') : w.inBounds := by
  unfold Map.alloc at h
  split at h
  · rename_i hc
    exact Window.inBoundsB_eq_true.mp hc.2.2
  · simp at h

theorem alloc_lookup_self {m : Map} {a : AllocId} {w : Window} {m' : Map}
    (h : m.alloc a w = some m') : m'.lookup? a = some w := by
  rw [Map.lookup?, alloc_entries h]
  exact lookupList?_cons_self a w m.entries

theorem alloc_lookup_other {m : Map} {a : AllocId} {w : Window} {m' : Map}
    (h : m.alloc a w = some m') {b : AllocId} (hb : b ≠ a) :
    m'.lookup? b = m.lookup? b := by
  rw [Map.lookup?, alloc_entries h, Map.lookup?]
  exact lookupList?_cons_other (fun heq => hb heq.symm) w m.entries

/-- Adding a fresh, disjoint, bounded window preserves the map invariant. -/
theorem alloc_wellFormed {m m' : Map} {a : AllocId} {w : Window}
    (hwf : m.WellFormed) (h : m.alloc a w = some m') : m'.WellFormed := by
  obtain ⟨hkeys, hnon, hbound⟩ := hwf
  have hlooknone : m.lookup? a = none := alloc_lookup_none h
  have hlookself : m'.lookup? a = some w := alloc_lookup_self h
  have hwbound : w.inBounds := alloc_bound h
  have hwover : m.nonOverlappingB w = true := alloc_nonOverlapping h
  refine ⟨?_, ?_, ?_⟩
  · rw [KeysNodup, alloc_entries h, List.map_cons, List.nodup_cons]
    refine ⟨?_, hkeys⟩
    intro hmem
    have hisSome : (m.lookup? a).isSome = true :=
      lookupList?_isSome_of_mem_key hmem
    rw [hlooknone] at hisSome
    simp at hisSome
  · intro b wb c vc hb hc hne
    by_cases hba : b = a
    · subst b
      have hwb : wb = w := (Option.some.inj (by simpa [hlookself] using hb)).symm
      subst wb
      by_cases hca : c = a
      · subst c
        have hvc : vc = w := (Option.some.inj (by simpa [hlookself] using hc)).symm
        subst vc
        exact absurd rfl hne
      · have hcold : m.lookup? c = some vc := by
          rw [← alloc_lookup_other h hca]
          exact hc
        exact nonOverlappingB_sound hwover hcold
    · have hbold : m.lookup? b = some wb := by
        rw [← alloc_lookup_other h hba]
        exact hb
      by_cases hca : c = a
      · subst c
        have hvc : vc = w := (Option.some.inj (by simpa [hlookself] using hc)).symm
        subst vc
        exact Window.Disjoint.symm (nonOverlappingB_sound hwover hbold)
      · have hcold : m.lookup? c = some vc := by
          rw [← alloc_lookup_other h hca]
          exact hc
        exact hnon b wb c vc hbold hcold hne
  · intro b wb hb
    by_cases hba : b = a
    · subst b
      have hwb : wb = w := (Option.some.inj (by simpa [hlookself] using hb)).symm
      subst wb
      exact hwbound
    · exact hbound b wb (by
        rw [← alloc_lookup_other h hba]
        exact hb)

/-- A used key cannot be allocated again. -/
theorem alloc_refuses_used {m : Map} {a : AllocId} {w : Window} {v : Window}
    (h : m.lookup? a = some v) : m.alloc a w = none := by
  unfold Map.alloc
  split
  · rename_i hc
    exact absurd hc.1 (by
      intro hnone
      rw [h] at hnone
      simp at hnone)
  · rfl

/-- An overlapping window is refused. -/
theorem alloc_refuses_overlap {m : Map} {a : AllocId} {w : Window} {b : AllocId}
    {v : Window} (hm : m.lookup? b = some v) (hov : ¬ w.Disjoint v) :
    m.alloc a w = none := by
  unfold Map.alloc
  split
  · rename_i hc
    exact absurd (nonOverlappingB_sound hc.2.1 hm) hov
  · rfl

/-- An unbounded window is refused. -/
theorem alloc_refuses_unbounded {m : Map} {a : AllocId} {w : Window}
    (h : ¬ w.inBounds) : m.alloc a w = none := by
  unfold Map.alloc
  split
  · rename_i hc
    exact absurd (Window.inBoundsB_eq_true.mp hc.2.2) h
  · rfl

/-- Remove a live allocation's window. A missing key is refused. -/
def free (m : Map) (a : AllocId) : Option Map :=
  if m.lookup? a = none then none
  else some ⟨m.entries.filter (fun p => !decide (p.1 = a))⟩

theorem free_entries {m m' : Map} {a : AllocId} (h : m.free a = some m') :
    m'.entries = m.entries.filter (fun p => !decide (p.1 = a)) := by
  unfold Map.free at h
  split at h
  · simp at h
  · simp only [Option.some.injEq] at h
    subst m'
    rfl

theorem lookupList?_filter_ne {l : List (AllocId × Window)} {a b : AllocId}
    (h : a ≠ b) :
    lookupList? (l.filter (fun p => !decide (p.1 = b))) a = lookupList? l a := by
  induction l with
  | nil => rfl
  | cons p rest ih =>
      obtain ⟨k, v⟩ := p
      by_cases hkb : k = b
      · subst k
        have hba : b ≠ a := fun heq => h heq.symm
        simpa [List.filter, lookupList?, hba] using ih
      · by_cases hka : k = a
        · subst k
          simp [List.filter, lookupList?, hkb]
        · simpa [List.filter, lookupList?, hkb, hka] using ih

theorem lookupList?_filter_self (l : List (AllocId × Window)) (a : AllocId) :
    lookupList? (l.filter (fun p => !decide (p.1 = a))) a = none := by
  induction l with
  | nil => rfl
  | cons p rest ih =>
      obtain ⟨k, v⟩ := p
      by_cases hk : k = a
      · subst k
        simpa [List.filter] using ih
      · simpa [List.filter, lookupList?, hk] using ih

theorem free_lookup_none {m m' : Map} {a : AllocId} (h : m.free a = some m') :
    m'.lookup? a = none := by
  rw [Map.lookup?, free_entries h]
  exact lookupList?_filter_self m.entries a

theorem free_lookup_other {m m' : Map} {a : AllocId} (h : m.free a = some m')
    {b : AllocId} (hb : b ≠ a) : m'.lookup? b = m.lookup? b := by
  rw [Map.lookup?, free_entries h, Map.lookup?]
  exact lookupList?_filter_ne hb

/-- Removing a live window preserves the map invariant. -/
theorem free_wellFormed {m m' : Map} {a : AllocId}
    (hwf : m.WellFormed) (h : m.free a = some m') : m'.WellFormed := by
  obtain ⟨hkeys, hnon, hbound⟩ := hwf
  refine ⟨?_, ?_, ?_⟩
  · rw [KeysNodup, free_entries h]
    exact List.Sublist.nodup (List.Sublist.map Prod.fst List.filter_sublist) hkeys
  · intro b wb c vc hb hc hne
    apply hnon b wb c vc
    · by_cases hba : b = a
      · subst b
        rw [free_lookup_none h] at hb
        simp at hb
      · rw [free_lookup_other h hba] at hb
        exact hb
    · by_cases hca : c = a
      · subst c
        rw [free_lookup_none h] at hc
        simp at hc
      · rw [free_lookup_other h hca] at hc
        exact hc
    · exact hne
  · intro b wb hb
    by_cases hba : b = a
    · subst b
      rw [free_lookup_none h] at hb
      simp at hb
    · rw [free_lookup_other h hba] at hb
      exact hbound b wb hb

theorem free_none_of_absent {m : Map} {a : AllocId} (h : m.lookup? a = none) :
    m.free a = none := by
  unfold Map.free
  rw [h]
  simp

end Map

/-- A key removed by `free` is absent from the filtered key list. -/
theorem removeAlloc_no_key (l : List Reconstruction.State) (a : AllocId) :
    a ∉ (removeAlloc a l).map (fun st => st.alloc) := by
  induction l with
  | nil => simp [removeAlloc]
  | cons head tail ih =>
      simp only [removeAlloc]
      by_cases hs : head.alloc = a
      · rw [if_pos hs]
        exact ih
      · rw [if_neg hs]
        rw [List.map_cons]
        intro hmem
        rcases List.mem_cons.mp hmem with hhead | htail
        · exact hs hhead.symm
        · exact ih htail

/-- A surviving component is still present after removing another key. -/
theorem mem_removeAlloc_of_key_ne {l : List Reconstruction.State}
    {st : Reconstruction.State} {a : AllocId}
    (h : st ∈ l) (hne : st.alloc ≠ a) : st ∈ removeAlloc a l := by
  induction l with
  | nil => simp at h
  | cons head tail ih =>
      simp only [removeAlloc]
      by_cases hs : head.alloc = a
      · rw [if_pos hs]
        rcases List.mem_cons.mp h with rfl | h
        · exact absurd hs hne
        · exact ih h
      · rw [if_neg hs]
        rcases List.mem_cons.mp h with rfl | h
        · exact List.mem_cons_self
        · exact List.mem_cons_of_mem head (ih h)

/-! ### The relation to the integrated state -/

/-- Every live allocation has a window, every window has the allocation's
recorded length, and every mapped key is live. -/
def Covers (m : Map) (s : Integrated.State) : Prop :=
  (∀ a ∈ s.allocIds, ∃ w, m.lookup? a = some w) ∧
  (∀ a w, m.lookup? a = some w → ∃ st, s.find? a = some st ∧ st.len = w.len) ∧
  (∀ a w, m.lookup? a = some w → a ∈ s.allocIds)

/-- The address map is well formed and covers the integrated state. -/
def Rel (m : Map) (s : Integrated.State) : Prop := m.WellFormed ∧ Covers m s

theorem Rel.window_unique {m : Map} {s : Integrated.State} (_ : Rel m s)
    {a : AllocId} {w₁ w₂ : Window} (h₁ : m.lookup? a = some w₁)
    (h₂ : m.lookup? a = some w₂) : w₁ = w₂ := by
  rw [h₁] at h₂
  exact Option.some.inj h₂

namespace Map

/-- An offset is inside an allocation's window. -/
def within (m : Map) (a : AllocId) (off : Nat) : Prop :=
  ∃ w, m.lookup? a = some w ∧ off < w.len

/-- The decidable form of `within`. -/
def withinB (m : Map) (a : AllocId) (off : Nat) : Bool :=
  match m.lookup? a with
  | none => false
  | some w => decide (off < w.len)

/-- The flat address of an in-window offset; `none` for a missing window or an
offset at or past the window's end. -/
def addr? (m : Map) (a : AllocId) (off : Nat) : Option Nat :=
  match m.lookup? a with
  | none => none
  | some w => if off < w.len then some (w.base + off) else none

theorem addr?_none_of_lookup_none {m : Map} {a : AllocId} {off : Nat}
    (h : m.lookup? a = none) : m.addr? a off = none := by
  simp [Map.addr?, h]

theorem addr?_some_of_within {m : Map} {a : AllocId} {off : Nat} {w : Window}
    (hw : m.lookup? a = some w) (h : off < w.len) :
    m.addr? a off = some (w.base + off) := by
  simp [Map.addr?, hw, h]

theorem addr?_none_of_out_of_window {m : Map} {a : AllocId} {off : Nat}
    {w : Window} (hw : m.lookup? a = some w) (h : w.len ≤ off) :
    m.addr? a off = none := by
  simp [Map.addr?, hw, Nat.not_lt.mpr h]

/-- A produced address is inside the pointer width. -/
theorem addr?_lt {m : Map} {a : AllocId} {off x : Nat}
    (hbound : m.AddressBound) (h : m.addr? a off = some x) : x < 2 ^ 64 := by
  unfold Map.addr? at h
  cases hlook : m.lookup? a with
  | none => simp [hlook] at h
  | some w =>
      by_cases hlt : off < w.len
      · simp only [hlook, hlt, if_pos, Option.some.injEq] at h
        subst x
        exact Window.addr_lt_of_contains (hbound a w hlook) hlt
      · simp [hlook, hlt] at h

end Map

theorem Rel.addr?_lt {m : Map} {s : Integrated.State} (h : Rel m s)
    {a : AllocId} {off x : Nat} (hx : m.addr? a off = some x) : x < 2 ^ 64 :=
  Map.addr?_lt h.1.2.2 hx

/-! ### Allocation and free -/

theorem State.alloc_allocIds {s s' : Integrated.State} {a : AllocId}
    {n D : Nat} {pos : 0 < D} {rootId disposalId : CapId}
    (h : s.alloc a n D pos rootId disposalId = some s') :
    s'.allocIds = a :: s.allocIds := by
  unfold Integrated.State.alloc at h
  split at h
  · simp only [Option.some.injEq] at h
    subst s'
    rfl
  · simp at h

theorem State.alloc_fresh {s s' : Integrated.State} {a : AllocId}
    {n D : Nat} {pos : 0 < D} {rootId disposalId : CapId}
    (h : s.alloc a n D pos rootId disposalId = some s') :
    a ∉ s.allocsIssued := by
  unfold Integrated.State.alloc at h
  split at h
  · rename_i hc
    exact hc.1
  · simp at h

theorem State.alloc_find_self {s s' : Integrated.State} {a : AllocId}
    {n D : Nat} {pos : 0 < D} {rootId disposalId : CapId}
    (h : s.alloc a n D pos rootId disposalId = some s') :
    s'.find? a = some (Reconstruction.State.initial a n D pos rootId disposalId) := by
  unfold Integrated.State.alloc at h
  split at h
  · simp only [Option.some.injEq] at h
    subst s'
    unfold Integrated.State.find?
    simp [Integrated.findState?, Reconstruction.State.initial]
  · simp at h

/-- An accepted allocation adds its window and preserves the rest. -/
theorem Rel.alloc {m m' : Map} {s s' : Integrated.State} {a : AllocId}
    {n D : Nat} {pos : 0 < D} {rootId disposalId : CapId} {w : Window}
    (hrel : Rel m s) (hinv : s.Inv)
    (halloc : s.alloc a n D pos rootId disposalId = some s')
    (hwlen : w.len = n) (hm : m.alloc a w = some m') : Rel m' s' := by
  obtain ⟨hwf, hcovLive, hcovLen, hcovBack⟩ := hrel
  obtain ⟨_, _, hlive, _, _⟩ := hinv
  have hfresh : a ∉ s.allocsIssued := State.alloc_fresh halloc
  have hnotlive : a ∉ s.allocIds := fun hm' => hfresh (hlive a hm')
  refine ⟨Map.alloc_wellFormed hwf hm, ?_, ?_, ?_⟩
  · intro x hx
    rw [State.alloc_allocIds halloc] at hx
    rcases List.mem_cons.mp hx with rfl | hx
    · exact ⟨w, Map.alloc_lookup_self hm⟩
    · have hxa : x ≠ a := fun heq => hnotlive (by simpa [heq] using hx)
      obtain ⟨v, hv⟩ := hcovLive x hx
      exact ⟨v, by rw [Map.alloc_lookup_other hm hxa]; exact hv⟩
  · intro x v hxv
    by_cases hxa : x = a
    · subst x
      rw [Map.alloc_lookup_self hm] at hxv
      have hv : v = w := (Option.some.inj hxv).symm
      subst w
      refine ⟨Reconstruction.State.initial a n D pos rootId disposalId,
        State.alloc_find_self halloc, ?_⟩
      simp [Reconstruction.State.initial, hwlen]
    · have hxa' : x ≠ a := hxa
      have hmx : m.lookup? x = some v := by
        rw [Map.alloc_lookup_other hm hxa'] at hxv
        exact hxv
      obtain ⟨st, hfind, hlen⟩ := hcovLen x v hmx
      exact ⟨st, by rw [State.alloc_frames_other halloc hxa']; exact hfind, hlen⟩
  · intro x v hxv
    by_cases hxa : x = a
    · subst x
      rw [State.alloc_allocIds halloc]
      exact List.mem_cons_self
    · have hmx : m.lookup? x = some v := by
        rw [Map.alloc_lookup_other hm hxa] at hxv
        exact hxv
      have hxold : x ∈ s.allocIds := hcovBack x v hmx
      rw [State.alloc_allocIds halloc]
      exact List.mem_cons_of_mem a hxold

theorem State.free_allocIds {s s' : Integrated.State} {a : AllocId}
    (h : s.free a = some s') :
    s'.allocIds = (removeAlloc a s.allocs).map (fun st => st.alloc) := by
  unfold Integrated.State.free at h
  cases hfind : s.find? a with
  | none => simp [hfind] at h
  | some st =>
      simp only [hfind] at h
      by_cases hc : st.restores = [] ∧ wholeActiveB st = true
      · rw [if_pos hc] at h
        simp only [Option.some.injEq] at h
        subst s'
        rfl
      · rw [if_neg hc] at h
        simp at h

/-- An accepted free removes its window and preserves the rest. -/
theorem Rel.free {m m' : Map} {s s' : Integrated.State} {a : AllocId}
    (hrel : Rel m s) (hinv : s.Inv)
    (hfree : s.free a = some s') (hm : m.free a = some m') : Rel m' s' := by
  obtain ⟨hwf, hcovLive, hcovLen, hcovBack⟩ := hrel
  refine ⟨Map.free_wellFormed hwf hm, ?_, ?_, ?_⟩
  · intro x hx
    have hxold : x ∈ s.allocIds := by
      rw [State.free_allocIds hfree] at hx
      exact removeAlloc_alloc_mem hx
    have hxa : x ≠ a := by
      intro heq
      subst x
      rw [State.free_allocIds hfree] at hx
      exact removeAlloc_no_key s.allocs a hx
    obtain ⟨v, hv⟩ := hcovLive x hxold
    exact ⟨v, by rw [Map.free_lookup_other hm hxa]; exact hv⟩
  · intro x v hxv
    have hxa : x ≠ a := by
      intro heq
      subst x
      rw [Map.free_lookup_none hm] at hxv
      simp at hxv
    have hmx : m.lookup? x = some v := by
      rw [Map.free_lookup_other hm hxa] at hxv
      exact hxv
    obtain ⟨st, hfind, hlen⟩ := hcovLen x v hmx
    exact ⟨st, by rw [State.free_frames_other hfree hxa]; exact hfind, hlen⟩
  · intro x v hxv
    have hxa : x ≠ a := by
      intro heq
      subst x
      rw [Map.free_lookup_none hm] at hxv
      simp at hxv
    have hmx : m.lookup? x = some v := by
      rw [Map.free_lookup_other hm hxa] at hxv
      exact hxv
    have hxold : x ∈ s.allocIds := hcovBack x v hmx
    rw [State.free_allocIds hfree]
    obtain ⟨st, hst, hkey⟩ := List.mem_map.mp hxold
    have hne : st.alloc ≠ a := by
      rw [hkey]
      exact hxa
    exact List.mem_map.mpr ⟨st, mem_removeAlloc_of_key_ne hst hne, hkey⟩

/-! ### Write framing -/

theorem updateState_alloc_mem_of_mem {l l' : List Reconstruction.State}
    {a : AllocId} {f : Reconstruction.State → Option Reconstruction.State}
    (h : updateState l a f = some l') {x : AllocId}
    (hx : x ∈ l.map (fun st => st.alloc)) : x ∈ l'.map (fun st => st.alloc) := by
  induction l generalizing l' with
  | nil => simp at hx
  | cons head tail ih =>
      simp only [updateState] at h
      by_cases hkey : head.alloc = a
      · rw [if_pos hkey] at h
        cases hf : f head with
        | none => simp [hf] at h
        | some next =>
            simp only [hf] at h
            by_cases hkey' : next.alloc = a
            · rw [if_pos hkey'] at h
              simp only [Option.some.injEq] at h
              rw [← h]
              simp only [List.map_cons, List.mem_cons] at hx ⊢
              rcases hx with hx0 | hx'
              · exact Or.inl (hx0.trans (hkey.trans hkey'.symm))
              · exact Or.inr hx'
            · rw [if_neg hkey'] at h
              simp at h
      · rw [if_neg hkey] at h
        cases hrec : updateState tail a f with
        | none => simp [hrec] at h
        | some tail' =>
            simp only [hrec] at h
            simp only [Option.some.injEq] at h
            subst l'
            rw [List.map_cons] at hx ⊢
            rcases List.mem_cons.mp hx with hx0 | hx'
            · exact List.mem_cons.mpr (Or.inl hx0)
            · exact List.mem_cons.mpr (Or.inr (ih hrec hx'))

theorem updateState_key_mem' {l l' : List Reconstruction.State} {a : AllocId}
    {f : Reconstruction.State → Option Reconstruction.State}
    (h : updateState l a f = some l') :
    a ∈ l'.map (fun st => st.alloc) := by
  induction l generalizing l' with
  | nil => simp [updateState] at h
  | cons head tail ih =>
      simp only [updateState] at h
      by_cases hkey : head.alloc = a
      · rw [if_pos hkey] at h
        cases hf : f head with
        | none => simp [hf] at h
        | some next =>
            simp only [hf] at h
            by_cases hkey' : next.alloc = a
            · rw [if_pos hkey'] at h
              simp only [Option.some.injEq] at h
              rw [← h, List.map_cons]
              exact List.mem_cons.mpr (Or.inl hkey'.symm)
            · rw [if_neg hkey'] at h
              simp at h
      · rw [if_neg hkey] at h
        cases hrec : updateState tail a f with
        | none => simp [hrec] at h
        | some tail' =>
            simp only [hrec] at h
            simp only [Option.some.injEq] at h
            subst l'
            exact List.mem_cons_of_mem head.alloc (ih hrec)

theorem State.update_allocIds_subset {s s' : Integrated.State} {a : AllocId}
    {f : Reconstruction.State → Option Reconstruction.State}
    (h : s.update a f = some s') {x : AllocId} (hx : x ∈ s'.allocIds) :
    x ∈ s.allocIds := by
  unfold Integrated.State.update at h
  cases hupd : updateState s.allocs a f with
  | none => simp [hupd] at h
  | some l' =>
      simp only [hupd, Option.map_some, Option.some.injEq] at h
      subst s'
      have hx' : x ∈ l'.map (fun st => st.alloc) := by simpa [Integrated.State.allocIds] using hx
      rcases updateState_alloc_mem hupd hx' with hmem | rfl
      · exact hmem
      · exact updateState_key_mem hupd

theorem State.update_allocIds_superset {s s' : Integrated.State} {a : AllocId}
    {f : Reconstruction.State → Option Reconstruction.State}
    (h : s.update a f = some s') {x : AllocId} (hx : x ∈ s.allocIds) :
    x ∈ s'.allocIds := by
  unfold Integrated.State.update at h
  cases hupd : updateState s.allocs a f with
  | none => simp [hupd] at h
  | some l' =>
      simp only [hupd, Option.map_some, Option.some.injEq] at h
      subst s'
      have hx' : x ∈ s.allocs.map (fun st => st.alloc) := by
        simpa [Integrated.State.allocIds] using hx
      simpa [Integrated.State.allocIds] using updateState_alloc_mem_of_mem hupd hx'

theorem State.update_key_mem' {s s' : Integrated.State} {a : AllocId}
    {f : Reconstruction.State → Option Reconstruction.State}
    (h : s.update a f = some s') : a ∈ s'.allocIds := by
  unfold Integrated.State.update at h
  cases hupd : updateState s.allocs a f with
  | none => simp [hupd] at h
  | some l' =>
      simp only [hupd, Option.map_some, Option.some.injEq] at h
      subst s'
      simpa [Integrated.State.allocIds] using updateState_key_mem' hupd

theorem findState?_updateState_self {l l' : List Reconstruction.State}
    {a : AllocId} {f : Reconstruction.State → Option Reconstruction.State}
    (h : updateState l a f = some l') {st : Reconstruction.State}
    (hst : findState? l a = some st) :
    ∃ st', f st = some st' ∧ findState? l' a = some st' := by
  induction l generalizing l' with
  | nil => simp [findState?] at hst
  | cons head tail ih =>
      unfold updateState at h
      by_cases hkey : head.alloc = a
      · rw [if_pos hkey] at h
        have hst' : st = head := by
          have hh := hst
          simp only [findState?, hkey, if_pos, Option.some.injEq] at hh
          exact hh.symm
        subst st
        cases hf : f head with
        | none => simp [hf] at h
        | some next =>
            simp only [hf] at h
            by_cases hkey' : next.alloc = a
            · rw [if_pos hkey'] at h
              simp only [Option.some.injEq] at h
              subst l'
              exact ⟨next, rfl, by simp [findState?, hkey']⟩
            · rw [if_neg hkey'] at h
              simp at h
      · rw [if_neg hkey] at h
        have hst_tail : findState? tail a = some st := by
          simpa [findState?, hkey] using hst
        cases hrec : updateState tail a f with
        | none => simp [hrec] at h
        | some tail' =>
            simp only [hrec] at h
            simp only [Option.some.injEq] at h
            subst l'
            obtain ⟨st', hf, hfind⟩ := ih hrec hst_tail
            exact ⟨st', hf, by simp [findState?, hkey, hfind]⟩

theorem State.update_find_self {s s' : Integrated.State} {a : AllocId}
    {f : Reconstruction.State → Option Reconstruction.State}
    (h : s.update a f = some s') {st : Reconstruction.State}
    (hst : s.find? a = some st) :
    ∃ st', f st = some st' ∧ s'.find? a = some st' := by
  unfold Integrated.State.update at h
  cases hupd : updateState s.allocs a f with
  | none => simp [hupd] at h
  | some l' =>
      simp only [hupd, Option.map_some, Option.some.injEq] at h
      subst s'
      exact findState?_updateState_self hupd hst

/-- A write changes only the heap, so the allocation's length is unchanged. -/
theorem State.write_len {s s' : Reconstruction.State} {id : CapId} {i : Nat}
    {v : UInt8} (h : s.write id i v = some s') : s'.len = s.len := by
  unfold Reconstruction.State.write at h
  split at h
  · simp at h
  · split at h
    · split at h
      · simp only [Option.some.injEq] at h
        subst s'
        rfl
      · simp at h
    · simp at h

/-- An accepted write preserves the map relation and frames every other
allocation's lookup and bytes. -/
theorem Rel.write {m : Map} {s s' : Integrated.State} {a : AllocId}
    {id : CapId} {i : Nat} {v : UInt8}
    (hrel : Rel m s) (h : s.exec (.write a id i v) = some s') :
    Rel m s' ∧
      (∀ b, b ≠ a → s'.find? b = s.find? b ∧
        s'.snapshot b = s.snapshot b) := by
  obtain ⟨hwf, hcovLive, hcovLen, hcovBack⟩ := hrel
  have hupd : s.update a (fun st => st.write id i v) = some s' := by
    simpa [Integrated.State.exec] using h
  refine ⟨⟨hwf, ?_, ?_, ?_⟩, ?_⟩
  · intro x hx
    exact hcovLive x (State.update_allocIds_subset hupd hx)
  · intro x w hxw
    obtain ⟨st, hfind, hlen⟩ := hcovLen x w hxw
    by_cases hxa : x = a
    · subst x
      obtain ⟨st', hwrite, hfind'⟩ := State.update_find_self hupd hfind
      have hlen' : st'.len = st.len := State.write_len hwrite
      exact ⟨st', hfind', by rw [hlen', hlen]⟩
    · exact ⟨st, by rw [State.update_frames_other hupd hxa]; exact hfind, hlen⟩
  · intro x w hxw
    by_cases hxa : x = a
    · subst x
      exact State.update_key_mem' hupd
    · have hxold : x ∈ s.allocIds := hcovBack x w hxw
      exact State.update_allocIds_superset hupd hxold
  · intro b hb
    have hfind := Integrated.State.exec_frames_other h hb
    exact ⟨hfind, by rw [Integrated.State.snapshot, Integrated.State.snapshot, hfind]⟩

/-- A command list that targets no window of an unrelated allocation preserves
the map's coverage of it and its bytes: the state still holds a component of the
window's recorded length, and its snapshot is unchanged. -/
theorem Rel.run_other {m : Map} {s s' : Integrated.State}
    {cmds : List Integrated.Cmd} (hrel : Rel m s)
    (h : Integrated.State.run s cmds = some s') {b : AllocId}
    (hmiss : ∀ c ∈ cmds, c.allocId ≠ b) :
    (∀ w, m.lookup? b = some w →
        ∃ st, s'.find? b = some st ∧ st.len = w.len) ∧
      s'.snapshot b = s.snapshot b := by
  refine ⟨?_, Integrated.State.run_snapshot_other h hmiss⟩
  intro w hw
  obtain ⟨st, hst, hlen⟩ := hrel.2.2.1 b w hw
  exact ⟨st, by rw [Integrated.State.run_frames_other h hmiss]; exact hst, hlen⟩

/-! ### The two-allocation fixture -/

def window0 : Window := { base := 4096, len := 64 }
def window3 : Window := { base := 8192, len := 32 }

def map0 : Map := Map.empty
def map1 : Map := ⟨[(⟨0⟩, window0)]⟩
def twoAllocMap : Map := ⟨[(⟨3⟩, window3), (⟨0⟩, window0)]⟩

def twoAllocState : Integrated.State :=
  { allocs :=
      [Reconstruction.State.initial ⟨3⟩ 32 32 (by decide) ⟨4⟩ ⟨5⟩,
       Reconstruction.State.initial ⟨0⟩ 64 64 (by decide) ⟨1⟩ ⟨2⟩]
    allocsIssued := [⟨3⟩, ⟨0⟩]
    issued := [⟨4⟩, ⟨5⟩, ⟨1⟩, ⟨2⟩] }

theorem map1_eq : map0.alloc ⟨0⟩ window0 = some map1 := by
  simp [map0, Map.empty, Map.alloc, map1, Map.lookup?, Map.lookupList?,
    Map.nonOverlappingB, Map.disjointB, Window.inBoundsB, Window.stop,
    show window0.base + window0.len ≤ 2 ^ 64 by simp [window0]]

theorem twoAllocMap_eq : map1.alloc ⟨3⟩ window3 = some twoAllocMap := by
  simp [map1, twoAllocMap, Map.alloc, Map.lookup?, Map.lookupList?,
    Map.nonOverlappingB, Map.disjointB, Window.inBoundsB, Window.stop,
    window0, window3,
    show (⟨0⟩ : AllocId) ≠ ⟨3⟩ by decide,
    show window3.base + window3.len ≤ 2 ^ 64 by simp [window3]]

theorem map1_wellFormed : map1.WellFormed :=
  Map.alloc_wellFormed Map.empty_wellFormed map1_eq

theorem twoAllocMap_wellFormed : twoAllocMap.WellFormed :=
  Map.alloc_wellFormed map1_wellFormed twoAllocMap_eq

theorem twoAllocMap_lookup0 : twoAllocMap.lookup? ⟨0⟩ = some window0 := by
  simp [twoAllocMap, Map.lookup?, Map.lookupList?, window0,
    show (⟨3⟩ : AllocId) ≠ ⟨0⟩ by decide]

theorem twoAllocMap_lookup3 : twoAllocMap.lookup? ⟨3⟩ = some window3 := by
  simp [twoAllocMap, Map.lookup?, Map.lookupList?, window3,
    show (⟨0⟩ : AllocId) ≠ ⟨3⟩ by decide]

theorem twoAllocMap_lookup_other {a : AllocId} (h0 : a ≠ ⟨0⟩) (h3 : a ≠ ⟨3⟩) :
    twoAllocMap.lookup? a = none := by
  simp [twoAllocMap, Map.lookup?, Map.lookupList?, Ne.symm h0, Ne.symm h3]

theorem twoAlloc_find0_len :
    (twoAllocState.find? ⟨0⟩).map Reconstruction.State.len = some 64 := by
  simp [twoAllocState, Integrated.State.find?, Integrated.findState?,
    Reconstruction.State.initial, show (⟨3⟩ : AllocId) ≠ ⟨0⟩ by decide]

theorem twoAlloc_find3_len :
    (twoAllocState.find? ⟨3⟩).map Reconstruction.State.len = some 32 := by
  simp [twoAllocState, Integrated.State.find?, Integrated.findState?,
    Reconstruction.State.initial]

theorem exists_of_map_len {o : Option Reconstruction.State} {n : Nat}
    (h : o.map Reconstruction.State.len = some n) :
    ∃ st, o = some st ∧ st.len = n := by
  cases o with
  | none => simp at h
  | some st =>
      simp only [Option.map_some, Option.some.injEq] at h
      exact ⟨st, rfl, h⟩

theorem twoAlloc_rel : Rel twoAllocMap twoAllocState := by
  refine ⟨twoAllocMap_wellFormed, ?_, ?_, ?_⟩
  · intro a ha
    simp [Integrated.State.allocIds, twoAllocState] at ha
    rcases ha with rfl | rfl
    · exact ⟨window3, twoAllocMap_lookup3⟩
    · exact ⟨window0, twoAllocMap_lookup0⟩
  · intro a w hw
    by_cases h0 : a = ⟨0⟩
    · subst a
      rw [twoAllocMap_lookup0] at hw
      have hv : w = window0 := (Option.some.inj hw).symm
      subst w
      have hlen := twoAlloc_find0_len
      obtain ⟨st, hfind, hstlen⟩ := exists_of_map_len hlen
      exact ⟨st, hfind, by simpa [window0] using hstlen⟩
    · by_cases h3 : a = ⟨3⟩
      · subst a
        rw [twoAllocMap_lookup3] at hw
        have hv : w = window3 := (Option.some.inj hw).symm
        subst w
        have hlen := twoAlloc_find3_len
        obtain ⟨st, hfind, hstlen⟩ := exists_of_map_len hlen
        exact ⟨st, hfind, by simpa [window3] using hstlen⟩
      · rw [twoAllocMap_lookup_other h0 h3] at hw
        simp at hw
  · intro a w hw
    by_cases h0 : a = ⟨0⟩
    · subst a
      simp only [Integrated.State.allocIds, twoAllocState]
      exact List.mem_cons_of_mem _ List.mem_cons_self
    · by_cases h3 : a = ⟨3⟩
      · subst a
        simp only [Integrated.State.allocIds, twoAllocState]
        exact List.mem_cons_self
      · rw [twoAllocMap_lookup_other h0 h3] at hw
        simp at hw

def exampleWrite : Integrated.Cmd := .write ⟨0⟩ ⟨1⟩ 5 9

/-- Writing allocation `⟨0⟩` leaves allocation `⟨3⟩`'s lookup and bytes as they
were, and the map still gives `⟨3⟩` its window. -/
theorem example_write_other {s' : Integrated.State}
    (h : twoAllocState.exec exampleWrite = some s') :
    s'.find? ⟨3⟩ = twoAllocState.find? ⟨3⟩ ∧
      s'.snapshot ⟨3⟩ = twoAllocState.snapshot ⟨3⟩ ∧
      twoAllocMap.lookup? ⟨3⟩ = some window3 := by
  have hframe := Integrated.State.exec_frames_other h (b := ⟨3⟩) (by decide)
  refine ⟨hframe, ?_, twoAllocMap_lookup3⟩
  rw [Integrated.State.snapshot, Integrated.State.snapshot, hframe]

theorem example_window_addr :
    twoAllocMap.addr? ⟨0⟩ 5 = some 4101 := by
  rw [Map.addr?_some_of_within twoAllocMap_lookup0 (by simp [window0])]
  simp [window0]

/-- The `⟨3⟩` component of the two-allocation fixture is a fresh whole
allocation. -/
theorem twoAlloc_find3 :
    twoAllocState.find? ⟨3⟩ =
      some (Reconstruction.State.initial ⟨3⟩ 32 32 (by decide) ⟨4⟩ ⟨5⟩) := by
  simp [twoAllocState, Integrated.State.find?, Integrated.findState?,
    Reconstruction.State.initial]

/-- A command list that targets only allocation `⟨0⟩`: two writes through its
root capability. -/
def exampleRun : List Integrated.Cmd :=
  [ .write ⟨0⟩ ⟨1⟩ 0 11,
    .write ⟨0⟩ ⟨1⟩ 63 12 ]

/-- No command of the list targets allocation `⟨3⟩`. -/
theorem exampleRun_untargeted :
    ∀ c ∈ exampleRun, c.allocId ≠ (⟨3⟩ : AllocId) := by
  intro c hc
  simp only [exampleRun, List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> decide

/-- A command list that targets only `⟨0⟩` frames `⟨3⟩` across the whole run: its
component, bytes and `Storage` certificate are unchanged, and the map still gives
it a window of its recorded length. -/
theorem example_run_other {s' : Integrated.State}
    (h : Integrated.State.run twoAllocState exampleRun = some s') :
    s'.find? ⟨3⟩ = twoAllocState.find? ⟨3⟩ ∧
      s'.snapshot ⟨3⟩ = twoAllocState.snapshot ⟨3⟩ ∧
      (∃ st, s'.find? ⟨3⟩ = some st ∧ st.Storage) ∧
      (∀ w, twoAllocMap.lookup? ⟨3⟩ = some w →
        ∃ st, s'.find? ⟨3⟩ = some st ∧ st.len = w.len) := by
  have hframe := Integrated.State.run_frames_other h exampleRun_untargeted
  have hrel := Rel.run_other twoAlloc_rel h exampleRun_untargeted
  refine ⟨hframe, hrel.2, ?_, hrel.1⟩
  have hstorage :
      (Reconstruction.State.initial ⟨3⟩ 32 32 (by decide) ⟨4⟩ ⟨5⟩).Storage :=
    Reconstruction.State.initial_storage ⟨3⟩ 32 32 (by decide) ⟨4⟩ ⟨5⟩
  exact ⟨_, by rw [hframe, twoAlloc_find3], hstorage⟩

theorem example_addr_lt :
    ∀ {a : AllocId} {off x : Nat}, twoAllocMap.addr? a off = some x → x < 2 ^ 64 :=
  fun hx => Map.addr?_lt twoAllocMap_wellFormed.2.2 hx

/-! ### Refused controls -/

/-- A window overlapping a live one is refused. -/
theorem overlapping_alloc_refused :
    (twoAllocMap.alloc ⟨9⟩ { base := 4128, len := 16 }).isNone = true := by
  have hov : ¬ ({ base := 4128, len := 16 } : Window).Disjoint window0 := by
    intro hd
    have hb : Map.disjointB ({ base := 4128, len := 16 } : Window) window0 = true :=
      Map.disjointB_eq_true.mpr hd
    simpa [Map.disjointB, Window.stop, window0] using hb
  rw [Map.alloc_refuses_overlap twoAllocMap_lookup0 hov]
  rfl

/-- A missing live window produces no address. -/
theorem missing_window_addr_none : twoAllocMap.addr? ⟨9⟩ 0 = none := by
  exact Map.addr?_none_of_lookup_none
    (twoAllocMap_lookup_other (show (⟨9⟩ : AllocId) ≠ ⟨0⟩ by decide)
      (show (⟨9⟩ : AllocId) ≠ ⟨3⟩ by decide))

theorem missing_window_withinB_false : twoAllocMap.withinB ⟨9⟩ 0 = false := by
  simp [Map.withinB,
    twoAllocMap_lookup_other (show (⟨9⟩ : AllocId) ≠ ⟨0⟩ by decide)
      (show (⟨9⟩ : AllocId) ≠ ⟨3⟩ by decide)]

/-- An offset at the window's end is outside it. -/
theorem out_of_window_addr_none : twoAllocMap.addr? ⟨0⟩ 64 = none := by
  exact Map.addr?_none_of_out_of_window twoAllocMap_lookup0 (by simp [window0])

theorem out_of_window_withinB_false : twoAllocMap.withinB ⟨0⟩ 64 = false := by
  simp [Map.withinB, twoAllocMap_lookup0, window0]

/-- An unbounded window is refused by `alloc`. -/
theorem unbounded_alloc_refused :
    (twoAllocMap.alloc ⟨9⟩ { base := 2 ^ 64, len := 1 }).isNone = true := by
  have h : ¬ ({ base := 2 ^ 64, len := 1 } : Window).inBounds := by
    simp [Window.inBounds]
  rw [Map.alloc_refuses_unbounded h]
  rfl

end AddressMap
end Cap
