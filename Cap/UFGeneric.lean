/-
General full-path union-find through the sealed boundary.

This module replaces the concrete two-call fixture as the *statement* of the
union-find result. The fixture in `Cap/UFIntegrated.lean` is an instance of the
theorems here; the algorithm, its representation relation and every preservation
claim are general over an arbitrary represented parent array.

### The completion contract

`chase?` is a *bounded* chase and says so: it returns `some (root, path)` only
when the parent reads reach a fixed point, and `none` when the fuel runs out (or
a parent is unreadable). It never reports `(x, [])` for a chase that stopped
merely because its fuel did. `chase?_none_iff` states the contract exactly: on a
represented, in-range, bounded array the bounded chase returns `none` precisely
when the functional chase has no root within that fuel, and `chase?_some_spec`
says any `some` result is the functional chase's root and path at the same fuel.
`chase?_eq_ranked` then shows a ranked forest's rank bound always completes the
chase, so a *verified* caller never sees the exhausted outcome.

### The representation and the read half

`decode` reads a byte buffer as a parent array, so a represented array's values
are below 256. `Rep s a p` says the allocation's snapshot decodes to `p`;
`Rep.read` derives the read-agreement premise from the representation itself, and
`Rep.snapshot_eq` reads the exact bytes back. Reads go through `Sealed.read?`,
which is the heap's index read: it checks only that the allocation exists and the
offset is in bounds, so the read half of this algorithm is *not*
capability-checked. Writes do carry capability evidence: `Writable` is the whole
active read--write fragment covering the allocation, and `Writable.write_exists`
derives acceptance from it.

### The write half

`sealed_write_component`, `sealed_write_snapshot_self` and `sealed_write_frames`
are the general single-write laws: an accepted `Sealed.write` replaces exactly
that allocation's buffer with the byte update, keeps its length and every
ownership record, and frames every other allocation's full component state, so
its bytes, authority, retired names and outstanding obligations are unchanged
too, while every allocation's authority, retired names and obligations survive.
`compressPath_spec` lifts the law over the whole compression path by induction,
and `sealedFind_spec` combines it with the chase correspondence to establish, for
an arbitrary represented ranked forest:

* the root is `UF.findRootF`'s root and is a fixed point;
* the post-buffer represents exactly `UF.compressAll p root (rootPath …)`;
* the represented array stays ranked, acyclic and in range, and `UF.Same` is
  preserved in both directions;
* the successor state satisfies `State.Inv` and `Writable`, so a second call's
  preconditions are the first call's conclusions (`findRanked_twice`);
* every unrelated allocation's full `Reconstruction.State` — hence its bytes,
  `Storage` certificate and, where an address map relates to the state, its
  window — and every allocation's authority, retired names and return
  obligations are framed (`WriteFrame`, `WriteFrame.rel_write`).

### What is not claimed

The representation is one byte per parent, so it needs `n ≤ 256`; the size limit
is explicit in `Precondition.fits` and no large-scale union-find performance is
claimed. The read interface permits unrestricted observation, as said above.
A single accepted write frames an unrelated allocation's full component, so that
allocation's `Reconstruction.State` and its `Storage` certificate are exactly
what they were, and where an address map relates to the state the map still
covers the successor and the other allocation's window and bytes are unchanged.
The command-list form of that frame is proved at the integrated boundary
(`State.run_frames_other`, and `Sealed.run_frames_other` with its
`Sealed.RunFrame`). What remains is the compiled-bridge connection: the
address-map relation here is a logical window assignment, not a loader's
assignment for the compiled kernel, and nothing in the bridge imports it; the
ABI, a loader and native execution are not claimed.
-/
import Cap.Sealed
import Cap.AddressMap
import Cap.UFReuseRunner

namespace Cap

/-! ### Bridge lemmas from the sealed observations to the state projection -/

theorem sealed_snapshot_state (s : Sealed) (a : AllocId) :
    s.snapshot a = s.state.snapshot a := rfl

theorem sealed_read_state (s : Sealed) (a : AllocId) (i : Nat) :
    s.read? a i = s.state.read? a i := rfl

theorem sealed_authority_state (s : Sealed) (a : AllocId) (id : CapId) :
    s.authority? a id = s.state.authority? a id := rfl

theorem sealed_retired_state (s : Sealed) (b : AllocId) :
    s.retiredOf b = s.state.retiredOf b := rfl

theorem sealed_restores_state (s : Sealed) (b : AllocId) :
    s.restoresOf b = s.state.restoresOf b := rfl

theorem sealed_allocations_state (s : Sealed) :
    s.allocations = s.state.allocIds := rfl

/-! ### Heap and component laws for one accepted write -/

/-- A snapshot fixes every read: an in-range offset reads the snapshot's byte. -/
theorem state_read?_snapshot {s : Integrated.State} {a : AllocId} {i : Nat}
    {bs : List UInt8} (h : s.snapshot a = some bs) : s.read? a i = bs[i]? := by
  cases hfind : s.find? a with
  | none => simp [Integrated.State.snapshot, hfind] at h
  | some st =>
      have hlook : st.heap.lookup? st.alloc = some bs := by
        simpa [Integrated.State.snapshot, hfind, Heap.snapshot?] using h
      simp [Integrated.State.read?, hfind, Heap.read?, hlook]

/-- A heap write replaces that allocation's buffer by the byte update. -/
theorem heap_write_lookup {h h' : Heap} {a : AllocId} {i : Nat} {v : UInt8}
    (hw : h.write? a i v = some h') :
    h'.lookup? a = (h.lookup? a).map (fun xs => xs.set i v) := by
  unfold Heap.write? at hw
  split at hw
  · simp at hw
  · rename_i xs hlook
    split at hw
    · rename_i hlt
      simp only [Option.some.injEq] at hw
      subst hw
      change Heap.lookupList? (Heap.updateList h.bufs a (xs.set i v)) a =
        Option.map (fun xs => xs.set i v) (Heap.lookupList? h.bufs a)
      rw [Heap.lookupList?_updateList h.bufs hlook]
      have hlook' : Heap.lookupList? h.bufs a = some xs := hlook
      rw [hlook']
      rfl
    · simp at hw

/-- Updating one key's buffer leaves every other key's lookup alone. -/
theorem heap_lookupList?_updateList_ne :
    ∀ (l : List (AllocId × List UInt8)) {a b : AllocId} {w : List UInt8},
      b ≠ a → Heap.lookupList? (Heap.updateList l a w) b = Heap.lookupList? l b
  | [], _, _, _, hba => by
      simp [Heap.updateList, Heap.lookupList?, Ne.symm hba]
  | (k, v) :: rest, a, b, w, hba => by
      by_cases hk : k = a
      · subst hk
        simp [Heap.updateList, Heap.lookupList?, Ne.symm hba]
      · by_cases hkb : k = b
        · subst hkb
          simp [Heap.updateList, Heap.lookupList?, hk]
        · simp only [Heap.updateList, if_neg hk, Heap.lookupList?, if_neg hkb]
          exact heap_lookupList?_updateList_ne rest hba

/-- A heap write frames every other allocation's buffer. -/
theorem heap_write_lookup_ne {h h' : Heap} {a b : AllocId} {i : Nat} {v : UInt8}
    (hw : h.write? a i v = some h') (hba : b ≠ a) :
    h'.lookup? b = h.lookup? b := by
  unfold Heap.write? at hw
  split at hw
  · simp at hw
  · rename_i xs hlook
    split at hw
    · rename_i hlt
      simp only [Option.some.injEq] at hw
      subst hw
      have hlook' : Heap.lookupList? h.bufs a = some xs := hlook
      exact heap_lookupList?_updateList_ne h.bufs hba
    · simp at hw

/-- A leaf is found by its own identifier. -/
theorem Reconstruction.Forest.findLeaf?_leaf {c : Leaf} {id : CapId} (h : c.id = id) :
    Reconstruction.Forest.findLeaf? id (.leaf c) = some c := by
  simp [Reconstruction.Forest.findLeaf?, h]

/-- The component operation a write performs: an accepted write names the current
leaf, checks its whole-share read--write guard, writes the heap and changes
nothing else. -/
theorem Reconstruction.State.write_component {st st' : Reconstruction.State}
    {id : CapId} {i : Nat} {v : UInt8} (h : st.write id i v = some st') :
    ∃ (c : Leaf) (h' : Heap), st.forest.findLeaf? id = some c ∧
      c.state = CapState.active ∧ c.q = st.D ∧ c.ceiling = Ceiling.readWrite ∧
      c.lo ≤ i ∧ i < c.hi ∧ st.heap.write? st.alloc i v = some h' ∧
      st' = { st with heap := h' } ∧ c.alloc = st.alloc := by
  unfold Reconstruction.State.write at h
  split at h
  · simp at h
  · rename_i c hfind
    by_cases hguard : st.WriteGuard c i
    · rw [dif_pos hguard] at h
      split at h
      · rename_i h' hw
        simp only [Option.some.injEq] at h
        exact ⟨c, h', hfind, hguard.1, hguard.2.1, hguard.2.2.1,
          hguard.2.2.2.2.1, hguard.2.2.2.2.2, hw, h.symm, hguard.2.2.2.1⟩
      · simp at h
    · rw [dif_neg hguard] at h
      simp at h

/-! ### Update laws for the multi-allocation state -/

theorem Integrated.findState?_updateState_self {l l' : List Reconstruction.State}
    {a : AllocId} {f : Reconstruction.State → Option Reconstruction.State}
    (h : Integrated.updateState l a f = some l') :
    Integrated.findState? l' a = (Integrated.findState? l a).bind f := by
  induction l generalizing l' with
  | nil => simp [Integrated.updateState] at h
  | cons head tail ih =>
      simp only [Integrated.updateState] at h
      by_cases hkey : head.alloc = a
      · rw [if_pos hkey] at h
        cases hf : f head with
        | none => simp [hf] at h
        | some next =>
            simp only [hf] at h
            by_cases hkey' : next.alloc = a
            · rw [if_pos hkey'] at h
              simp only [Option.some.injEq] at h
              subst h
              simp [Integrated.findState?, hkey, hkey', hf]
            · rw [if_neg hkey'] at h
              simp at h
      · rw [if_neg hkey] at h
        cases hrec : Integrated.updateState tail a f with
        | none => simp [hrec] at h
        | some tail' =>
            simp only [hrec] at h
            simp only [Option.some.injEq] at h
            subst h
            simp only [Integrated.findState?, hkey, if_false]
            exact ih hrec

theorem Integrated.findState?_updateState_some {l l' : List Reconstruction.State}
    {a : AllocId} {f : Reconstruction.State → Option Reconstruction.State}
    (h : Integrated.updateState l a f = some l')
    {st : Reconstruction.State} (hfind : Integrated.findState? l a = some st) :
    ∃ st', f st = some st' := by
  induction l generalizing l' with
  | nil => simp [Integrated.findState?] at hfind
  | cons head tail ih =>
      simp only [Integrated.updateState] at h
      by_cases hkey : head.alloc = a
      · rw [if_pos hkey] at h
        have hst0 : head = st := by
          simpa [Integrated.findState?, hkey] using hfind
        have hst : st = head := hst0.symm
        rw [hst]
        cases hf : f head with
        | none => simp [hf] at h
        | some next => exact ⟨next, rfl⟩
      · rw [if_neg hkey] at h
        have hfind' : Integrated.findState? tail a = some st := by
          simpa [Integrated.findState?, hkey] using hfind
        cases hrec : Integrated.updateState tail a f with
        | none => simp [hrec] at h
        | some tail' => exact ih hrec hfind'

theorem Integrated.updateState_none_of_find_none {l : List Reconstruction.State}
    {a : AllocId} {f : Reconstruction.State → Option Reconstruction.State}
    (h : Integrated.findState? l a = none) : Integrated.updateState l a f = none := by
  induction l with
  | nil => rfl
  | cons head tail ih =>
      by_cases hkey : head.alloc = a
      · simp [Integrated.findState?, hkey] at h
      · simp only [Integrated.updateState, Integrated.findState?, hkey, if_false] at h ⊢
        simp only [ih h]

theorem Integrated.updateState_exists {l : List Reconstruction.State} {a : AllocId}
    {f : Reconstruction.State → Option Reconstruction.State}
    {st st' : Reconstruction.State} (hfind : Integrated.findState? l a = some st)
    (hf : f st = some st') (halt : st'.alloc = a) :
    ∃ l', Integrated.updateState l a f = some l' := by
  induction l with
  | nil => simp [Integrated.findState?] at hfind
  | cons head tail ih =>
      by_cases hkey : head.alloc = a
      · have hst0 : head = st := by
          simpa [Integrated.findState?, hkey] using hfind
        have hst : st = head := hst0.symm
        rw [hst] at hf
        refine ⟨st' :: tail, ?_⟩
        simp only [Integrated.updateState, if_pos hkey, hf, if_pos halt]
      · have hfind' : Integrated.findState? tail a = some st := by
          simpa [Integrated.findState?, hkey] using hfind
        obtain ⟨tail', hrec⟩ := ih hfind'
        refine ⟨head :: tail', ?_⟩
        simp only [Integrated.updateState, if_neg hkey, hrec]

theorem Integrated.updateState_allocIds {l l' : List Reconstruction.State}
    {a : AllocId} {f : Reconstruction.State → Option Reconstruction.State}
    (h : Integrated.updateState l a f = some l') :
    l'.map (fun st => st.alloc) = l.map (fun st => st.alloc) := by
  induction l generalizing l' with
  | nil => simp [Integrated.updateState] at h
  | cons head tail ih =>
      simp only [Integrated.updateState] at h
      by_cases hkey : head.alloc = a
      · rw [if_pos hkey] at h
        cases hf : f head with
        | none => simp [hf] at h
        | some next =>
            simp only [hf] at h
            by_cases hnext : next.alloc = a
            · rw [if_pos hnext] at h
              simp only [Option.some.injEq] at h
              subst h
              simp only [List.map_cons]
              rw [hnext, hkey]
            · rw [if_neg hnext] at h
              simp at h
      · rw [if_neg hkey] at h
        cases hrec : Integrated.updateState tail a f with
        | none => simp [hrec] at h
        | some tail' =>
            simp only [hrec] at h
            simp only [Option.some.injEq] at h
            subst h
            simp only [List.map_cons]
            rw [ih hrec]

theorem Integrated.State.update_find_self {s s' : Integrated.State} {a : AllocId}
    {f : Reconstruction.State → Option Reconstruction.State}
    (h : s.update a f = some s') : s'.find? a = (s.find? a).bind f := by
  unfold Integrated.State.update at h
  cases hupd : Integrated.updateState s.allocs a f with
  | none => simp [hupd] at h
  | some l' =>
      simp only [hupd, Option.map_some, Option.some.injEq] at h
      subst h
      exact Integrated.findState?_updateState_self hupd

theorem Integrated.State.update_allocIds {s s' : Integrated.State} {a : AllocId}
    {f : Reconstruction.State → Option Reconstruction.State}
    (h : s.update a f = some s') : s'.allocIds = s.allocIds := by
  unfold Integrated.State.update at h
  cases hupd : Integrated.updateState s.allocs a f with
  | none => simp [hupd] at h
  | some l' =>
      simp only [hupd, Option.map_some, Option.some.injEq] at h
      subst h
      exact Integrated.updateState_allocIds hupd

/-! ### The general single-write law -/

/-- An accepted sealed write acts on exactly one component and returns the state
that component operation produced. -/
theorem sealed_write_component {s s' : Sealed} {a : AllocId} {id : CapId}
    {i : Nat} {v : UInt8} (h : Sealed.write s a id i v = .ok s') :
    ∃ (st st' : Reconstruction.State), s.state.find? a = some st ∧
      st.write id i v = some st' ∧ s'.state.find? a = some st' := by
  have hexec : s.state.exec (.write a id i v) = some s'.state :=
    (Integrated.Sealed.write_ok_iff s a id i v s').mp h
  have hupd : s.state.update a (fun st => st.write id i v) = some s'.state := by
    simpa [Integrated.State.exec] using hexec
  have hfind := Integrated.State.update_find_self hupd
  cases hfa : s.state.find? a with
  | none =>
      have hnone : Integrated.updateState s.state.allocs a
          (fun st => st.write id i v) = none :=
        Integrated.updateState_none_of_find_none hfa
      unfold Integrated.State.update at hupd
      rw [hnone] at hupd
      simp at hupd
  | some st =>
      have hsome : ∃ st', st.write id i v = some st' := by
        cases hrec : Integrated.updateState s.state.allocs a
            (fun st => st.write id i v) with
        | none =>
            unfold Integrated.State.update at hupd
            rw [hrec] at hupd
            simp at hupd
        | some l' => exact Integrated.findState?_updateState_some hrec hfa
      obtain ⟨st', hw⟩ := hsome
      refine ⟨st, st', rfl, hw, ?_⟩
      rw [hfa] at hfind
      simp only [Option.bind_some] at hfind
      rw [hw] at hfind
      exact hfind

/-- An accepted sealed write replaces that allocation's bytes by the byte
update. -/
theorem sealed_write_snapshot_self {s s' : Sealed} {a : AllocId} {id : CapId}
    {i : Nat} {v : UInt8} (h : Sealed.write s a id i v = .ok s') :
    s'.snapshot a = (s.snapshot a).map (fun xs => xs.set i v) := by
  obtain ⟨st, st', hfa, hw, hfind'⟩ := sealed_write_component h
  obtain ⟨c, h', -, -, -, -, -, -, hheapw, hst', -⟩ :=
    Reconstruction.State.write_component hw
  subst hst'
  have hstate : s'.state.snapshot a =
      (s.state.snapshot a).map (fun xs => xs.set i v) := by
    simp only [Integrated.State.snapshot, hfind', hfa, Option.map_some,
      Heap.snapshot?]
    rw [heap_write_lookup hheapw]
  rwa [sealed_snapshot_state, sealed_snapshot_state]

/-- What one accepted sealed write leaves alone: every other allocation's full
component state, every allocation's ownership observations, and the live list. -/
structure WriteFrame (s s' : Sealed) (a : AllocId) : Prop where
  /-- Every other allocation's component is unchanged: its byte heap, forest,
  histories and outstanding obligations are the same `Reconstruction.State`. -/
  component : ∀ b : AllocId, b ≠ a → s'.state.find? b = s.state.find? b
  authority : ∀ (b : AllocId) (id' : CapId), s'.authority? b id' = s.authority? b id'
  retired : ∀ b : AllocId, s'.retiredOf b = s.retiredOf b
  restores : ∀ b : AllocId, s'.restoresOf b = s.restoresOf b
  allocations : s'.allocations = s.allocations

/-- The component frame fixes every other allocation's bytes: a snapshot is a
projection of that allocation's component state. -/
theorem WriteFrame.snapshot_other {s s' : Sealed} {a : AllocId}
    (h : WriteFrame s s' a) (b : AllocId) (hb : b ≠ a) :
    s'.snapshot b = s.snapshot b := by
  rw [sealed_snapshot_state, sealed_snapshot_state]
  simp only [Integrated.State.snapshot]
  rw [h.component b hb]

/-- An unrelated allocation's component, if present, is the same component after
the write: its full `Reconstruction.State` is unchanged. -/
theorem WriteFrame.component_other {s s' : Sealed} {a b : AllocId}
    (h : WriteFrame s s' a) (hb : b ≠ a) {st : Reconstruction.State}
    (hst : s.state.find? b = some st) : s'.state.find? b = some st := by
  rw [h.component b hb, hst]

/-- An unrelated allocation's `Storage` certificate is unchanged: the successor
holds a component with `Storage` exactly when the predecessor does. -/
theorem WriteFrame.storage_other {s s' : Sealed} {a b : AllocId}
    (h : WriteFrame s s' a) (hb : b ≠ a) :
    (∃ st, s'.state.find? b = some st ∧ st.Storage) ↔
      (∃ st, s.state.find? b = some st ∧ st.Storage) := by
  constructor
  · rintro ⟨st, hst, hstorage⟩
    exact ⟨st, by rw [← h.component b hb]; exact hst, hstorage⟩
  · rintro ⟨st, hst, hstorage⟩
    exact ⟨st, by rw [h.component b hb, hst], hstorage⟩

/-- The identity frame. -/
theorem WriteFrame.refl (s : Sealed) (a : AllocId) : WriteFrame s s a :=
  ⟨fun _ _ => rfl, fun _ _ => rfl, fun _ => rfl, fun _ => rfl, rfl⟩

/-- Frames compose along two calls. -/
theorem WriteFrame.trans {s₁ s₂ s₃ : Sealed} {a : AllocId}
    (h₁ : WriteFrame s₁ s₂ a) (h₂ : WriteFrame s₂ s₃ a) :
    WriteFrame s₁ s₃ a :=
  ⟨fun b hb => (h₂.component b hb).trans (h₁.component b hb),
   fun b id' => (h₂.authority b id').trans (h₁.authority b id'),
   fun b => (h₂.retired b).trans (h₁.retired b),
   fun b => (h₂.restores b).trans (h₁.restores b),
   h₂.allocations.trans h₁.allocations⟩

/-- An accepted sealed write frames every other allocation's full component
state and every allocation's ownership observations. -/
theorem sealed_write_frames {s s' : Sealed} {a : AllocId} {id : CapId}
    {i : Nat} {v : UInt8} (h : Sealed.write s a id i v = .ok s') :
    WriteFrame s s' a := by
  obtain ⟨st, st', hfa, hw, hfind'⟩ := sealed_write_component h
  obtain ⟨_, _, _, _, _, _, _, _, _, hst', _⟩ :=
    Reconstruction.State.write_component hw
  subst hst'
  have hexec : s.state.exec (.write a id i v) = some s'.state :=
    (Integrated.Sealed.write_ok_iff s a id i v s').mp h
  have hupd : s.state.update a (fun st => st.write id i v) = some s'.state := by
    simpa [Integrated.State.exec] using hexec
  have hframe : ∀ b, b ≠ a → s'.state.find? b = s.state.find? b :=
    fun b hb => Integrated.State.update_frames_other hupd hb
  have hauth : ∀ b id', s'.state.authority? b id' = s.state.authority? b id' := by
    intro b id'
    by_cases hb : b = a
    · subst hb
      simp only [Integrated.State.authority?, hfind', hfa]
      rfl
    · simp only [Integrated.State.authority?, hframe b hb]
  have hret : ∀ b, s'.state.retiredOf b = s.state.retiredOf b := by
    intro b
    by_cases hb : b = a
    · subst hb
      simp only [Integrated.State.retiredOf, hfind', hfa]
    · simp only [Integrated.State.retiredOf, hframe b hb]
  have hres : ∀ b, s'.state.restoresOf b = s.state.restoresOf b := by
    intro b
    by_cases hb : b = a
    · subst hb
      simp only [Integrated.State.restoresOf, hfind', hfa]
    · simp only [Integrated.State.restoresOf, hframe b hb]
  refine ⟨hframe, ?_, ?_, ?_, ?_⟩
  · intro b id'
    rw [sealed_authority_state, sealed_authority_state]
    exact hauth b id'
  · intro b
    rw [sealed_retired_state, sealed_retired_state]
    exact hret b
  · intro b
    rw [sealed_restores_state, sealed_restores_state]
    exact hres b
  · rw [sealed_allocations_state, sealed_allocations_state]
    exact Integrated.State.update_allocIds hupd

/-- An accepted sealed write preserves the address map's relation to the state
and leaves an unrelated allocation's window and bytes unchanged: the map still
names a window of that allocation's length, and its snapshot is the same. -/
theorem WriteFrame.rel_write {m : AddressMap.Map} {s s' : Sealed} {a : AllocId}
    {id : CapId} {i : Nat} {v : UInt8} (h : Sealed.write s a id i v = .ok s')
    (hrel : AddressMap.Rel m s.state) :
    AddressMap.Rel m s'.state ∧ WriteFrame s s' a ∧
      ∀ (b : AllocId) (w : AddressMap.Window), b ≠ a → m.lookup? b = some w →
        (∃ st, s'.state.find? b = some st ∧ st.len = w.len) ∧
          s'.snapshot b = s.snapshot b := by
  have hexec : s.state.exec (.write a id i v) = some s'.state :=
    (Integrated.Sealed.write_ok_iff s a id i v s').mp h
  have hrelw := AddressMap.Rel.write hrel hexec
  have hrel' : AddressMap.Rel m s'.state := hrelw.1
  have hcovLen : ∀ (x : AllocId) (w : AddressMap.Window), m.lookup? x = some w →
      ∃ st, s'.state.find? x = some st ∧ st.len = w.len := hrel'.2.2.1
  have hframe : WriteFrame s s' a := sealed_write_frames h
  refine ⟨hrel', hframe, ?_⟩
  intro b w hb hw
  obtain ⟨st, hst, hlen⟩ := hcovLen b w hw
  exact ⟨⟨st, hst, hlen⟩, hframe.snapshot_other b hb⟩

namespace UFGeneric

open UF

/-! ### The representation relation -/

/-- The parent array a byte buffer encodes. -/
def decode (bs : List UInt8) : UF.Arr := bs.map UInt8.toNat

/-- Every entry of a parent array fits in one byte. -/
def FitsBytes (arr : UF.Arr) : Prop := ∀ x ∈ arr, x < 256

/-- One sealed allocation represents a parent array when its bytes decode to that
array. Because the bytes are `UInt8`, a represented array's in-range values are
below 256 and its length is the buffer's. -/
def Rep (s : Sealed) (a : AllocId) (arr : UF.Arr) : Prop :=
  ∃ bs, s.snapshot a = some bs ∧ decode bs = arr

/-- A represented array has no value outside the byte range. -/
theorem Rep.fits {s : Sealed} {a : AllocId} {arr : UF.Arr} (h : Rep s a arr) :
    FitsBytes arr := by
  obtain ⟨bs, -, hdec⟩ := h
  intro x hx
  have hx' : x ∈ decode bs := by rw [hdec]; exact hx
  unfold decode at hx'
  obtain ⟨b, -, hb⟩ := List.mem_map.mp hx'
  rw [← hb]
  exact b.toNat_lt_size

/-- A decoded list determines its bytes when every entry fits. -/
theorem eq_map_ofNat_of_map_toNat {bs : List UInt8} {arr : UF.Arr}
    (h : bs.map UInt8.toNat = arr) : bs = arr.map UInt8.ofNat := by
  induction bs generalizing arr with
  | nil =>
      have : arr = [] := by simpa using h.symm
      simp [this]
  | cons b bs ih =>
      cases arr with
      | nil => simp at h
      | cons x xs =>
          simp only [List.map_cons, List.cons.injEq] at h
          obtain ⟨hx, htail⟩ := h
          have hb : UInt8.ofNat x = b := by
            rw [← hx]
            exact UInt8.ofNat_toNat
          rw [List.map_cons, ← hb, ih htail]

/-- A represented array is read back exactly: the snapshot is the natural-number
encoding of the array. -/
theorem Rep.snapshot_eq {s : Sealed} {a : AllocId} {arr : UF.Arr}
    (h : Rep s a arr) (hf : FitsBytes arr) :
    s.snapshot a = some (arr.map UInt8.ofNat) := by
  obtain ⟨bs, hsnap, hdec⟩ := h
  have hbs : bs = arr.map UInt8.ofNat := eq_map_ofNat_of_map_toNat hdec
  rw [hbs] at hsnap
  exact hsnap

/-- Read one parent pointer through the sealed boundary. This is the heap's
index read: it checks that the allocation is present and the offset in bounds,
not that the caller holds a capability for it. -/
def readParent? (s : Sealed) (a : AllocId) (x : Nat) : Option Nat :=
  (s.read? a x).map (fun b => b.toNat)

/-- The read agreement a chase needs is a consequence of the representation, not
a separate premise. -/
theorem Rep.read {s : Sealed} {a : AllocId} {p : UF.Arr} (h : Rep s a p) :
    ∀ i, i < p.length → readParent? s a i = some (UF.step p i) := by
  obtain ⟨bs, hsnap, hdec⟩ := h
  have hlen : p.length = bs.length := by rw [← hdec]; simp [decode]
  intro i hi
  have hib : i < bs.length := by omega
  have hread : s.read? a i = bs[i]? := state_read?_snapshot hsnap
  have hb : bs[i]? = some bs[i] := List.getElem?_eq_getElem hib
  have hstep : UF.step p i = (bs[i]).toNat := by
    show p.getD i i = (bs[i]).toNat
    rw [List.getD_eq_getElem?_getD, ← hdec]
    simp only [decode, List.getElem?_map, hb, Option.map_some]
    rfl
  unfold readParent?
  rw [hread, hb]
  simp [hstep]

/-! ### The bounded chase and its completion contract -/

/-- Chase from `x` through the bytes of one allocation. `some (root, path)` means
the reads reached a fixed point `root`; `none` means the fuel ran out (or a read
failed). Exhaustion is never reported as a successful root find. -/
def chase? (s : Sealed) (a : AllocId) : Nat → Nat → Option (Nat × List Nat)
  | 0, _ => none
  | fuel + 1, x =>
      match readParent? s a x with
      | none => none
      | some y =>
          if y = x then some (x, [])
          else
            match chase? s a fuel y with
            | none => none
            | some (r, path) => some (r, x :: path)

/-- A completed chase is the functional root search: under agreement and bound
premises, a chase that reaches a fixed point within the fuel returns exactly
`UF.findRootF` and `rootPath` at that fuel. -/
theorem chase?_eq_of_stops {s : Sealed} {a : AllocId} {p : UF.Arr}
    (hread : ∀ i, i < p.length → readParent? s a i = some (UF.step p i))
    (hbound : ∀ i, i < p.length → UF.step p i < p.length) :
    ∀ (fuel x : Nat), x < p.length → UF.StopsAt p fuel x →
      chase? s a fuel x = some (UF.findRootF p fuel x, rootPath p fuel x) := by
  intro fuel
  induction fuel with
  | zero => intro x _ hstop; exact absurd hstop (UF.stopsAt_zero p x)
  | succ fuel ih =>
      intro x hx hstop
      rw [chase?, hread x hx, UF.findRootF_succ, rootPath]
      dsimp only
      rcases (UF.stopsAt_succ p fuel x).mp hstop with hroot | ⟨hnotroot, htail⟩
      · have hroot' : UF.step p x = x := hroot
        rw [if_pos hroot', if_pos hroot', if_pos hroot']
      · have hnr : ¬ (UF.step p x = x) := fun h => hnotroot h
        rw [if_neg hnr, if_neg hnr, if_neg hnr]
        rw [ih (UF.step p x) (hbound x hx) htail]

/-- A chase result is a completed functional chase: its root and path are
`UF.findRootF` and `rootPath`, and the functional search stops within the fuel. -/
theorem chase?_some_spec {s : Sealed} {a : AllocId} {p : UF.Arr}
    (hread : ∀ i, i < p.length → readParent? s a i = some (UF.step p i))
    (hbound : ∀ i, i < p.length → UF.step p i < p.length) :
    ∀ (fuel x r : Nat) (path : List Nat), x < p.length →
      chase? s a fuel x = some (r, path) →
      r = UF.findRootF p fuel x ∧ path = rootPath p fuel x ∧
        UF.StopsAt p fuel x := by
  intro fuel
  induction fuel with
  | zero =>
      intro x r path _ h
      simp [chase?] at h
  | succ fuel ih =>
      intro x r path hx h
      rw [chase?, hread x hx] at h
      dsimp only at h
      by_cases hroot : UF.step p x = x
      · rw [if_pos hroot] at h
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        exact ⟨by rw [UF.findRootF_succ, if_pos hroot],
          by rw [rootPath, if_pos hroot],
          (UF.stopsAt_succ p fuel x).mpr (Or.inl hroot)⟩
      · rw [if_neg hroot] at h
        cases hc : chase? s a fuel (UF.step p x) with
        | none => rw [hc] at h; simp at h
        | some q =>
            obtain ⟨r0, path0⟩ := q
            rw [hc] at h
            simp only [Option.some.injEq, Prod.mk.injEq] at h
            obtain ⟨rfl, rfl⟩ := h
            obtain ⟨hr, hp, hstop⟩ := ih (UF.step p x) r0 path0 (hbound x hx) hc
            exact ⟨by rw [UF.findRootF_succ, if_neg hroot, hr],
              by rw [rootPath, if_neg hroot, hp],
              (UF.stopsAt_succ p fuel x).mpr (Or.inr ⟨hroot, hstop⟩)⟩

/-- The exhausted outcome is exactly the absence of a completed functional chase:
on a represented in-range array with bounded parents, `none` means the fuel did
not suffice, never that a root was found. -/
theorem chase?_none_iff {s : Sealed} {a : AllocId} {p : UF.Arr}
    (hread : ∀ i, i < p.length → readParent? s a i = some (UF.step p i))
    (hbound : ∀ i, i < p.length → UF.step p i < p.length)
    {fuel x : Nat} (hx : x < p.length) :
    chase? s a fuel x = none ↔ ¬ UF.StopsAt p fuel x := by
  constructor
  · intro h hstop
    have hsome := chase?_eq_of_stops hread hbound fuel x hx hstop
    rw [hsome] at h
    simp at h
  · intro hns
    cases hc : chase? s a fuel x with
    | none => rfl
    | some q =>
        obtain ⟨r, path⟩ := q
        exact absurd (chase?_some_spec hread hbound fuel x r path hx hc).2.2 hns

/-- A ranked forest always completes its chase within the rank bound. -/
theorem chase?_eq_ranked {s : Sealed} {a : AllocId} {p : UF.Arr} {n : Nat}
    {rank : Nat → Nat} (hrep : Rep s a p) (hlen : p.length = n)
    (hr : Ranked p n rank) {x : Nat} (hx : x < n) :
    chase? s a (rank x + 1) x =
      some (UF.findRootF p (rank x + 1) x, rootPath p (rank x + 1) x) := by
  have hxp : x < p.length := by omega
  refine chase?_eq_of_stops (Rep.read hrep) (fun i hi => ?_) (rank x + 1) x hxp ?_
  · have hlt := hr.1 i (by omega)
    omega
  · exact stopsAt_of_ranked hr (rank x + 1) x (by omega) (by omega)

/-! ### Whole-fragment write authority -/

/-- The computational check behind `Writable`: the allocation's frontier is one
leaf named `id` that is active, whole, of read--write ceiling and of the whole
share. -/
def writableB (s : Sealed) (a : AllocId) (id : CapId) (n : Nat) : Bool :=
  match s.state.find? a with
  | none => false
  | some st =>
      match st.forest with
      | .leaf c =>
          decide (c.id = id ∧ c.state = CapState.active ∧
            c.ceiling = Ceiling.readWrite ∧ c.lo = 0 ∧ c.hi = n ∧
            c.q = st.D ∧ st.len = n)
      | .split _ _ _ _ _ _ => false

/-- Whole-fragment write authority: the access name is the allocation's single
active read--write leaf spanning the whole of `[0, n)`. This is the capability
evidence a compression step needs; it is a property of the read-only integrated
projection because neither the share denominator nor the frontier shape is part
of the observation interface. -/
def Writable (s : Sealed) (a : AllocId) (id : CapId) (n : Nat) : Prop :=
  writableB s a id n = true

/-- The structural reading of the write authority. -/
theorem Writable.component {s : Sealed} {a : AllocId} {id : CapId} {n : Nat}
    (h : Writable s a id n) :
    ∃ (st : Reconstruction.State) (c : Leaf), s.state.find? a = some st ∧
      st.forest = .leaf c ∧ c.id = id ∧ c.state = CapState.active ∧
      c.ceiling = Ceiling.readWrite ∧ c.lo = 0 ∧ c.hi = n ∧ c.q = st.D ∧
      st.len = n := by
  unfold Writable writableB at h
  cases hf : s.state.find? a with
  | none => simp [hf] at h
  | some st =>
      cases hforest : st.forest with
      | leaf c =>
          rw [hf] at h
          dsimp only at h
          rw [hforest] at h
          dsimp only at h
          simp only [decide_eq_true_eq] at h
          exact ⟨st, c, rfl, hforest, h.1, h.2.1, h.2.2.1, h.2.2.2.1,
            h.2.2.2.2.1, h.2.2.2.2.2.1, h.2.2.2.2.2.2⟩
      | split k p lr rr l r =>
          rw [hf] at h
          dsimp only at h
          rw [hforest] at h
          dsimp only at h
          simp at h

/-- Write authority makes every in-range write accepted. This is where the write
half of the algorithm is capability-checked: the guard is the whole-share
read--write fragment, not a bare index bound. -/
theorem Writable.write_exists {s : Sealed} {a : AllocId} {id : CapId} {n : Nat}
    (h : Writable s a id n) {i : Nat} (hi : i < n) (v : UInt8) :
    ∃ s', Sealed.write s a id i v = .ok s' := by
  obtain ⟨st, c, hfind, hforest, hid, hstate, hceil, hlo, hhi, hq, hlen⟩ :=
    h.component
  obtain ⟨-, hstorage⟩ := Integrated.State.find?_inv s.state_inv hfind
  obtain ⟨xs, hlook, hxslen⟩ := hstorage
  have hxs : i < xs.length := by omega
  have hheapwrite : st.heap.write? st.alloc i v =
      some ⟨Heap.updateList st.heap.bufs st.alloc (xs.set i v)⟩ := by
    unfold Heap.write?
    rw [hlook]
    dsimp only
    rw [if_pos hxs]
  have halloc : c.alloc = st.alloc := by
    have hinv : st.Inv := (Integrated.State.find?_inv s.state_inv hfind).1
    have hc : c ∈ st.forest.nodes := by rw [hforest]; simp [Reconstruction.Forest.nodes]
    exact (hinv.scope.node_scope c hc).1
  have hstwrite : st.write id i v =
      some { st with heap := ⟨Heap.updateList st.heap.bufs st.alloc (xs.set i v)⟩ } := by
    unfold Reconstruction.State.write
    rw [hforest]
    rw [Reconstruction.Forest.findLeaf?_leaf hid]
    dsimp only
    have hguard : st.WriteGuard c i :=
      ⟨hstate, hq, hceil, halloc, by rw [hlo]; exact Nat.zero_le i,
        by rw [hhi]; exact hi⟩
    rw [dif_pos hguard]
    simp only [hheapwrite]
  have halt : ({ st with
      heap := ⟨Heap.updateList st.heap.bufs st.alloc (xs.set i v)⟩ } :
        Reconstruction.State).alloc = a := by
    show st.alloc = a
    exact Integrated.State.find?_alloc hfind
  obtain ⟨l', hupd⟩ := Integrated.updateState_exists
    (f := fun st => st.write id i v) hfind hstwrite halt
  have hexec : ∃ t : Integrated.State, s.state.exec (.write a id i v) = some t := by
    unfold Integrated.State.exec Integrated.State.update
    dsimp only
    rw [hupd]
    exact ⟨_, rfl⟩
  exact Integrated.Sealed.write_exists_of_exec s a id i v hexec

/-- An accepted write preserves the whole-fragment authority of its own
allocation. -/
theorem Writable.write_preserved {s s' : Sealed} {a : AllocId} {id : CapId}
    {n : Nat} {i : Nat} {v : UInt8} (h : Writable s a id n)
    (hw : Sealed.write s a id i v = .ok s') : Writable s' a id n := by
  obtain ⟨st, c, hfind, hforest, hid, hstate, hceil, hlo, hhi, hq, hlen⟩ :=
    h.component
  obtain ⟨st0, st', hfa, hwrite, hfind'⟩ := sealed_write_component hw
  have hst0 : st0 = st := Option.some.inj (hfa.symm.trans hfind)
  obtain rfl : st0 = st := hst0
  obtain ⟨c', h', hleaf, -, -, -, -, -, -, hst', -⟩ :=
    Reconstruction.State.write_component hwrite
  subst hst'
  have hcc : c' = c := by
    rw [hforest] at hleaf
    rw [Reconstruction.Forest.findLeaf?_leaf hid] at hleaf
    exact (Option.some.inj hleaf).symm
  obtain rfl : c' = c := hcc
  unfold Writable writableB
  rw [hfind']
  dsimp only
  rw [hforest]
  dsimp only
  simp [hid, hstate, hceil, hlo, hhi, hq, hlen]

/-- An accepted write of another allocation preserves the authority. -/
theorem Writable.frames {s s' : Sealed} {a : AllocId} {id : CapId} {i : Nat}
    {v : UInt8} (hw : Sealed.write s a id i v = .ok s') {b : AllocId} (hba : b ≠ a)
    {id' : CapId} {n : Nat} (h : Writable s b id' n) : Writable s' b id' n := by
  have hexec : s.state.exec (.write a id i v) = some s'.state :=
    (Integrated.Sealed.write_ok_iff s a id i v s').mp hw
  have hupd : s.state.update a (fun st => st.write id i v) = some s'.state := by
    simpa [Integrated.State.exec] using hexec
  have hfindb : s'.state.find? b = s.state.find? b :=
    Integrated.State.update_frames_other hupd hba
  unfold Writable writableB at h ⊢
  rw [hfindb]
  exact h

/-! ### Compression over the sealed boundary -/

/-- Write `root` at every node of `path` through the sealed boundary, in path
order. Each step is one `Sealed.write`; there is no other mutation. -/
def compressPath (s : Sealed) (a : AllocId) (id : CapId) (root : Nat) :
    List Nat → Except String Sealed
  | [] => .ok s
  | x :: xs =>
      match s.write a id x (UInt8.ofNat root) with
      | .ok s' => compressPath s' a id root xs
      | .error e => .error e

/-- Compressing a path in the functional model is a fold of byte updates. -/
theorem decode_set {bs : List UInt8} {i v : Nat} (hiv : i < bs.length)
    (hv : v < 256) :
    decode (bs.set i (UInt8.ofNat v)) = (decode bs).set i v := by
  have hto : (UInt8.ofNat v).toNat = v := by
    rw [show UInt8.ofNat v = OfNat.ofNat v from rfl, UInt8.toNat_ofNat]
    exact Nat.mod_eq_of_lt (by omega)
  unfold decode
  rw [List.map_set, hto]

/-- Each sealed compression step updates exactly one represented byte and frames
every other allocation's full component state, so the whole path compression is
the functional `UF.compressAll`. -/
theorem compressPath_spec {a : AllocId} {id : CapId} (root : Nat) :
    ∀ (ys : List Nat) (s : Sealed) (p : UF.Arr), Rep s a p →
      Writable s a id p.length → root < 256 →
      (∀ y ∈ ys, y < p.length) →
      ∃ s', compressPath s a id root ys = .ok s' ∧
        Rep s' a (UF.compressAll p root ys) ∧ Writable s' a id p.length ∧
        WriteFrame s s' a := by
  intro ys
  induction ys with
  | nil =>
      intro s p hrep hauth hroot hys
      exact ⟨s, rfl, hrep, hauth, WriteFrame.refl s a⟩
  | cons y ys ih =>
      intro s p hrep hauth hroot hys
      have hyp : y < p.length := hys y (List.mem_cons_self ..)
      have hys' : ∀ z ∈ ys, z < p.length := fun z hz =>
        hys z (List.mem_cons_of_mem y hz)
      obtain ⟨s1, hw1⟩ := hauth.write_exists hyp (UInt8.ofNat root)
      have hframe1 : WriteFrame s s1 a := sealed_write_frames hw1
      have hrep1 : Rep s1 a (UF.compress p y root) := by
        obtain ⟨bs, hbs, hdec⟩ := hrep
        have hlenbs : y < bs.length := by
          have hp : y < p.length := hyp
          rw [← hdec] at hp
          simpa [decode] using hp
        refine ⟨bs.set y (UInt8.ofNat root), ?_, ?_⟩
        · rw [sealed_write_snapshot_self hw1, hbs]
          rfl
        · rw [decode_set hlenbs hroot, hdec, UF.compress_def]
      have hauth1 : Writable s1 a id p.length := hauth.write_preserved hw1
      have hlen1 : (UF.compress p y root).length = p.length := by
        rw [UF.compress, List.length_set]
      have hys'' : ∀ z ∈ ys, z < (UF.compress p y root).length := by
        intro z hz
        rw [hlen1]
        exact hys' z hz
      have hstep : compressPath s a id root (y :: ys) =
          compressPath s1 a id root ys := by
        simp [compressPath, hw1]
      obtain ⟨s2, hcp, hrep2, hauth2, hframe2⟩ :=
        ih s1 (UF.compress p y root) hrep1 (by rwa [hlen1]) hroot hys''
      exact ⟨s2, hstep.trans hcp, hrep2, (by rwa [← hlen1]), hframe1.trans hframe2⟩

/-! ### The verified find and its specification -/

/-- The message a find returns when the chase did not complete: the fuel was
insufficient, so no root was found. -/
def exhaustedMessage : String :=
  "find refused: the chase did not complete within the fuel"

/-- One find-and-compress through the sealed boundary: read the chase, and if it
completed, write the root at every node of its path. An exhausted chase is a
refusal, never a root. -/
def sealedFind (s : Sealed) (a : AllocId) (id : CapId) (fuel x : Nat) :
    Except String (Nat × Sealed) :=
  match chase? s a fuel x with
  | none => .error exhaustedMessage
  | some (r, path) =>
      match compressPath s a id r path with
      | .ok s' => .ok (r, s')
      | .error e => .error e

/-- An accepted find returns the root its chase completed at and wrote exactly
that path's nodes to that root. -/
theorem sealedFind_some {s s' : Sealed} {a : AllocId} {id : CapId} {fuel x r : Nat}
    (h : sealedFind s a id fuel x = .ok (r, s')) :
    ∃ path, chase? s a fuel x = some (r, path) ∧
      compressPath s a id r path = .ok s' := by
  unfold sealedFind at h
  cases hc : chase? s a fuel x with
  | none => rw [hc] at h; simp at h
  | some q =>
      obtain ⟨r0, path⟩ := q
      rw [hc] at h
      dsimp only at h
      cases hw : compressPath s a id r0 path with
      | error e => rw [hw] at h; simp at h
      | ok s1 =>
          rw [hw] at h
          simp only [Except.ok.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl⟩ := h
          exact ⟨path, rfl, hw⟩

/-- An accepted find is a completed chase: the root the call returned is the
result of a search that actually reached a fixed point within its fuel, not an
artifact of a bounded evaluator running out. -/
theorem sealedFind_ok_stops {s s' : Sealed} {a : AllocId} {id : CapId} {p : UF.Arr}
    {fuel x r : Nat}
    (hread : ∀ i, i < p.length → readParent? s a i = some (UF.step p i))
    (hbound : ∀ i, i < p.length → UF.step p i < p.length)
    (hx : x < p.length)
    (h : sealedFind s a id fuel x = .ok (r, s')) : UF.StopsAt p fuel x := by
  obtain ⟨path, hchase, -⟩ := sealedFind_some h
  exact (chase?_some_spec hread hbound fuel x r path hx hchase).2.2

/-- An exhausted chase makes the find refuse: arbitrary fuel cannot masquerade as
a completed root find. -/
theorem sealedFind_error_of_no_stops {s : Sealed} {a : AllocId} {id : CapId}
    {p : UF.Arr} {fuel x : Nat}
    (hread : ∀ i, i < p.length → readParent? s a i = some (UF.step p i))
    (hbound : ∀ i, i < p.length → UF.step p i < p.length)
    (hx : x < p.length) (hns : ¬ UF.StopsAt p fuel x) :
    sealedFind s a id fuel x = .error exhaustedMessage := by
  unfold sealedFind
  rw [(chase?_none_iff hread hbound hx).mpr hns]

/-- The general find theorem. For an arbitrary represented ranked forest with
whole-fragment write authority, a find at the rank-derived fuel completes and: the
root is the functional root, the post-buffer is exactly the full-path
compression, the represented array stays ranked, acyclic and within bounds, the
partition is preserved, the successor keeps the write authority, every unrelated
allocation's full component state is framed, and the returned state carries the
integrated invariant. -/
theorem sealedFind_spec {s : Sealed} {a : AllocId} {id : CapId} {p : UF.Arr}
    {n : Nat} {rank : Nat → Nat} {x : Nat}
    (hrep : Rep s a p) (hlen : p.length = n) (hr : Ranked p n rank)
    (hn : n ≤ 256) (hauth : Writable s a id n) (hx : x < n) :
    ∃ r s', sealedFind s a id (rank x + 1) x = .ok (r, s') ∧
      r = UF.findRootF p (rank x + 1) x ∧
      UF.IsRoot p r ∧
      Rep s' a (UF.compressAll p r (rootPath p (rank x + 1) x)) ∧
      (UF.compressAll p r (rootPath p (rank x + 1) x)).length = n ∧
      Writable s' a id n ∧
      Ranked (UF.compressAll p r (rootPath p (rank x + 1) x)) n rank ∧
      (∀ u v, UF.Same (UF.compressAll p r (rootPath p (rank x + 1) x)) u v ↔
        UF.Same p u v) ∧
      Acyclic (UF.compressAll p r (rootPath p (rank x + 1) x)) n ∧
      s'.state.Inv ∧ WriteFrame s s' a := by
  have hxp : x < p.length := by omega
  have hstop : UF.StopsAt p (rank x + 1) x :=
    stopsAt_of_ranked hr (rank x + 1) x (by omega) (by omega)
  have hchase := chase?_eq_of_stops (Rep.read hrep)
    (fun i hi => by have hlt := hr.1 i (by omega); omega)
    (rank x + 1) x hxp hstop
  have hrootlt : UF.findRootF p (rank x + 1) x < 256 := by
    have := findRootF_lt (n := n) (fuel := rank x + 1) hr.1
      (by omega : x < n)
    omega
  have hpath : ∀ y ∈ rootPath p (rank x + 1) x, y < p.length := by
    intro y hy
    have := Ranked.reach_lt hr (by omega : x < n)
      (rootPath_mem_reach_from hy)
    omega
  obtain ⟨s', hcompress, hrep', hauth', hframe⟩ :=
    compressPath_spec (a := a) (id := id) (root := UF.findRootF p (rank x + 1) x)
      (rootPath p (rank x + 1) x) s p hrep (by rwa [hlen]) hrootlt hpath
  unfold sealedFind
  rw [hchase]
  dsimp only
  rw [hcompress]
  dsimp only
  exact ⟨UF.findRootF p (rank x + 1) x, s', rfl, rfl, UF.findRootF_root hstop,
    hrep', by rw [compressAll_length, hlen], by rwa [← hlen],
    compressAll_chase_ranked hlen hr (by omega : x < n),
    compressAll_chase_same_iff hlen hr (by omega : x < n),
    acyclic_of_ranked (compressAll_chase_ranked hlen hr (by omega : x < n)),
    s'.state_inv, hframe⟩

/-- The preconditions of one verified find, and the shape a successor restores
them in: a represented ranked forest with whole-fragment write authority. -/
structure Precondition (s : Sealed) (a : AllocId) (id : CapId) (p : UF.Arr)
    (n : Nat) (rank : Nat → Nat) : Prop where
  rep : Rep s a p
  length : p.length = n
  ranked : Ranked p n rank
  fits : n ≤ 256
  writable : Writable s a id n

/-- The verified wrapper: the caller supplies the represented forest's rank and
the start node, and the fuel is derived from the rank rather than chosen by the
caller. -/
def findRanked (s : Sealed) (a : AllocId) (id : CapId) (rank : Nat → Nat)
    (x : Nat) : Except String (Nat × Sealed) :=
  sealedFind s a id (rank x + 1) x

/-- The wrapper's run is the sealed find at the rank-derived fuel. -/
theorem findRanked_eq (s : Sealed) (a : AllocId) (id : CapId) (rank : Nat → Nat)
    (x : Nat) : findRanked s a id rank x = sealedFind s a id (rank x + 1) x := rfl

/-- One verified find returns the correct root, the functional compression, the
preserved forest certificates, a `WriteFrame` for every unrelated allocation, and
a successor that satisfies the same preconditions. -/
theorem findRanked_spec {s : Sealed} {a : AllocId} {id : CapId} {p : UF.Arr}
    {n : Nat} {rank : Nat → Nat} {x : Nat}
    (hpre : Precondition s a id p n rank) (hx : x < n) :
    ∃ r s', findRanked s a id rank x = .ok (r, s') ∧
      r = UF.findRootF p (rank x + 1) x ∧ UF.IsRoot p r ∧
      Precondition s' a id (UF.compressAll p r (rootPath p (rank x + 1) x)) n rank ∧
      (∀ u v, UF.Same (UF.compressAll p r (rootPath p (rank x + 1) x)) u v ↔
        UF.Same p u v) ∧
      Acyclic (UF.compressAll p r (rootPath p (rank x + 1) x)) n ∧
      s'.state.Inv ∧ WriteFrame s s' a := by
  obtain ⟨r, s', h, hroot, hrootp, hrep, hlen, hauth, hranked, hsame, hacyc,
    hinv, hframe⟩ :=
    sealedFind_spec hpre.rep hpre.length hpre.ranked hpre.fits hpre.writable hx
  exact ⟨r, s', h, hroot, hrootp,
    ⟨hrep, hlen, hranked, hpre.fits, hauth⟩, hsame, hacyc, hinv, hframe⟩

/-- Two verified finds on one arbitrary represented forest, the second consuming
the first call's successor state with no manual precondition reconstruction; the
composed frame covers every unrelated allocation across both calls. -/
theorem findRanked_twice {s : Sealed} {a : AllocId} {id : CapId} {p : UF.Arr}
    {n : Nat} {rank : Nat → Nat} {x₁ x₂ : Nat}
    (hpre : Precondition s a id p n rank) (hx₁ : x₁ < n) (hx₂ : x₂ < n) :
    ∃ r₁ s₁ r₂ s₂,
      findRanked s a id rank x₁ = .ok (r₁, s₁) ∧
      findRanked s₁ a id rank x₂ = .ok (r₂, s₂) ∧
      r₁ = UF.findRootF p (rank x₁ + 1) x₁ ∧
      Precondition s₁ a id (UF.compressAll p r₁ (rootPath p (rank x₁ + 1) x₁)) n rank ∧
      Rep s₂ a (UF.compressAll
        (UF.compressAll p r₁ (rootPath p (rank x₁ + 1) x₁)) r₂
        (rootPath (UF.compressAll p r₁ (rootPath p (rank x₁ + 1) x₁))
          (rank x₂ + 1) x₂)) ∧
      (∀ u v, UF.Same (UF.compressAll
        (UF.compressAll p r₁ (rootPath p (rank x₁ + 1) x₁)) r₂
        (rootPath (UF.compressAll p r₁ (rootPath p (rank x₁ + 1) x₁))
          (rank x₂ + 1) x₂)) u v ↔ UF.Same p u v) ∧
      s₂.state.Inv ∧ WriteFrame s s₂ a := by
  obtain ⟨r₁, s₁, h₁, hr₁, -, hpre₁, hsame₁, -, hinv₁, hframe₁⟩ :=
    findRanked_spec hpre hx₁
  obtain ⟨r₂, s₂, h₂, -, -, hpre₂, hsame₂, -, hinv₂, hframe₂⟩ :=
    findRanked_spec hpre₁ hx₂
  exact ⟨r₁, s₁, r₂, s₂, h₁, h₂, hr₁, hpre₁, hpre₂.rep,
    fun u v => (hsame₂ u v).trans (hsame₁ u v), hinv₂, hframe₁.trans hframe₂⟩

end UFGeneric

end Cap
