/-
An integrated multi-allocation reconstruction semantics.

`Cap.Reconstruction` models one allocation: a reference byte heap, a forest of
current fragments, the names ever issued and retired, and the outstanding return
obligations. This module lifts that model to a collection of allocations keyed by
`AllocId`:

* `State` is a list of `Reconstruction.State` values, one per live allocation.
  `State.Inv` requires the allocation identifiers to be distinct, every component
  to satisfy the reconstruction invariant, and every component heap to hold its
  allocation with the recorded `len` (`Reconstruction.State.Storage`). Access
  names are scoped to their allocation: every checked command names the
  allocation it acts on, and the observations take the same allocation
  identifier.
* `Cmd` is the checked command language: allocation, write, borrow, spatial and
  fractional subdivision, reconstruction, return and free. Each command acts on
  one allocation and delegates to the component operation. A command on an
  absent allocation is refused. The frame theorem `State.exec_frames_other`
  shows that an accepted command leaves every other allocation's lookup — and
  therefore its snapshot — unchanged.
* `free` is the deallocation guard the review asks for: it is accepted only when
  the allocation is a single whole active leaf, with no outstanding return
  obligation. Freeing one allocation drops only that component.
* `State.run` executes a command list; `State.run_inv` carries `State.Inv`
  through an accepted run, and `State.exec_inv` through one accepted command.
* `Prog` is the typed wrapper: a command list together with the boolean run of
  the real checker from an invariant start state. `Prog.never_refuses` derives an
  accepting run from the certificate, so a `Prog` cannot be built from a step the
  checker refuses.
* `Sealed` is the private boundary over the integrated state. Its constructor and
  carried invariant are private; the only way to obtain one is `initial`, an
  accepted operation, or `Sealed.run` over the checked command list. Observations
  are a per-allocation heap snapshot, a byte read, a fragment description, the
  retired names and the outstanding return obligations. The 64-byte lifecycle
  borrows the whole fragment, splits it into `[0,32)` and `[32,64)`, writes both
  halves, reconstructs and returns the loan, and the bytes survive. A second full
  cycle and a second allocation are accepted on the output.

This module is the one sealed path. `Cap.Sealed` re-exports `Sealed` and its
observations, so a client of the sealed boundary runs the integrated `Cmd`
language rather than the `World`/`UCmd` checker. `Cap.ReconstructionSealed` has
been retired; its lifecycle and controls live here, and the single-allocation
`Reconstruction.State` is now only a component of this state.

What `State.Inv` is: distinct live allocations; a persistent allocation history
`allocsIssued` that contains every live identifier and is never rewritten by
`free`; a persistent capability history `issued` that contains every name any
component has issued; each component's `Reconstruction.State.Inv`, whose
accounting component constrains current authority, issuance, retirement, dormant
lenders and outstanding restoration obligations; and each component's
`Reconstruction.State.Storage` — the component heap holds that allocation with
exactly `len` bytes. `State.alloc` refuses an allocation identifier that is in
`allocsIssued` and either initial capability name that is in `issued`, so a
disposed allocation cannot be reissued and an old capability cannot authorize a
replacement allocation. It is still not the combined `World.FullInv`: the ledger
and world loan bookkeeping remain on the world path, and this module does not
claim that `World.splitAtChecked` consults the reconstruction forest. It also
does not turn a `World` into a component.

The private constructor is what prevents manufacture; the state is pure data, so
a copied sealed value shares its representation. That is the same model boundary
as before, and it is stated rather than claimed away.
-/
import Cap.Reconstruction

namespace Cap

namespace Integrated

/-! ### The multi-allocation state -/

/-- A multi-allocation reconstruction state: the live allocations, each with its
own heap, forest, issuance history and return obligations, together with the
session's persistent allocation and capability histories. -/
structure State where
  allocs : List Reconstruction.State
  /-- Every allocation identifier ever allocated in the session. `free` does not
  remove an entry, so an identifier cannot be reissued after disposal. -/
  allocsIssued : List AllocId
  /-- Every capability name ever issued in the session, across allocations. A
  freed allocation leaves its names here. -/
  issued : List CapId

/-- The live allocation identifiers. -/
def State.allocIds (s : State) : List AllocId :=
  s.allocs.map (fun st => st.alloc)

/-- The integrated invariant: the live allocations are distinct; every component
is a valid reconstruction state whose heap holds its allocation with the
recorded `len`; the allocation identifiers in use belong to the persistent
allocation history; every capability a component has issued belongs to the
persistent capability history. -/
def State.Inv (s : State) : Prop :=
  s.allocIds.Nodup ∧
  s.allocsIssued.Nodup ∧
  (∀ a ∈ s.allocIds, a ∈ s.allocsIssued) ∧
  (∀ st ∈ s.allocs, st.Inv ∧ st.Storage) ∧
  (∀ st ∈ s.allocs, ∀ id ∈ st.issued, id ∈ s.issued)

/-- The empty state has no live allocation and empty histories. -/
def State.empty : State := { allocs := [], allocsIssued := [], issued := [] }

theorem State.empty_inv : State.empty.Inv := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> simp [State.empty, State.allocIds]

/-- One allocation's reconstruction state, keyed by its allocation identifier.
The first entry for an allocation wins; `State.Inv` makes the components
distinct, so the key is exact on invariant states. -/
def findState? : List Reconstruction.State → AllocId → Option Reconstruction.State
  | [], _ => none
  | st :: rest, a => if st.alloc = a then some st else findState? rest a

/-- The component state of an allocation, if present. -/
def State.find? (s : State) (a : AllocId) : Option Reconstruction.State :=
  findState? s.allocs a

/-- Replace the component state of an allocation. A missing allocation, or a
component operation that refuses, yields `none`; a replacement whose allocation
identifier differs from the key is refused so the list stays keyed. -/
def updateState : List Reconstruction.State → AllocId →
    (Reconstruction.State → Option Reconstruction.State) → Option (List Reconstruction.State)
  | [], _, _ => none
  | st :: rest, a, f =>
      if st.alloc = a then
        match f st with
        | some st' => if st'.alloc = a then some (st' :: rest) else none
        | none => none
      else
        match updateState rest a f with
        | some rest' => some (st :: rest')
        | none => none

/-- Apply a component operation to the named allocation. The persistent
capability history grows to cover every currently issued name; the allocation
history is unchanged. -/
def State.update (s : State) (a : AllocId)
    (f : Reconstruction.State → Option Reconstruction.State) : Option State :=
  (updateState s.allocs a f).map (fun allocs =>
    { allocs := allocs
      allocsIssued := s.allocsIssued
      issued := allocs.flatMap (fun st => st.issued) ++ s.issued })

/-- Remove the component state of an allocation. -/
def removeAlloc (a : AllocId) : List Reconstruction.State → List Reconstruction.State
  | [] => []
  | st :: rest => if st.alloc = a then removeAlloc a rest else st :: removeAlloc a rest

/-- A component is a single whole active leaf of the allocation: its frontier is
exactly one active leaf spanning `[0, len)` with the whole share `D`. -/
def wholeActiveB (st : Reconstruction.State) : Bool :=
  match st.forest with
  | .leaf c =>
      decide (c.state = .active) && decide (c.lo = 0) &&
        decide (c.hi = st.len) && decide (c.q = st.D)
  | .split _ _ _ _ _ _ => false

/-- The structural reading of the free guard. -/
theorem wholeActiveB_iff (st : Reconstruction.State) :
    wholeActiveB st = true ↔
      ∃ c : Leaf, st.forest = .leaf c ∧ c.state = .active ∧ c.lo = 0 ∧
        c.hi = st.len ∧ c.q = st.D := by
  cases hf : st.forest with
  | leaf c =>
      simp only [wholeActiveB, hf, Bool.and_eq_true, decide_eq_true_eq]
      constructor
      · intro h
        exact ⟨c, rfl, h.1.1.1, h.1.1.2, h.1.2, h.2⟩
      · intro ⟨c', hc', hstate, hlo, hhi, hq⟩
        cases hc'
        exact ⟨⟨⟨hstate, hlo⟩, hhi⟩, hq⟩
  | split k p lr rr l r =>
      simp [wholeActiveB, hf]

/-- Free an allocation: accepted only when it is a single whole active leaf and
no return obligation is outstanding. -/
def State.free (s : State) (a : AllocId) : Option State :=
  match s.find? a with
  | none => none
  | some st =>
      if st.restores = [] ∧ wholeActiveB st = true then
        some { allocs := removeAlloc a s.allocs
               allocsIssued := s.allocsIssued
               issued := s.issued }
      else none

/-- The canonical one-allocation state: `n` zero bytes of share `D`, a root
access name and a disposal name. -/
def State.initial (a : AllocId) (n D : Nat) (pos : 0 < D)
    (rootId disposalId : CapId) : State :=
  { allocs := [Reconstruction.State.initial a n D pos rootId disposalId]
    allocsIssued := [a]
    issued := [rootId, disposalId] }

theorem State.initial_inv (a : AllocId) (n D : Nat) (pos : 0 < D)
    (rootId disposalId : CapId) :
    (State.initial a n D pos rootId disposalId).Inv := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · simp [State.initial, State.allocIds]
  · simp [State.initial]
  · intro a' ha'
    simp [State.initial, State.allocIds] at ha'
    subst ha'
    simp [State.initial]
  · intro st hst
    simp [State.initial] at hst
    subst hst
    exact ⟨Reconstruction.State.initial_inv a n D pos rootId disposalId,
      Reconstruction.State.initial_storage a n D pos rootId disposalId⟩
  · intro st hst id hid
    simp [State.initial] at hst
    subst hst
    simp [Reconstruction.State.initial] at hid
    rcases hid with rfl | rfl <;> simp [State.initial]

/-- The 64-byte integrated fixture: allocation `⟨0⟩`, root `⟨1⟩`, disposal
`⟨2⟩`. -/
def State.initial64 : State :=
  State.initial ⟨0⟩ 64 64 (by decide) ⟨1⟩ ⟨2⟩

theorem State.initial64_inv : State.initial64.Inv :=
  State.initial_inv ⟨0⟩ 64 64 (by decide) ⟨1⟩ ⟨2⟩

/-- Add a fresh allocation to the state. The allocation identifier and both
initial capability names must be unused for the whole session, so a freed
allocation identifier cannot be reissued and an old capability cannot authorize
a replacement allocation. -/
def State.alloc (s : State) (a : AllocId) (n D : Nat) (pos : 0 < D)
    (rootId disposalId : CapId) : Option State :=
  if h : a ∉ s.allocsIssued ∧ rootId ∉ s.issued ∧ disposalId ∉ s.issued then
    some { allocs :=
             Reconstruction.State.initial a n D pos rootId disposalId :: s.allocs
           allocsIssued := a :: s.allocsIssued
           issued := rootId :: disposalId :: s.issued }
  else none

/-! ### Lookup facts -/

theorem findState?_eq_some_mem {l : List Reconstruction.State} {a : AllocId}
    {st : Reconstruction.State} (h : findState? l a = some st) :
    st ∈ l ∧ st.alloc = a := by
  induction l with
  | nil => simp [findState?] at h
  | cons head tail ih =>
      simp only [findState?] at h
      by_cases hx : head.alloc = a
      · rw [if_pos hx] at h
        simp only [Option.some.injEq] at h
        subst st
        exact ⟨by simp, hx⟩
      · rw [if_neg hx] at h
        obtain ⟨hmem, halloc⟩ := ih h
        exact ⟨List.mem_cons_of_mem head hmem, halloc⟩

theorem State.find?_inv {s : State} (hinv : s.Inv) {a : AllocId}
    {st : Reconstruction.State} (h : s.find? a = some st) :
    st.Inv ∧ st.Storage := by
  obtain ⟨hmem, _⟩ := findState?_eq_some_mem h
  exact hinv.2.2.2.1 st hmem

theorem State.find?_alloc {s : State} {a : AllocId}
    {st : Reconstruction.State} (h : s.find? a = some st) : st.alloc = a := by
  exact (findState?_eq_some_mem h).2

/-! ### List facts for the update and free operations -/

theorem updateState_alloc_mem {l l' : List Reconstruction.State} {a : AllocId}
    {f : Reconstruction.State → Option Reconstruction.State}
    (h : updateState l a f = some l') {x : AllocId}
    (hx : x ∈ l'.map (fun st => st.alloc)) :
    x ∈ l.map (fun st => st.alloc) ∨ x = a := by
  induction l generalizing l' with
  | nil => simp [updateState] at h
  | cons head tail ih =>
      simp only [updateState] at h
      by_cases hkey : head.alloc = a
      · rw [if_pos hkey] at h
        cases hfst : f head with
        | none => simp [hfst] at h
        | some next =>
            simp only [hfst] at h
            by_cases hkey' : next.alloc = a
            · rw [if_pos hkey'] at h
              simp only [Option.some.injEq] at h
              subst l'
              rw [List.map_cons] at hx
              rcases List.mem_cons.mp hx with hx0 | hx'
              · exact Or.inr (by rw [hx0, hkey'])
              · exact Or.inl (List.mem_cons.mpr (Or.inr hx'))
            · rw [if_neg hkey'] at h
              simp at h
      · rw [if_neg hkey] at h
        cases hrec : updateState tail a f with
        | none => simp [hrec] at h
        | some tail' =>
            simp only [hrec] at h
            simp only [Option.some.injEq] at h
            subst l'
            rw [List.map_cons] at hx
            rcases List.mem_cons.mp hx with hx0 | hx'
            · exact Or.inl (List.mem_cons.mpr (Or.inl hx0))
            · rcases ih hrec hx' with hmem | ha
              · exact Or.inl (List.mem_cons.mpr (Or.inr hmem))
              · exact Or.inr ha

/-- A successful update names an allocation already present. -/
theorem updateState_key_mem {l l' : List Reconstruction.State} {a : AllocId}
    {f : Reconstruction.State → Option Reconstruction.State}
    (h : updateState l a f = some l') :
    a ∈ l.map (fun st => st.alloc) := by
  induction l generalizing l' with
  | nil => simp [updateState] at h
  | cons head tail ih =>
      simp only [updateState] at h
      by_cases hkey : head.alloc = a
      · exact List.mem_map.mpr ⟨head, by simp, hkey⟩
      · rw [if_neg hkey] at h
        cases hrec : updateState tail a f with
        | none => simp [hrec] at h
        | some tail' =>
            exact List.mem_cons_of_mem head.alloc (ih hrec)

theorem mem_removeAlloc {l : List Reconstruction.State} {a : AllocId}
    {st : Reconstruction.State} (h : st ∈ removeAlloc a l) : st ∈ l := by
  induction l with
  | nil => simp [removeAlloc] at h
  | cons head tail ih =>
      simp only [removeAlloc] at h
      by_cases hx : head.alloc = a
      · rw [if_pos hx] at h
        exact List.mem_cons_of_mem head (ih h)
      · rw [if_neg hx] at h
        rcases List.mem_cons.mp h with rfl | h
        · exact List.mem_cons_self
        · exact List.mem_cons_of_mem head (ih h)

theorem removeAlloc_alloc_mem {l : List Reconstruction.State} {a x : AllocId}
    (h : x ∈ (removeAlloc a l).map (fun st => st.alloc)) :
    x ∈ l.map (fun st => st.alloc) := by
  induction l with
  | nil => simp [removeAlloc] at h
  | cons head tail ih =>
      simp only [removeAlloc] at h
      by_cases hs : head.alloc = a
      · rw [if_pos hs] at h
        exact List.mem_cons_of_mem head.alloc (ih h)
      · rw [if_neg hs] at h
        rw [List.map_cons] at h
        rw [List.map_cons]
        rcases List.mem_cons.mp h with hx | hx
        · exact List.mem_cons.mpr (Or.inl hx)
        · exact List.mem_cons.mpr (Or.inr (ih hx))

theorem removeAlloc_nodup {l : List Reconstruction.State} {a : AllocId}
    (h : (l.map (fun st => st.alloc)).Nodup) :
    ((removeAlloc a l).map (fun st => st.alloc)).Nodup := by
  induction l with
  | nil => simp [removeAlloc]
  | cons head tail ih =>
      rw [List.map_cons, List.nodup_cons] at h
      simp only [removeAlloc]
      by_cases hs : head.alloc = a
      · rw [if_pos hs]
        exact ih h.2
      · rw [if_neg hs]
        rw [List.map_cons, List.nodup_cons]
        refine ⟨?_, ih h.2⟩
        intro hmem
        exact h.1 (removeAlloc_alloc_mem hmem)

/-! ### Preserving the integrated invariant -/

theorem updateState_inv {l l' : List Reconstruction.State} {a : AllocId}
    {f : Reconstruction.State → Option Reconstruction.State}
    (h : updateState l a f = some l')
    (hnodup : (l.map (fun st => st.alloc)).Nodup)
    (hall : ∀ st ∈ l, st.Inv ∧ st.Storage)
    (hf : ∀ st st', st.Inv → st.Storage → f st = some st' → st'.Inv ∧ st'.Storage) :
    (l'.map (fun st => st.alloc)).Nodup ∧ ∀ st ∈ l', st.Inv ∧ st.Storage := by
  induction l generalizing l' with
  | nil => simp [updateState] at h
  | cons head tail ih =>
      simp only [updateState] at h
      have hnd : (head.alloc :: tail.map (fun s => s.alloc)).Nodup := by
        simpa [List.map_cons] using hnodup
      rw [List.nodup_cons] at hnd
      by_cases hkey : head.alloc = a
      · rw [if_pos hkey] at h
        cases hfst : f head with
        | none => simp [hfst] at h
        | some next =>
            simp only [hfst] at h
            by_cases hkey' : next.alloc = a
            · rw [if_pos hkey'] at h
              simp only [Option.some.injEq] at h
              subst l'
              refine ⟨?_, ?_⟩
              · rw [List.map_cons, List.nodup_cons]
                refine ⟨?_, hnd.2⟩
                simpa [hkey', hkey] using hnd.1
              · intro x hx
                rcases List.mem_cons.mp hx with heq | hx
                · rw [heq]
                  exact hf head next (hall head (by simp)).1 (hall head (by simp)).2 hfst
                · exact hall x (by simp [hx])
            · rw [if_neg hkey'] at h
              simp at h
      · rw [if_neg hkey] at h
        cases hrec : updateState tail a f with
        | none => simp [hrec] at h
        | some tail' =>
            simp only [hrec] at h
            simp only [Option.some.injEq] at h
            subst l'
            obtain ⟨hnd', hall'⟩ :=
              ih hrec hnd.2 (fun x hx => hall x (by simp [hx]))
            refine ⟨?_, ?_⟩
            · rw [List.map_cons, List.nodup_cons]
              refine ⟨?_, hnd'⟩
              intro hmem
              rcases updateState_alloc_mem hrec hmem with hmem' | heq
              · exact hnd.1 hmem'
              · exact hkey heq
            · intro x hx
              rcases List.mem_cons.mp hx with heq | hx
              · rw [heq]
                exact hall head (by simp)
              · exact hall' x hx

theorem State.update_inv {s s' : State} {a : AllocId}
    {f : Reconstruction.State → Option Reconstruction.State}
    (h : s.update a f = some s') (hinv : s.Inv)
    (hf : ∀ st st', st.Inv → st.Storage → f st = some st' → st'.Inv ∧ st'.Storage) :
    s'.Inv := by
  obtain ⟨hnodup, hIssNodup, hlive, hall, hids⟩ := hinv
  unfold State.update at h
  cases hupd : updateState s.allocs a f with
  | none => simp [hupd] at h
  | some l' =>
      simp only [hupd, Option.map_some, Option.some.injEq] at h
      subst s'
      obtain ⟨hnodup', hall'⟩ := updateState_inv hupd hnodup hall hf
      refine ⟨hnodup', hIssNodup, ?_, hall', ?_⟩
      · intro x hx
        rcases updateState_alloc_mem hupd hx with hx' | rfl
        · exact hlive x hx'
        · exact hlive x (updateState_key_mem hupd)
      · intro st hst id hid
        exact List.mem_append.mpr (Or.inl (List.mem_flatMap.mpr ⟨st, hst, hid⟩))

theorem State.alloc_inv {s s' : State} {a : AllocId} {n D : Nat} {pos : 0 < D}
    {rootId disposalId : CapId}
    (h : s.alloc a n D pos rootId disposalId = some s') (hinv : s.Inv) : s'.Inv := by
  obtain ⟨hnodup, hIssNodup, hlive, hall, hids⟩ := hinv
  unfold State.alloc at h
  split at h
  · rename_i hfresh
    obtain ⟨hfA, hfRoot, hfDisposal⟩ := hfresh
    simp only [Option.some.injEq] at h
    subst s'
    have hliveA : a ∉ s.allocIds := fun hm => hfA (hlive a hm)
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · simp only [State.allocIds, List.map_cons]
      exact List.nodup_cons.mpr ⟨hliveA, hnodup⟩
    · exact List.nodup_cons.mpr ⟨hfA, hIssNodup⟩
    · intro x hx
      simp only [State.allocIds, List.map_cons] at hx
      rcases List.mem_cons.mp hx with rfl | hx
      · exact List.mem_cons_self
      · exact List.mem_cons_of_mem _ (hlive x hx)
    · intro st hst
      rw [List.mem_cons] at hst
      rcases hst with rfl | hst
      · exact ⟨Reconstruction.State.initial_inv a n D pos rootId disposalId,
          Reconstruction.State.initial_storage a n D pos rootId disposalId⟩
      · exact hall st hst
    · intro st hst id hid
      rw [List.mem_cons] at hst
      rcases hst with rfl | hst
      · simp only [Reconstruction.State.initial, List.mem_cons, List.mem_nil_iff,
          or_false] at hid
        rcases hid with rfl | rfl
        · exact List.mem_cons_self
        · exact List.mem_cons_of_mem _ List.mem_cons_self
      · exact List.mem_cons_of_mem _
          (List.mem_cons_of_mem _ (hids st hst id hid))
  · simp at h

theorem State.free_inv {s s' : State} {a : AllocId}
    (h : s.free a = some s') (hinv : s.Inv) : s'.Inv := by
  obtain ⟨hnodup, hIssNodup, hlive, hall, hids⟩ := hinv
  unfold State.free at h
  cases hfind : s.find? a with
  | none => simp [hfind] at h
  | some st =>
      simp only [hfind] at h
      by_cases hcond : st.restores = [] ∧ wholeActiveB st = true
      · rw [if_pos hcond] at h
        simp only [Option.some.injEq] at h
        subst s'
        refine ⟨removeAlloc_nodup hnodup, hIssNodup, ?_, ?_, ?_⟩
        · intro x hx
          exact hlive x (removeAlloc_alloc_mem hx)
        · intro st' hst'
          exact hall st' (mem_removeAlloc hst')
        · intro st' hst' id hid
          exact hids st' (mem_removeAlloc hst') id hid
      · rw [if_neg hcond] at h
        simp at h

/-- Freeing an allocation leaves both persistent histories intact: a disposed
allocation identifier and its capability names are never reissued. -/
theorem State.free_histories_intact {s s' : State} {a : AllocId}
    (h : s.free a = some s') :
    s'.allocsIssued = s.allocsIssued ∧ s'.issued = s.issued := by
  unfold State.free at h
  cases hfind : s.find? a with
  | none => simp [hfind] at h
  | some st =>
      simp only [hfind] at h
      by_cases hcond : st.restores = [] ∧ wholeActiveB st = true
      · rw [if_pos hcond] at h
        simp only [Option.some.injEq] at h
        subst s'
        exact ⟨rfl, rfl⟩
      · rw [if_neg hcond] at h
        simp at h

/-- Allocation refuses an identifier that was ever used in the session, not only
one that is currently live. -/
theorem State.alloc_refuses_issued_allocation {s : State} {a : AllocId} {n D : Nat}
    {pos : 0 < D} {rootId disposalId : CapId} (h : a ∈ s.allocsIssued) :
    s.alloc a n D pos rootId disposalId = none := by
  unfold State.alloc
  exact dif_neg (fun hc => hc.1 h)

/-- Allocation refuses a capability name that was ever issued in the session. -/
theorem State.alloc_refuses_issued_capability {s : State} {a : AllocId} {n D : Nat}
    {pos : 0 < D} {rootId disposalId : CapId}
    (h : rootId ∈ s.issued ∨ disposalId ∈ s.issued) :
    s.alloc a n D pos rootId disposalId = none := by
  unfold State.alloc
  exact dif_neg (fun hc => by
    rcases h with h | h
    · exact hc.2.1 h
    · exact hc.2.2 h)

/-- Allocation succeeds when its identifier and both initial capability names are
unused. -/
theorem State.alloc_fresh_some {s : State} {a : AllocId} {n D : Nat}
    {pos : 0 < D} {rootId disposalId : CapId}
    (h1 : a ∉ s.allocsIssued) (h2 : rootId ∉ s.issued)
    (h3 : disposalId ∉ s.issued) :
    (s.alloc a n D pos rootId disposalId).isSome = true := by
  unfold State.alloc
  rw [dif_pos ⟨h1, h2, h3⟩]
  rfl

/-- Reallocating an identifier after free is refused because the identifier stays
in the persistent allocation history. -/
theorem State.reallocate_after_free_refused {s s' : State} {a : AllocId} {n D : Nat}
    {pos : 0 < D} {rootId disposalId : CapId}
    (hf : s.free a = some s') (hmem : a ∈ s.allocsIssued) :
    s'.alloc a n D pos rootId disposalId = none := by
  exact State.alloc_refuses_issued_allocation
    (by rw [(State.free_histories_intact hf).1]; exact hmem)

/-- A concrete stale-identity regression: after freeing allocation `⟨0⟩`, the
canonical allocation identifier cannot be reissued. -/
theorem State.realloc_initial64_refused {s' : State}
    (hf : State.free State.initial64 ⟨0⟩ = some s') :
    s'.alloc ⟨0⟩ 64 64 (by decide) ⟨1⟩ ⟨2⟩ = none := by
  exact State.reallocate_after_free_refused hf (by simp [State.initial64, State.initial])

/-- A fresh allocation identifier with fresh capability names is accepted after a
free. -/
theorem State.alloc_fresh_after_free_some {s' : State}
    (hf : State.free State.initial64 ⟨0⟩ = some s') :
    (s'.alloc ⟨1⟩ 64 64 (by decide) ⟨20⟩ ⟨21⟩).isSome = true := by
  refine State.alloc_fresh_some ?_ ?_ ?_
  · rw [(State.free_histories_intact hf).1]
    simp [State.initial64, State.initial]
  · rw [(State.free_histories_intact hf).2]
    simp [State.initial64, State.initial]
  · rw [(State.free_histories_intact hf).2]
    simp [State.initial64, State.initial]

/-- A capability issued by the freed allocation cannot be reused for a fresh
allocation: free leaves the capability history intact. -/
theorem State.alloc_reusing_old_capability_refused {s' : State}
    (hf : State.free State.initial64 ⟨0⟩ = some s') :
    s'.alloc ⟨1⟩ 64 64 (by decide) ⟨1⟩ ⟨21⟩ = none := by
  apply State.alloc_refuses_issued_capability (h := Or.inl ?_)
  rw [(State.free_histories_intact hf).2]
  simp [State.initial64, State.initial]

/-- An accepted free names a component that is a single whole active leaf with no
outstanding return obligation. -/
theorem State.free_guard {s s' : State} {a : AllocId}
    (h : s.free a = some s') :
    ∃ st, s.find? a = some st ∧ st.restores = [] ∧ wholeActiveB st = true := by
  unfold State.free at h
  cases hfind : s.find? a with
  | none => simp [hfind] at h
  | some st =>
      simp only [hfind] at h
      by_cases hcond : st.restores = [] ∧ wholeActiveB st = true
      · exact ⟨st, rfl, hcond.1, hcond.2⟩
      · rw [if_neg hcond] at h
        simp at h

/-! ### Framing other allocations -/

theorem findState?_updateState_other {l l' : List Reconstruction.State}
    {a b : AllocId} {f : Reconstruction.State → Option Reconstruction.State}
    (h : updateState l a f = some l') (hba : b ≠ a) :
    findState? l' b = findState? l b := by
  induction l generalizing l' with
  | nil => simp [updateState] at h
  | cons head tail ih =>
      simp only [updateState] at h
      by_cases hkey : head.alloc = a
      · rw [if_pos hkey] at h
        cases hfst : f head with
        | none => simp [hfst] at h
        | some next =>
            simp only [hfst] at h
            by_cases hkey' : next.alloc = a
            · rw [if_pos hkey'] at h
              simp only [Option.some.injEq] at h
              subst l'
              have hne : next.alloc ≠ b := by
                rw [hkey']
                exact fun hb => hba hb.symm
              have hne0 : head.alloc ≠ b := by
                rw [hkey]
                exact fun hb => hba hb.symm
              simp [findState?, hne, hne0]
            · rw [if_neg hkey'] at h
              simp at h
      · rw [if_neg hkey] at h
        cases hrec : updateState tail a f with
        | none => simp [hrec] at h
        | some tail' =>
            simp only [hrec] at h
            simp only [Option.some.injEq] at h
            subst l'
            by_cases hb : head.alloc = b
            · simp [findState?, hb]
            · simp only [findState?, hb, if_false]
              exact ih hrec

theorem State.update_frames_other {s s' : State} {a : AllocId}
    {f : Reconstruction.State → Option Reconstruction.State}
    (h : s.update a f = some s') {b : AllocId} (hb : b ≠ a) :
    s'.find? b = s.find? b := by
  unfold State.update at h
  cases hupd : updateState s.allocs a f with
  | none => simp [hupd] at h
  | some l' =>
      simp only [hupd, Option.map_some, Option.some.injEq] at h
      subst s'
      unfold State.find?
      exact findState?_updateState_other hupd hb

theorem findState?_removeAlloc_other {l : List Reconstruction.State} {a b : AllocId}
    (hb : b ≠ a) : findState? (removeAlloc a l) b = findState? l b := by
  induction l with
  | nil => simp [removeAlloc, findState?]
  | cons head tail ih =>
      simp only [removeAlloc]
      by_cases hs : head.alloc = a
      · rw [if_pos hs]
        have hne : head.alloc ≠ b := by
          rw [hs]
          exact fun h => hb h.symm
        simp [findState?, hne, ih]
      · rw [if_neg hs]
        by_cases hsb : head.alloc = b
        · simp [findState?, hsb]
        · simp [findState?, hsb, ih]

theorem State.free_frames_other {s s' : State} {a : AllocId}
    (h : s.free a = some s') {b : AllocId} (hb : b ≠ a) :
    s'.find? b = s.find? b := by
  unfold State.free at h
  cases hfind : s.find? a with
  | none => simp [hfind] at h
  | some st =>
      simp only [hfind] at h
      by_cases hcond : st.restores = [] ∧ wholeActiveB st = true
      · rw [if_pos hcond] at h
        simp only [Option.some.injEq] at h
        subst s'
        unfold State.find?
        exact findState?_removeAlloc_other hb
      · rw [if_neg hcond] at h
        simp at h

theorem State.alloc_frames_other {s s' : State} {a : AllocId} {n D : Nat}
    {pos : 0 < D} {rootId disposalId : CapId}
    (h : s.alloc a n D pos rootId disposalId = some s') {b : AllocId} (hb : b ≠ a) :
    s'.find? b = s.find? b := by
  unfold State.alloc at h
  split at h
  · rename_i hfresh
    simp only [Option.some.injEq] at h
    subst s'
    unfold State.find?
    have hne : (Reconstruction.State.initial a n D pos rootId disposalId).alloc ≠ b := by
      simp [Reconstruction.State.initial]
      exact fun hb' => hb hb'.symm
    simp [findState?, hne]
  · simp at h

/-! ### Commands and their invariants -/

/-- The checked command language. Every command names the allocation it acts on.
`ret` is the return of a borrowed fragment; `return` is a Lean keyword. -/
inductive Cmd where
  | alloc (a : AllocId) (n D : Nat) (pos : 0 < D) (rootId disposalId : CapId)
  | write (a : AllocId) (id : CapId) (i : Nat) (v : UInt8)
  | borrow (a : AllocId) (lender borrower : CapId)
  | splitSpatial (a : AllocId) (parentId c1 c2 : CapId) (lo1 hi1 lo2 hi2 : Nat)
  | splitFraction (a : AllocId) (parentId c1 c2 : CapId) (q1 q2 : Nat)
  | reconstruct (a : AllocId) (parentId : CapId)
  | ret (a : AllocId) (borrower : CapId)
  | free (a : AllocId)

/-- The allocation a command targets. -/
def Cmd.allocId : Cmd → AllocId
  | .alloc a _ _ _ _ _ => a
  | .write a _ _ _ => a
  | .borrow a _ _ => a
  | .splitSpatial a _ _ _ _ _ _ _ => a
  | .splitFraction a _ _ _ _ _ => a
  | .reconstruct a _ => a
  | .ret a _ => a
  | .free a => a

/-- Execute one checked command. A command on an absent allocation, or a
component operation the checker refuses, yields `none`. -/
def State.exec (s : State) (c : Cmd) : Option State :=
  match c with
  | .alloc a n D pos rootId disposalId => s.alloc a n D pos rootId disposalId
  | .write a id i v => s.update a (fun st => st.write id i v)
  | .borrow a lender borrower => s.update a (fun st => st.borrow lender borrower)
  | .splitSpatial a parentId c1 c2 lo1 hi1 lo2 hi2 =>
      s.update a (fun st => st.splitSpatial parentId c1 c2 lo1 hi1 lo2 hi2)
  | .splitFraction a parentId c1 c2 q1 q2 =>
      s.update a (fun st => st.splitFraction parentId c1 c2 q1 q2)
  | .reconstruct a parentId => s.update a (fun st => st.reconstruct parentId)
  | .ret a borrower => s.update a (fun st => st.return borrower)
  | .free a => s.free a

/-- An accepted command preserves the integrated invariant. -/
theorem State.exec_inv {s s' : State} {c : Cmd}
    (h : s.exec c = some s') (hinv : s.Inv) : s'.Inv := by
  cases c with
  | alloc a n D pos rootId disposalId =>
      exact State.alloc_inv h hinv
  | write a id i v =>
      exact State.update_inv h hinv
        (fun st st' hst hstor hw =>
          ⟨Reconstruction.State.write_inv hw hst,
           Reconstruction.State.write_storage hw hstor⟩)
  | borrow a lender borrower =>
      exact State.update_inv h hinv
        (fun st st' hst hstor hb =>
          ⟨Reconstruction.State.borrow_inv hb hst,
           Reconstruction.State.borrow_storage hb hstor⟩)
  | splitSpatial a parentId c1 c2 lo1 hi1 lo2 hi2 =>
      exact State.update_inv h hinv
        (fun st st' hst hstor hs =>
          ⟨Reconstruction.State.splitSpatial_inv hs hst,
           Reconstruction.State.splitSpatial_storage hs hstor⟩)
  | splitFraction a parentId c1 c2 q1 q2 =>
      exact State.update_inv h hinv
        (fun st st' hst hstor hs =>
          ⟨Reconstruction.State.splitFraction_inv hs hst,
           Reconstruction.State.splitFraction_storage hs hstor⟩)
  | reconstruct a parentId =>
      exact State.update_inv h hinv
        (fun st st' hst hstor hr =>
          ⟨Reconstruction.State.reconstruct_inv hr hst,
           Reconstruction.State.reconstruct_storage hr hstor⟩)
  | ret a borrower =>
      exact State.update_inv h hinv
        (fun st st' hst hstor hr =>
          ⟨Reconstruction.State.return_inv hr hst,
           Reconstruction.State.return_storage hr hstor⟩)
  | free a =>
      exact State.free_inv h hinv

/-- An accepted command frames every other allocation: its lookup, and therefore
its snapshot, is unchanged. -/
theorem State.exec_frames_other {s s' : State} {c : Cmd}
    (h : s.exec c = some s') {b : AllocId} (hb : b ≠ c.allocId) :
    s'.find? b = s.find? b := by
  cases c with
  | alloc a n D pos rootId disposalId =>
      exact State.alloc_frames_other h (by simpa [Cmd.allocId] using hb)
  | write a id i v =>
      exact State.update_frames_other h (by simpa [Cmd.allocId] using hb)
  | borrow a lender borrower =>
      exact State.update_frames_other h (by simpa [Cmd.allocId] using hb)
  | splitSpatial a parentId c1 c2 lo1 hi1 lo2 hi2 =>
      exact State.update_frames_other h (by simpa [Cmd.allocId] using hb)
  | splitFraction a parentId c1 c2 q1 q2 =>
      exact State.update_frames_other h (by simpa [Cmd.allocId] using hb)
  | reconstruct a parentId =>
      exact State.update_frames_other h (by simpa [Cmd.allocId] using hb)
  | ret a borrower =>
      exact State.update_frames_other h (by simpa [Cmd.allocId] using hb)
  | free a =>
      exact State.free_frames_other h (by simpa [Cmd.allocId] using hb)

/-- Run a command list, stopping at the first refusal. -/
def State.run : State → List Cmd → Option State
  | s, [] => some s
  | s, c :: cs =>
      match s.exec c with
      | some s' => State.run s' cs
      | none => none

/-- An accepted command list frames every allocation no command targets: the
component lookup is unchanged across the whole run. -/
theorem State.run_frames_other {s s' : State} {cmds : List Cmd}
    (h : State.run s cmds = some s') {b : AllocId}
    (hmiss : ∀ c ∈ cmds, c.allocId ≠ b) :
    s'.find? b = s.find? b := by
  have H : ∀ (s s' : State), (∀ c ∈ cmds, c.allocId ≠ b) →
      State.run s cmds = some s' → s'.find? b = s.find? b := by
    clear h hmiss s s'
    induction cmds with
    | nil =>
        intro s s' hmiss h
        simp only [State.run, Option.some.injEq] at h
        subst s'
        rfl
    | cons c cs ih =>
        intro s s' hmiss h
        cases hexec : s.exec c with
        | none =>
            simp only [State.run, hexec] at h
            simp at h
        | some mid =>
            simp only [State.run, hexec] at h
            have hstep : mid.find? b = s.find? b :=
              State.exec_frames_other hexec (Ne.symm (hmiss c (by simp)))
            have hrest : ∀ d ∈ cs, d.allocId ≠ b :=
              fun d hd => hmiss d (List.mem_cons_of_mem c hd)
            exact (ih mid s' hrest h).trans hstep
  exact H s s' hmiss h

/-- An accepted run preserves the integrated invariant. -/
theorem State.run_inv {s s' : State} {cmds : List Cmd}
    (h : State.run s cmds = some s') (hinv : s.Inv) : s'.Inv := by
  revert s
  induction cmds with
  | nil =>
      intro s h hinv
      simp only [State.run, Option.some.injEq] at h
      subst s'
      exact hinv
  | cons c cs ih =>
      intro s h hinv
      cases hexec : s.exec c with
      | none =>
          simp only [State.run, hexec] at h
          simp at h
      | some mid =>
          simp only [State.run, hexec] at h
          exact ih h (State.exec_inv hexec hinv)

/-! ### The typed wrapper -/

/-- The boolean run of the real checker: true exactly when every step of the
command list is accepted. -/
def State.checkRun : State → List Cmd → Bool
  | _, [] => true
  | s, c :: cs =>
      match s.exec c with
      | some s' => State.checkRun s' cs
      | none => false

/-- A passing boolean run is an accepting run: no step is refused. -/
theorem State.checkRun_sound {s : State} {cmds : List Cmd}
    (h : State.checkRun s cmds = true) : ∃ s', State.run s cmds = some s' := by
  revert s
  induction cmds with
  | nil =>
      intro s _
      exact ⟨s, rfl⟩
  | cons c cs ih =>
      intro s h
      simp only [State.checkRun] at h
      cases hexec : s.exec c with
      | none => simp [hexec] at h
      | some mid =>
          simp only [hexec] at h
          obtain ⟨s'', hrun⟩ := ih h
          refine ⟨s'', ?_⟩
          show (match s.exec c with
              | some s' => State.run s' cs
              | none => none) = some s''
          rw [hexec]
          exact hrun

/-- A typed integrated program, indexed by its invariant start state and by the
evidence that the real checker accepts every step. -/
structure Prog (start : State) (_ : start.Inv) where
  cmds : List Cmd
  checked : State.checkRun start cmds = true

/-- The finish state of a program, if the run completes. -/
def Prog.finish? {start : State} {hstart : start.Inv} (p : Prog start hstart) :
    Option State :=
  State.run start p.cmds

/-- A program never refuses: its check witnesses an accepting run. -/
theorem Prog.never_refuses {start : State} {hstart : start.Inv}
    (p : Prog start hstart) : p.finish?.isSome = true := by
  obtain ⟨s', hs'⟩ := State.checkRun_sound p.checked
  show (State.run start p.cmds).isSome = true
  rw [hs']
  rfl

/-- A program's finish state satisfies the integrated invariant. -/
theorem Prog.finish_inv {start : State} {hstart : start.Inv}
    (p : Prog start hstart) {s' : State} (h : p.finish? = some s') : s'.Inv := by
  exact State.run_inv h hstart

/-! ### Observations -/

/-- A copy of one allocation's bytes. -/
def State.snapshot (s : State) (a : AllocId) : Option (List UInt8) :=
  match s.find? a with
  | some st => st.heap.snapshot? st.alloc
  | none => none

/-- One byte of one allocation. -/
def State.read? (s : State) (a : AllocId) (i : Nat) : Option UInt8 :=
  match s.find? a with
  | some st => st.heap.read? st.alloc i
  | none => none

/-- The exported description of a current fragment. -/
def stateFragment? (st : Reconstruction.State) (id : CapId) :
    Option Reconstruction.Fragment :=
  (st.forest.findLeaf? id).map (fun c =>
    { alloc := c.alloc, lo := c.lo, hi := c.hi, q := c.q,
      ceiling := c.ceiling, state := c.state })

/-- The current fragment of one allocation with the given access name. -/
def State.authority? (s : State) (a : AllocId) (id : CapId) :
    Option Reconstruction.Fragment :=
  match s.find? a with
  | some st => stateFragment? st id
  | none => none

/-- The access names retired by one allocation, most recent first. -/
def State.retiredOf (s : State) (a : AllocId) : List CapId :=
  match s.find? a with
  | some st => st.retired
  | none => []

/-- The outstanding return obligations of one allocation, most recent first. -/
def State.restoresOf (s : State) (a : AllocId) : List Reconstruction.Restore :=
  match s.find? a with
  | some st => st.restores
  | none => []

/-- An accepted run frames every allocation no command targets: its bytes are
unchanged. -/
theorem State.run_snapshot_other {s s' : State} {cmds : List Cmd}
    (h : State.run s cmds = some s') {b : AllocId}
    (hmiss : ∀ c ∈ cmds, c.allocId ≠ b) :
    s'.snapshot b = s.snapshot b := by
  rw [State.snapshot, State.snapshot, State.run_frames_other h hmiss]

/-- An accepted run leaves every allocation no command targets with exactly the
`Storage` certificate it had: one exists in the successor precisely when one
existed in the predecessor. -/
theorem State.run_storage_other {s s' : State} {cmds : List Cmd}
    (h : State.run s cmds = some s') {b : AllocId}
    (hmiss : ∀ c ∈ cmds, c.allocId ≠ b) :
    (∃ st, s'.find? b = some st ∧ st.Storage) ↔
      (∃ st, s.find? b = some st ∧ st.Storage) := by
  rw [State.run_frames_other h hmiss]

/-! ### The sealed boundary -/

/-- An integrated state reachable only through this module's checked operations,
carrying the integrated invariant. The pure state is exposed read-only for
composed proofs; the constructor, invariant field and mutations remain sealed. -/
structure Sealed where
  private mk ::
  private s : State
  private inv : s.Inv

private def mkSealed (s : State) (h : s.Inv) : Sealed := Sealed.mk s h

private def openSealed (s : Sealed) : State := s.s

/-- Every sealed state, however obtained, satisfies the integrated invariant. -/
theorem Sealed.invariant (s : Sealed) : s.s.Inv := s.inv

/-- The integrated state a sealed value carries. Read-only: the constructor and
the invariant field stay private, so a caller can inspect the state but cannot
manufacture a sealed value or replace its proof. -/
def Sealed.state (s : Sealed) : State := s.s

/-- The state a sealed value carries satisfies the integrated invariant. -/
theorem Sealed.state_inv (s : Sealed) : s.state.Inv := s.inv

/-- Two sealed values whose states agree are equal; the invariant field is a
proof and so carries no information. -/
theorem Sealed.eq_of_state {s t : Sealed} (h : s.s = t.s) : s = t := by
  obtain ⟨s0, hs⟩ := s
  obtain ⟨t0, ht⟩ := t
  have h0 : s0 = t0 := h
  cases h0
  exact congrArg (Sealed.mk _) (Subsingleton.elim _ _)

/-- The sealed state's live allocations. -/
def Sealed.allocations (s : Sealed) : List AllocId := (openSealed s).allocIds

/-- The canonical sealed state: one whole fresh allocation. -/
def Sealed.initial (a : AllocId) (n D : Nat) (pos : 0 < D)
    (rootId disposalId : CapId) : Sealed :=
  mkSealed (State.initial a n D pos rootId disposalId)
    (State.initial_inv a n D pos rootId disposalId)

/-- The 64-byte fixture: allocation `⟨0⟩` over `[0,64)` with share `64`, root
access name `⟨1⟩` and disposal name `⟨2⟩`. -/
def Sealed.initial64 : Sealed :=
  Sealed.initial ⟨0⟩ 64 64 (by decide) ⟨1⟩ ⟨2⟩

private def Sealed.runCmd (s : Sealed) (c : Cmd) (msg : String) :
    Except String Sealed :=
  match h : (openSealed s).exec c with
  | some s' => .ok (mkSealed s' (State.exec_inv h s.inv))
  | none => .error msg

/-- Add a fresh allocation. -/
def Sealed.alloc (s : Sealed) (a : AllocId) (n D : Nat) (pos : 0 < D)
    (rootId disposalId : CapId) : Except String Sealed :=
  s.runCmd (.alloc a n D pos rootId disposalId)
    "alloc refused: the allocation identifier or an initial capability name was already used"

/-- Write one byte through a current active whole-share fragment of a
read--write ceiling. -/
def Sealed.write (s : Sealed) (a : AllocId) (id : CapId) (i : Nat) (v : UInt8) :
    Except String Sealed :=
  s.runCmd (.write a id i v)
    "write refused: not an active whole-share read--write fragment or offset out of range"

/-- An accepted sealed write is exactly the underlying state's accepted write
command: the sealed boundary runs `State.exec` and returns the state it
produced, so a caller may reason about the write at either level. -/
theorem Sealed.write_ok_iff (s : Sealed) (a : AllocId) (id : CapId) (i : Nat)
    (v : UInt8) (s' : Sealed) :
    Sealed.write s a id i v = .ok s' ↔ s.state.exec (.write a id i v) = some s'.state := by
  unfold Sealed.write Sealed.runCmd
  split
  · rename_i s'' hexec
    constructor
    · intro h
      cases h
      simpa [Sealed.state, openSealed, mkSealed] using hexec
    · intro h
      have hst : s'' = s'.state := Option.some.inj (hexec.symm.trans h)
      have hstate : s' = mkSealed s'' (State.exec_inv hexec s.inv) :=
        Sealed.eq_of_state hst.symm
      subst hstate
      exact congrArg Except.ok (congrArg (mkSealed s'') (Subsingleton.elim _ _))
  · rename_i hnone
    constructor
    · intro h
      cases h
    · intro h
      simp only [Sealed.state, openSealed] at h hnone
      rw [hnone] at h
      simp at h

/-- A write command the underlying state accepts produces a sealed successor:
the boundary returns exactly the state the command produced. This is the
existence half of `Sealed.write_ok_iff` that a caller uses when it has derived
the state-level acceptance from the capability evidence rather than observed an
accepted write. -/
theorem Sealed.write_exists_of_exec (s : Sealed) (a : AllocId) (id : CapId)
    (i : Nat) (v : UInt8)
    (h : ∃ t : State, s.state.exec (.write a id i v) = some t) :
    ∃ s' : Sealed, Sealed.write s a id i v = .ok s' := by
  obtain ⟨t, ht⟩ := h
  refine ⟨mkSealed t (State.exec_inv ht s.inv), ?_⟩
  exact (Sealed.write_ok_iff s a id i v _).2 (by
    simpa [Sealed.state, mkSealed] using ht)

/-- Borrow a current active fragment of one allocation. -/
def Sealed.borrow (s : Sealed) (a : AllocId) (lender borrower : CapId) :
    Except String Sealed :=
  s.runCmd (.borrow a lender borrower)
    "borrow refused: lender is not an active current fragment or borrower name is not fresh"

/-- Spatially subdivide a current fragment of one allocation. -/
def Sealed.splitSpatial (s : Sealed) (a : AllocId) (parentId c1 c2 : CapId)
    (lo1 hi1 lo2 hi2 : Nat) : Except String Sealed :=
  s.runCmd (.splitSpatial a parentId c1 c2 lo1 hi1 lo2 hi2)
    "splitSpatial refused: children do not partition an active fragment or a child name is not fresh"

/-- Fractionally subdivide a current fragment of one allocation. -/
def Sealed.splitFraction (s : Sealed) (a : AllocId) (parentId c1 c2 : CapId)
    (q1 q2 : Nat) : Except String Sealed :=
  s.runCmd (.splitFraction a parentId c1 c2 q1 q2)
    "splitFraction refused: child shares are not positive and equal to the parent's or a child name is not fresh"

/-- Reconstruct a suspended fragment of one allocation. -/
def Sealed.reconstruct (s : Sealed) (a : AllocId) (parentId : CapId) :
    Except String Sealed :=
  s.runCmd (.reconstruct a parentId)
    "reconstruct refused: no suspension with that parent or a descendant is still subdivided or lent"

/-- Return a borrowed fragment of one allocation. -/
def Sealed.return (s : Sealed) (a : AllocId) (borrower : CapId) :
    Except String Sealed :=
  s.runCmd (.ret a borrower)
    "return refused: no matching obligation or the borrowed resource is not the reconstructed whole fragment"

/-- Free a whole active allocation with no outstanding obligation. -/
def Sealed.free (s : Sealed) (a : AllocId) : Except String Sealed :=
  s.runCmd (.free a)
    "free refused: not a single whole active leaf or a return obligation is outstanding"

/-- Run a command list inside the sealed boundary. The invariant is carried
through `State.run_inv`, so an accepted run yields a sealed state and a refused
step yields no state. -/
def Sealed.run (s : Sealed) (cmds : List Cmd) : Except String Sealed :=
  match h : State.run (openSealed s) cmds with
  | some s' => .ok (mkSealed s' (State.run_inv h s.inv))
  | none => .error "run refused: a command was rejected by the checker"

/-- An accepted sealed run is exactly the underlying state's accepted run: the
sealed boundary runs `State.run` and returns the state it produced, so a caller
may reason about a command list at either level. -/
theorem Sealed.run_ok_iff (s : Sealed) (cmds : List Cmd) (s' : Sealed) :
    s.run cmds = .ok s' ↔ State.run s.state cmds = some s'.state := by
  unfold Sealed.run
  split
  · rename_i s0 hrun
    constructor
    · intro h
      cases h
      simpa [Sealed.state, openSealed, mkSealed] using hrun
    · intro h
      have hst : s0 = s'.state := Option.some.inj (hrun.symm.trans h)
      have hstate : s' = mkSealed s0 (State.run_inv hrun s.inv) :=
        Sealed.eq_of_state hst.symm
      subst hstate
      exact congrArg Except.ok (congrArg (mkSealed s0) (Subsingleton.elim _ _))
  · rename_i hnone
    constructor
    · intro h
      cases h
    · intro h
      simp only [Sealed.state, openSealed] at h hnone
      rw [hnone] at h
      simp at h

/-- An accepted run's sealed result carries the integrated invariant. -/
theorem Sealed.run_invariant {s s' : Sealed} {cmds : List Cmd}
    (h : s.run cmds = .ok s') : s'.s.Inv := s'.inv

/-- A copy of one allocation's bytes. -/
def Sealed.snapshot (s : Sealed) (a : AllocId) : Option (List UInt8) :=
  (openSealed s).snapshot a

/-- Read one byte of one allocation. -/
def Sealed.read? (s : Sealed) (a : AllocId) (i : Nat) : Option UInt8 :=
  (openSealed s).read? a i

/-- The current fragment of one allocation with the given access name. -/
def Sealed.authority? (s : Sealed) (a : AllocId) (id : CapId) :
    Option Reconstruction.Fragment :=
  (openSealed s).authority? a id

/-- The access names retired by one allocation, most recent first. -/
def Sealed.retiredOf (s : Sealed) (a : AllocId) : List CapId :=
  (openSealed s).retiredOf a

/-- The outstanding return obligations of one allocation, most recent first. -/
def Sealed.restoresOf (s : Sealed) (a : AllocId) : List Reconstruction.Restore :=
  (openSealed s).restoresOf a

/-- What an accepted sealed command list leaves alone for an allocation no
command targets: its component is the same `Reconstruction.State`, so its bytes
and its `Storage` certificate are unchanged too. -/
structure Sealed.RunFrame (s s' : Sealed) (b : AllocId) : Prop where
  /-- The allocation's component is the same `Reconstruction.State`. -/
  component : s'.state.find? b = s.state.find? b
  /-- Its bytes are unchanged. -/
  snapshot : s'.snapshot b = s.snapshot b
  /-- Its `Storage` certificate holds exactly when it did before. -/
  storage : (∃ st, s'.state.find? b = some st ∧ st.Storage) ↔
    (∃ st, s.state.find? b = some st ∧ st.Storage)

/-- An accepted sealed run frames every allocation no command targets. -/
theorem Sealed.run_frames_other {s s' : Sealed} {cmds : List Cmd}
    (h : s.run cmds = .ok s') {b : AllocId}
    (hmiss : ∀ c ∈ cmds, c.allocId ≠ b) : Sealed.RunFrame s s' b := by
  have hrun : State.run s.state cmds = some s'.state :=
    (Sealed.run_ok_iff s cmds s').mp h
  refine ⟨State.run_frames_other hrun hmiss, ?_, ?_⟩
  · show s'.state.snapshot b = s.state.snapshot b
    exact State.run_snapshot_other hrun hmiss
  · exact State.run_storage_other hrun hmiss

/-! ### The 64-byte lifecycle -/

/-- The 64-byte lifecycle on allocation `⟨0⟩`: borrow the whole fragment `⟨1⟩`
as `⟨3⟩`, split it into `⟨4⟩ : [0,32)` and `⟨5⟩ : [32,64)`, write both halves,
reconstruct `[0,64)`, and return `⟨3⟩` to `⟨1⟩`. -/
def Sealed.lifecycle64 (s : Sealed) : Except String Sealed := do
  let s1 ← s.borrow ⟨0⟩ ⟨1⟩ ⟨3⟩
  let s2 ← s1.splitSpatial ⟨0⟩ ⟨3⟩ ⟨4⟩ ⟨5⟩ 0 32 32 64
  let s3 ← s2.write ⟨0⟩ ⟨4⟩ 0 7
  let s4 ← s3.write ⟨0⟩ ⟨5⟩ 40 9
  let s5 ← s4.reconstruct ⟨0⟩ ⟨3⟩
  s5.return ⟨0⟩ ⟨3⟩

/-- A second full cycle on the output of the first: borrow `⟨1⟩` as `⟨6⟩`, split
it, write both halves at different offsets, reconstruct and return `⟨6⟩`. -/
def Sealed.reuseLifecycle (s : Sealed) : Except String Sealed := do
  let s1 ← s.borrow ⟨0⟩ ⟨1⟩ ⟨6⟩
  let s2 ← s1.splitSpatial ⟨0⟩ ⟨6⟩ ⟨7⟩ ⟨8⟩ 0 32 32 64
  let s3 ← s2.write ⟨0⟩ ⟨7⟩ 1 12
  let s4 ← s3.write ⟨0⟩ ⟨8⟩ 33 13
  let s5 ← s4.reconstruct ⟨0⟩ ⟨6⟩
  s5.return ⟨0⟩ ⟨6⟩

/-- The first lifecycle followed by the second. -/
def lifecycle64ThenReuse : Except String Sealed := do
  let s ← Sealed.lifecycle64 Sealed.initial64
  s.reuseLifecycle

/-- The first lifecycle followed by allocating a second 32-byte allocation
`⟨1⟩` with root `⟨10⟩`, writing through its root, so a multi-allocation state is
accepted on the output. -/
def lifecycle64ThenAlloc : Except String Sealed := do
  let s ← Sealed.lifecycle64 Sealed.initial64
  let s1 ← s.alloc ⟨1⟩ 32 32 (by decide) ⟨10⟩ ⟨11⟩
  s1.write ⟨1⟩ ⟨10⟩ 0 5

/-- The second allocation's bytes after its root write. -/
def secondAllocBytes : List UInt8 := 5 :: List.replicate 31 0

/-- The second allocation's whole active fragment. -/
def secondAllocFragment : Reconstruction.Fragment :=
  { alloc := ⟨1⟩, lo := 0, hi := 32, q := 32, ceiling := .readWrite, state := .active }

/-- The restored whole fragment of the 64-byte fixture, as observed. -/
def wholeFragment64 : Reconstruction.Fragment := Reconstruction.wholeFragment

/-- The lifecycle is accepted. -/
theorem lifecycle64_ok : (Sealed.lifecycle64 Sealed.initial64).isOk = true := by
  decide

/-- The bytes the two children wrote survive reconstruction and return. -/
theorem lifecycle64_snapshot :
    (Sealed.lifecycle64 Sealed.initial64).toOption.map
        (fun s => s.snapshot ⟨0⟩) =
      some (some Reconstruction.firstSnapshot) := by
  decide

/-- The restored lender is the whole `[0,64)` fragment and the parent and child
names are gone from the current frontier. -/
theorem lifecycle64_authority :
    (Sealed.lifecycle64 Sealed.initial64).toOption.map
        (fun s => (s.authority? ⟨0⟩ ⟨1⟩, s.authority? ⟨0⟩ ⟨3⟩,
          s.authority? ⟨0⟩ ⟨4⟩, s.authority? ⟨0⟩ ⟨5⟩)) =
      some (some wholeFragment64, none, none, none) := by
  decide

/-- The borrowed and child names are retired and the obligation is discharged. -/
theorem lifecycle64_retired :
    (Sealed.lifecycle64 Sealed.initial64).toOption.map
        (fun s => s.retiredOf ⟨0⟩) = some [⟨3⟩, ⟨4⟩, ⟨5⟩] := by
  decide

/-- The completed lifecycle leaves no outstanding return obligation. -/
theorem lifecycle64_restores :
    (Sealed.lifecycle64 Sealed.initial64).toOption.map
        (fun s => s.restoresOf ⟨0⟩) =
      some ([] : List Reconstruction.Restore) := by
  decide

/-- An accepted lifecycle observes exactly the two written bytes. -/
theorem lifecycle64_snapshot_of_ok {s' : Sealed}
    (h : Sealed.lifecycle64 Sealed.initial64 = .ok s') :
    s'.snapshot ⟨0⟩ = some Reconstruction.firstSnapshot := by
  have hc := lifecycle64_snapshot
  rw [h] at hc
  change some (s'.snapshot ⟨0⟩) =
    some (some Reconstruction.firstSnapshot) at hc
  simpa using hc

/-- An accepted lifecycle restores the whole lender fragment and retires the
parent and both children. -/
theorem lifecycle64_authority_of_ok {s' : Sealed}
    (h : Sealed.lifecycle64 Sealed.initial64 = .ok s') :
    s'.authority? ⟨0⟩ ⟨1⟩ = some wholeFragment64 ∧
      s'.authority? ⟨0⟩ ⟨3⟩ = none ∧ s'.authority? ⟨0⟩ ⟨4⟩ = none ∧
      s'.authority? ⟨0⟩ ⟨5⟩ = none := by
  have hc := lifecycle64_authority
  rw [h] at hc
  change some (s'.authority? ⟨0⟩ ⟨1⟩, s'.authority? ⟨0⟩ ⟨3⟩,
      s'.authority? ⟨0⟩ ⟨4⟩, s'.authority? ⟨0⟩ ⟨5⟩) =
      some (some wholeFragment64, none, none, none) at hc
  simpa only [Option.some.injEq, Prod.mk.injEq, and_assoc] using hc

/-- An accepted lifecycle retires the borrowed and child names. -/
theorem lifecycle64_retired_of_ok {s' : Sealed}
    (h : Sealed.lifecycle64 Sealed.initial64 = .ok s') :
    s'.retiredOf ⟨0⟩ = [⟨3⟩, ⟨4⟩, ⟨5⟩] := by
  have hc := lifecycle64_retired
  rw [h] at hc
  change some (s'.retiredOf ⟨0⟩) = some [⟨3⟩, ⟨4⟩, ⟨5⟩] at hc
  simpa using hc

/-- An accepted lifecycle leaves no outstanding return obligation. -/
theorem lifecycle64_restores_of_ok {s' : Sealed}
    (h : Sealed.lifecycle64 Sealed.initial64 = .ok s') :
    s'.restoresOf ⟨0⟩ = [] := by
  have hc := lifecycle64_restores
  rw [h] at hc
  change some (s'.restoresOf ⟨0⟩) =
    some ([] : List Reconstruction.Restore) at hc
  simpa using hc

/-- An accepted lifecycle carries the integrated invariant. -/
theorem lifecycle64_inv_of_ok {s' : Sealed}
    (_h : Sealed.lifecycle64 Sealed.initial64 = .ok s') : s'.s.Inv := s'.inv

/-! ### Reuse on the lifecycle's output -/

/-- The second cycle is accepted on the first cycle's output. -/
theorem reuse64_ok : lifecycle64ThenReuse.isOk = true := by
  decide

/-- Both cycles' writes are observed: the first cycle's bytes survive the second
cycle, and the second cycle's bytes are added. -/
theorem reuse64_snapshot :
    lifecycle64ThenReuse.toOption.map (fun s => s.snapshot ⟨0⟩) =
      some (some Reconstruction.secondSnapshot) := by
  decide

/-- After both cycles the lender again holds the whole fragment and all four
borrower and child names of the second cycle are gone. -/
theorem reuse64_authority :
    lifecycle64ThenReuse.toOption.map
        (fun s => (s.authority? ⟨0⟩ ⟨1⟩, s.authority? ⟨0⟩ ⟨6⟩,
          s.authority? ⟨0⟩ ⟨7⟩, s.authority? ⟨0⟩ ⟨8⟩)) =
      some (some wholeFragment64, none, none, none) := by
  decide

/-- Both cycles' names are retired, most recent first. -/
theorem reuse64_retired :
    lifecycle64ThenReuse.toOption.map (fun s => s.retiredOf ⟨0⟩) =
      some [⟨6⟩, ⟨7⟩, ⟨8⟩, ⟨3⟩, ⟨4⟩, ⟨5⟩] := by
  decide

/-- An accepted second cycle again restores the whole lender fragment. -/
theorem reuse64_authority_of_ok {s' : Sealed}
    (h : lifecycle64ThenReuse = .ok s') :
    s'.authority? ⟨0⟩ ⟨1⟩ = some wholeFragment64 ∧
      s'.authority? ⟨0⟩ ⟨6⟩ = none ∧ s'.authority? ⟨0⟩ ⟨7⟩ = none ∧
      s'.authority? ⟨0⟩ ⟨8⟩ = none := by
  have hc := reuse64_authority
  rw [h] at hc
  change some (s'.authority? ⟨0⟩ ⟨1⟩, s'.authority? ⟨0⟩ ⟨6⟩,
      s'.authority? ⟨0⟩ ⟨7⟩, s'.authority? ⟨0⟩ ⟨8⟩) =
      some (some wholeFragment64, none, none, none) at hc
  simpa only [Option.some.injEq, Prod.mk.injEq, and_assoc] using hc

/-- An accepted second cycle carries the integrated invariant. -/
theorem reuse64_inv_of_ok {s' : Sealed}
    (_h : lifecycle64ThenReuse = .ok s') : s'.s.Inv := s'.inv

/-! ### A second allocation on the lifecycle's output -/

/-- The lifecycle followed by a second allocation and a root write is accepted. -/
theorem lifecycleThenAlloc_ok : lifecycle64ThenAlloc.isOk = true := by
  decide

/-- The first allocation's bytes are unchanged and the second allocation holds
the byte written through its root. -/
theorem lifecycleThenAlloc_snapshot :
    lifecycle64ThenAlloc.toOption.map
        (fun s => (s.snapshot ⟨0⟩, s.snapshot ⟨1⟩, s.read? ⟨1⟩ 0,
          s.allocations)) =
      some (some Reconstruction.firstSnapshot, some secondAllocBytes, some 5,
        [⟨1⟩, ⟨0⟩]) := by
  decide

/-- The second allocation is an active whole-share fragment. -/
theorem lifecycleThenAlloc_authority :
    lifecycle64ThenAlloc.toOption.map (fun s => s.authority? ⟨1⟩ ⟨10⟩) =
      some (some secondAllocFragment) := by
  decide

/-- An accepted run carries the integrated invariant. -/
theorem lifecycleThenAlloc_inv_of_ok {s' : Sealed}
    (_h : lifecycle64ThenAlloc = .ok s') : s'.s.Inv := s'.inv

/-! ### A command list over two allocations -/

/-- The two-allocation sealed state: the 64-byte lifecycle's output with the
second 32-byte allocation added and its root written. -/
def twoAllocSealed : Sealed :=
  match lifecycle64ThenAlloc with
  | .ok s => s
  | .error _ => Sealed.initial64

/-- A command list that writes only the second allocation. -/
def secondAllocRun : List Cmd :=
  [ .write ⟨1⟩ ⟨10⟩ 31 21 ]

/-- No command of the list targets the first allocation. -/
theorem secondAllocRun_untargeted :
    ∀ c ∈ secondAllocRun, c.allocId ≠ (⟨0⟩ : AllocId) := by
  intro c hc
  simp only [secondAllocRun, List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl
  decide

/-- The two-command run on the second allocation is accepted. -/
theorem secondAllocRun_ok : (twoAllocSealed.run secondAllocRun).isOk = true := by
  decide

/-- The run frames the first allocation: its component, bytes and `Storage`
certificate are unchanged. -/
theorem secondAllocRun_frames {s' : Sealed}
    (h : twoAllocSealed.run secondAllocRun = .ok s') :
    s'.state.find? ⟨0⟩ = twoAllocSealed.state.find? ⟨0⟩ ∧
      s'.snapshot ⟨0⟩ = twoAllocSealed.snapshot ⟨0⟩ ∧
      ((∃ st, s'.state.find? ⟨0⟩ = some st ∧ st.Storage) ↔
        (∃ st, twoAllocSealed.state.find? ⟨0⟩ = some st ∧ st.Storage)) := by
  have hf := Sealed.run_frames_other h secondAllocRun_untargeted
  exact ⟨hf.component, hf.snapshot, hf.storage⟩

/-- The first allocation still holds the lifecycle's bytes, the second holds the
byte the list wrote and the byte it had, and both allocations are live. -/
theorem secondAllocRun_observes :
    (twoAllocSealed.run secondAllocRun).toOption.map
        (fun s => (s.snapshot ⟨0⟩, s.read? ⟨1⟩ 31, s.read? ⟨1⟩ 0,
          s.allocations)) =
      some (some Reconstruction.firstSnapshot, some 21, some 5, [⟨1⟩, ⟨0⟩]) := by
  decide

/-! ### The typed lifecycle -/

/-- The 64-byte lifecycle as a typed program: the boolean run of the real
checker accepts every step, so the program never refuses. -/
def lifecycle64Prog : Prog State.initial64 State.initial64_inv where
  cmds :=
    [ .borrow ⟨0⟩ ⟨1⟩ ⟨3⟩,
      .splitSpatial ⟨0⟩ ⟨3⟩ ⟨4⟩ ⟨5⟩ 0 32 32 64,
      .write ⟨0⟩ ⟨4⟩ 0 7,
      .write ⟨0⟩ ⟨5⟩ 40 9,
      .reconstruct ⟨0⟩ ⟨3⟩,
      .ret ⟨0⟩ ⟨3⟩ ]
  checked := by decide

/-- The typed lifecycle never refuses. -/
theorem lifecycle64Prog_no_refusal : lifecycle64Prog.finish?.isSome = true :=
  lifecycle64Prog.never_refuses

/-- The typed lifecycle's finish state, when it completes, is invariant. -/
theorem lifecycle64Prog_finish_inv {s' : State}
    (h : lifecycle64Prog.finish? = some s') : s'.Inv :=
  lifecycle64Prog.finish_inv h

end Integrated

end Cap
