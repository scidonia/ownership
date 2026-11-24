/-
The single legal-disposal predicate for the model.

`DisposalState` pairs a `World` with the loan bookkeeping that the world itself
does not carry. `Legal` is the one predicate under which an allocation may be
freed: `findOwner?` returns an owner for the allocation, that owner is fully
covered, the supplied capability is its recorded disposal entitlement, the loan
list is empty, and the owner's root view is reconstructed (the design's
`rootReconstructed`: the decomposition is a single active leaf of the whole share
over the whole allocation, so no delegated fragment is outstanding). Because
`Ctx.Realizes` in `World.Rel` keeps allocation identifiers distinct, the owner
`findOwner?` returns is the unique owner of the allocation.

`free?` is the checked disposal route. It succeeds exactly when those
conditions hold, runs `World.freeWith?` (hence `Ctx.freeWith?`, so the context
side is the existing disposal check), and clears the backend at the allocation.
The remaining capability names are invalidated by the owner's removal: every
lookup goes through `findOwner?`, which no longer resolves the allocation.

Proved:
* `free?_spec` — a successful disposal exposes the owner, the root leaf, the
  entitlement, the empty loan list and the resulting world.
* `free?_none_of_not_legal` — a state that is not legal refuses disposal.
* `free?_legal` — a legal state disposes, yielding a successor state.
* `free?_removes_owner` — after disposal the allocation has no owner, so its
  capability names do not resolve.
* `free?_none_after_free` — the entitlement cannot be replayed.
* `free?_none_of_disposal_ne` / `free?_none_of_loan` — the two refusals.
* Concrete examples: missing entitlement refused, outstanding loan refused, and
  a legal disposal that succeeds and leaves no owner for the allocation.

This is the single legal-disposal predicate for the model. It is not yet wired
into `Cap.Unified`, whose instruction language still covers writes and no-ops
only. The predicate does not derive the root view from a capability state, and
it does not model arena generation: names of the freed allocation are invalidated
by the owner's removal, not by reuse of their numbers.
-/
import Cap.World
import Cap.Loans

namespace Cap

/-! ### Looking an owner up and freeing it -/

/-- An owner returned by `findOwner?` is recorded for the requested allocation. -/
private theorem findOwner?_alloc {C : Ctx} {a : AllocId} {o : Owner}
    (h : C.findOwner? a = some o) : o.alloc = a := by
  unfold Ctx.findOwner? at h
  have hp : (fun x : Owner => decide (x.alloc = a)) o = true :=
    List.find?_some (p := fun x : Owner => decide (x.alloc = a)) h
  exact of_decide_eq_true hp

/-- Freeing an allocation leaves no owner for it. -/
private theorem findOwner?_free (C : Ctx) (a : AllocId) :
    (C.free a).findOwner? a = none := by
  unfold Ctx.free Ctx.findOwner?
  rw [List.find?_eq_none]
  intro x hx
  exact fun hpx => of_decide_eq_true (List.mem_filter.mp hx).2
    (of_decide_eq_true hpx)

/-- A successful context disposal leaves no owner for the allocation. -/
private theorem findOwner?_freeWith {C C' : Ctx} {a : AllocId} {d : CapId}
    (h : C.freeWith? a d = some C') : C'.findOwner? a = none := by
  unfold Ctx.freeWith? at h
  cases hf : C.findOwner? a with
  | none => simp [hf] at h
  | some o =>
    by_cases hd : o.disposal = d
    · simp [hf, hd] at h
      cases h
      exact findOwner?_free C a
    · simp [hf, hd] at h

/-- A successful world disposal leaves no owner for the allocation. -/
theorem World.freeWith?_removes_owner {w w' : World} {a : AllocId} {d : CapId}
    (h : w.freeWith? a d = some w') : w'.ctx.findOwner? a = none := by
  unfold World.freeWith? at h
  cases hc : w.ctx.freeWith? a d with
  | none => simp [hc] at h
  | some ctx' =>
    simp [hc] at h
    cases h
    exact findOwner?_freeWith hc

/-! ### The disposal state and its predicate -/

/-- The root authority is reconstructed: the owner's decomposition is a single
active leaf carrying the whole share over the whole allocation, so no delegated
fragment remains. This is the design's `rootReconstructed` condition, stated as a
shape on the tree because the model has no separate root view. -/
def Owner.RootReconstructed (o : Owner) (D : Nat) : Prop :=
  ∃ c, o.root = .leaf c ∧ c.state = .active ∧ c.q = D ∧ c.alloc = o.alloc ∧
    c.lo = 0 ∧ c.hi = o.len

/-- A reconstructed root is covered. -/
theorem Owner.rootReconstructed_covered {o : Owner} {D : Nat}
    (h : o.RootReconstructed D) : o.Covered D := by
  obtain ⟨c, hr, hstate, hq, _halloc, hlo, hhi⟩ := h
  intro x hx
  have hne : c.state ≠ .consumed := by rw [hstate]; decide
  have hx' : c.lo ≤ x ∧ x < c.hi := by
    rw [hlo, hhi]
    exact ⟨Nat.zero_le x, hx⟩
  rw [hr]
  simp [Tree.budget, Leaf.budget, hne, hx', hq]

/-- A world together with the loan bookkeeping a disposal must also consult. -/
structure DisposalState where
  world : World
  loans : LoanCtx

/-- The owner at `a` is the unique owner of that allocation (`findOwner?` returns
it and allocation identifiers are distinct under `Ctx.Realizes`), it is fully
covered, the supplied capability is its recorded disposal entitlement, no loan is
outstanding, and the root view is reconstructed. -/
def DisposalState.Legal (s : DisposalState) (a : AllocId) (d : CapId) : Prop :=
  ∃ o, s.world.ctx.findOwner? a = some o ∧ o.Covered s.world.ctx.D ∧
    o.disposal = d ∧ s.loans.loans = [] ∧ o.RootReconstructed s.world.ctx.D

/-- Checked disposal. It succeeds only on a legal state, frees the allocation
through `World.freeWith?` (which dispatches `Ctx.freeWith?`) and clears the
backend at that allocation. -/
def DisposalState.free? (s : DisposalState) (a : AllocId) (d : CapId) :
    Option DisposalState :=
  match s.world.ctx.findOwner? a with
  | none => none
  | some o =>
    if o.disposal = d then
      match s.loans.loans with
      | [] =>
        match o.root with
        | .leaf c =>
          if c.state = .active ∧ c.q = s.world.ctx.D ∧ c.alloc = a ∧
              c.lo = 0 ∧ c.hi = o.len then
            (s.world.freeWith? a d).map (fun w => { s with world := w })
          else none
        | .frac _ _ _ => none
        | .spatial _ _ _ => none
      | _ :: _ => none
    else none

/-- A successful disposal exposes exactly the facts its check used. -/
theorem DisposalState.free?_spec {s s' : DisposalState} {a : AllocId} {d : CapId}
    (h : s.free? a d = some s') :
    ∃ o c w, s.world.ctx.findOwner? a = some o ∧ o.disposal = d ∧
      s.loans.loans = [] ∧ o.root = .leaf c ∧ c.state = .active ∧
      c.q = s.world.ctx.D ∧ c.alloc = a ∧ c.lo = 0 ∧ c.hi = o.len ∧
      s.world.freeWith? a d = some w ∧ s' = { s with world := w } := by
  unfold DisposalState.free? at h
  cases hf : s.world.ctx.findOwner? a with
  | none =>
    rw [hf] at h
    cases h
  | some o =>
    rw [hf] at h
    dsimp only at h
    by_cases hd : o.disposal = d
    · rw [ite_eq_left hd] at h
      cases hl : s.loans.loans with
      | nil =>
        rw [hl] at h
        dsimp only at h
        cases hr : o.root with
        | leaf c =>
          rw [hr] at h
          dsimp only at h
          by_cases hc : c.state = .active ∧ c.q = s.world.ctx.D ∧
              c.alloc = a ∧ c.lo = 0 ∧ c.hi = o.len
          · rw [ite_eq_left hc] at h
            cases hw : s.world.freeWith? a d with
            | none =>
              rw [hw] at h
              cases h
            | some w =>
              rw [hw] at h
              change some { s with world := w } = some s' at h
              have hs' : s' = { s with world := w } := (Option.some.inj h).symm
              exact ⟨o, c, w, rfl, hd, rfl, hr, hc.1, hc.2.1, hc.2.2.1,
                hc.2.2.2.1, hc.2.2.2.2, rfl, hs'⟩
          · rw [ite_eq_right hc] at h
            cases h
        | frac i l r =>
          rw [hr] at h
          cases h
        | spatial i l r =>
          rw [hr] at h
          cases h
      | cons x xs =>
        rw [hl] at h
        cases h
    · rw [ite_eq_right hd] at h
      cases h

/-- A successful disposal is legal. -/
theorem DisposalState.legal_of_free? {s s' : DisposalState} {a : AllocId} {d : CapId}
    (h : s.free? a d = some s') : s.Legal a d := by
  obtain ⟨o, c, _w, hf, hd, hl, hr, hstate, hq, halloc, hlo, hhi, _hw, _hs'⟩ :=
    free?_spec h
  have hoalloc : o.alloc = a := findOwner?_alloc hf
  have hroot : o.RootReconstructed s.world.ctx.D :=
    ⟨c, hr, hstate, hq, halloc.trans hoalloc.symm, hlo, hhi⟩
  exact ⟨o, hf, Owner.rootReconstructed_covered hroot, hd, hl, hroot⟩

/-- A state that is not legal refuses disposal. -/
theorem DisposalState.free?_none_of_not_legal {s : DisposalState} {a : AllocId}
    {d : CapId} (h : ¬ s.Legal a d) : s.free? a d = none := by
  cases hf : s.free? a d with
  | none => rfl
  | some s' => exact absurd (legal_of_free? hf) h

/-- A spatial root is not reconstructed, so disposal refuses it. This names the
  unsupported case rather than deriving refusal from a failed shape match. -/
theorem DisposalState.free?_none_of_spatial_root {s : DisposalState} {a : AllocId}
    {d : CapId} {o : Owner} {id : CapId} {l r : Tree}
    (hf : s.world.ctx.findOwner? a = some o) (hr : o.root = .spatial id l r) :
    s.free? a d = none := by
  apply DisposalState.free?_none_of_not_legal
  intro hl
  obtain ⟨o', hf', _hcov, _hd, _hloans, hroot⟩ := hl
  rw [hf] at hf'
  cases hf'
  obtain ⟨c, hc, _hstate, _hq, _halloc, _hlo, _hhi⟩ := hroot
  rw [hr] at hc
  cases hc

/-- A legal state disposes. -/
theorem DisposalState.free?_legal {s : DisposalState} {a : AllocId} {d : CapId}
    (hl : s.Legal a d) : ∃ s', s.free? a d = some s' := by
  obtain ⟨o, hf, _hcov, hd, hloans, hroot⟩ := hl
  obtain ⟨c, hrootleaf, hstate, hq, halloc, hlo, hhi⟩ := hroot
  have hoalloc : o.alloc = a := findOwner?_alloc hf
  have hc : c.state = .active ∧ c.q = s.world.ctx.D ∧ c.alloc = a ∧
      c.lo = 0 ∧ c.hi = o.len :=
    ⟨hstate, hq, halloc.trans hoalloc, hlo, hhi⟩
  let w : World := { s.world with ctx := s.world.ctx.free a, heaps := fun x => if x = a then none else s.world.heaps x }
  have hw : s.world.freeWith? a d = some w := by
    dsimp only [w]
    unfold World.freeWith? Ctx.freeWith?
    rw [hf]
    simp [hd]
  have hval : s.free? a d = some { s with world := w } := by
    unfold DisposalState.free?
    rw [hf]
    dsimp only
    rw [ite_eq_left hd]
    rw [hloans]
    dsimp only
    rw [hrootleaf]
    dsimp only
    rw [ite_eq_left hc]
    rw [hw]
    rfl
  exact ⟨{ s with world := w }, hval⟩

/-- After a successful disposal the allocation has no owner, so the remaining
capability names for it no longer resolve. -/
theorem DisposalState.free?_removes_owner {s s' : DisposalState} {a : AllocId}
    {d : CapId} (h : s.free? a d = some s') : s'.world.ctx.findOwner? a = none := by
  obtain ⟨_o, _c, w, _hf, _hd, _hl, _hr, _hs, _hq, _ha, _hlo, _hhi, hw, hs'⟩ :=
    free?_spec h
  rw [hs']
  exact World.freeWith?_removes_owner hw

/-- The entitlement cannot be replayed: a disposed state refuses the same
allocation and capability. -/
theorem DisposalState.free?_none_after_free {s s' : DisposalState} {a : AllocId}
    {d : CapId} (h : s.free? a d = some s') : s'.free? a d = none := by
  unfold DisposalState.free?
  rw [DisposalState.free?_removes_owner h]

/-- A capability other than the recorded entitlement is refused. -/
theorem DisposalState.free?_none_of_disposal_ne {s : DisposalState} {a : AllocId}
    {d : CapId} {o : Owner} (hf : s.world.ctx.findOwner? a = some o)
    (hd : o.disposal ≠ d) : s.free? a d = none := by
  unfold DisposalState.free?
  rw [hf]
  dsimp only
  rw [ite_eq_right hd]

/-- An outstanding loan refuses disposal. -/
theorem DisposalState.free?_none_of_loan {s : DisposalState} {a : AllocId} {d : CapId}
    {o : Owner} (hf : s.world.ctx.findOwner? a = some o) (hl : s.loans.loans ≠ []) :
    s.free? a d = none := by
  unfold DisposalState.free?
  rw [hf]
  dsimp only
  by_cases hd : o.disposal = d
  · rw [ite_eq_left hd]
    cases hls : s.loans.loans with
    | nil => exact absurd hls hl
    | cons x xs => rfl
  · rw [ite_eq_right hd]

/-! ### Concrete checks -/

namespace DisposalExamples

/-- The example's allocation. -/
def alloc : AllocId := ⟨0⟩

/-- The whole-share root leaf of the example allocation. -/
def rootLeaf : Leaf :=
  { id := ⟨1⟩, alloc := alloc, lo := 0, hi := 64, ordered := by decide,
    q := 64, pos := by decide, ceiling := .readWrite, state := .active }

/-- The example owner: one 64-byte whole-share leaf and its disposal capability. -/
def owner : Owner :=
  { alloc := alloc, len := 64, root := .leaf rootLeaf, disposal := ⟨2⟩ }

/-- The example world: one owner and its backend. -/
def world : World :=
  { ctx := { owners := [owner], D := 64, nextAlloc := 1, issued := [⟨2⟩, ⟨1⟩], loans := .rootOnly },
    heaps := fun a => if a = alloc then some (Backend.empty 64) else none }

/-- The example disposal state: no loans are outstanding. -/
def state : DisposalState := { world := world, loans := ⟨[], []⟩ }

theorem owner_covered : owner.Covered 64 :=
  Owner.rootReconstructed_covered
    ⟨rootLeaf, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem findOwner : state.world.ctx.findOwner? alloc = some owner := by
  simp [state, world, owner, alloc, Ctx.findOwner?]

theorem state_legal : state.Legal alloc ⟨2⟩ := by
  refine ⟨owner, findOwner, owner_covered, rfl, rfl, ?_⟩
  exact ⟨rootLeaf, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- A capability that is not the recorded entitlement cannot dispose. -/
theorem state_not_legal_missing : ¬ state.Legal alloc ⟨9⟩ := by
  intro h
  obtain ⟨o, hf, _hcov, hd, _hloans, _hroot⟩ := h
  rw [findOwner] at hf
  have ho : o = owner := (Option.some.inj hf).symm
  rw [ho] at hd
  have hdisp : (⟨2⟩ : CapId) = ⟨9⟩ := hd
  exact absurd hdisp (by decide)

example : state.free? alloc ⟨9⟩ = none :=
  DisposalState.free?_none_of_not_legal state_not_legal_missing

/-- An outstanding loan refuses disposal. -/
def loanState : DisposalState :=
  { state with loans := ⟨[], [{ id := ⟨0⟩, alloc := ⟨0⟩, lender := ⟨1⟩, borrower := ⟨3⟩, lifetime := ⟨0⟩ }]⟩ }

theorem loanState_not_legal : ¬ loanState.Legal alloc ⟨2⟩ := by
  intro h
  obtain ⟨_o, _hf, _hcov, _hd, hloans, _hroot⟩ := h
  have hnonempty : loanState.loans.loans ≠ [] := by simp [loanState, state]
  exact hnonempty hloans

example : loanState.free? alloc ⟨2⟩ = none :=
  DisposalState.free?_none_of_not_legal loanState_not_legal

/-- A legal disposal succeeds. -/
example : ∃ s', state.free? alloc ⟨2⟩ = some s' :=
  DisposalState.free?_legal state_legal

/-- A legal disposal is accepted by the checked route. -/
example : (state.free? alloc ⟨2⟩).isSome = true := by
  obtain ⟨s', hs'⟩ := DisposalState.free?_legal state_legal
  rw [hs']
  rfl

/-- A legal disposal leaves no owner for the allocation. -/
example (s' : DisposalState) (h : state.free? alloc ⟨2⟩ = some s') :
    s'.world.ctx.findOwner? alloc = none :=
  DisposalState.free?_removes_owner h

/-- The entitlement cannot be replayed after the allocation is gone. -/
example (s' : DisposalState) (h : state.free? alloc ⟨2⟩ = some s') :
    s'.free? alloc ⟨2⟩ = none :=
  DisposalState.free?_none_after_free h

end DisposalExamples

end Cap
