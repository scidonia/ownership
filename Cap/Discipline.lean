/-
A checked world coupled to a nested delegation chain.

The correspondence requires the world's loan list to be exactly the chain edges,
the chain holder to be the active leaf, and the chain's allocation, footprint,
share and ceiling to agree with that leaf. Writes through the holder preserve the
correspondence because they change only the backend.
-/
import Cap.Borrow
import Cap.Delegation
import Cap.Unified

namespace Cap

namespace Discipline

/-- The loan records represented by a delegation chain. -/
def chainToLoans (c : Delegation.Chain) : List Loan :=
  c.edges.map (fun e =>
    { id := e.id, alloc := e.alloc, lender := e.lender,
      borrower := e.borrower, lifetime := e.lifetime })

/-- A world coupled to a delegation chain. -/
structure State where
  world : World
  chain : Delegation.Chain

/-- The correspondence invariant. -/
def State.OK (s : State) : Prop :=
  s.world.BorrowOK
  ∧ s.chain.OK
  ∧ s.world.ctx.loans.loans = chainToLoans s.chain
  ∧ ∃ o c, s.world.ctx.findOwner? s.chain.alloc = some o ∧
      o.root.find? s.chain.holder = some c ∧ c.state = .active ∧
      c.alloc = s.chain.alloc ∧ c.lo = s.chain.lo ∧ c.hi = s.chain.hi ∧
      c.q = s.chain.q ∧ c.ceiling = s.chain.ceiling

private def initialLeaf : Leaf :=
  { id := ⟨1⟩, alloc := ⟨0⟩, lo := 0, hi := 64, ordered := by decide,
    q := 64, pos := by decide, ceiling := .readWrite, state := .active }

/-- The concrete 64-byte world coupled to the empty chain, held by its root. -/
def initialState : State :=
  { world := uWorld
    chain := { base := ⟨1⟩, holder := ⟨1⟩, alloc := ⟨0⟩, lo := 0, hi := 64,
               q := 64, ceiling := .readWrite, edges := [] } }

/-- The initial coupled state satisfies the correspondence. -/
theorem initialState_OK : State.OK initialState := by
  refine ⟨World.uWorld_borrowOK, ?_, rfl, ?_⟩
  · unfold Delegation.Chain.OK
    refine ⟨by simp [initialState], by simp [initialState], by simp [initialState],
      ?_, ?_, ?_, ?_, ?_⟩
    · intro e he; simp [initialState] at he
    · intro e he; simp [initialState] at he
    · intro i e1 e2 h1 h2; simp [initialState] at h1
    · intro e he; simp [initialState] at he
    · simp [initialState]
  · refine ⟨Cap.uOwner, initialLeaf, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · change uWorld.ctx.findOwner? ⟨0⟩ = some Cap.uOwner
      simp [uWorld, uOwner, Ctx.findOwner?, Owner.init]
    · simp [initialState, uWorld, uOwner, initialLeaf, Tree.find?, Owner.init]
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl

/-- A write through the chain holder. -/
def State.write (s : State) (v : UInt8) : Option State :=
  match s.world.writeChecked s.chain.alloc s.chain.holder 0 v with
  | .ok w' => some { s with world := w' }
  | .error _ => none

/-- A checked write through the holder preserves the correspondence. -/
theorem State.write_OK {s s' : State} {v : UInt8}
    (h : s.write v = some s') (hok : s.OK) : s'.OK := by
  obtain ⟨hborrow, hchain, hloans, hcorr⟩ := hok
  obtain ⟨o, c, hfind, hleaf, hactive, halloc, hlo, hhi, hq, hceil⟩ := hcorr
  unfold State.write at h
  cases hw : s.world.writeChecked s.chain.alloc s.chain.holder 0 v with
  | error e => simp [hw] at h
  | ok w' =>
    simp [hw] at h
    cases h
    obtain ⟨_, _, _, _, _, _, _, hctx, _⟩ := World.writeChecked_sound hw
    refine ⟨World.borrowOK_write hw hborrow, hchain, ?_, ?_⟩
    · rw [hctx]
      exact hloans
    · refine ⟨o, c, ?_, hleaf, hactive, halloc, hlo, hhi, hq, hceil⟩
      rw [hctx]
      exact hfind

end Discipline

end Cap
