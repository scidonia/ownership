import Cap.Discipline

open Cap

/-!
Executable regression controls for the repaired nested-delegation chain.

The controls below are the counterexamples the earlier predicate admitted and
the refusals the checked route must make. Every negative control is paired with
an affirmative one on the same fixture or through the same detector, so a
refusal is never a wholesale rejection:

* the two-edge cycle `⟨3⟩ → ⟨4⟩, ⟨4⟩ → ⟨3⟩`, whose lender and borrower lists are
  separately distinct, is admitted by those lists and rejected by the
  capability-path condition;
* a disconnected cycle whose declared base is `⟨5⟩` is rejected because its
  first edge is not lent by that base;
* empty and nonempty chains naming an unrelated holder are rejected because the
  stored holder must equal the derived one;
* the checked `beginCheck` refuses a wrong lender, a reused borrower, a
  duplicate loan identifier, a changed allocation, footprint, share or ceiling,
  and an unlive lifetime, while the admissible edge is accepted;
* `end?` refuses an empty chain and pops a nonempty one.
-/

namespace CapChainRepair

open Delegation

/-- The empty chain of the initial 64-byte world: base and holder `⟨1⟩`. -/
def rootChain : Delegation.Chain := Discipline.initialState.chain

/-- A loan context in which lifetime `⟨0⟩` is live. -/
def chainCtx : LoanCtx := LoanCtx.rootOnly

/-- The accepted first edge `⟨1⟩ → ⟨3⟩` over the whole 64-byte range. -/
def e1 : Delegation.Edge :=
  { id := ⟨9⟩, alloc := ⟨0⟩, lender := ⟨1⟩, borrower := ⟨3⟩, lifetime := ⟨0⟩,
    lo := 0, hi := 64, q := 64, ceiling := .readWrite }

/-- The accepted second edge `⟨3⟩ → ⟨4⟩`. -/
def e2 : Delegation.Edge :=
  { id := ⟨10⟩, alloc := ⟨0⟩, lender := ⟨3⟩, borrower := ⟨4⟩, lifetime := ⟨0⟩,
    lo := 0, hi := 64, q := 64, ceiling := .readWrite }

/-- The chain after the accepted first edge. -/
def c1 : Delegation.Chain := (rootChain.begin? chainCtx e1).getD rootChain

/-- The chain after the accepted second edge. -/
def c2 : Delegation.Chain := (c1.begin? chainCtx e2).getD c1

/-! ### Affirmative controls: a valid chain and the checked lifecycle -/

/-- The initial empty chain is a valid chain. -/
example : rootChain.OK := Discipline.initialState_OK.2.1

#guard (rootChain.begin? chainCtx e1).isSome
#guard (c1.begin? chainCtx e2).isSome

/- The checked return pops the innermost edge. -/
#guard c2.end?.isSome
#guard (match c2.end? with
  | some c => c.edges.length == 1
  | none => false)
#guard (match c2.end? with
  | some c => c.end?.isSome
  | none => false)

/-! ### The two-edge cycle -/

/-- The `⟨3⟩ → ⟨4⟩` edge of the cycle fixture. -/
def cycleOuter : Delegation.Edge :=
  { id := ⟨9⟩, alloc := ⟨0⟩, lender := ⟨3⟩, borrower := ⟨4⟩, lifetime := ⟨0⟩,
    lo := 0, hi := 64, q := 64, ceiling := .readWrite }

/-- The `⟨4⟩ → ⟨3⟩` edge of the cycle fixture. -/
def cycleInner : Delegation.Edge :=
  { id := ⟨10⟩, alloc := ⟨0⟩, lender := ⟨4⟩, borrower := ⟨3⟩, lifetime := ⟨0⟩,
    lo := 0, hi := 64, q := 64, ceiling := .readWrite }

/-- The cycle `⟨3⟩ → ⟨4⟩ → ⟨3⟩` rooted at `⟨3⟩`. -/
def cyclicChain : Delegation.Chain :=
  { base := ⟨3⟩, holder := ⟨4⟩, alloc := ⟨0⟩, lo := 0, hi := 64, q := 64,
    ceiling := .readWrite, edges := [cycleOuter, cycleInner] }

/- The older shape of the invariant — distinct loans, lenders and borrowers —
is satisfied by the cycle, so uniqueness alone cannot exclude it. -/
#guard (decide ((cyclicChain.edges.map (·.id)).Nodup) &&
  decide ((cyclicChain.edges.map (·.lender)).Nodup) &&
  decide ((cyclicChain.edges.map (·.borrower)).Nodup))

/-- The capability path of the cycle is `[⟨3⟩, ⟨4⟩, ⟨3⟩]`. -/
example : cyclicChain.path = [(⟨3⟩ : CapId), ⟨4⟩, ⟨3⟩] := rfl

/-- The repaired predicate rejects the cycle: the capability path repeats. -/
example : ¬ cyclicChain.OK := by
  intro h
  have hp : [(⟨3⟩ : CapId), ⟨4⟩, ⟨3⟩].Nodup := h.1
  rw [List.nodup_cons] at hp
  exact hp.1 (by simp)

/-! ### The disconnected cycle -/

/-- The same cycle declared over the base `⟨5⟩`, which its edges never mention. -/
def disconnectedCycle : Delegation.Chain :=
  { base := ⟨5⟩, holder := ⟨4⟩, alloc := ⟨0⟩, lo := 0, hi := 64, q := 64,
    ceiling := .readWrite, edges := [cycleOuter, cycleInner] }

/- The disconnected cycle's path is simple, so the path condition is not the
detector here: its first edge is not lent by the declared base. -/
#guard (decide disconnectedCycle.path.Nodup)

example : ¬ disconnectedCycle.OK := by
  intro h
  have hfl : cycleOuter.lender = disconnectedCycle.base := by
    simpa [Delegation.Chain.firstLenderOK, disconnectedCycle] using h.2.1
  exact (by decide : cycleOuter.lender ≠ disconnectedCycle.base) hfl

/-! ### Malformed holders -/

/-- An empty chain naming `⟨2⟩` as holder, though its holder must be its base. -/
def emptyBadHolder : Delegation.Chain :=
  { base := ⟨1⟩, holder := ⟨2⟩, alloc := ⟨0⟩, lo := 0, hi := 64, q := 64,
    ceiling := .readWrite, edges := [] }

/-- The same base and holder is valid — the affirmative control for the
holder refusal. -/
example : rootChain.OK := Discipline.initialState_OK.2.1

example : ¬ emptyBadHolder.OK := by
  intro h
  have hh : (⟨2⟩ : CapId) = ⟨1⟩ := by
    simpa [Delegation.Chain.derivedHolder, emptyBadHolder] using h.2.2.1
  exact (by decide : (⟨2⟩ : CapId) ≠ ⟨1⟩) hh

/-- A one-edge chain naming the unrelated `⟨7⟩` as holder. -/
def edgeBadHolder : Delegation.Chain :=
  { base := ⟨1⟩, holder := ⟨7⟩, alloc := ⟨0⟩, lo := 0, hi := 64, q := 64,
    ceiling := .readWrite, edges := [e1] }

example : ¬ edgeBadHolder.OK := by
  intro h
  have hh : edgeBadHolder.holder = e1.borrower := by
    simpa [Delegation.Chain.derivedHolder, edgeBadHolder] using h.2.2.1
  exact (by decide : (⟨7⟩ : CapId) ≠ e1.borrower) hh

/-! ### Checked `beginCheck` refusals -/

/-- An edge lent by `⟨2⟩` rather than the current holder `⟨1⟩`. -/
def wrongLender : Delegation.Edge := { e1 with lender := ⟨2⟩ }

#guard (rootChain.beginCheck chainCtx wrongLender) = false

/- The affirmative control for the same fixture: the holder lends it. -/
#guard rootChain.beginCheck chainCtx e1

/-- An edge whose borrower is the chain's base, already on the path. -/
def reusedBaseBorrower : Delegation.Edge :=
  { id := ⟨11⟩, alloc := ⟨0⟩, lender := ⟨3⟩, borrower := ⟨1⟩, lifetime := ⟨0⟩,
    lo := 0, hi := 64, q := 64, ceiling := .readWrite }

#guard (c1.beginCheck chainCtx reusedBaseBorrower) = false

/-- An edge whose borrower is its own lender, also already on the path. -/
def reusedLenderBorrower : Delegation.Edge :=
  { id := ⟨11⟩, alloc := ⟨0⟩, lender := ⟨3⟩, borrower := ⟨3⟩, lifetime := ⟨0⟩,
    lo := 0, hi := 64, q := 64, ceiling := .readWrite }

#guard (c1.beginCheck chainCtx reusedLenderBorrower) = false

/-- The fresh edge the following refusals vary one field of. -/
def freshEdge : Delegation.Edge :=
  { id := ⟨11⟩, alloc := ⟨0⟩, lender := ⟨3⟩, borrower := ⟨4⟩, lifetime := ⟨0⟩,
    lo := 0, hi := 64, q := 64, ceiling := .readWrite }

/- The affirmative control: the fresh edge is admitted and appended. -/
#guard c1.beginCheck chainCtx freshEdge
#guard (c1.begin? chainCtx freshEdge).isSome

/- A loan identity already on the chain. -/
#guard (c1.beginCheck chainCtx { freshEdge with id := ⟨9⟩ }) = false

/- A changed allocation. -/
#guard (c1.beginCheck chainCtx { freshEdge with alloc := ⟨1⟩ }) = false

/- A changed lower bound. -/
#guard (c1.beginCheck chainCtx { freshEdge with lo := 1 }) = false

/- A changed upper bound. -/
#guard (c1.beginCheck chainCtx { freshEdge with hi := 32 }) = false

/- A changed share. -/
#guard (c1.beginCheck chainCtx { freshEdge with q := 32 }) = false

/- A changed ceiling. -/
#guard (c1.beginCheck chainCtx { freshEdge with ceiling := .readOnly }) = false

/- A lifetime that is not live in the context. -/
#guard (c1.beginCheck chainCtx { freshEdge with lifetime := ⟨7⟩ }) = false

/-! ### Checked `end?` controls -/

/- An empty chain has nothing to return. -/
#guard rootChain.end?.isNone

/- The affirmative control: a nonempty chain returns its innermost edge. -/
#guard c1.end?.isSome
#guard (match c1.end? with
  | some c => c.edges.length == 0
  | none => false)

end CapChainRepair
