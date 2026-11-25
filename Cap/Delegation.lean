/-
A first-class nested-delegation chain.

The chain is the ownership state for one delegated allocation. Each edge records
the lender, the fresh borrower, the allocation and the resource description
carried down the chain. The holder is the innermost borrower (or the base
capability). Beginning appends an edge whose lender is the current holder;
returning removes the innermost edge only. Resource metadata is required to agree
across every edge, so delegation never changes the allocation, footprint, share
or ceiling. The linear chain makes restoration dependencies explicit and
acyclic by construction.
-/
import Cap.Ledger

namespace Cap

namespace Delegation

/-- One delegation edge. -/
structure Edge where
  id : LoanId
  alloc : AllocId
  lender : CapId
  borrower : CapId
  lifetime : LifetimeId
  lo : Nat
  hi : Nat
  q : Nat
  ceiling : Ceiling
deriving DecidableEq, Repr

/-- A nested delegation chain, outermost first. -/
structure Chain where
  base : CapId
  holder : CapId
  alloc : AllocId
  lo : Nat
  hi : Nat
  q : Nat
  ceiling : Ceiling
  edges : List Edge
deriving Repr

/-- Two edges carry the same allocation and resource description. -/
def Edge.SameResource (e e' : Edge) : Prop :=
  e.alloc = e'.alloc ∧ e.lo = e'.lo ∧ e.hi = e'.hi ∧ e.q = e'.q ∧
  e.ceiling = e'.ceiling

/-- The chain agrees on its resource and has distinct loan identities and
distinct lenders and borrowers. Each inner edge is lent by the previous holder. -/
def Chain.OK (c : Chain) : Prop :=
  (c.edges.map (·.id)).Nodup
  ∧ (c.edges.map (·.lender)).Nodup
  ∧ (c.edges.map (·.borrower)).Nodup
  ∧ (∀ e ∈ c.edges, e.alloc = c.alloc ∧ e.lo = c.lo ∧ e.hi = c.hi ∧
      e.q = c.q ∧ e.ceiling = c.ceiling)
  ∧ (∀ e ∈ c.edges, e.lender ≠ e.borrower)
  ∧ (∀ i e₁ e₂, c.edges[i]? = some e₁ → c.edges[i+1]? = some e₂ →
      e₂.lender = e₁.borrower)
  ∧ (∀ e ∈ c.edges, e.lender = c.base ∨
      ∃ e' ∈ c.edges, e'.borrower = e.lender)

/-- Beginning appends an edge whose lender is the current holder. The edge's
resource fields must match the chain and its identities must be fresh. -/
def Chain.begin (c : Chain) (e : Edge) : Chain :=
  { c with edges := c.edges ++ [e], holder := e.borrower }

/-- Return removes the innermost edge and restores its lender as holder. -/
def Chain.end (c : Chain) : Option Chain :=
  match c.edges.getLast? with
  | none => none
  | some e =>
      some { c with edges := c.edges.dropLast, holder := e.lender }

/-- The holder after appending is the new borrower. -/
theorem Chain.holder_begin (c : Chain) (e : Edge) :
    (c.begin e).holder = e.borrower := rfl

/-- Returning restores the removed edge's lender as holder. -/
theorem Chain.holder_end {c c' : Chain} (h : c.end = some c') :
    ∃ e, c.edges.getLast? = some e ∧ c'.holder = e.lender := by
  unfold Chain.end at h
  cases hl : c.edges.getLast? with
  | none => simp [hl] at h
  | some e =>
    simp [hl] at h
    cases h
    exact ⟨e, rfl, rfl⟩

end Delegation

end Cap
