/-
A pure lifetime and loan model.

This module has no heap and no capability ledger: it records which lifetimes exist,
which loans are outstanding, and the parent pointers that order lifetimes. It is
the bookkeeping the ledger will consult when a borrow begins or ends; capability
states and footprints stay in `Cap.Ledger`.

`begin` takes the side conditions as a proof (`BeginOK`); an executable front end
can decide them separately. `endLoan` only needs a decidable comparison of the
lifetime's state. Proved: the begun lifetime and loan are present, and ending a
loan removes it from the loan list.
-/
import Cap.Id

namespace Cap

inductive LifeState where
  | live
  | ended
deriving DecidableEq, Repr

structure Lifetime where
  id : LifetimeId
  parent : Option LifetimeId
  state : LifeState
deriving Repr

structure Loan where
  id : LoanId
  lender : CapId
  borrower : CapId
  lifetime : LifetimeId
deriving Repr

structure LoanCtx where
  lifetimes : List Lifetime
  loans : List Loan
deriving Repr

namespace LoanCtx

def findLifetime? (Γ : LoanCtx) (id : LifetimeId) : Option Lifetime :=
  Γ.lifetimes.find? (fun l => l.id = id)

def findLoan? (Γ : LoanCtx) (id : LoanId) : Option Loan :=
  Γ.loans.find? (fun l => l.id = id)

/-- The parent of a recorded lifetime. -/
def parent (Γ : LoanCtx) (id : LifetimeId) : Option LifetimeId :=
  (Γ.findLifetime? id).bind (·.parent)

/-- A lifetime is live exactly when recorded and not ended. -/
def live (Γ : LoanCtx) (id : LifetimeId) : Bool :=
  match Γ.findLifetime? id with
  | some l => l.state == .live
  | none => false

/-- The side conditions of beginning a borrow. -/
structure BeginOK (Γ : LoanCtx) (loan : Loan) (life : Lifetime) : Prop where
  freshLifetime : Γ.findLifetime? life.id = none
  freshLoan : Γ.findLoan? loan.id = none
  live : life.state = .live
  parentLive : ∀ p, life.parent = some p → Γ.live p = true

/-- Begin a loan: the conditions are supplied by `h`. -/
def begin (Γ : LoanCtx) (loan : Loan) (life : Lifetime) (_h : BeginOK Γ loan life) :
    LoanCtx :=
  { lifetimes := life :: Γ.lifetimes, loans := loan :: Γ.loans }

theorem begin_mem_lifetime {Γ : LoanCtx} {loan : Loan} {life : Lifetime}
    {h : BeginOK Γ loan life} : life ∈ (Γ.begin loan life h).lifetimes := by
  simp [begin]

theorem begin_mem_loan {Γ : LoanCtx} {loan : Loan} {life : Lifetime}
    {h : BeginOK Γ loan life} : loan ∈ (Γ.begin loan life h).loans := by
  simp [begin]

/-- End a loan: it must be present and its lifetime live. The loan is removed and
the lifetime is marked ended. -/
def endLoan (Γ : LoanCtx) (id : LoanId) : Option LoanCtx :=
  match Γ.findLoan? id with
  | none => none
  | some loan =>
    match Γ.findLifetime? loan.lifetime with
    | some life =>
      if life.state = .live then
        some {
          lifetimes := Γ.lifetimes.map (fun l =>
            if l.id = loan.lifetime then { l with state := .ended } else l),
          loans := Γ.loans.filter (fun l => l.id ≠ id) }
      else none
    | none => none

private theorem find?_filter_ne (l : List Loan) (id : LoanId) :
    (l.filter (fun x => x.id ≠ id)).find? (fun x => x.id = id) = none := by
  induction l with
  | nil => rfl
  | cons x xs ih =>
    by_cases h : x.id = id
    · simp [List.filter, h, ih]
    · simp [List.filter, h, ih]

theorem endLoan_removes_loan {Γ Γ' : LoanCtx} {id : LoanId}
    (h : Γ.endLoan id = some Γ') : Γ'.findLoan? id = none := by
  unfold endLoan at h
  cases hl : Γ.findLoan? id with
  | none => simp [hl] at h
  | some loan =>
    cases hf : Γ.findLifetime? loan.lifetime with
    | none => simp [hl, hf] at h
    | some life =>
      by_cases hstate : life.state = .live
      · simp [hl, hf, hstate] at h
        cases h
        simp [findLoan?, find?_filter_ne]
      · simp [hl, hf, hstate] at h

end LoanCtx

end Cap
