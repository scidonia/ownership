/-
A pure lifetime and loan model.

This module has no heap and no capability ledger: it records which lifetimes exist,
which loans are outstanding, and the parent pointers that order lifetimes. It is
the bookkeeping the ledger will consult when a borrow begins or ends; capability
states and footprints stay in `Cap.Ledger`, and this model still does not thread
either of them through the transitions.

`begin` takes the side conditions as a proof (`BeginOK`); an executable front end
can decide them separately. Those conditions bind the begun loan to the lifetime
it inserts (`loan.lifetime = life.id`) and require the lender and borrower
capabilities to be distinct. `endLoan` only needs a decidable comparison of the
lifetime's state, plus a traversal of the recorded parent function: it refuses
while a recorded loan descends from the lifetime being ended.

`Descends` is the strict (one-or-more-step) transitive closure of the recorded
parent function. Proved: the begun lifetime and loan are present, ending a loan
removes it from the loan list, and ending is refused whenever a descendant loan is
recorded.
-/
import Cap.Ledger

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

/-- One outstanding loan. Besides the loan's identities it records the chain's
base capability and the resource description carried by the authoritative leaf,
so comparison with shell code needs no existential chain witness. -/
structure Loan where
  id : LoanId
  alloc : AllocId
  /-- The chain's base capability name: the allocation's root capability or a
  split or join child name, never a borrower name. -/
  base : CapId
  lender : CapId
  borrower : CapId
  lifetime : LifetimeId
  lo : Nat
  hi : Nat
  q : Nat
  ceiling : Ceiling
deriving Repr

structure LoanCtx where
  lifetimes : List Lifetime
  loans : List Loan
  /-- Fresh lifetime identifier source. Each begun loan records this value and
  advances the counter; `LifetimesBoundedOK` bounds every recorded lifetime by
  it. -/
  nextLifetime : Nat
deriving Repr

namespace LoanCtx

/-- The lifetime of the initial borrow: shared by a hand-built world's loan
records and never marked ended by the executable return bookkeeping. -/
def rootLifetime : LifetimeId := ⟨0⟩

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

/-- The pure bookkeeping of an accepted return: remove the loan record and mark
its non-root lifetime ended. The root lifetime is never marked ended, so a
hand-built world whose loan records the root lifetime keeps accepting a later
begin. -/
def endBorrowBookkeeping (Γ : LoanCtx) (l : Loan) : LoanCtx :=
  { Γ with
    lifetimes := Γ.lifetimes.map (fun x =>
      if x.id = l.lifetime ∧ x.id ≠ rootLifetime then { x with state := .ended } else x),
    loans := Γ.loans.filter (fun m => m.id ≠ l.id) }

/-- Strict descent over the recorded parent function: `Descends Γ inner outer`
holds when following parent pointers from `inner` reaches `outer` in one or more
steps. Reflexivity is deliberately absent, so a loan never descends from its own
lifetime unless the recorded parents form a cycle. -/
inductive Descends (Γ : LoanCtx) : LifetimeId → LifetimeId → Prop where
  | step {child p : LifetimeId} : Γ.parent child = some p → Descends Γ child p
  | trans {a b c : LifetimeId} : Descends Γ a b → Descends Γ b c → Descends Γ a c

/-- The side conditions of beginning a borrow. The loan is bound to the inserted
lifetime, and the lender and borrower capabilities are distinct. -/
structure BeginOK (Γ : LoanCtx) (loan : Loan) (life : Lifetime) : Prop where
  freshLifetime : Γ.findLifetime? life.id = none
  freshLoan : Γ.findLoan? loan.id = none
  live : life.state = .live
  parentLive : ∀ p, life.parent = some p → Γ.live p = true
  bound : loan.lifetime = life.id
  lender_ne_borrower : loan.lender ≠ loan.borrower

/-- Begin a loan: the conditions are supplied by `h`. -/
def begin (Γ : LoanCtx) (loan : Loan) (life : Lifetime) (_h : BeginOK Γ loan life) :
    LoanCtx :=
  { lifetimes := life :: Γ.lifetimes, loans := loan :: Γ.loans, nextLifetime := Γ.nextLifetime }

theorem begin_mem_lifetime {Γ : LoanCtx} {loan : Loan} {life : Lifetime}
    {h : BeginOK Γ loan life} : life ∈ (Γ.begin loan life h).lifetimes := by
  simp [begin]

theorem begin_mem_loan {Γ : LoanCtx} {loan : Loan} {life : Lifetime}
    {h : BeginOK Γ loan life} : loan ∈ (Γ.begin loan life h).loans := by
  simp [begin]

/-- Walk at most `n` parent steps from `a`, looking for `root`. -/
def descendsFuel (Γ : LoanCtx) : Nat → LifetimeId → LifetimeId → Bool
  | 0, _, _ => false
  | n + 1, a, root =>
    match Γ.parent a with
    | none => false
    | some p => if p = root then true else descendsFuel Γ n p root

/-- Does any recorded loan descend from `root`? The traversal is bounded by the
number of recorded lifetimes, so it terminates even on a malformed cycle. -/
def hasDescendant (Γ : LoanCtx) (root : LifetimeId) : Bool :=
  Γ.loans.any (fun l => descendsFuel Γ Γ.lifetimes.length l.lifetime root)

/-- The fuel traversal only finds genuine descents. -/
theorem descendsFuel_sound {Γ : LoanCtx} :
    ∀ (n : Nat) {a root : LifetimeId}, descendsFuel Γ n a root = true → Descends Γ a root := by
  intro n
  induction n with
  | zero =>
    intro a root h
    simp [descendsFuel] at h
  | succ n ih =>
    intro a root h
    cases hp : Γ.parent a with
    | none => simp [descendsFuel, hp] at h
    | some p =>
      by_cases hpr : p = root
      · exact Descends.step (by rw [hp, hpr])
      · have hrest : descendsFuel Γ n p root = true := by
          simpa [descendsFuel, hp, hpr] using h
        exact Descends.trans (Descends.step hp) (ih hrest)

/-- The descendant check is sound: a reported descendant is a recorded loan that
strictly descends from the given lifetime. -/
theorem hasDescendant_sound {Γ : LoanCtx} {root : LifetimeId}
    (h : Γ.hasDescendant root = true) :
    ∃ loan, loan ∈ Γ.loans ∧ Descends Γ loan.lifetime root := by
  unfold hasDescendant at h
  rw [List.any_eq_true] at h
  obtain ⟨loan, hmem, hdesc⟩ := h
  exact ⟨loan, hmem, descendsFuel_sound _ hdesc⟩

/-- End a loan: it must be present, its lifetime live, and no recorded loan may
descend from that lifetime. The loan is removed and the lifetime is marked
ended. -/
def endLoan (Γ : LoanCtx) (id : LoanId) : Option LoanCtx :=
  match Γ.findLoan? id with
  | none => none
  | some loan =>
    match Γ.findLifetime? loan.lifetime with
    | some life =>
      if life.state = .live then
        if Γ.hasDescendant loan.lifetime then none
        else some (Γ.endBorrowBookkeeping loan)
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
      · by_cases hd : Γ.hasDescendant loan.lifetime
        · simp [hl, hf, hstate, hd] at h
        · simp [hl, hf, hstate, hd] at h
          have hloanid : loan.id = id := by
            have := List.find?_some (p := fun x : Loan => x.id = id) hl
            simpa using this
          cases h
          simp only [endBorrowBookkeeping, findLoan?]
          rw [hloanid]
          exact find?_filter_ne Γ.loans id
      · simp [hl, hf, hstate] at h

/-- Ending is refused while a recorded loan descends from the lifetime being
ended. -/
theorem endLoan_none_of_descendant {Γ : LoanCtx} {id : LoanId} {loan : Loan}
    (hl : Γ.findLoan? id = some loan) (hd : Γ.hasDescendant loan.lifetime = true) :
    Γ.endLoan id = none := by
  unfold endLoan
  rw [hl]
  cases hf : Γ.findLifetime? loan.lifetime with
  | none => simp [hf]
  | some life =>
    by_cases hstate : life.state = .live
    · simp [hf, hstate, hd]
    · simp [hf, hstate]

end LoanCtx

/-- The loan context of a fresh world: one live root lifetime and no loans.
Every loan begun through `World.beginLoanChecked` is bound to this root
lifetime. -/
def LoanCtx.rootOnly : LoanCtx :=
  { lifetimes := [{ id := ⟨0⟩, parent := none, state := .live }], loans := [],
    nextLifetime := 1 }

end Cap
