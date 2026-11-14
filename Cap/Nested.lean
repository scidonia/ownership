/-
A two-level lexical borrow model with suspension and restoration.

This is a lender/borrower bookkeeping model, not a semantic one: a `Lender` is a
capability name, its share and whether it is currently lent out; a `Borrow`
records the lender snapshot, the borrower capability, and the loan and lifetime
names. Beginning a borrow suspends the lender and issues the borrower; ending it
restores the lender to `active` and does not return the borrower capability.
Suspension blocks a further borrow, so a nested scope can only be entered after
the parent borrow ends, and restoration returns the parent's share rather than
the allocation root's.

Footprints and capability states (the `Cap.Ledger` leaves) are not threaded
here: no `Owner`, `Tree` or `LoanCtx` is updated, and the lender and borrower
capabilities are not tied to ledger leaves. `Lender.canWrite` pairs activity
with `Cap.Policy.Writable`, but this module proves no frame rule and says
nothing about the suspended obligations that a real suspension would leave
behind. That full frame rule, with its suspended obligations, is not proved.

Proved:
* `begin_suspends` — a successful begin returns a suspended lender with the
  original share.
* `end_restores` — ending a borrow from the suspended lender yields an active
  lender with the same capability and share.
* `suspended_not_writable` — a suspended lender cannot write, even when policy
  permits the underlying capability.
* `nested_begin` — a second borrow, begun after the first ends, suspends the
  restored lender and keeps the share it had before the first borrow.
-/
import Cap.Ledger
import Cap.Policy

namespace Cap

inductive LenderState where
  | active
  | suspended

structure Lender where
  cap : CapId
  state : LenderState
  share : Nat

structure Borrow where
  lender : Lender
  borrower : CapId
  loan : LoanId
  lifetime : LifetimeId

/-- Begin: the lender is suspended and a borrower is issued. Only an active
lender can be lent out. -/
def beginBorrow (l : Lender) (borrower : CapId) (loan : LoanId) (lifetime : LifetimeId) :
    Option (Borrow × Lender) :=
  match l.state with
  | .active =>
    some ({ lender := l, borrower := borrower, loan := loan, lifetime := lifetime },
      { l with state := .suspended })
  | .suspended => none

/-- End: the lender is restored, the borrower capability is not returned. The
borrow must name the same lender capability that is being restored. -/
def endBorrow (b : Borrow) (lender : Lender) : Option Lender :=
  match lender.state with
  | .suspended =>
    if lender.cap = b.lender.cap then some { lender with state := .active } else none
  | .active => none

/-- On success the returned lender is suspended and keeps its share. -/
theorem begin_suspends {l : Lender} {borrower : CapId} {loan : LoanId}
    {lifetime : LifetimeId} {b : Borrow} {lender' : Lender}
    (h : beginBorrow l borrower loan lifetime = some (b, lender')) :
    lender'.state = .suspended ∧ lender'.share = l.share := by
  unfold beginBorrow at h
  cases hs : l.state with
  | active =>
    simp only [hs, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨_, rfl⟩ := h
    exact ⟨rfl, rfl⟩
  | suspended => simp [hs] at h

/-- Ending a borrow from the suspended lender restores an active lender with the
same capability and share. -/
theorem end_restores {b : Borrow} {lender lender' : Lender}
    (h : endBorrow b lender = some lender') :
    lender'.state = .active ∧ lender'.cap = lender.cap ∧ lender'.share = lender.share := by
  unfold endBorrow at h
  cases hs : lender.state with
  | active => simp [hs] at h
  | suspended =>
    by_cases hc : lender.cap = b.lender.cap
    · simp [hs, hc] at h
      cases h
      exact ⟨rfl, hc.symm, rfl⟩
    · simp [hs, hc] at h

/-- A lender is active exactly when its recorded state is `active`. -/
def Lender.Active (l : Lender) : Prop :=
  l.state = .active

/-- A suspended lender is not active, so it cannot lend or write. -/
theorem Lender.not_active_of_suspended {l : Lender} (h : l.state = .suspended) :
    ¬ l.Active := by
  intro ha
  unfold Lender.Active at ha
  rw [h] at ha
  cases ha

/-- A lender may write when it is active and the policy admits a write on its
capability under the given lifetime. This is a predicate, not a decision
procedure. -/
def Lender.canWrite (l : Lender) (p : Policy) (o : Owner) (D : Nat) (i : Nat)
    (lifetime : LifetimeId) : Prop :=
  l.Active ∧ p.Writable o D l.cap i lifetime

/-- A suspended lender cannot write, regardless of the policy. -/
theorem suspended_not_writable {l : Lender} {p : Policy} {o : Owner} {D : Nat}
    {i : Nat} {lifetime : LifetimeId} (h : l.state = .suspended) :
    ¬ l.canWrite p o D i lifetime := by
  intro hw
  exact Lender.not_active_of_suspended h hw.1

/-- A second borrow, begun on the lender restored by the first borrow's end,
suspends it again with the share it held before the first borrow: a nested
scope restores to the parent state rather than to the allocation root. -/
theorem nested_begin {l l1 l2 l3 : Lender} {b1 b2 : Borrow} {borrower1 borrower2 : CapId}
    {loan1 loan2 : LoanId} {lifetime1 lifetime2 : LifetimeId}
    (hb1 : beginBorrow l borrower1 loan1 lifetime1 = some (b1, l1))
    (he : endBorrow b1 l1 = some l2)
    (hb2 : beginBorrow l2 borrower2 loan2 lifetime2 = some (b2, l3)) :
    l2.state = .active ∧ l3.state = .suspended ∧ l3.share = l.share := by
  obtain ⟨h1state, h1share⟩ := begin_suspends hb1
  obtain ⟨h2state, _, h2share⟩ := end_restores he
  obtain ⟨h3state, h3share⟩ := begin_suspends hb2
  exact ⟨h2state, h3state, by rw [h3share, h2share, h1share]⟩

end Cap
