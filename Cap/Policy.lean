/-
The owner write guard composed with loan liveness.

`Policy.Writable` is a predicate combination: the ledger's owner guard
(`Owner.Writable`, from `Cap.Ledger`) conjoined with the liveness of a named
lifetime in a pure loan context (`Cap.Loans`). It is not an executable checker:
it has no `Decidable` instance, no transition, and it touches neither a heap nor
a ledger. The loan context is carried beside the owner but is not threaded by the
session: nothing here ties a capability's leaf to an outstanding loan, and no
state change is performed.

Proved:
* `Policy.writable_owner` / `Policy.writable_live` — the two conjuncts.
* `LoanCtx.live_of_find` — a recorded lifetime whose state is `.live` is live.
* `Policy.not_writable_of_dead` — a dead lifetime forbids a write.
* `Policy.not_writable_ended` — a lifetime recorded as `.ended` is not live, so it
  forbids a write.
* `LoanCtx.live_false_of_endLoan` — a successful `endLoan` marks the loan's
  lifetime ended, so that lifetime is not live afterwards.
* `Policy.not_writable_after_endLoan` — consequently the resulting policy permits
  no write under that lifetime.

Not proved: how a session threads the loan context (there is no session
transition here), and that the owner's leaves are related to the loan's lender
and borrower capabilities beyond the bare conjunction.
-/
import Cap.Ledger
import Cap.Loans

namespace Cap

/-- The owner's decomposition together with the loan bookkeeping that a write
must also consult. -/
structure Policy where
  loans : LoanCtx

/-- A write is permitted when the owner guard holds and the named lifetime is
live. This is a predicate, not a decision procedure. -/
def Policy.Writable (p : Policy) (o : Owner) (D : Nat) (id : CapId) (i : Nat)
    (lifetime : LifetimeId) : Prop :=
  o.Writable D id i ∧ LoanCtx.live p.loans lifetime = true

theorem Policy.writable_owner {p : Policy} {o : Owner} {D : Nat} {id : CapId} {i : Nat}
    {lifetime : LifetimeId} (h : p.Writable o D id i lifetime) : o.Writable D id i :=
  h.1

theorem Policy.writable_live {p : Policy} {o : Owner} {D : Nat} {id : CapId} {i : Nat}
    {lifetime : LifetimeId} (h : p.Writable o D id i lifetime) :
    LoanCtx.live p.loans lifetime = true :=
  h.2

/-- A lifetime that is recorded in the live state is live. -/
theorem LoanCtx.live_of_find {Γ : LoanCtx} {id : LifetimeId} {l : Lifetime}
    (hf : Γ.findLifetime? id = some l) (hs : l.state = .live) : Γ.live id = true := by
  unfold LoanCtx.live
  rw [hf]
  dsimp only
  rw [hs]
  decide

/-- A dead lifetime forbids a write. -/
theorem Policy.not_writable_of_dead {p : Policy} {o : Owner} {D : Nat} {id : CapId}
    {i : Nat} {lifetime : LifetimeId}
    (hdead : LoanCtx.live p.loans lifetime = false) :
    ¬ p.Writable o D id i lifetime := by
  intro h
  have h2 : LoanCtx.live p.loans lifetime = true := h.2
  rw [hdead] at h2
  exact Bool.false_ne_true h2

/-- A lifetime recorded in the ended state is not live, so it forbids a write. -/
theorem Policy.not_writable_ended {p : Policy} {o : Owner} {D : Nat} {id : CapId}
    {i : Nat} {lifetime : LifetimeId} {l : Lifetime}
    (hf : p.loans.findLifetime? lifetime = some l) (hs : l.state = .ended) :
    ¬ p.Writable o D id i lifetime := by
  apply Policy.not_writable_of_dead
  unfold LoanCtx.live
  rw [hf]
  dsimp only
  rw [hs]
  decide

/-- A lookup only returns a lifetime carrying the requested identifier. -/
private theorem findLifetime?_some_id {Γ : LoanCtx} {id : LifetimeId} {l : Lifetime}
    (h : Γ.findLifetime? id = some l) : l.id = id := by
  unfold LoanCtx.findLifetime? at h
  have hp : decide (l.id = id) = true :=
    List.find?_some (p := fun (x : Lifetime) => decide (x.id = id)) h
  exact of_decide_eq_true hp

/-- Looking a lifetime up in a mapped list returns the mapped lifetime. -/
private theorem findLifetime?_map (l : List Lifetime) (g : Lifetime → Lifetime)
    (hg : ∀ x, (g x).id = x.id) (id : LifetimeId) :
    (l.map g).find? (fun x => x.id = id)
      = (l.find? (fun x => x.id = id)).map g := by
  rw [List.find?_map]
  have hcomp : (fun x => decide (x.id = id)) ∘ g = (fun x => decide (x.id = id)) := by
    funext x
    rw [Function.comp_apply, hg x]
  rw [hcomp]

/-- Ending a loan marks its lifetime ended, so the lifetime is no longer live. -/
theorem LoanCtx.live_false_of_endLoan {Γ Γ' : LoanCtx} {loanId : LoanId} {loan : Loan}
    {life : Lifetime}
    (hl : Γ.findLoan? loanId = some loan)
    (hf : Γ.findLifetime? loan.lifetime = some life)
    (hs : life.state = .live)
    (he : Γ.endLoan loanId = some Γ') :
    Γ'.live loan.lifetime = false := by
  have hid : life.id = loan.lifetime := findLifetime?_some_id hf
  unfold LoanCtx.endLoan at he
  rw [hl] at he
  dsimp only at he
  rw [hf] at he
  dsimp only at he
  rw [ite_eq_left hs] at he
  cases hb : Γ.hasDescendant loan.lifetime with
  | true => simp [hb] at he
  | false =>
    simp [hb] at he
    cases he
    have hg : ∀ x : Lifetime,
        (if x.id = loan.lifetime then { x with state := .ended } else x).id = x.id := by
      intro x
      split <;> rfl
    have hf' : Γ.lifetimes.find? (fun x => x.id = loan.lifetime) = some life := hf
    have hfind : (Γ.lifetimes.map
        (fun y => if y.id = loan.lifetime then { y with state := .ended } else y)).find?
          (fun x => x.id = loan.lifetime) = some { life with state := .ended } := by
      rw [findLifetime?_map _ _ hg, hf']
      show some (if life.id = loan.lifetime then { life with state := .ended } else life)
          = some { life with state := .ended }
      rw [ite_eq_left hid]
    unfold LoanCtx.live
    unfold LoanCtx.findLifetime?
    rw [hfind]
    dsimp only
    decide

  /-- After a successful `endLoan`, the policy built from the resulting context
  permits no write under the ended lifetime. -/
  theorem Policy.not_writable_after_endLoan {p : Policy} {o : Owner} {D : Nat}
      {id : CapId} {i : Nat} {loanId : LoanId} {loan : Loan} {life : Lifetime}
      {Γ' : LoanCtx}
      (hl : p.loans.findLoan? loanId = some loan)
      (hf : p.loans.findLifetime? loan.lifetime = some life)
      (hs : life.state = .live)
      (he : p.loans.endLoan loanId = some Γ') :
      ¬ (Policy.Writable { loans := Γ' } o D id i loan.lifetime) := by
    apply Policy.not_writable_of_dead
    exact LoanCtx.live_false_of_endLoan hl hf hs he

end Cap
