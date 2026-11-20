/-
Reborrowing chains: usable borrowers and nested scopes.

`Cap.Nested` proves that beginning a borrow suspends the lender and ending it
restores the lender. It does not let the *borrower* lend onward: there is no
representation of a chain of outstanding loans in which each borrower is the
next lender. This module supplies that bookkeeping.

A `Link` records one outstanding loan: its allocation, lender, a *distinct*
borrower, and the lifetime it is recorded against. A `Chain base ls` is a stack
of outstanding loans, outermost first, where each loan's lender is the holder
produced by the chain before it — the base capability for the first link, and
the previous link's borrower thereafter. `holder` therefore names exactly one
capability at any time: the innermost borrower, or the base when nothing is lent.

The conservation statement is on the share attached to the delegation chain:
the holder's weight is the whole context share `D` and every other name's is
zero. Delegating moves `D` from the previous holder to the new borrower; ending
moves it back. Nothing is duplicated and nothing disappears — which is what
"usable borrower" means for this layer: the borrower holds the authority the
lender gave up, and may in turn lend it onward.

This is a lender/borrower name model, not a semantic one: it does not thread
`Cap.Ledger` leaves, footprints, heaps or the world's `LoanCtx`, and it says
nothing about what the borrower does inside its scope. Those integrations are
named non-claims.
-/
import Cap.Ledger
import Cap.Loans

namespace Cap

/-- One outstanding loan in a delegation chain. -/
structure Link where
  loanId : LoanId
  alloc : AllocId
  lender : CapId
  borrower : CapId
  lifetime : LifetimeId

/-- The holder of the delegated authority: the innermost borrower, or the base
capability when nothing is lent. -/
def holder (base : CapId) : List Link → CapId
  | [] => base
  | l :: rest => holder l.borrower rest

/-- A chain of outstanding loans rooted at `base`: each loan's lender is the
holder of the chain before it, the borrower is distinct from its lender, and the
remainder is a chain rooted at the borrower. -/
def Chain (base : CapId) : List Link → Prop
  | [] => True
  | l :: rest => l.lender = base ∧ l.lender ≠ l.borrower ∧ Chain l.borrower rest

/-- Delegating the holder's authority to a fresh borrower extends the chain. -/
def delegate (base : CapId) (chain : List Link) (l : Link) : List Link :=
  chain ++ [l]

/-- Ending the innermost loan removes the last link. -/
def retract (chain : List Link) : List Link :=
  chain.dropLast

/-- The holder of a chain with a new link appended is that link's borrower,
provided the link lends from the current holder. -/
theorem holder_append {base : CapId} {chain : List Link} {l : Link}
    (hl : l.lender = holder base chain) :
    holder base (chain ++ [l]) = l.borrower := by
  induction chain generalizing base with
  | nil => simp [holder]
  | cons x xs ih =>
    simp only [List.cons_append, holder] at hl ⊢
    exact ih hl

/-- Delegating the current holder's authority makes the new borrower the holder. -/
theorem holder_delegate {base : CapId} {chain : List Link} {l : Link}
    (hl : l.lender = holder base chain) :
    holder base (delegate base chain l) = l.borrower :=
  holder_append hl

/-- Ending a delegation restores the previous holder. -/
theorem holder_retract_delegate {base : CapId} {chain : List Link} {l : Link} :
    holder base (retract (delegate base chain l)) = holder base chain := by
  unfold retract delegate
  rw [List.dropLast_concat]

/-- Every capability name occurring in a chain, lenders and borrowers together. -/
def names : List Link → List CapId
  | [] => []
  | l :: rest => l.lender :: l.borrower :: names rest

/-- A well-formed chain has no repeated capability name, base included. -/
def Chain.NoDup (base : CapId) (chain : List Link) : Prop :=
  (base :: names chain).Nodup

/-- The chain as loan-context records, in the order `endLoanChecked` filters
them: the outermost loan first. -/
def Chain.toLoans : List Link → List Loan
  | [] => []
  | l :: rest =>
      { id := l.loanId, lender := l.lender, borrower := l.borrower,
        lifetime := l.lifetime } :: Chain.toLoans rest

/-- The lenders of a chain are a sublist of its names. -/
theorem lenders_sublist_names : ∀ chain : List Link,
    (Chain.toLoans chain).map (·.lender) |>.Sublist (names chain)
  | [] => List.Sublist.slnil
  | l :: rest => by
    simp only [Chain.toLoans, names]
    exact List.Sublist.cons_cons l.lender
      (List.Sublist.cons l.borrower (lenders_sublist_names rest))

/-- A well-formed chain has distinct lenders: the loan-context invariant's
lender-distinctness field holds for the chain's records. -/
theorem Chain.lenders_nodup {base : CapId} {chain : List Link}
    (h : Chain.NoDup base chain) :
    (Chain.toLoans chain).map (·.lender) |>.Nodup := by
  have hn : (names chain).Nodup := (List.nodup_cons.mp h).2
  exact (lenders_sublist_names chain).nodup hn

/-- The chain's records append, link by link. -/
theorem toLoans_append (chain : List Link) (l : Link) :
    Chain.toLoans (chain ++ [l]) = Chain.toLoans chain ++ Chain.toLoans [l] := by
  induction chain with
  | nil => simp [Chain.toLoans]
  | cons x xs ih => simp [Chain.toLoans, ih]

/-- Ending the innermost link is the loan-list filter `endLoanChecked` performs:
from the chain's records, removing the last loan's identifier leaves exactly the
records of the retracted chain, provided identifiers are unique. -/
theorem toLoans_filter_retract {base : CapId} {chain : List Link} {l : Link}
    (hids : ∀ k ∈ chain, k.loanId ≠ l.loanId) :
    List.filter (fun x => x.id ≠ l.loanId) (Chain.toLoans (delegate base chain l))
      = Chain.toLoans chain := by
  unfold delegate
  rw [toLoans_append, List.filter_append]
  have hsingle : List.filter (fun x : Loan => x.id ≠ l.loanId) (Chain.toLoans [l]) = [] := by
    simp [Chain.toLoans]
  rw [hsingle, List.append_nil]
  induction chain with
  | nil => rfl
  | cons x xs ih =>
    simp only [Chain.toLoans, List.filter_cons]
    rw [if_pos (by simp [hids x (List.mem_cons_self ..)])]
    rw [ih (fun k hk => hids k (List.mem_cons_of_mem x hk))]

/-- The weight of a capability in a delegation chain: the holder carries the
whole share `D`, every other name carries zero. -/
def weight (D : Nat) (base : CapId) (chain : List Link) (c : CapId) : Nat :=
  if c = holder base chain then D else 0

/-- A delegation moves the whole share from the previous holder to the new
borrower and leaves every other name at zero: authority is conserved. -/
theorem delegate_conserved {D : Nat} {base : CapId} {chain : List Link} {l : Link}
    (hl : l.lender = holder base chain) :
    weight D base (delegate base chain l) l.borrower = D ∧
    weight D base (delegate base chain l) (holder base chain) =
      (if holder base chain = l.borrower then D else 0) := by
  have hnew : holder base (delegate base chain l) = l.borrower := holder_delegate hl
  constructor
  · unfold weight
    rw [hnew]
    simp
  · unfold weight
    rw [hnew]

/-- A borrower that is distinct from the previous holder receives the whole
share and the previous holder keeps zero: the conservation in its operative
form. -/
theorem delegate_moves_share {D : Nat} {base : CapId} {chain : List Link} {l : Link}
    (hl : l.lender = holder base chain) (hne : holder base chain ≠ l.borrower) :
    weight D base (delegate base chain l) l.borrower = D ∧
    weight D base (delegate base chain l) (holder base chain) = 0 := by
  obtain ⟨h1, h2⟩ := delegate_conserved (D := D) hl
  refine ⟨h1, ?_⟩
  rw [h2]
  simp [hne]

/-- Ending the innermost delegation returns the whole share to the previous
holder. -/
theorem retract_restores {D : Nat} {base : CapId} {chain : List Link} {l : Link}
    (hl : l.lender = holder base chain) :
    weight D base (retract (delegate base chain l)) (holder base chain) = D := by
  unfold weight
  rw [holder_retract_delegate]
  simp

/-- A two-level nested reborrow: `base` lends to `b1`, which lends to `b2`; the
holder is `b2`, and ending the inner loan restores `b1` while `base`'s loan
remains outstanding. -/
theorem nested_two_level {D : Nat} {base b1 b2 : CapId} {a : AllocId}
    {l1 l2 : LifetimeId} (hne1 : base ≠ b1) (hne2 : b1 ≠ b2) :
    holder base
      (delegate base
        (delegate base [] { loanId := ⟨1⟩, alloc := a, lender := base, borrower := b1, lifetime := l1 })
        { loanId := ⟨2⟩, alloc := a, lender := b1, borrower := b2, lifetime := l2 }) = b2 := by
  unfold delegate
  simp [holder]

/-- Ending the inner loan of a two-level nest restores the outer borrower, and
ending the outer loan restores the base: two retractions unwind the chain. -/
theorem nested_two_level_unwind {D : Nat} {base b1 b2 : CapId} {a : AllocId}
    {l1 l2 : LifetimeId} :
    holder base
      (retract (retract
        (delegate base
          (delegate base [] { loanId := ⟨1⟩, alloc := a, lender := base, borrower := b1, lifetime := l1 })
          { loanId := ⟨2⟩, alloc := a, lender := b1, borrower := b2, lifetime := l2 }))) = base := by
  unfold delegate retract
  simp [holder]

end Cap
