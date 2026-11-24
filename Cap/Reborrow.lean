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
deriving DecidableEq, Repr

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

/-! ### Chain freshness

The first version of this module counted a link's lender *and* its borrower in
the occurrence list. Because `Chain` forces the first lender to be the base,
that list repeated the base, so the freshness predicate was uninhabited for any
nonempty chain. The defect is recorded as `LegacyFresh`; the current predicate
counts each introduced identity once: the base plus the links' borrowers, with
the lenders inherited rather than re-counted. -/

/-- The capability identities a chain introduces: each link's borrower, in order.
The chain's base is not included. -/
def borrowers (chain : List Link) : List CapId := chain.map (·.borrower)

/-- The historical occurrence list, lender and borrower of every link. -/
def legacyNames : List Link → List CapId
  | [] => []
  | l :: rest => l.lender :: l.borrower :: legacyNames rest

/-- The historical freshness predicate, kept so the defect is a theorem. -/
def LegacyFresh (base : CapId) (chain : List Link) : Prop :=
  (base :: legacyNames chain).Nodup

/-- The historical predicate is inconsistent with any nonempty chain. -/
theorem legacy_fresh_uninhabited {base : CapId} {l : Link} {rest : List Link}
    (h : Chain base (l :: rest)) : ¬ LegacyFresh base (l :: rest) := by
  intro hnd
  simp only [LegacyFresh, legacyNames, List.nodup_cons] at hnd
  have hl : l.lender = base := by
    have h' := h
    simp only [Chain] at h'
    exact h'.1
  rw [hl] at hnd
  exact hnd.1 (List.mem_cons_self ..)

/-- A chain is fresh when it is connected and the base together with the
introduced borrowers is duplicate-free. -/
def Chain.Fresh (base : CapId) (chain : List Link) : Prop :=
  Chain base chain ∧ (base :: borrowers chain).Nodup

/-- Every link uses the same allocation. -/
def Chain.SameAlloc (a : AllocId) (chain : List Link) : Prop :=
  ∀ l ∈ chain, l.alloc = a

/-- Loan identifiers are distinct, as the loan context requires. -/
def Chain.LoanIdsFresh (chain : List Link) : Prop :=
  (chain.map (·.loanId)).Nodup

/-- No introduced borrower was already issued by the world. This is separate
from freshness within the chain. -/
def Chain.WorldFresh (issued : List CapId) (chain : List Link) : Prop :=
  ∀ l ∈ chain, l.borrower ∉ issued

/-- The inner loan's lifetime descends from its outer loan's. -/
def Chain.LifetimeNested (parentOf : LifetimeId → Option LifetimeId) :
    List Link → Prop
  | [] => True
  | [_] => True
  | l₁ :: l₂ :: rest =>
      parentOf l₂.lifetime = some l₁.lifetime ∧ LifetimeNested parentOf (l₂ :: rest)

/-- The complete chain invariant of this layer: connectivity with fresh
introduced identities, one allocation, distinct loan identifiers, world-level
freshness, and nested lifetimes. -/
def Chain.WF (base : CapId) (a : AllocId) (issued : List CapId)
    (parentOf : LifetimeId → Option LifetimeId) (chain : List Link) : Prop :=
  Chain.Fresh base chain ∧ Chain.SameAlloc a chain ∧ Chain.LoanIdsFresh chain ∧
    Chain.WorldFresh issued chain ∧ Chain.LifetimeNested parentOf chain

/-- Extending a chain by a link from the current holder to a distinct borrower
preserves connectivity. -/
theorem Chain.append {base : CapId} {chain : List Link} {l : Link}
    (hc : Chain base chain) (hne : l.lender ≠ l.borrower)
    (hl : l.lender = holder base chain) : Chain base (chain ++ [l]) := by
  induction chain generalizing base with
  | nil =>
    simp only [List.nil_append, Chain]
    exact ⟨hl, hne, trivial⟩
  | cons x xs ih =>
    simp only [Chain] at hc ⊢
    obtain ⟨h1, h2, h3⟩ := hc
    refine ⟨h1, h2, ?_⟩
    have hl' : l.lender = holder x.borrower xs := by
      simpa only [holder] using hl
    exact ih h3 hl'

/-- Delegating from the current holder to a fresh borrower preserves freshness. -/
theorem Chain.Fresh_delegate {base : CapId} {chain : List Link} {l : Link}
    (hf : Chain.Fresh base chain) (hne : l.lender ≠ l.borrower)
    (hl : l.lender = holder base chain)
    (hfresh : l.borrower ∉ base :: borrowers chain) :
    Chain.Fresh base (delegate base chain l) := by
  obtain ⟨hc, hnd⟩ := hf
  constructor
  · exact Chain.append hc hne hl
  · unfold delegate
    rw [borrowers, List.map_append, List.map_singleton]
    rw [← List.cons_append]
    apply List.nodup_append.mpr
    refine ⟨hnd, by simp, ?_⟩
    intro a ha b hb
    simp only [List.mem_singleton] at hb
    subst hb
    exact fun heq => hfresh (heq ▸ ha)

/-- Ending the innermost delegation restores the previous freshness. -/
theorem Chain.Fresh_retract_delegate {base : CapId} {chain : List Link} {l : Link}
    (_hne : l.lender ≠ l.borrower) (_hl : l.lender = holder base chain) :
    Chain.Fresh base (retract (delegate base chain l)) ↔ Chain.Fresh base chain := by
  unfold retract delegate
  rw [List.dropLast_concat]

/-- The newest borrower is fresh against the base and every earlier borrower. -/
theorem Chain.Fresh.newest_fresh {base : CapId} {chain : List Link} {l : Link}
    (hf : Chain.Fresh base (chain ++ [l])) :
    l.borrower ∉ base :: borrowers chain := by
  obtain ⟨-, hnd⟩ := hf
  rw [borrowers, List.map_append, List.map_singleton] at hnd
  rw [← List.cons_append] at hnd
  obtain ⟨-, -, hdisj⟩ := List.nodup_append.mp hnd
  intro hmem
  exact hdisj l.borrower hmem l.borrower (List.mem_singleton.mpr rfl) rfl

/-- The chain as loan-context records, in the order `endLoanChecked` filters
them: the outermost loan first. -/
def Chain.toLoans : List Link → List Loan
  | [] => []
  | l :: rest =>
      { id := l.loanId, alloc := l.alloc, lender := l.lender, borrower := l.borrower,
        lifetime := l.lifetime } :: Chain.toLoans rest

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

/-- The lenders of a chain are the base and earlier borrowers, hence a sublist of
the counted identities. -/
theorem lenders_sublist {base : CapId} {chain : List Link}
    (hc : Chain base chain) :
    (Chain.toLoans chain).map (·.lender) |>.Sublist (base :: borrowers chain) := by
  induction chain generalizing base with
  | nil => exact List.nil_sublist _
  | cons x xs ih =>
    simp only [Chain] at hc
    obtain ⟨h1, h2, h3⟩ := hc
    simp only [Chain.toLoans, List.map_cons, borrowers, List.map_cons]
    rw [h1]
    exact List.Sublist.cons_cons base (ih h3)

/-- A fresh chain has distinct lenders: the loan-context invariant's
lender-distinctness field holds for the chain's records. -/
theorem Chain.Fresh.lenders_nodup {base : CapId} {chain : List Link}
    (hf : Chain.Fresh base chain) :
    (Chain.toLoans chain).map (·.lender) |>.Nodup :=
  (lenders_sublist hf.1).nodup hf.2

/-- Ending a loan closes only the innermost scope: an identifier other than the
last link's is refused while inner loans remain. -/
def endLink (chain : List Link) (id : LoanId) : Option (List Link) :=
  match chain.reverse with
  | [] => none
  | l :: _ => if l.loanId = id then some chain.dropLast else none

/-- Ending the innermost loan succeeds and leaves the retracted chain. -/
theorem endLink_inner {chain : List Link} {l : Link} :
    endLink (chain ++ [l]) l.loanId = some chain := by
  unfold endLink
  simp

/-- Ending an outer loan while an inner loan is outstanding is refused. -/
theorem endLink_outer_none {chain : List Link} {l : Link} {id : LoanId}
    (hne : l.loanId ≠ id) : endLink (chain ++ [l]) id = none := by
  unfold endLink
  simp [hne]

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

/-! ### Inhabited instances and controls -/

/-- Concrete identifiers for the chain instances. -/
def demoBase : CapId := ⟨0⟩
def demoB1 : CapId := ⟨1⟩
def demoB2 : CapId := ⟨2⟩
def demoAlloc : AllocId := ⟨0⟩
def demoLoan1 : LoanId := ⟨10⟩
def demoLoan2 : LoanId := ⟨11⟩
def demoLife1 : LifetimeId := ⟨0⟩
def demoLife2 : LifetimeId := ⟨1⟩

/-- Parent lifetime map for the two-level instance: life 1 descends from life 0. -/
def demoParent (life : LifetimeId) : Option LifetimeId :=
  if life.val = 1 then some ⟨0⟩ else none

def demoLink1 : Link :=
  { loanId := demoLoan1, alloc := demoAlloc, lender := demoBase,
    borrower := demoB1, lifetime := demoLife1 }

def demoLink2 : Link :=
  { loanId := demoLoan2, alloc := demoAlloc, lender := demoB1,
    borrower := demoB2, lifetime := demoLife2 }

/-- A one-loan instance satisfies the complete chain invariant. -/
example : Chain.WF demoBase demoAlloc [] demoParent [demoLink1] := by
  simp [Chain.WF, Chain.Fresh, Chain, Chain.SameAlloc, Chain.LoanIdsFresh,
    Chain.WorldFresh, Chain.LifetimeNested, borrowers, demoLink1, demoParent,
    demoBase, demoB1, demoAlloc, demoLoan1, demoLife1]

/-- A two-level instance satisfies the complete chain invariant. -/
example : Chain.WF demoBase demoAlloc [] demoParent [demoLink1, demoLink2] := by
  simp [Chain.WF, Chain.Fresh, Chain, Chain.SameAlloc, Chain.LoanIdsFresh,
    Chain.WorldFresh, Chain.LifetimeNested, borrowers, demoLink1, demoLink2,
    demoParent, demoBase, demoB1, demoB2, demoAlloc, demoLoan1, demoLoan2,
    demoLife1, demoLife2]

/-- The historical freshness predicate was uninhabited: the base is repeated. -/
example (h : Chain demoBase [demoLink1]) :
    ¬ LegacyFresh demoBase [demoLink1] :=
  legacy_fresh_uninhabited h

/-- A borrower equal to the base is rejected. -/
example : ¬ Chain.Fresh demoBase [{ demoLink1 with borrower := demoBase }] := by
  simp [Chain.Fresh, Chain, borrowers, demoLink1, demoBase]

/-- A previously issued borrower is rejected by world freshness. -/
example : ¬ Chain.WorldFresh [demoB2] [demoLink2] := by
  simp [Chain.WorldFresh, demoLink2, demoB2]

/-- A reused loan identifier is rejected. -/
example : ¬ Chain.LoanIdsFresh [demoLink1, demoLink1] := by
  simp [Chain.LoanIdsFresh, demoLink1]

/-- A wrong allocation is rejected. -/
example : ¬ Chain.SameAlloc demoAlloc [{ demoLink1 with alloc := ⟨1⟩ }] := by
  simp [Chain.SameAlloc, demoLink1, demoAlloc]

/-- An invalid lifetime parent is rejected. -/
example : ¬ Chain.LifetimeNested (fun _ => none) [demoLink1, demoLink2] := by
  simp [Chain.LifetimeNested, demoLink1, demoLink2]

/-- Ending the inner loan restores the outer chain. -/
example : endLink ([demoLink1] ++ [demoLink2]) demoLoan2 = some [demoLink1] :=
  endLink_inner

/-- Ending the outer loan while the inner loan is outstanding is refused. -/
example : endLink ([demoLink1] ++ [demoLink2]) demoLoan1 = none :=
  endLink_outer_none (l := demoLink2) (by decide)

end Cap
