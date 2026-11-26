/-
The integrated distinct-borrower delegation invariant.

`BorrowOK` collects the facts the signed-out ownership discipline needs: distinct
loan, lender, borrower and lifetime names; no self-alias; issuance of every name
the loan mentions; live and bounded lifetimes; an owner for every allocation; a
recorded chain base and base-or-chain lender; global detachment of every lender
from the live identifier lists; active-terminal-or-delegated authority with the
leaf's resource description; agreement of adjacent edges; issued-order
monotonicity; and the derived bounded-search acyclicity.
-/
import Cap.Retag
import Cap.Unified
import Cap.History

namespace Cap

/-- Positive-length reachability along loan edges. -/
def BorrowReaches (loans : List Loan) : Nat → CapId → CapId → Bool
  | 0, _, _ => false
  | n + 1, a, b =>
      loans.any (fun l => l.lender = a && (l.borrower = b || BorrowReaches loans n l.borrower b))

/-- No lender reaches itself by a positive-length delegation path. -/
def World.BorrowAcyclic (w : World) : Prop :=
  ∀ l ∈ w.ctx.loans.loans,
    BorrowReaches w.ctx.loans.loans (w.ctx.loans.loans.length + 1)
      l.lender l.lender = false

namespace World

/-- Loan, lender, borrower and lifetime identifiers are pairwise distinct. -/
def LoansDistinctOK (w : World) : Prop :=
  (w.ctx.loans.loans.map (·.id)).Nodup
  ∧ (w.ctx.loans.loans.map (·.lender)).Nodup
  ∧ (w.ctx.loans.loans.map (·.borrower)).Nodup
  ∧ (w.ctx.loans.loans.map (·.lifetime)).Nodup

/-- No loan lends to itself. -/
def LoansNonAliasOK (w : World) : Prop :=
  ∀ l ∈ w.ctx.loans.loans, l.lender ≠ l.borrower

/-- Every name a loan mentions has been issued. -/
def LoansIssuedOK (w : World) : Prop :=
  ∀ l ∈ w.ctx.loans.loans,
    l.lender ∈ w.ctx.issued ∧ l.borrower ∈ w.ctx.issued ∧ l.base ∈ w.ctx.issued

/-- Live, bounded lifetimes. -/
def LifetimesBoundedOK (w : World) : Prop :=
  (∀ l ∈ w.ctx.loans.loans, w.ctx.loans.live l.lifetime = true)
  ∧ (∀ lt ∈ w.ctx.loans.lifetimes, lt.id.val < w.ctx.loans.nextLifetime)

/-- Every loan's allocation resolves to an owner. -/
def LoansAllocOK (w : World) : Prop :=
  ∀ l ∈ w.ctx.loans.loans, ∃ o, w.ctx.findOwner? l.alloc = some o

/-- Every delegated lender is absent from every owner's identifier list. -/
def LoansDetachedOK (w : World) : Prop :=
  ∀ l ∈ w.ctx.loans.loans, l.lender ∉ w.ctx.ids

/-- Every lender is the chain's recorded base or the borrower of a same-base
loan. -/
def LoansBaseOK (w : World) : Prop :=
  ∀ l ∈ w.ctx.loans.loans,
    l.lender = l.base ∨ ∃ m ∈ w.ctx.loans.loans, m.base = l.base ∧ m.borrower = l.lender

/-- Active-terminal-or-delegated authority with the leaf's resource description. -/
def LoansTerminalOK (w : World) : Prop :=
  ∀ l ∈ w.ctx.loans.loans, ∃ o, w.ctx.findOwner? l.alloc = some o ∧
    ((∃ c, o.root.find? l.borrower = some c ∧ c.state = .active ∧
        c.alloc = l.alloc ∧ c.lo = l.lo ∧ c.hi = l.hi ∧ c.q = l.q
        ∧ c.ceiling = l.ceiling)
     ∨ (∃ m ∈ w.ctx.loans.loans, m.lender = l.borrower ∧ m.alloc = l.alloc
        ∧ m.base = l.base))

/-- Adjacent edges agree on base, allocation and resource description. -/
def LoansAgreeOK (w : World) : Prop :=
  ∀ l ∈ w.ctx.loans.loans, ∀ m ∈ w.ctx.loans.loans,
    (m.lender = l.borrower ∨ m.borrower = l.lender) →
      m.base = l.base ∧ m.alloc = l.alloc ∧ m.lo = l.lo ∧ m.hi = l.hi
      ∧ m.q = l.q ∧ m.ceiling = l.ceiling

/-- Every borrower was issued before its lender. -/
def LoansOrderOK (w : World) : Prop :=
  ∀ l ∈ w.ctx.loans.loans, w.ctx.issued.idxOf l.borrower < w.ctx.issued.idxOf l.lender

/-- The integrated delegation invariant. -/
def BorrowOK (w : World) : Prop :=
  LoansDistinctOK w ∧ LoansNonAliasOK w ∧ LoansIssuedOK w ∧ LifetimesBoundedOK w
  ∧ LoansAllocOK w ∧ LoansDetachedOK w ∧ LoansBaseOK w ∧ LoansTerminalOK w
  ∧ LoansAgreeOK w ∧ LoansOrderOK w ∧ w.BorrowAcyclic

/-- `BorrowOK` carries the three command-level loan-readiness facts. -/
theorem borrowOK_loansReady {w : World} (h : w.BorrowOK) : Ctx.LoansReady w.ctx := by
  obtain ⟨hd, _, hi, _, _, hdet, _, _, _, _, _⟩ := h
  exact ⟨hd.2.1, hdet, fun l hl => (hi l hl).1⟩

end World

/-! ### Issued-order acyclicity -/

private theorem borrowReaches_idx {loans : List Loan} {issued : List CapId}
    (hord : ∀ l ∈ loans, issued.idxOf l.borrower < issued.idxOf l.lender) :
    ∀ n a b, BorrowReaches loans n a b = true → issued.idxOf b < issued.idxOf a := by
  intro n
  induction n with
  | zero =>
    intro a b h
    simp [BorrowReaches] at h
  | succ n ih =>
    intro a b h
    simp only [BorrowReaches, List.any_eq_true, Bool.and_eq_true, Bool.or_eq_true,
      decide_eq_true_eq] at h
    obtain ⟨l, hl, hla, hb | hr⟩ := h
    · subst hla; subst hb; exact hord l hl
    · subst hla; exact Nat.lt_trans (ih l.borrower b hr) (hord l hl)

/-- Issued-order monotonicity implies bounded-search acyclicity. -/
theorem World.borrowAcyclic_of_issuedOrder {w : World} (h : World.LoansOrderOK w) :
    w.BorrowAcyclic := by
  intro l hl
  cases hb : BorrowReaches w.ctx.loans.loans (w.ctx.loans.loans.length + 1)
      l.lender l.lender with
  | false => rfl
  | true =>
    exact absurd (borrowReaches_idx h (w.ctx.loans.loans.length + 1)
      l.lender l.lender hb) (Nat.lt_irrefl _)

namespace World

/-- A lookup for a different allocation survives owner replacement. -/
theorem Ctx.findOwner?_update_of_ne (C : Ctx) (a : AllocId) (o' : Owner)
    {b : AllocId} (h : b ≠ a) (ho' : o'.alloc = a) :
    (C.update a o').findOwner? b = C.findOwner? b := by
  unfold Ctx.update Ctx.findOwner?
  induction C.owners with
  | nil => rfl
  | cons o os ih =>
    by_cases hb : o.alloc = b
    · have hba : o.alloc ≠ a := by intro ha; exact h (hb.symm.trans ha)
      simp [List.map, List.find?, hb, h]
    · by_cases ha : o.alloc = a
      · have hb' : o'.alloc ≠ b := by rw [ho']; exact h.symm
        have hba : ¬ a = b := fun h' => h h'.symm
        simp [List.map, List.find?, hb, ha, hb', hba, ih]
      · simp [List.map, List.find?, hb, ha, ih]

/-- A lookup for a different allocation survives freeing. -/
theorem Ctx.findOwner?_free_of_ne (C : Ctx) {a b : AllocId} (h : b ≠ a) :
    (C.free a).findOwner? b = C.findOwner? b := by
  unfold Ctx.free Ctx.findOwner?
  rw [List.find?_filter]
  congr 1
  funext o
  by_cases hb : o.alloc = b
  · have hba : ¬ b = a := h
    simp [hb, hba]
  · simp [hb]

/-- A fresh allocation does not change lookup of a different allocation. -/
theorem Ctx.findOwner?_alloc_of_ne {C : Ctx} {a b : AllocId} {n : Nat}
    {pos : 0 < C.D} {rootId disposal : CapId}
    (hf : a ∉ C.owners.map (·.alloc)) (hne : b ≠ a) :
    (C.alloc a n pos rootId disposal hf).findOwner? b = C.findOwner? b := by
  unfold Ctx.alloc Ctx.findOwner?
  simp [Owner.init, hne.symm]

/-- The allocation named by a successful owner lookup. -/
private theorem findOwner_alloc {C : Ctx} {a : AllocId} {o : Owner}
    (h : C.findOwner? a = some o) : o.alloc = a := by
  unfold Ctx.findOwner? at h
  have hp : (fun x : Owner => decide (x.alloc = a)) o = true :=
    List.find?_some (p := fun x : Owner => decide (x.alloc = a)) h
  exact of_decide_eq_true hp

private theorem idxOf_cons_ne {l : List CapId} {a b : CapId} (h : a ≠ b) :
    (a :: l).idxOf b = l.idxOf b + 1 := by
  simp [List.idxOf_cons, h]

private theorem idxOf_cons2_ne {l : List CapId} {a b c : CapId}
    (ha : a ≠ c) (hb : b ≠ c) :
    (a :: b :: l).idxOf c = l.idxOf c + 2 := by
  rw [List.idxOf_cons]
  simp [ha, idxOf_cons_ne hb]

/-- Allocation preserves the delegation invariant. -/
theorem borrowOK_allocChecked {w w' : World} {n : Nat}
    {rootId disposal : CapId} {po : 0 < w.ctx.D}
    (hw : w.allocChecked n rootId disposal po = .ok w') (h : w.BorrowOK) :
    w'.BorrowOK := by
  unfold World.allocChecked at hw
  split at hw
  · rename_i hf
    split at hw
    · rename_i hfr
      simp only [Except.ok.injEq] at hw
      cases hw
      obtain ⟨hd, hna, hi, hlife, halloc, hdet, hbase, hterm, hagree, horder, hacyc⟩ := h
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · simpa [LoansDistinctOK, Ctx.alloc] using hd
      · simpa [LoansNonAliasOK, Ctx.alloc] using hna
      · intro l hl
        obtain ⟨h1, h2, h3⟩ := hi l hl
        exact ⟨List.mem_cons_of_mem _ (List.mem_cons_of_mem _ h1),
          List.mem_cons_of_mem _ (List.mem_cons_of_mem _ h2),
          List.mem_cons_of_mem _ (List.mem_cons_of_mem _ h3)⟩
      · simpa [LifetimesBoundedOK, Ctx.alloc] using hlife
      · intro l hl
        obtain ⟨o, ho⟩ := halloc l hl
        have hmemO : o ∈ w.ctx.owners := List.mem_of_find?_eq_some (by simpa [Ctx.findOwner?] using ho)
        have hoalloc : o.alloc = l.alloc := findOwner_alloc ho
        have hne : l.alloc ≠ ⟨w.ctx.nextAlloc⟩ := by
          intro heq
          apply hf
          have hmem : l.alloc ∈ w.ctx.owners.map (·.alloc) := by
            rw [← hoalloc]; exact List.mem_map_of_mem hmemO
          rwa [heq] at hmem
        refine ⟨o, ?_⟩
        rw [Ctx.findOwner?_alloc_of_ne (C := w.ctx) (a := ⟨w.ctx.nextAlloc⟩)
          (b := l.alloc) hf hne]
        exact ho
      · intro l hl hmem
        have hshape : (w.ctx.alloc ⟨w.ctx.nextAlloc⟩ n po rootId disposal hf).ids
            = [disposal, rootId] ++ w.ctx.ids := by
          simp [Ctx.alloc, Ctx.ids, Owner.ids, Owner.init, Tree.ids]
        rw [hshape, List.mem_append] at hmem
        rcases hmem with hnew | hold
        · simp only [List.mem_cons, List.mem_nil_iff] at hnew
          rcases hnew with h | h | hnil
          · exact hfr.2.2.2.2 (h ▸ (hi l hl).1)
          · exact hfr.2.2.2.1 (h ▸ (hi l hl).1)
          · exact absurd hnil (by simp)
        · exact hdet l hl hold
      · simpa [LoansBaseOK, Ctx.alloc] using hbase
      · intro l hl
        obtain ⟨o, ho, hcond⟩ := hterm l hl
        have hmemO : o ∈ w.ctx.owners := List.mem_of_find?_eq_some (by simpa [Ctx.findOwner?] using ho)
        have hoalloc : o.alloc = l.alloc := findOwner_alloc ho
        have hne : l.alloc ≠ ⟨w.ctx.nextAlloc⟩ := by
          intro heq
          apply hf
          have hmem : l.alloc ∈ w.ctx.owners.map (·.alloc) := by
            rw [← hoalloc]; exact List.mem_map_of_mem hmemO
          rwa [heq] at hmem
        refine ⟨o, ?_, hcond⟩
        rw [Ctx.findOwner?_alloc_of_ne (C := w.ctx) (a := ⟨w.ctx.nextAlloc⟩)
          (b := l.alloc) hf hne]
        exact ho
      · simpa [LoansAgreeOK, Ctx.alloc] using hagree
      · intro l hl
        have hb := (hi l hl).2.1
        have hlend := (hi l hl).1
        have hbroot : l.borrower ≠ rootId := fun h' => hfr.2.2.2.1 (h' ▸ hb)
        have hbdisp : l.borrower ≠ disposal := fun h' => hfr.2.2.2.2 (h' ▸ hb)
        have hlroot : l.lender ≠ rootId := fun h' => hfr.2.2.2.1 (h' ▸ hlend)
        have hldisp : l.lender ≠ disposal := fun h' => hfr.2.2.2.2 (h' ▸ hlend)
        have hord := horder l hl
        rw [show (w.ctx.alloc ⟨w.ctx.nextAlloc⟩ n po rootId disposal hf).issued
              = rootId :: disposal :: w.ctx.issued from rfl,
          idxOf_cons2_ne (a := rootId) (b := disposal) (c := l.borrower)
            (fun h => hbroot h.symm) (fun h => hbdisp h.symm),
          idxOf_cons2_ne (a := rootId) (b := disposal) (c := l.lender)
            (fun h => hlroot h.symm) (fun h => hldisp h.symm)]
        omega
      · simpa [BorrowAcyclic, Ctx.alloc] using hacyc
    · simp at hw
  · simp at hw

/-- A list element satisfying a predicate, unique among the satisfying elements,
is the one `find?` returns. -/
private theorem List.find?_eq_some_of_unique {α : Type} {p : α → Bool} :
    ∀ {l : List α} {m : α}, m ∈ l → p m = true →
      (∀ y ∈ l, p y = true → y = m) → l.find? p = some m
  | [], m, hm, _, _ => by simp at hm
  | x :: xs, m, hm, hp, huniq => by
      by_cases hx : p x = true
      · rw [List.find?_cons_of_pos hx]
        exact congrArg some (huniq x (by simp) hx)
      · rw [List.find?_cons_of_neg hx]
        have hmxs : m ∈ xs := by
          rcases List.mem_cons.mp hm with rfl | h
          · exact absurd hp hx
          · exact h
        exact List.find?_eq_some_of_unique hmxs hp
          (fun y hy hyp => huniq y (by simp [hy]) hyp)

/-- The found loan's base and parent are the derived borrow values. -/
theorem Ctx.borrowBase_eq_of_find {C : Ctx} {lender : CapId} {m : Loan}
    (hf : C.loans.loans.find? (fun x => x.borrower = lender) = some m) :
    C.borrowBase lender = m.base ∧ C.borrowParent lender = some m.lifetime := by
  unfold Ctx.borrowBase Ctx.borrowParent
  rw [hf]
  exact ⟨rfl, rfl⟩

/-- The derived base is the lender itself or a same-borrower loan's base. -/
theorem Ctx.borrowBase_eq_or_mem (C : Ctx) (lender : CapId) :
    C.borrowBase lender = lender ∨
      ∃ m ∈ C.loans.loans, m.borrower = lender ∧ C.borrowBase lender = m.base := by
  unfold Ctx.borrowBase
  cases hf : C.loans.loans.find? (fun m => m.borrower = lender) with
  | none => exact Or.inl (by simp [hf])
  | some m =>
    right
    refine ⟨m, List.mem_of_find?_eq_some hf, ?_, ?_⟩
    · have := List.find?_some (p := fun x : Loan => decide (x.borrower = lender)) hf
      simpa using this
    · simp [hf]

/-- Two loans with the same borrower are equal, by borrower distinctness. -/
theorem World.LoansDistinctOK.borrower_unique {w : World} (hd : World.LoansDistinctOK w)
    {m l : Loan} (hm : m ∈ w.ctx.loans.loans) (hl : l ∈ w.ctx.loans.loans)
    (heq : m.borrower = l.borrower) : m = l :=
  List.nodup_map_inj hd.2.2.1 m hm l hl heq

/-- The loan with a given borrower, when present, is the one `find?` returns. -/
theorem World.LoansDistinctOK.find?_borrower_eq_some {w : World}
    (hd : World.LoansDistinctOK w) {m : Loan} (hm : m ∈ w.ctx.loans.loans) :
    w.ctx.loans.loans.find? (fun x => x.borrower = m.borrower) = some m := by
  apply List.find?_eq_some_of_unique hm (by simp)
  intro y hy hyp
  exact World.LoansDistinctOK.borrower_unique hd hy hm (by simpa using hyp)

/-- Two owners found at different allocations that share a live leaf are the
same owner, by global identifier distinctness. -/
theorem Ctx.findOwner?_eq_of_shared_leaf {C : Ctx} {a b : AllocId} {o o' : Owner}
    {id : CapId} {c c' : Leaf}
    (hnd : C.ids.Nodup)
    (ha : C.findOwner? a = some o) (hb : C.findOwner? b = some o')
    (hc : o.root.find? id = some c) (hc' : o'.root.find? id = some c') :
    o = o' := by
  by_cases hne : o = o'
  · exact hne
  · exfalso
    have ho : o ∈ C.owners := List.mem_of_find?_eq_some ha
    have ho' : o' ∈ C.owners := List.mem_of_find?_eq_some hb
    have hid : id ∈ o.ids := List.mem_cons_of_mem _ (Tree.mem_ids_of_find? hc)
    have hid' : id ∈ o'.ids := List.mem_cons_of_mem _ (Tree.mem_ids_of_find? hc')
    exact Ctx.ids_disjoint_of_ne hnd ho ho' hne id hid hid'

/-- A loan's lifetime is strictly below the fresh lifetime counter. -/
private theorem lifetime_ne_next {w : World} {l : Loan}
    (hlife : World.LifetimesBoundedOK w) (hl : l ∈ w.ctx.loans.loans) :
    l.lifetime ≠ ⟨w.ctx.loans.nextLifetime⟩ := by
  have hv := hlife.1 l hl
  unfold LoanCtx.live at hv
  cases hf : w.ctx.loans.findLifetime? l.lifetime with
  | none => simp [hf] at hv
  | some lt =>
    have hmem := List.mem_of_find?_eq_some hf
    have hpred : lt.id = l.lifetime := by
      have := List.find?_some (p := fun x : Lifetime => x.id = l.lifetime) hf
      simpa using this
    have hlt := hlife.2 lt hmem
    intro heq
    rw [hpred, heq] at hlt
    exact Nat.lt_irrefl _ hlt

/-- Prepending a distinct lifetime does not change a lifetime's liveness. -/
private theorem LoanCtx.live_cons_of_ne {Γ : LoanCtx} {life : Lifetime}
    {id : LifetimeId} (h : life.id ≠ id) :
    ({ Γ with lifetimes := life :: Γ.lifetimes }).live id = Γ.live id := by
  unfold LoanCtx.live LoanCtx.findLifetime?
  rw [List.find?_cons_of_neg (by simpa using h)]

/-- The new loan's chain and resource fields agree with the predecessor loan that
lent to the retagged name. -/
theorem beginBorrow_newLoan_fields {w : World} {a : AllocId} {lender borrower : CapId}
    {o o' : Owner} {c : Leaf}
    (hwf : w.WellFormed) (h : w.BorrowOK)
    (hfind : w.ctx.findOwner? a = some o)
    (hretag : o.retagLeafFind? lender borrower = some (o', c))
    {p : Loan} (hp : p ∈ w.ctx.loans.loans) (hbp : p.borrower = lender) :
    Ctx.borrowBase w.ctx lender = p.base ∧ a = p.alloc ∧ c.lo = p.lo
      ∧ c.hi = p.hi ∧ c.q = p.q ∧ c.ceiling = p.ceiling := by
  obtain ⟨hd, _hna, _hi, _hlife, _halloc, hdet, _hbase, hterm, _hagree, _horder, _hacyc⟩ := h
  obtain ⟨hc, _hact, _hfresh⟩ := Owner.retagLeafFind?_leaf hretag
  have hmem : o ∈ w.ctx.owners := List.mem_of_find?_eq_some hfind
  have hlendC : lender ∈ w.ctx.ids :=
    Ctx.owner_ids_sub_ids hmem lender
      (List.mem_cons_of_mem o.disposal (Tree.mem_ids_of_find? hc))
  have hfp : w.ctx.loans.loans.find? (fun m => m.borrower = lender) = some p := by
    rw [← hbp]
    exact World.LoansDistinctOK.find?_borrower_eq_some hd hp
  have hpb := (Ctx.borrowBase_eq_of_find hfp).1
  obtain ⟨op, hop, hcond⟩ := hterm p hp
  have hnotsucc : ¬ ∃ m ∈ w.ctx.loans.loans,
      m.lender = p.borrower ∧ m.alloc = p.alloc ∧ m.base = p.base := by
    rintro ⟨m, hm, hml, -, -⟩
    exact hdet m hm (hml.trans hbp ▸ hlendC)
  have hact := hcond.resolve_right hnotsucc
  obtain ⟨c2, hc2, _hact2, halloc2, hlo2, hhi2, hq2, hceil2⟩ := hact
  have hcop : o = op := by
    apply Ctx.findOwner?_eq_of_shared_leaf hwf.1.2.2 hfind hop hc
    simpa [hbp] using hc2
  have hcc : c2 = c := by
    rw [← hcop] at hc2
    rw [hbp] at hc2
    rw [hc] at hc2
    exact (Option.some.inj hc2).symm
  subst hcc
  have hpa : p.alloc = a := by
    have h1 := findOwner_alloc hop
    rw [← h1, ← hcop, findOwner_alloc hfind]
  exact ⟨hpb, hpa.symm, hlo2, hhi2, hq2, hceil2⟩

/-- Projections of the begun-borrow context. -/
@[simp] theorem Ctx.beginBorrowNext_issued (C : Ctx) (a : AllocId) (o o' : Owner)
    (c : Leaf) (lender borrower : CapId) (loanId : LoanId) :
    (C.beginBorrowNext a o o' c lender borrower loanId).issued = borrower :: C.issued := rfl

@[simp] theorem Ctx.beginBorrowNext_ids (C : Ctx) (a : AllocId) (o o' : Owner)
    (c : Leaf) (lender borrower : CapId) (loanId : LoanId) :
    (C.beginBorrowNext a o o' c lender borrower loanId).ids =
      (C.update o.alloc o').ids := rfl

@[simp] theorem Ctx.beginBorrowNext_loanList (C : Ctx) (a : AllocId) (o o' : Owner)
    (c : Leaf) (lender borrower : CapId) (loanId : LoanId) :
    (C.beginBorrowNext a o o' c lender borrower loanId).loans.loans =
      C.loans.loans ++
        [{ id := loanId, alloc := a, base := C.borrowBase lender, lender := lender,
           borrower := borrower, lifetime := ⟨C.loans.nextLifetime⟩,
           lo := c.lo, hi := c.hi, q := c.q, ceiling := c.ceiling }] := rfl

@[simp] theorem Ctx.beginBorrowNext_lifetimes (C : Ctx) (a : AllocId) (o o' : Owner)
    (c : Leaf) (lender borrower : CapId) (loanId : LoanId) :
    (C.beginBorrowNext a o o' c lender borrower loanId).loans.lifetimes =
      { id := ⟨C.loans.nextLifetime⟩, parent := C.borrowParent lender, state := .live }
        :: C.loans.lifetimes := rfl

@[simp] theorem Ctx.beginBorrowNext_nextLifetime (C : Ctx) (a : AllocId) (o o' : Owner)
    (c : Leaf) (lender borrower : CapId) (loanId : LoanId) :
    (C.beginBorrowNext a o o' c lender borrower loanId).loans.nextLifetime =
      C.loans.nextLifetime + 1 := rfl

/-- Beginning a borrow preserves active-terminal-or-delegated authority. -/
theorem World.beginBorrow_terminal {w w' : World} {a : AllocId}
    {lender borrower : CapId} {loanId : LoanId}
    (hw : w.beginBorrowChecked a lender borrower loanId = .ok w')
    (hinv : w.CommandInv) (h : w.BorrowOK) : World.LoansTerminalOK w' := by
  obtain ⟨hwf, hh, hlr⟩ := hinv
  obtain ⟨C, hC, hw'⟩ := World.beginBorrowChecked_sound hw
  obtain ⟨o, o', c, hfind, hretag, hiss, hroot, hloan, hlive, hCeq⟩ :=
    Ctx.beginBorrow?_sound hC
  subst hCeq
  subst hw'
  obtain ⟨hd, hna, hi, hlife, halloc, hdet, hbase, hterm, hagree, horder, hacyc⟩ := h
  have hB : w.BorrowOK := ⟨hd, hna, hi, hlife, halloc, hdet, hbase, hterm, hagree, horder, hacyc⟩
  obtain ⟨hc, hact, hfreshNew⟩ := Owner.retagLeafFind?_leaf hretag
  have hmem : o ∈ w.ctx.owners := List.mem_of_find?_eq_some hfind
  have hoa : o.alloc = a := by
    have := List.find?_some (p := fun x : Owner => decide (x.alloc = a))
      (by simpa [Ctx.findOwner?] using hfind)
    simpa using this
  have hrect : o.retagLeaf? lender borrower = some o' := Owner.retagLeafFind?_fst hretag
  have ho'alloc : o'.alloc = o.alloc := Owner.retagLeaf?_alloc hrect
  have ho'eq : o' = { o with root := o.root.retag lender borrower } := Owner.retagLeaf?_eq hrect
  have hfun : (w.ctx.update o.alloc o').Functional :=
    Ctx.update_functional ho'alloc hwf.1.1.2
  have hmem_update : o' ∈ (w.ctx.update o.alloc o').owners :=
    List.mem_map.mpr ⟨o, hmem, by simp [hoa]⟩
  have hfind_update : (w.ctx.update o.alloc o').findOwner? o'.alloc = some o' :=
    Ctx.findOwner?_eq_some_of_mem_of_functional hfun hmem_update
  have hc_alloc : c.alloc = a := by
    have := ((hwf.1.2.1 o hmem).2.1 lender c hc).1
    simpa [hoa] using this
  have hlendC : lender ∈ w.ctx.ids :=
    Ctx.owner_ids_sub_ids hmem lender
      (List.mem_cons_of_mem o.disposal (Tree.mem_ids_of_find? hc))
  intro l hl
  rw [Ctx.beginBorrowNext_loanList] at hl
  rcases List.mem_append.mp hl with hl | hl
  · obtain ⟨o2, ho2, hcond⟩ := hterm l hl
    by_cases hla : l.alloc = o.alloc
    · by_cases hbl : l.borrower = lender
      · -- successor is the new loan
        obtain ⟨hbase_eq, halloc_eq, hlo_eq, hhi_eq, hq_eq, hceil_eq⟩ :=
          beginBorrow_newLoan_fields hwf hB hfind hretag hl hbl
        refine ⟨o', ?_, Or.inr ⟨
          { id := loanId, alloc := a, base := Ctx.borrowBase w.ctx lender,
            lender := lender, borrower := borrower,
            lifetime := ⟨w.ctx.loans.nextLifetime⟩, lo := c.lo, hi := c.hi,
            q := c.q, ceiling := c.ceiling }, ?_, ?_, ?_, ?_⟩⟩
        · change (Ctx.update w.ctx o.alloc o').findOwner? l.alloc = some o'
          rw [hla]
          change (Ctx.update w.ctx o.alloc o').findOwner? o.alloc = some o'
          simpa [ho'alloc] using hfind_update
        · change _ ∈ (Ctx.beginBorrowNext w.ctx a o o' c lender borrower loanId).loans.loans
          rw [Ctx.beginBorrowNext_loanList]
          exact List.mem_append_right _ (by simp)
        · exact hbl.symm
        · exact halloc_eq
        · exact hbase_eq
      · -- the old leaf is unchanged by the retag
        refine ⟨o', ?_, ?_⟩
        · change (Ctx.update w.ctx o.alloc o').findOwner? l.alloc = some o'
          rw [hla]
          change (Ctx.update w.ctx o.alloc o').findOwner? o.alloc = some o'
          simpa [ho'alloc] using hfind_update
        · rcases hcond with ⟨c2, hc2, hact2, halloc2, hlo2, hhi2, hq2, hceil2⟩ |
            ⟨m, hm, hml, hma, hmb⟩
          · have ho2o : o2 = o := by
              have h' := ho2
              rw [hla] at h'
              have hfa : w.ctx.findOwner? o.alloc = some o := by rw [hoa]; exact hfind
              exact Option.some.inj (h'.symm.trans hfa)
            have hc2o : o.root.find? l.borrower = some c2 := by
              simpa [ho2o] using hc2
            have hne2 : l.borrower ≠ borrower := by
              intro h'
              exact hroot (h' ▸ Tree.mem_ids_of_find? hc2o)
            refine Or.inl ⟨c2, ?_, hact2, halloc2, hlo2, hhi2, hq2, hceil2⟩
            rw [ho'eq]
            rw [Tree.find?_retag_of_ne (old := lender) (new := borrower) (x := l.borrower)
              hbl hne2]
            exact hc2o
          · exact Or.inr ⟨m, List.mem_append_left _ hm, hml, hma, hmb⟩
    · refine ⟨o2, ?_, ?_⟩
      · change (Ctx.update w.ctx o.alloc o').findOwner? l.alloc = some o2
        rw [Ctx.findOwner?_update_of_ne w.ctx o.alloc o' hla ho'alloc]
        exact ho2
      · rcases hcond with h | ⟨m, hm, hml, hma, hmb⟩
        · exact Or.inl h
        · refine Or.inr ⟨m, ?_, hml, hma, hmb⟩
          change m ∈ (Ctx.beginBorrowNext w.ctx a o o' c lender borrower loanId).loans.loans
          rw [Ctx.beginBorrowNext_loanList]
          exact List.mem_append_left _ hm
  · simp only [List.mem_singleton] at hl
    subst hl
    refine ⟨o', ?_, Or.inl ⟨{ c with id := borrower }, ?_, hact, hc_alloc,
      rfl, rfl, rfl, rfl⟩⟩
    · change (Ctx.update w.ctx o.alloc o').findOwner? a = some o'
      have hlu : a = o'.alloc := by rw [← hoa, ← ho'alloc]
      rw [hlu]
      exact hfind_update
    · rw [ho'eq]
      exact Tree.find?_retag_new hc hfreshNew

/-- Beginning a borrow preserves adjacent-edge agreement. -/
theorem World.beginBorrow_agree {w w' : World} {a : AllocId}
    {lender borrower : CapId} {loanId : LoanId}
    (hw : w.beginBorrowChecked a lender borrower loanId = .ok w')
    (hinv : w.CommandInv) (h : w.BorrowOK) : World.LoansAgreeOK w' := by
  obtain ⟨hwf, _hh, _hlr⟩ := hinv
  obtain ⟨C, hC, hw'⟩ := World.beginBorrowChecked_sound hw
  obtain ⟨o, o', c, hfind, hretag, hiss, hroot, _hloan, _hlive, hCeq⟩ :=
    Ctx.beginBorrow?_sound hC
  subst hCeq
  subst hw'
  obtain ⟨hd, hna, hi, hlife, halloc, hdet, hbase, hterm, hagree, horder, hacyc⟩ := h
  have hB : w.BorrowOK := ⟨hd, hna, hi, hlife, halloc, hdet, hbase, hterm, hagree, horder, hacyc⟩
  obtain ⟨hc, _hact, _hfreshNew⟩ := Owner.retagLeafFind?_leaf hretag
  intro l hl m hm hadj
  rw [Ctx.beginBorrowNext_loanList] at hl hm
  rcases List.mem_append.mp hl with hl | hl <;>
    rcases List.mem_append.mp hm with hm | hm
  · exact hagree l hl m hm hadj
  · simp only [List.mem_singleton] at hm
    have hml : m.lender = lender := by rw [hm]
    have hmb : m.borrower = borrower := by rw [hm]
    subst hm
    cases hadj with
    | inl h =>
      have hbl : l.borrower = lender := h.symm.trans hml
      obtain ⟨hbase_eq, halloc_eq, hlo_eq, hhi_eq, hq_eq, hceil_eq⟩ :=
        beginBorrow_newLoan_fields hwf hB hfind hretag hl hbl
      exact ⟨hbase_eq, halloc_eq, hlo_eq, hhi_eq, hq_eq, hceil_eq⟩
    | inr h =>
      exfalso
      have hb : borrower = l.lender := hmb.trans h
      exact hiss (by rw [hb]; exact (hi l hl).1)
  · simp only [List.mem_singleton] at hl
    have hll : l.lender = lender := by rw [hl]
    have hlb : l.borrower = borrower := by rw [hl]
    subst hl
    cases hadj with
    | inl h =>
      exfalso
      have hb : borrower = m.lender := (h.trans hlb).symm
      exact hiss (by rw [hb]; exact (hi m hm).1)
    | inr h =>
      have hbm : m.borrower = lender := h.trans hll
      obtain ⟨hbase_eq, halloc_eq, hlo_eq, hhi_eq, hq_eq, hceil_eq⟩ :=
        beginBorrow_newLoan_fields hwf hB hfind hretag hm hbm
      exact ⟨hbase_eq.symm, halloc_eq.symm, hlo_eq.symm, hhi_eq.symm,
        hq_eq.symm, hceil_eq.symm⟩
  · simp only [List.mem_singleton] at hl hm
    have hll : l.lender = lender := by rw [hl]
    have hlb : l.borrower = borrower := by rw [hl]
    have hml : m.lender = lender := by rw [hm]
    have hmb : m.borrower = borrower := by rw [hm]
    subst hl
    subst hm
    cases hadj with
    | inl h =>
      exfalso
      have hb : lender = borrower := by rw [← hll, h, hmb]
      exact hroot (by rw [← hb]; exact Tree.mem_ids_of_find? hc)
    | inr h =>
      exfalso
      have hb : lender = borrower := by rw [← hll, ← h, hmb]
      exact hroot (by rw [← hb]; exact Tree.mem_ids_of_find? hc)

/-- Beginning a borrow preserves issued-order monotonicity. -/
theorem World.beginBorrow_order {w w' : World} {a : AllocId} {lender borrower : CapId}
    {loanId : LoanId} (hw : w.beginBorrowChecked a lender borrower loanId = .ok w')
    (hinv : w.CommandInv) (h : w.BorrowOK) : World.LoansOrderOK w' := by
  obtain ⟨_hwf, _hh, _hlr⟩ := hinv
  obtain ⟨C, hC, hw'⟩ := World.beginBorrowChecked_sound hw
  obtain ⟨o, o', c, _hfind, _hretag, hiss, _hroot, _hloan, _hlive, hCeq⟩ :=
    Ctx.beginBorrow?_sound hC
  subst hCeq
  subst hw'
  obtain ⟨_hd, _hna, hi, _hlife, _halloc, _hdet, _hbase, _hterm, _hagree, horder, _hacyc⟩ := h
  obtain ⟨hc, _hact, _hfresh⟩ := Owner.retagLeafFind?_leaf _hretag
  intro l hl
  rw [Ctx.beginBorrowNext_loanList] at hl
  rcases List.mem_append.mp hl with hl | hl
  · have hb := (hi l hl).2.1
    have hn := (hi l hl).1
    have hbne : l.borrower ≠ borrower := fun h' => hiss (h' ▸ hb)
    have hlne : l.lender ≠ borrower := fun h' => hiss (h' ▸ hn)
    have hord := horder l hl
    rw [Ctx.beginBorrowNext_issued]
    rw [idxOf_cons_ne (a := borrower) (b := l.borrower) (fun h => hbne h.symm),
        idxOf_cons_ne (a := borrower) (b := l.lender) (fun h => hlne h.symm)]
    omega
  · simp only [List.mem_singleton] at hl
    subst hl
    have hbne : borrower ≠ lender := by
      intro h'
      have hlend : lender ∈ w.ctx.ids := Ctx.owner_ids_sub_ids
        (List.mem_of_find?_eq_some _hfind) lender
        (List.mem_cons_of_mem o.disposal (Tree.mem_ids_of_find? hc))
      exact hiss (by rw [← h'] at hlend; exact _hh.2 borrower hlend)
    rw [Ctx.beginBorrowNext_issued]
    rw [List.idxOf_cons_self]
    rw [idxOf_cons_ne (a := borrower) (b := lender) hbne]
    omega

/-- Beginning a borrow preserves the integrated delegation invariant. -/
theorem borrowOK_beginBorrow {w w' : World} {a : AllocId}
    {lender borrower : CapId} {loanId : LoanId}
    (hw : w.beginBorrowChecked a lender borrower loanId = .ok w')
    (hinv : w.CommandInv) (h : w.BorrowOK) : w'.BorrowOK := by
  obtain ⟨hwf, hh, _hlr⟩ := hinv
  obtain ⟨C, hC, hw'⟩ := World.beginBorrowChecked_sound hw
  obtain ⟨o, o', c, hfind, hretag, hiss, hroot, hloan, hlive, hCeq⟩ :=
    Ctx.beginBorrow?_sound hC
  subst hCeq
  subst hw'
  obtain ⟨hd, hna, hi, hlife, halloc, hdet, hbase, hterm, hagree, horder, hacyc⟩ := h
  have hB : w.BorrowOK := ⟨hd, hna, hi, hlife, halloc, hdet, hbase, hterm, hagree, horder, hacyc⟩
  obtain ⟨hc, _hact, _hfresh⟩ := Owner.retagLeafFind?_leaf hretag
  have hmem : o ∈ w.ctx.owners := List.mem_of_find?_eq_some hfind
  have hoa : o.alloc = a := by
    have := List.find?_some (p := fun x : Owner => decide (x.alloc = a))
      (by simpa [Ctx.findOwner?] using hfind)
    simpa using this
  have hrect : o.retagLeaf? lender borrower = some o' := Owner.retagLeafFind?_fst hretag
  have ho'alloc : o'.alloc = o.alloc := Owner.retagLeaf?_alloc hrect
  have hoid : o.ids.Nodup := Ctx.owner_ids_nodup hwf.1.2.2 hmem
  have hnewCids : borrower ∉ w.ctx.ids := by
    intro hm; exact hiss (hh.2 borrower hm)
  have hdisp : borrower ≠ o.disposal := by
    intro heq
    have hmemid : o.disposal ∈ w.ctx.ids :=
      List.mem_flatMap.mpr ⟨o, hmem, by simp [Owner.ids]⟩
    exact hnewCids (heq ▸ hmemid)
  have ho'nd : o'.ids.Nodup := Owner.retagLeaf?_ids_nodup hrect hoid hdisp
  have hsub : ∀ x ∈ o'.ids, x ∈ o.ids ∨ x = borrower := Owner.retagLeaf?_ids_sub hrect
  have hlend_owner : lender ∈ o.ids :=
    List.mem_cons_of_mem o.disposal (Tree.mem_ids_of_find? hc)
  have hlendC : lender ∈ w.ctx.ids := Ctx.owner_ids_sub_ids hmem lender hlend_owner
  have hlendIss : lender ∈ w.ctx.issued := hh.2 lender hlendC
  have hnewDetach : lender ∉ (w.ctx.update o.alloc o').ids :=
    Ctx.not_mem_ids_update_of_owner hwf.1.1 hwf.1.2.2 hmem rfl hlend_owner
      (Owner.retagLeaf?_detached hrect hoid)
  have holdDetach : ∀ m ∈ w.ctx.loans.loans,
      m.lender ∉ (w.ctx.update o.alloc o').ids := by
    intro m hm hmemx
    rcases (flatMap_update_ids_nodup_of_sub w.ctx.owners o.alloc o o' borrower
      hwf.1.1.2 hwf.1.2.2 hmem rfl ho'nd hsub hnewCids).2 m.lender hmemx with
      hold | heq
    · exact hdet m hm hold
    · exact hiss (heq ▸ (hi m hm).1)
  have hmem_update : o' ∈ (w.ctx.update o.alloc o').owners := by
    unfold Ctx.update
    exact List.mem_map.mpr ⟨o, hmem, by simp⟩
  have hfind_update : (w.ctx.update o.alloc o').findOwner? o'.alloc = some o' :=
    Ctx.findOwner?_eq_some_of_mem_of_functional
      (C := w.ctx.update o.alloc o') (o := o')
      (Ctx.update_functional ho'alloc hwf.1.1.2) hmem_update
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- distinct
    unfold LoansDistinctOK
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [show (w.ctx.beginBorrowNext a o o' c lender borrower loanId).loans.loans.map (·.id)
          = (w.ctx.loans.loans.map (·.id)) ++ [loanId] from by
        rw [Ctx.beginBorrowNext_loanList]; simp]
      rw [List.nodup_append]
      refine ⟨hd.1, by simp, ?_⟩
      intro x hx y hy
      simp at hy
      subst y
      intro hxy
      exact hloan (hxy ▸ hx)
    · rw [show (w.ctx.beginBorrowNext a o o' c lender borrower loanId).loans.loans.map (·.lender)
          = (w.ctx.loans.loans.map (·.lender)) ++ [lender] from by
        rw [Ctx.beginBorrowNext_loanList]; simp]
      rw [List.nodup_append]
      refine ⟨hd.2.1, by simp, ?_⟩
      intro x hx y hy
      simp at hy
      subst y
      intro hxy
      rcases List.mem_map.mp hx with ⟨m, hm', hmx⟩
      exact hdet m hm' (by rw [hmx, hxy]; exact hlendC)
    · rw [show (w.ctx.beginBorrowNext a o o' c lender borrower loanId).loans.loans.map (·.borrower)
          = (w.ctx.loans.loans.map (·.borrower)) ++ [borrower] from by
        rw [Ctx.beginBorrowNext_loanList]; simp]
      rw [List.nodup_append]
      refine ⟨hd.2.2.1, by simp, ?_⟩
      intro x hx y hy
      simp at hy
      subst y
      intro hxy
      rcases List.mem_map.mp hx with ⟨m, hm', hmx⟩
      exact hiss (by simpa [hmx, hxy] using (hi m hm').2.1)
    · rw [show (w.ctx.beginBorrowNext a o o' c lender borrower loanId).loans.loans.map (·.lifetime)
          = (w.ctx.loans.loans.map (·.lifetime)) ++ [⟨w.ctx.loans.nextLifetime⟩] from by
        rw [Ctx.beginBorrowNext_loanList]; simp]
      rw [List.nodup_append]
      refine ⟨hd.2.2.2, by simp, ?_⟩
      intro x hx y hy
      simp at hy
      subst y
      intro hxy
      rcases List.mem_map.mp hx with ⟨m, hm', hmx⟩
      exact lifetime_ne_next hlife hm' (by rw [hmx, hxy])
  · -- non-alias
    intro l hl
    rw [Ctx.beginBorrowNext_loanList] at hl
    rcases List.mem_append.mp hl with hl | hl
    · exact hna l hl
    · simp only [List.mem_singleton] at hl
      subst hl
      intro heq
      change lender = borrower at heq
      exact hroot (heq ▸ Tree.mem_ids_of_find? hc)
  · -- issued
    intro l hl
    rw [Ctx.beginBorrowNext_loanList] at hl
    rcases List.mem_append.mp hl with hl | hl
    · obtain ⟨h1, h2, h3⟩ := hi l hl
      exact ⟨List.mem_cons_of_mem _ h1, List.mem_cons_of_mem _ h2,
        List.mem_cons_of_mem _ h3⟩
    · simp only [List.mem_singleton] at hl
      subst hl
      refine ⟨List.mem_cons_of_mem _ hlendIss, List.mem_cons_self, ?_⟩
      rcases Ctx.borrowBase_eq_or_mem w.ctx lender with hb | ⟨m, hm, hbm, hbs⟩
      · rw [hb]; exact List.mem_cons_of_mem _ hlendIss
      · rw [hbs]; exact List.mem_cons_of_mem _ (hi m hm).2.2
  · -- lifetimes
    refine ⟨?_, ?_⟩
    · intro l hl
      rw [Ctx.beginBorrowNext_loanList] at hl
      rcases List.mem_append.mp hl with hl | hl
      · have hne : (⟨w.ctx.loans.nextLifetime⟩ : LifetimeId) ≠ l.lifetime :=
          Ne.symm (lifetime_ne_next hlife hl)
        change (Ctx.beginBorrowNext w.ctx a o o' c lender borrower loanId).loans.live
          l.lifetime = true
        unfold LoanCtx.live LoanCtx.findLifetime?
        rw [Ctx.beginBorrowNext_lifetimes]
        rw [List.find?_cons_of_neg (by simp [hne])]
        exact hlife.1 l hl
      · simp only [List.mem_singleton] at hl
        subst hl
        change (Ctx.beginBorrowNext w.ctx a o o' c lender borrower loanId).loans.live
          ⟨w.ctx.loans.nextLifetime⟩ = true
        unfold LoanCtx.live LoanCtx.findLifetime?
        rw [Ctx.beginBorrowNext_lifetimes]
        simp [List.find?_cons, LoanCtx.rootLifetime]
    · intro lt hlt
      change lt ∈ (Ctx.beginBorrowNext w.ctx a o o' c lender borrower loanId).loans.lifetimes at hlt
      rw [Ctx.beginBorrowNext_lifetimes] at hlt
      simp only [List.mem_cons] at hlt
      rcases hlt with rfl | hlt
      · rw [Ctx.beginBorrowNext_nextLifetime]; simp
      · have := hlife.2 lt hlt
        rw [Ctx.beginBorrowNext_nextLifetime]
        omega
  · -- allocation
    intro l hl
    rw [Ctx.beginBorrowNext_loanList] at hl
    rcases List.mem_append.mp hl with hl | hl
    · by_cases hla : l.alloc = o.alloc
      · refine ⟨o', ?_⟩
        have hlu : l.alloc = o'.alloc := by rw [hla, ← ho'alloc]
        change (Ctx.update w.ctx o.alloc o').findOwner? l.alloc = some o'
        rw [hlu]
        exact hfind_update
      · obtain ⟨o2, ho2⟩ := halloc l hl
        refine ⟨o2, ?_⟩
        change (Ctx.update w.ctx o.alloc o').findOwner? l.alloc = some o2
        rw [Ctx.findOwner?_update_of_ne w.ctx o.alloc o' hla ho'alloc]
        exact ho2
    · simp only [List.mem_singleton] at hl
      subst hl
      refine ⟨o', ?_⟩
      have hlu : a = o'.alloc := by rw [← hoa, ← ho'alloc]
      change (Ctx.update w.ctx o.alloc o').findOwner? a = some o'
      rw [hlu]
      exact hfind_update
  · -- detached
    intro l hl
    rw [Ctx.beginBorrowNext_loanList] at hl
    rcases List.mem_append.mp hl with hl | hl
    · exact holdDetach l hl
    · simp only [List.mem_singleton] at hl
      subst hl
      change lender ∉ (Ctx.beginBorrowNext w.ctx a o o' c lender borrower loanId).ids
      rw [Ctx.beginBorrowNext_ids]
      exact hnewDetach
  · -- base
    intro l hl
    rw [Ctx.beginBorrowNext_loanList] at hl
    rcases List.mem_append.mp hl with hl | hl
    · rcases hbase l hl with h | ⟨m, hm, hmb, hml⟩
      · exact Or.inl h
      · refine Or.inr ⟨m, ?_, hmb, hml⟩
        change m ∈ (Ctx.beginBorrowNext w.ctx a o o' c lender borrower loanId).loans.loans
        rw [Ctx.beginBorrowNext_loanList]
        exact List.mem_append_left _ hm
    · simp only [List.mem_singleton] at hl
      subst hl
      rcases Ctx.borrowBase_eq_or_mem w.ctx lender with hb | ⟨m, hm, hbm, hbs⟩
      · refine Or.inl ?_
        simpa using hb.symm
      · refine Or.inr ⟨m, ?_, ?_, ?_⟩
        · change m ∈ (Ctx.beginBorrowNext w.ctx a o o' c lender borrower loanId).loans.loans
          rw [Ctx.beginBorrowNext_loanList]
          exact List.mem_append_left _ hm
        · simpa using hbs.symm
        · simpa using hbm
  · exact World.beginBorrow_terminal hw ⟨hwf, hh, _hlr⟩ hB
  · exact World.beginBorrow_agree hw ⟨hwf, hh, _hlr⟩ hB
  · exact World.beginBorrow_order hw ⟨hwf, hh, _hlr⟩ hB
  · exact World.borrowAcyclic_of_issuedOrder (World.beginBorrow_order hw ⟨hwf, hh, _hlr⟩ hB)

/-- Projections of the returned-borrow context. -/
@[simp] theorem Ctx.endBorrowNext_issued (C : Ctx) (o o' : Owner) (loan : Loan) :
    (C.endBorrowNext o o' loan).issued = C.issued := rfl

@[simp] theorem Ctx.endBorrowNext_ids (C : Ctx) (o o' : Owner) (loan : Loan) :
    (C.endBorrowNext o o' loan).ids = (C.update o.alloc o').ids := rfl

@[simp] theorem Ctx.endBorrowNext_loanList (C : Ctx) (o o' : Owner) (loan : Loan) :
    (C.endBorrowNext o o' loan).loans.loans =
      C.loans.loans.filter (fun m => m.id ≠ loan.id) := rfl

@[simp] theorem Ctx.endBorrowNext_lifetimes (C : Ctx) (o o' : Owner) (loan : Loan) :
    (C.endBorrowNext o o' loan).loans.lifetimes =
      (C.loans.endBorrowBookkeeping loan).lifetimes := rfl

/-- Lifetime lookup is unchanged by the return bookkeeping for a different lifetime. -/
theorem LoanCtx.findLifetime?_endBorrowBookkeeping_of_ne {Γ : LoanCtx} {l : Loan}
    {id : LifetimeId} (h : id ≠ l.lifetime) :
    (Γ.endBorrowBookkeeping l).findLifetime? id = Γ.findLifetime? id := by
  simp only [LoanCtx.endBorrowBookkeeping, LoanCtx.findLifetime?]
  rw [List.find?_map]
  have hpred : ((fun y : Lifetime => decide (y.id = id)) ∘ fun x : Lifetime =>
        if x.id = l.lifetime ∧ x.id ≠ LoanCtx.rootLifetime then
          { x with state := .ended } else x) =
      (fun x : Lifetime => decide (x.id = id)) := by
    funext x
    simp only [Function.comp]
    have hid : (if x.id = l.lifetime ∧ x.id ≠ LoanCtx.rootLifetime then
        { x with state := .ended } else x).id = x.id := by
      split <;> rfl
    simp only [hid]
  rw [hpred]
  cases hf : Γ.lifetimes.find? (fun x : Lifetime => x.id = id) with
  | none => rfl
  | some lt =>
    have hid : lt.id = id := by
      have := List.find?_some (p := fun x : Lifetime => x.id = id) hf
      simpa using this
    have hne : lt.id ≠ l.lifetime := by rw [hid]; exact h
    simp [hf, hne]

/-- Liveness is unchanged by the return bookkeeping for a different lifetime. -/
theorem LoanCtx.live_endBorrowBookkeeping_of_ne {Γ : LoanCtx} {l : Loan}
    {id : LifetimeId} (h : id ≠ l.lifetime) :
    (Γ.endBorrowBookkeeping l).live id = Γ.live id := by
  unfold LoanCtx.live
  rw [LoanCtx.findLifetime?_endBorrowBookkeeping_of_ne h]

/-- The return bookkeeping preserves the lifetime bound. -/
theorem LoanCtx.endBorrowBookkeeping_lifetimes_bounded {Γ : LoanCtx} {l : Loan}
    (h : ∀ lt ∈ Γ.lifetimes, lt.id.val < Γ.nextLifetime) :
    ∀ lt ∈ (Γ.endBorrowBookkeeping l).lifetimes,
      lt.id.val < (Γ.endBorrowBookkeeping l).nextLifetime := by
  intro lt hlt
  unfold LoanCtx.endBorrowBookkeeping at hlt ⊢
  rw [List.mem_map] at hlt
  obtain ⟨x, hx, rfl⟩ := hlt
  have hx' := h x hx
  have hidv : (if x.id = l.lifetime ∧ x.id ≠ LoanCtx.rootLifetime then
        { x with state := .ended } else x).id.val = x.id.val := by
    split <;> rfl
  simpa [hidv] using hx'

/-- Ending a borrow preserves active-terminal-or-delegated authority. -/
theorem World.endBorrow_terminal {w w' : World} {a : AllocId} {loanId : LoanId}
    (hw : w.endBorrowChecked a loanId = .ok w')
    (hinv : w.CommandInv) (h : w.BorrowOK) : World.LoansTerminalOK w' := by
  obtain ⟨hwf, _hh, _hlr⟩ := hinv
  obtain ⟨C, hC, hw'⟩ := World.endBorrowChecked_sound hw
  obtain ⟨loan, o, o', hloan, hfind, hret, hsuc, _hdesc, hCeq⟩ :=
    Ctx.endBorrow?_sound hC
  subst hCeq
  subst hw'
  obtain ⟨hd, hna, _hi, _hlife, _halloc, hdet, _hbase, hterm, hagree, _horder,
    _hacyc⟩ := h
  have hloan_mem : loan ∈ w.ctx.loans.loans := List.mem_of_find?_eq_some hloan
  have hloan_id : loan.id = loanId := by
    have := List.find?_some (p := fun x : Loan => x.id = loanId) hloan
    simpa using this
  have hmem : o ∈ w.ctx.owners := List.mem_of_find?_eq_some hfind
  have hoa : o.alloc = a := by
    have := List.find?_some (p := fun x : Owner => decide (x.alloc = a))
      (by simpa [Ctx.findOwner?] using hfind)
    simpa using this
  have ho'alloc : o'.alloc = o.alloc := Owner.retagLeaf?_alloc hret
  have ho'eq : o' = { o with root := o.root.retag loan.borrower loan.lender } :=
    Owner.retagLeaf?_eq hret
  have hfresh : loan.lender ∉ o.root.ids := Owner.retagLeaf?_fresh hret
  have hmem_update : o' ∈ (w.ctx.update o.alloc o').owners := by
    unfold Ctx.update
    exact List.mem_map.mpr ⟨o, hmem, by simp⟩
  have hfind_update : (w.ctx.update o.alloc o').findOwner? o'.alloc = some o' :=
    Ctx.findOwner?_eq_some_of_mem_of_functional
      (C := w.ctx.update o.alloc o') (o := o')
      (Ctx.update_functional ho'alloc hwf.1.1.2) hmem_update
  -- The removed loan is never a successor of a surviving loan.
  have hsucc_impossible : ¬ ∃ m ∈ w.ctx.loans.loans,
      m.lender = loan.borrower ∧ m.alloc = loan.alloc ∧ m.base = loan.base := by
    rintro ⟨m, hm, hml, _hma, _hmb⟩
    by_cases hmid : m.id = loanId
    · have hm_eq : m = loan :=
        List.nodup_map_inj hd.1 m hm loan hloan_mem (by rw [hmid, hloan_id])
      rw [hm_eq] at hml
      exact hna loan hloan_mem hml
    · exact hsuc m hm hmid hml
  -- The ended loan's authoritative leaf, in the owner being retagged.
  have hself : ∃ c, w.ctx.findOwner? loan.alloc = some o ∧
      o.root.find? loan.borrower = some c ∧ c.state = .active ∧
      c.alloc = loan.alloc ∧ c.lo = loan.lo ∧ c.hi = loan.hi ∧
      c.q = loan.q ∧ c.ceiling = loan.ceiling := by
    rcases hterm loan hloan_mem with ⟨o0, ho0, hleaf | hsucc⟩
    · rcases hleaf with ⟨c0, hc0, hact0, halloc0, hlo0, hhi0, hq0, hceil0⟩
      obtain ⟨c1, hc1, _⟩ := Owner.retagLeaf?_active hret
      have hoo : o0 = o :=
        Ctx.findOwner?_eq_of_shared_leaf hwf.1.2.2 ho0 hfind hc0 hc1
      exact ⟨c0, hoo ▸ ho0, hoo ▸ hc0, hact0, halloc0, hlo0, hhi0, hq0, hceil0⟩
    · exact absurd hsucc hsucc_impossible
  obtain ⟨c0, hfind_loan, hc0, hc0act, hc0alloc, hc0lo, hc0hi, hc0q, hc0ceil⟩ :=
    hself
  have ho_alloc_loan : o.alloc = loan.alloc := by
    have := List.find?_some (p := fun x : Owner => decide (x.alloc = loan.alloc))
      (by simpa [Ctx.findOwner?] using hfind_loan)
    simpa using this
  have hloana : loan.alloc = a := ho_alloc_loan.symm.trans hoa
  have hfind_o : (Ctx.update w.ctx o.alloc o').findOwner? o.alloc = some o' := by
    simpa [ho'alloc] using hfind_update
  intro l hl
  change l ∈ (w.ctx.endBorrowNext o o' loan).loans.loans at hl
  simp only [Ctx.endBorrowNext, LoanCtx.endBorrowBookkeeping, List.mem_filter] at hl
  obtain ⟨hl_old, hlid⟩ := hl
  have hl_id : l.id ≠ loan.id := by simpa using hlid
  have hl_id' : l.id ≠ loanId := by simpa [hloan_id] using hl_id
  obtain ⟨o2, ho2, hcond⟩ := hterm l hl_old
  by_cases hla : l.alloc = o.alloc
  · by_cases hbl : l.borrower = loan.borrower
    · have hEq : l = loan := List.nodup_map_inj hd.2.2.1 l hl_old loan hloan_mem hbl
      exact absurd (by rw [hEq]) hl_id
    · by_cases hbn : l.borrower = loan.lender
      · -- the predecessor's leaf is the restored one
        obtain ⟨_hlbase, hlalloc, hllo, hlhi, hlq, hlceil⟩ :=
          hagree loan hloan_mem l hl_old (Or.inr hbn)
        refine ⟨o', ?_, Or.inl ⟨{ c0 with id := loan.lender }, ?_, ?_, ?_, ?_, ?_,
          ?_, ?_⟩⟩
        · change (Ctx.update w.ctx o.alloc o').findOwner? l.alloc = some o'
          rw [hla]
          exact hfind_o
        · rw [ho'eq]
          rw [hbn]
          exact Tree.find?_retag_new hc0 hfresh
        · simpa using hc0act
        · simpa using hc0alloc.trans hlalloc.symm
        · simpa using hc0lo.trans hllo.symm
        · simpa using hc0hi.trans hlhi.symm
        · simpa using hc0q.trans hlq.symm
        · simpa using hc0ceil.trans hlceil.symm
      · rcases hcond with
          ⟨c2, hc2, hact2, halloc2, hlo2, hhi2, hq2, hceil2⟩ |
          ⟨m, hm, hml, hma, hmb⟩
        · -- a leaf at another name is untouched
          have hfind_a : w.ctx.findOwner? o.alloc = some o := by
            rw [hoa]
            exact hfind
          have ho2o : o2 = o := by
            have h' : w.ctx.findOwner? o.alloc = some o2 := by
              simpa [hla] using ho2
            exact Option.some.inj (h'.symm.trans hfind_a)
          have hc2o : o.root.find? l.borrower = some c2 := ho2o ▸ hc2
          refine ⟨o', ?_, Or.inl ⟨c2, ?_, hact2, halloc2, hlo2, hhi2, hq2,
            hceil2⟩⟩
          · change (Ctx.update w.ctx o.alloc o').findOwner? l.alloc = some o'
            rw [hla]
            exact hfind_o
          · rw [ho'eq]
            rw [Tree.find?_retag_of_ne hbl hbn]
            exact hc2o
        · by_cases hmid : m.id = loan.id
          · have hm_eq : m = loan :=
              List.nodup_map_inj hd.1 m hm loan hloan_mem (by rw [hmid, hloan_id])
            exact absurd (by rw [hm_eq] at hml; exact hml.symm) hbn
          · -- a surviving successor
            refine ⟨o', ?_, Or.inr ⟨m, ?_, hml, hma, hmb⟩⟩
            · change (Ctx.update w.ctx o.alloc o').findOwner? l.alloc = some o'
              rw [hla]
              exact hfind_o
            · simp only [Ctx.endBorrowNext, LoanCtx.endBorrowBookkeeping,
                List.mem_filter]
              exact ⟨hm, by simpa using hmid⟩
  · -- the owner holding `l` is not retagged
    rcases hcond with
      ⟨c2, hc2, hact2, halloc2, hlo2, hhi2, hq2, hceil2⟩ |
      ⟨m, hm, hml, hma, hmb⟩
    · refine ⟨o2, ?_, Or.inl ⟨c2, ?_, hact2, halloc2, hlo2, hhi2, hq2, hceil2⟩⟩
      · change (Ctx.update w.ctx o.alloc o').findOwner? l.alloc = some o2
        rw [Ctx.findOwner?_update_of_ne w.ctx o.alloc o' hla ho'alloc]
        exact ho2
      · exact hc2
    · by_cases hmid : m.id = loan.id
      · have hm_eq : m = loan :=
          List.nodup_map_inj hd.1 m hm loan hloan_mem (by rw [hmid, hloan_id])
        exact absurd (by rw [← hma, hm_eq, hloana, hoa]) hla
      · refine ⟨o2, ?_, Or.inr ⟨m, ?_, hml, hma, hmb⟩⟩
        · change (Ctx.update w.ctx o.alloc o').findOwner? l.alloc = some o2
          rw [Ctx.findOwner?_update_of_ne w.ctx o.alloc o' hla ho'alloc]
          exact ho2
        · simp only [Ctx.endBorrowNext, LoanCtx.endBorrowBookkeeping,
            List.mem_filter]
          exact ⟨hm, by simpa using hmid⟩

/-- Ending a borrow preserves the integrated delegation invariant. -/
theorem borrowOK_endBorrow {w w' : World} {a : AllocId} {loanId : LoanId}
    (hw : w.endBorrowChecked a loanId = .ok w')
    (hinv : w.CommandInv) (h : w.BorrowOK) : w'.BorrowOK := by
  obtain ⟨hwf, hh, hlr⟩ := hinv
  obtain ⟨C, hC, hw'⟩ := World.endBorrowChecked_sound hw
  obtain ⟨loan, o, o', hloan, hfind, hret, hsuc, hdesc, hCeq⟩ :=
    Ctx.endBorrow?_sound hC
  subst hCeq
  subst hw'
  obtain ⟨hd, hna, hi, hlife, halloc, hdet, hbase, hterm, hagree, horder,
    hacyc⟩ := h
  have hB : w.BorrowOK :=
    ⟨hd, hna, hi, hlife, halloc, hdet, hbase, hterm, hagree, horder, hacyc⟩
  have hloan_mem : loan ∈ w.ctx.loans.loans := List.mem_of_find?_eq_some hloan
  have hloan_id : loan.id = loanId := by
    have := List.find?_some (p := fun x : Loan => x.id = loanId) hloan
    simpa using this
  have hmem : o ∈ w.ctx.owners := List.mem_of_find?_eq_some hfind
  have ho'alloc : o'.alloc = o.alloc := Owner.retagLeaf?_alloc hret
  have hmem_update : o' ∈ (w.ctx.update o.alloc o').owners := by
    unfold Ctx.update
    exact List.mem_map.mpr ⟨o, hmem, by simp⟩
  have hfind_update : (w.ctx.update o.alloc o').findOwner? o'.alloc = some o' :=
    Ctx.findOwner?_eq_some_of_mem_of_functional
      (C := w.ctx.update o.alloc o') (o := o')
      (Ctx.update_functional ho'alloc hwf.1.1.2) hmem_update
  have horder' : World.LoansOrderOK { w with ctx := w.ctx.endBorrowNext o o' loan } := by
    intro l hl
    change l ∈ (w.ctx.endBorrowNext o o' loan).loans.loans at hl
    simp only [Ctx.endBorrowNext, LoanCtx.endBorrowBookkeeping, List.mem_filter] at hl
    exact horder l hl.1
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, horder',
    World.borrowAcyclic_of_issuedOrder horder'⟩
  · -- distinct
    unfold LoansDistinctOK
    refine ⟨?_, ?_, ?_, ?_⟩
    · change ((w.ctx.endBorrowNext o o' loan).loans.loans.map (·.id)).Nodup
      simp only [Ctx.endBorrowNext, LoanCtx.endBorrowBookkeeping]
      exact List.Sublist.nodup
        (List.Sublist.map (fun m => m.id)
          (List.filter_sublist (l := w.ctx.loans.loans)
            (p := fun m => m.id ≠ loan.id))) hd.1
    · change ((w.ctx.endBorrowNext o o' loan).loans.loans.map (·.lender)).Nodup
      simp only [Ctx.endBorrowNext, LoanCtx.endBorrowBookkeeping]
      exact List.Sublist.nodup
        (List.Sublist.map (fun m => m.lender)
          (List.filter_sublist (l := w.ctx.loans.loans)
            (p := fun m => m.id ≠ loan.id))) hd.2.1
    · change ((w.ctx.endBorrowNext o o' loan).loans.loans.map (·.borrower)).Nodup
      simp only [Ctx.endBorrowNext, LoanCtx.endBorrowBookkeeping]
      exact List.Sublist.nodup
        (List.Sublist.map (fun m => m.borrower)
          (List.filter_sublist (l := w.ctx.loans.loans)
            (p := fun m => m.id ≠ loan.id))) hd.2.2.1
    · change ((w.ctx.endBorrowNext o o' loan).loans.loans.map (·.lifetime)).Nodup
      simp only [Ctx.endBorrowNext, LoanCtx.endBorrowBookkeeping]
      exact List.Sublist.nodup
        (List.Sublist.map (fun m => m.lifetime)
          (List.filter_sublist (l := w.ctx.loans.loans)
            (p := fun m => m.id ≠ loan.id))) hd.2.2.2
  · -- non-alias
    intro l hl
    change l ∈ (w.ctx.endBorrowNext o o' loan).loans.loans at hl
    simp only [Ctx.endBorrowNext, LoanCtx.endBorrowBookkeeping, List.mem_filter] at hl
    exact hna l hl.1
  · -- issued
    intro l hl
    change l ∈ (w.ctx.endBorrowNext o o' loan).loans.loans at hl
    simp only [Ctx.endBorrowNext, LoanCtx.endBorrowBookkeeping, List.mem_filter] at hl
    exact hi l hl.1
  · -- lifetimes
    refine ⟨?_, ?_⟩
    · intro l hl
      change l ∈ (w.ctx.endBorrowNext o o' loan).loans.loans at hl
      simp only [Ctx.endBorrowNext, LoanCtx.endBorrowBookkeeping, List.mem_filter] at hl
      obtain ⟨hl_old, hlid⟩ := hl
      have hl_id : l.id ≠ loan.id := by simpa using hlid
      have hne : l.lifetime ≠ loan.lifetime := by
        intro heq
        have hEq : l = loan := List.nodup_map_inj hd.2.2.2 l hl_old loan hloan_mem heq
        exact hl_id (by rw [hEq])
      have hgoal : (w.ctx.endBorrowNext o o' loan).loans.live l.lifetime
          = w.ctx.loans.live l.lifetime := by
        change (w.ctx.loans.endBorrowBookkeeping loan).live l.lifetime
          = w.ctx.loans.live l.lifetime
        exact LoanCtx.live_endBorrowBookkeeping_of_ne hne
      exact hgoal.trans (hlife.1 l hl_old)
    · intro lt hlt
      change lt ∈ (w.ctx.endBorrowNext o o' loan).loans.lifetimes at hlt
      rw [Ctx.endBorrowNext_lifetimes] at hlt
      exact LoanCtx.endBorrowBookkeeping_lifetimes_bounded hlife.2 lt hlt
  · -- allocation
    intro l hl
    change l ∈ (w.ctx.endBorrowNext o o' loan).loans.loans at hl
    simp only [Ctx.endBorrowNext, LoanCtx.endBorrowBookkeeping, List.mem_filter] at hl
    obtain ⟨hl_old, _⟩ := hl
    obtain ⟨o2, ho2⟩ := halloc l hl_old
    by_cases hla : l.alloc = o.alloc
    · refine ⟨o', ?_⟩
      change (Ctx.update w.ctx o.alloc o').findOwner? l.alloc = some o'
      rw [hla]
      change (Ctx.update w.ctx o.alloc o').findOwner? o.alloc = some o'
      simpa [ho'alloc] using hfind_update
    · refine ⟨o2, ?_⟩
      change (Ctx.update w.ctx o.alloc o').findOwner? l.alloc = some o2
      rw [Ctx.findOwner?_update_of_ne w.ctx o.alloc o' hla ho'alloc]
      exact ho2
  · -- detached
    intro l hl hmeml
    change l ∈ (w.ctx.endBorrowNext o o' loan).loans.loans at hl
    simp only [Ctx.endBorrowNext, LoanCtx.endBorrowBookkeeping, List.mem_filter] at hl
    obtain ⟨hl_old, hlid⟩ := hl
    have hl_id : l.id ≠ loan.id := by simpa using hlid
    have hmem' : l.lender ∈ (w.ctx.update o.alloc o').ids := by simpa using hmeml
    rcases Ctx.ids_update_sub (C := w.ctx) (a := o.alloc) (o' := o') l.lender hmem'
      with hold | hnew
    · exact hdet l hl_old hold
    · rcases Owner.retagLeaf?_ids_sub hret l.lender hnew with hold | heq
      · exact hdet l hl_old (Ctx.owner_ids_sub_ids hmem l.lender hold)
      · have hEq : l = loan := List.nodup_map_inj hd.2.1 l hl_old loan hloan_mem heq
        exact hl_id (by rw [hEq])
  · -- base
    intro l hl
    change l ∈ (w.ctx.endBorrowNext o o' loan).loans.loans at hl
    simp only [Ctx.endBorrowNext, LoanCtx.endBorrowBookkeeping, List.mem_filter] at hl
    obtain ⟨hl_old, hlid⟩ := hl
    have hl_id' : l.id ≠ loanId := by
      have : l.id ≠ loan.id := by simpa using hlid
      simpa [hloan_id] using this
    rcases hbase l hl_old with h | ⟨m, hm, hmb, hml⟩
    · exact Or.inl h
    · refine Or.inr ⟨m, ?_, hmb, hml⟩
      simp only [Ctx.endBorrowNext, LoanCtx.endBorrowBookkeeping, List.mem_filter]
      refine ⟨hm, ?_⟩
      have hm_id : m.id ≠ loan.id := by
        intro heq
        have hm_eq : m = loan := List.nodup_map_inj hd.1 m hm loan hloan_mem heq
        rw [hm_eq] at hml
        exact hsuc l hl_old (by simpa [hloan_id] using hl_id') (hml.symm)
      simpa using hm_id
  · -- terminal
    exact World.endBorrow_terminal hw ⟨hwf, hh, hlr⟩ hB
  · -- agree
    intro l hl m hm hadj
    change l ∈ (w.ctx.endBorrowNext o o' loan).loans.loans at hl
    change m ∈ (w.ctx.endBorrowNext o o' loan).loans.loans at hm
    simp only [Ctx.endBorrowNext, LoanCtx.endBorrowBookkeeping, List.mem_filter] at hl hm
    exact hagree l hl.1 m hm.1 hadj

/-- A successful spatial split has no outstanding loan for the allocation. -/
theorem World.splitAtChecked_no_loan {w w' : World} {a : AllocId}
    {id id1 id2 : CapId} {k : Nat}
    (hw : w.splitAtChecked a id id1 id2 k = .ok w') :
    ∀ l ∈ w.ctx.loans.loans, l.alloc ≠ a := by
  unfold World.splitAtChecked at hw
  split at hw
  · simp at hw
  · rename_i o hf
    split at hw
    · rename_i halloc
      split at hw
      · exact halloc
      · simp at hw
    · simp at hw

/-- A spatial split preserves the delegation invariant. -/
theorem borrowOK_splitAtChecked {w w' : World} {a : AllocId}
    {id id1 id2 : CapId} {k : Nat}
    (hw : w.splitAtChecked a id id1 id2 k = .ok w') (hwf : w.WellFormed)
    (h : w.BorrowOK) : w'.BorrowOK := by
  unfold World.splitAtChecked at hw
  split at hw
  · simp at hw
  · rename_i o hfind
    split at hw
    · rename_i halloc
      split at hw
      · rename_i hfr
        split at hw
        · rename_i C' hs
          simp only [Except.ok.injEq] at hw
          cases hw
          unfold Ctx.splitAtOwner? at hs
          cases ho : o.splitAt? id id1 id2 k with
          | none => simp [ho] at hs
          | some o' =>
            simp only [ho, Option.map_some, Option.some.injEq] at hs
            subst hs
            obtain ⟨hd, hna, hi, hlife, halloc', hdet, hbase, hterm, hagree, horder, hacyc⟩ := h
            have hmem : o ∈ w.ctx.owners := List.mem_of_find?_eq_some hfind
            have hoids : o.ids.Nodup := Ctx.owner_ids_nodup hwf.1.2.2 hmem
            have hoalloc : o'.alloc = o.alloc := Owner.splitAt?_alloc ho
            have hon : o'.len = o.len := Owner.splitAt?_len ho
            refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
            · simpa [LoansDistinctOK, Ctx.update] using hd
            · simpa [LoansNonAliasOK, Ctx.update] using hna
            · intro l hl
              obtain ⟨h1, h2, h3⟩ := hi l hl
              exact ⟨List.mem_cons_of_mem _ (List.mem_cons_of_mem _ h1),
                List.mem_cons_of_mem _ (List.mem_cons_of_mem _ h2),
                List.mem_cons_of_mem _ (List.mem_cons_of_mem _ h3)⟩
            · simpa [LifetimesBoundedOK, Ctx.update] using hlife
            · intro l hl
              obtain ⟨o2, ho2⟩ := halloc' l hl
              have hne : l.alloc ≠ o.alloc := by
                intro heq
                exact halloc l hl (heq.trans (findOwner_alloc hfind))
              refine ⟨o2, ?_⟩
              change (Ctx.update w.ctx o.alloc o').findOwner? l.alloc = _
              rw [Ctx.findOwner?_update_of_ne w.ctx o.alloc o' hne hoalloc]
              exact ho2
            · intro l hl hmeml
              rcases Ctx.ids_update_sub (C := w.ctx) (a := o.alloc) (o' := o') l.lender hmeml with
                hold | hnew
              · exact hdet l hl hold
              · rcases Owner.splitAt?_ids_sub hoids ho l.lender hnew with hsub | hid1 | hid2
                · exact hdet l hl (Ctx.owner_ids_sub_ids hmem l.lender hsub)
                · exact hfr.2.2.2.1 (hid1 ▸ (hi l hl).1)
                · exact hfr.2.2.2.2.1 (hid2 ▸ (hi l hl).1)
            · simpa [LoansBaseOK, Ctx.update] using hbase
            · intro l hl
              obtain ⟨o2, ho2, hcond⟩ := hterm l hl
              have hne : l.alloc ≠ o.alloc := by
                intro heq
                exact halloc l hl (heq.trans (findOwner_alloc hfind))
              refine ⟨o2, ?_, hcond⟩
              change (Ctx.update w.ctx o.alloc o').findOwner? l.alloc = _
              rw [Ctx.findOwner?_update_of_ne w.ctx o.alloc o' hne hoalloc]
              exact ho2
            · simpa [LoansAgreeOK, Ctx.update] using hagree
            · intro l hl
              have hb := (hi l hl).2.1
              have hlend := (hi l hl).1
              have hb1 : l.borrower ≠ id1 := fun h' => hfr.2.2.2.1 (h' ▸ hb)
              have hb2 : l.borrower ≠ id2 := fun h' => hfr.2.2.2.2.1 (h' ▸ hb)
              have hl1 : l.lender ≠ id1 := fun h' => hfr.2.2.2.1 (h' ▸ hlend)
              have hl2 : l.lender ≠ id2 := fun h' => hfr.2.2.2.2.1 (h' ▸ hlend)
              have hord := horder l hl
              change (id1 :: id2 :: w.ctx.issued).idxOf l.borrower
                < (id1 :: id2 :: w.ctx.issued).idxOf l.lender
              rw [idxOf_cons2_ne (a := id1) (b := id2) (c := l.borrower)
                    (fun h => hb1 h.symm) (fun h => hb2 h.symm),
                  idxOf_cons2_ne (a := id1) (b := id2) (c := l.lender)
                    (fun h => hl1 h.symm) (fun h => hl2 h.symm)]
              omega
            · simpa [BorrowAcyclic, Ctx.update] using hacyc
        · simp at hw
      · simp at hw
    · simp at hw

/-- A fractional split preserves the delegation invariant. -/
theorem borrowOK_splitFractionChecked {w w' : World} {a : AllocId}
    {id id1 id2 : CapId} {q1 q2 : Nat} {p1 : 0 < q1} {p2 : 0 < q2}
    (hw : w.splitFractionChecked a id id1 id2 q1 q2 p1 p2 = .ok w') (hwf : w.WellFormed)
    (h : w.BorrowOK) : w'.BorrowOK := by
  unfold World.splitFractionChecked at hw
  split at hw
  · simp at hw
  · rename_i o hfind
    split at hw
    · rename_i halloc
      split at hw
      · rename_i hfr
        split at hw
        · rename_i C' hs
          simp only [Except.ok.injEq] at hw
          cases hw
          unfold Ctx.splitFractionOwner? at hs
          cases ho : o.splitFraction? id id1 id2 q1 q2 p1 p2 with
          | none => simp [ho] at hs
          | some o' =>
            simp only [ho, Option.map_some, Option.some.injEq] at hs
            subst hs
            obtain ⟨hd, hna, hi, hlife, halloc', hdet, hbase, hterm, hagree, horder, hacyc⟩ := h
            have hmem : o ∈ w.ctx.owners := List.mem_of_find?_eq_some hfind
            have hoids : o.ids.Nodup := Ctx.owner_ids_nodup hwf.1.2.2 hmem
            have hoalloc : o'.alloc = o.alloc := Owner.splitFraction?_alloc ho
            have hon : o'.len = o.len := Owner.splitFraction?_len ho
            refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
            · simpa [LoansDistinctOK, Ctx.update] using hd
            · simpa [LoansNonAliasOK, Ctx.update] using hna
            · intro l hl
              obtain ⟨h1, h2, h3⟩ := hi l hl
              exact ⟨List.mem_cons_of_mem _ (List.mem_cons_of_mem _ h1),
                List.mem_cons_of_mem _ (List.mem_cons_of_mem _ h2),
                List.mem_cons_of_mem _ (List.mem_cons_of_mem _ h3)⟩
            · simpa [LifetimesBoundedOK, Ctx.update] using hlife
            · intro l hl
              obtain ⟨o2, ho2⟩ := halloc' l hl
              have hne : l.alloc ≠ o.alloc := by
                intro heq
                exact halloc l hl (heq.trans (findOwner_alloc hfind))
              refine ⟨o2, ?_⟩
              change (Ctx.update w.ctx o.alloc o').findOwner? l.alloc = _
              rw [Ctx.findOwner?_update_of_ne w.ctx o.alloc o' hne hoalloc]
              exact ho2
            · intro l hl hmeml
              rcases Ctx.ids_update_sub (C := w.ctx) (a := o.alloc) (o' := o') l.lender hmeml with
                hold | hnew
              · exact hdet l hl hold
              · rcases Owner.splitFraction?_ids_sub hoids ho l.lender hnew with hsub | hid1 | hid2
                · exact hdet l hl (Ctx.owner_ids_sub_ids hmem l.lender hsub)
                · exact hfr.2.2.2.1 (hid1 ▸ (hi l hl).1)
                · exact hfr.2.2.2.2.1 (hid2 ▸ (hi l hl).1)
            · simpa [LoansBaseOK, Ctx.update] using hbase
            · intro l hl
              obtain ⟨o2, ho2, hcond⟩ := hterm l hl
              have hne : l.alloc ≠ o.alloc := by
                intro heq
                exact halloc l hl (heq.trans (findOwner_alloc hfind))
              refine ⟨o2, ?_, hcond⟩
              change (Ctx.update w.ctx o.alloc o').findOwner? l.alloc = _
              rw [Ctx.findOwner?_update_of_ne w.ctx o.alloc o' hne hoalloc]
              exact ho2
            · simpa [LoansAgreeOK, Ctx.update] using hagree
            · intro l hl
              have hb := (hi l hl).2.1
              have hlend := (hi l hl).1
              have hb1 : l.borrower ≠ id1 := fun h' => hfr.2.2.2.1 (h' ▸ hb)
              have hb2 : l.borrower ≠ id2 := fun h' => hfr.2.2.2.2.1 (h' ▸ hb)
              have hl1 : l.lender ≠ id1 := fun h' => hfr.2.2.2.1 (h' ▸ hlend)
              have hl2 : l.lender ≠ id2 := fun h' => hfr.2.2.2.2.1 (h' ▸ hlend)
              have hord := horder l hl
              change (id1 :: id2 :: w.ctx.issued).idxOf l.borrower
                < (id1 :: id2 :: w.ctx.issued).idxOf l.lender
              rw [idxOf_cons2_ne (a := id1) (b := id2) (c := l.borrower)
                    (fun h => hb1 h.symm) (fun h => hb2 h.symm),
                  idxOf_cons2_ne (a := id1) (b := id2) (c := l.lender)
                    (fun h => hl1 h.symm) (fun h => hl2 h.symm)]
              omega
            · simpa [BorrowAcyclic, Ctx.update] using hacyc
        · simp at hw
      · simp at hw
    · simp at hw

/-- A successful fractional join has no outstanding loan for the allocation. -/
theorem World.joinChecked_no_loan {w w' : World} {a : AllocId} {node newId : CapId}
    (hw : w.joinChecked a node newId = .ok w') :
    ∀ l ∈ w.ctx.loans.loans, l.alloc ≠ a := by
  unfold World.joinChecked at hw
  split at hw
  · simp at hw
  · rename_i o hf
    split at hw
    · rename_i halloc
      split at hw
      · exact halloc
      · simp at hw
    · simp at hw

/-- A fractional join preserves the delegation invariant. -/
theorem borrowOK_joinChecked {w w' : World} {a : AllocId} {node newId : CapId}
    (hw : w.joinChecked a node newId = .ok w') (hwf : w.WellFormed)
    (h : w.BorrowOK) : w'.BorrowOK := by
  unfold World.joinChecked at hw
  split at hw
  · simp at hw
  · rename_i o hfind
    split at hw
    · rename_i halloc
      split at hw
      · rename_i hfresh
        split at hw
        · rename_i C' hs
          simp only [Except.ok.injEq] at hw
          cases hw
          unfold Ctx.joinFractionOwner? at hs
          cases ho : o.joinFraction? node newId with
          | none => simp [ho] at hs
          | some o' =>
            simp only [ho, Option.map_some, Option.some.injEq] at hs
            subst hs
            obtain ⟨hd, hna, hi, hlife, halloc', hdet, hbase, hterm, hagree, horder, hacyc⟩ := h
            have hmem : o ∈ w.ctx.owners := List.mem_of_find?_eq_some hfind
            have hoids : o.ids.Nodup := Ctx.owner_ids_nodup hwf.1.2.2 hmem
            have hoalloc : o'.alloc = o.alloc := Owner.joinFraction_alloc ho
            have hon : o'.len = o.len := Owner.joinFraction?_len ho
            refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
            · simpa [LoansDistinctOK, Ctx.update] using hd
            · simpa [LoansNonAliasOK, Ctx.update] using hna
            · intro l hl
              obtain ⟨h1, h2, h3⟩ := hi l hl
              exact ⟨List.mem_cons_of_mem _ h1, List.mem_cons_of_mem _ h2,
                List.mem_cons_of_mem _ h3⟩
            · simpa [LifetimesBoundedOK, Ctx.update] using hlife
            · intro l hl
              obtain ⟨o2, ho2⟩ := halloc' l hl
              have hne : l.alloc ≠ o.alloc := by
                intro heq
                exact halloc l hl (heq.trans (findOwner_alloc hfind))
              refine ⟨o2, ?_⟩
              change (Ctx.update w.ctx o.alloc o').findOwner? l.alloc = _
              rw [Ctx.findOwner?_update_of_ne w.ctx o.alloc o' hne hoalloc]
              exact ho2
            · intro l hl hmeml
              rcases Ctx.ids_update_sub (C := w.ctx) (a := o.alloc) (o' := o') l.lender hmeml with
                hold | hnew
              · exact hdet l hl hold
              · rcases Owner.joinFraction?_ids_sub' ho l.lender hnew with hsub | hid
                · exact hdet l hl (Ctx.owner_ids_sub_ids hmem l.lender hsub)
                · exact hfresh.2 (hid ▸ (hi l hl).1)
            · simpa [LoansBaseOK, Ctx.update] using hbase
            · intro l hl
              obtain ⟨o2, ho2, hcond⟩ := hterm l hl
              have hne : l.alloc ≠ o.alloc := by
                intro heq
                exact halloc l hl (heq.trans (findOwner_alloc hfind))
              refine ⟨o2, ?_, hcond⟩
              change (Ctx.update w.ctx o.alloc o').findOwner? l.alloc = _
              rw [Ctx.findOwner?_update_of_ne w.ctx o.alloc o' hne hoalloc]
              exact ho2
            · simpa [LoansAgreeOK, Ctx.update] using hagree
            · intro l hl
              have hb := (hi l hl).2.1
              have hlend := (hi l hl).1
              have hb1 : l.borrower ≠ newId := fun h' => hfresh.2 (h' ▸ hb)
              have hl1 : l.lender ≠ newId := fun h' => hfresh.2 (h' ▸ hlend)
              have hord := horder l hl
              change (newId :: w.ctx.issued).idxOf l.borrower
                < (newId :: w.ctx.issued).idxOf l.lender
              rw [idxOf_cons_ne (a := newId) (b := l.borrower) (fun h => hb1 h.symm),
                  idxOf_cons_ne (a := newId) (b := l.lender) (fun h => hl1 h.symm)]
              omega
            · simpa [BorrowAcyclic, Ctx.update] using hacyc
        · simp at hw
      · simp at hw
    · simp at hw

/-- Disposal preserves the delegation invariant: it is refused while any loan
names the allocation, and every other loan's witness survives the owner filter. -/
theorem borrowOK_freeChecked {w w' : World} {a : AllocId} {d : CapId}
    (hw : w.freeChecked a d = .ok w') (h : w.BorrowOK) : w'.BorrowOK := by
  unfold World.freeChecked at hw
  split at hw
  · simp at hw
  · rename_i o hfind
    split at hw
    · rename_i halloc
      split at hw
      · rename_i hloan
        cases hf : w.freeWith? a d with
        | none => simp [hf] at hw
        | some w1 =>
          simp [hf] at hw
          cases hw
          unfold World.freeWith? at hf
          cases hc : w.ctx.freeWith? a d with
          | none => simp [hc] at hf
          | some ctx' =>
            simp [hc] at hf
            cases hf
            have heq : ctx' = w.ctx.free a := Ctx.freeWith?_eq_free hc
            subst heq
            obtain ⟨hd, hna, hi, hlife, halloc', hdet, hbase, hterm, hagree, horder, hacyc⟩ := h
            refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
            · simpa [LoansDistinctOK, Ctx.free] using hd
            · simpa [LoansNonAliasOK, Ctx.free] using hna
            · simpa [LoansIssuedOK, Ctx.free] using hi
            · simpa [LifetimesBoundedOK, Ctx.free] using hlife
            · intro l hl
              obtain ⟨o2, ho2⟩ := halloc' l hl
              have hne : l.alloc ≠ a := halloc l hl
              refine ⟨o2, ?_⟩
              rw [Ctx.findOwner?_free_of_ne (C := w.ctx) (a := a) (b := l.alloc) hne]
              exact ho2
            · intro l hl hmem
              exact hdet l hl (Ctx.ids_free_sub l.lender hmem)
            · simpa [LoansBaseOK, Ctx.free] using hbase
            · intro l hl
              obtain ⟨o2, ho2, hcond⟩ := hterm l hl
              have hne : l.alloc ≠ a := halloc l hl
              refine ⟨o2, ?_, hcond⟩
              rw [Ctx.findOwner?_free_of_ne (C := w.ctx) (a := a) (b := l.alloc) hne]
              exact ho2
            · simpa [LoansAgreeOK, Ctx.free] using hagree
            · simpa [LoansOrderOK, Ctx.free] using horder
            · simpa [BorrowAcyclic, Ctx.free] using hacyc
      · simp at hw
    · simp at hw

/-- A write leaves the delegation bookkeeping unchanged. -/
theorem borrowOK_write {w w' : World} {a : AllocId} {id : CapId} {i : Nat}
    {v : UInt8} (hw : w.writeChecked a id i v = .ok w') (h : w.BorrowOK) :
    w'.BorrowOK := by
  obtain ⟨_, _, _, _, _, _, _, hctx, _⟩ := World.writeChecked_sound hw
  simpa [BorrowOK, LoansDistinctOK, LoansNonAliasOK, LoansIssuedOK, LifetimesBoundedOK,
    LoansAllocOK, LoansDetachedOK, LoansBaseOK, LoansTerminalOK, LoansAgreeOK,
    LoansOrderOK, World.BorrowAcyclic, hctx] using h

/-- The concrete 64-byte world has no loans. -/
theorem uWorld_borrowOK : World.BorrowOK uWorld := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [World.LoansDistinctOK, uWorld, LoanCtx.rootOnly]
  · intro l hl; simp [uWorld, LoanCtx.rootOnly] at hl
  · intro l hl; simp [uWorld, LoanCtx.rootOnly] at hl
  · simp [World.LifetimesBoundedOK, uWorld, LoanCtx.rootOnly]
  · intro l hl; simp [uWorld, LoanCtx.rootOnly] at hl
  · intro l hl; simp [uWorld, LoanCtx.rootOnly] at hl
  · intro l hl; simp [uWorld, LoanCtx.rootOnly] at hl
  · intro l hl; simp [uWorld, LoanCtx.rootOnly] at hl
  · intro l hl; simp [uWorld, LoanCtx.rootOnly] at hl
  · intro l hl; simp [uWorld, LoanCtx.rootOnly] at hl
  · intro l hl; simp [uWorld, LoanCtx.rootOnly] at hl

end World

end Cap
