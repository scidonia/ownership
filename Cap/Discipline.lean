/-
A checked world coupled to a nested delegation chain.

The correspondence requires the world's loan list to be exactly the chain's
projected loans, the chain holder to be the active leaf, and the chain's
allocation, footprint, share and ceiling to agree with that leaf. Writes through
the holder preserve the correspondence because they change only the backend.
-/
import Cap.FullInv
import Cap.Delegation
import Cap.Unified

namespace Cap

namespace World

/-- Within each `(alloc, base)` group the world loan list is in chain order: the
filtered subsequence's consecutive loans satisfy the delegation adjacency, and
its first loan is lent by the group's base. `BorrowOK` does not determine loan
list order, so the correspondence theorem carries this as a separate hypothesis. -/
def LoansChainOrderOK (w : World) : Prop :=
  (∀ (a : AllocId) (b : CapId) (i : Nat) (l₁ l₂ : Loan),
      (w.ctx.loans.loans.filter (fun l => l.alloc = a ∧ l.base = b))[i]? = some l₁ →
      (w.ctx.loans.loans.filter (fun l => l.alloc = a ∧ l.base = b))[i+1]? = some l₂ →
        l₂.lender = l₁.borrower)
  ∧ (∀ (a : AllocId) (b : CapId) (l : Loan),
      (w.ctx.loans.loans.filter (fun l => l.alloc = a ∧ l.base = b)).head? = some l →
        l.lender = b)

/-- The distinct `(alloc, base)` groups in order of first occurrence. -/
private def distinctPairsAux : List Loan → List (AllocId × CapId) →
    List (AllocId × CapId)
  | [], acc => acc
  | l :: ls, acc =>
      distinctPairsAux ls
        (if (l.alloc, l.base) ∈ acc then acc else acc ++ [(l.alloc, l.base)])

private def loanPairs (w : World) : List (AllocId × CapId) :=
  distinctPairsAux w.ctx.loans.loans []

private theorem distinctPairsAux_mem {ls : List Loan}
    {acc : List (AllocId × CapId)} {p : AllocId × CapId} :
    p ∈ distinctPairsAux ls acc ↔ p ∈ acc ∨ ∃ l ∈ ls, (l.alloc, l.base) = p := by
  induction ls generalizing acc with
  | nil => simp [distinctPairsAux]
  | cons l ls ih =>
      simp only [distinctPairsAux]
      have hacc : p ∈ (if (l.alloc, l.base) ∈ acc then acc
          else acc ++ [(l.alloc, l.base)]) ↔ p ∈ acc ∨ (l.alloc, l.base) = p := by
        by_cases h : (l.alloc, l.base) ∈ acc
        · rw [if_pos h]
          constructor
          · intro hp; exact Or.inl hp
          · rintro (hp | heq)
            · exact hp
            · exact heq ▸ h
        · rw [if_neg h]
          constructor
          · intro hp
            rcases List.mem_append.mp hp with hp | hp
            · exact Or.inl hp
            · right
              simpa [eq_comm] using hp
          · rintro (hp | heq)
            · exact List.mem_append.mpr (Or.inl hp)
            · exact List.mem_append.mpr (Or.inr (by simpa [eq_comm] using heq))
      rw [ih, hacc]
      constructor
      · rintro ((h | h) | ⟨x, hx, hp⟩)
        · exact Or.inl h
        · exact Or.inr ⟨l, by simp, h⟩
        · exact Or.inr ⟨x, List.mem_cons_of_mem _ hx, hp⟩
      · rintro (h | ⟨x, hx, hp⟩)
        · exact Or.inl (Or.inl h)
        · rcases List.mem_cons.mp hx with rfl | hx'
          · exact Or.inl (Or.inr hp)
          · exact Or.inr ⟨x, hx', hp⟩

private theorem distinctPairsAux_nodup (ls : List Loan)
    (acc : List (AllocId × CapId)) (h : acc.Nodup) :
    (distinctPairsAux ls acc).Nodup := by
  induction ls generalizing acc with
  | nil => simpa [distinctPairsAux] using h
  | cons l ls ih =>
      simp only [distinctPairsAux]
      apply ih
      by_cases hmem : (l.alloc, l.base) ∈ acc
      · simpa [hmem] using h
      · rw [if_neg hmem, List.nodup_append]
        refine ⟨h, by simp, ?_⟩
        intro x hx y hy
        simp only [List.mem_singleton] at hy
        subst hy
        exact fun hxy => hmem (hxy ▸ hx)

/-- The chains of a world, one per distinct `(alloc, base)` group. -/
def delegationChains (w : World) : List Delegation.Chain :=
  (loanPairs w).map (fun p =>
    Delegation.Chain.ofPath
      (w.ctx.loans.loans.filter (fun l => l.alloc = p.1 ∧ l.base = p.2))
      p.1 p.2)

private theorem find?_eq_some_of_unique {α : Type} {p : α → Bool} :
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
        exact find?_eq_some_of_unique hmxs hp
          (fun y hy hyp => huniq y (by simp [hy]) hyp)

/-- Every element of a list belongs to the filter of its own key. -/
private theorem mem_filter_self (l : List Loan) (x : Loan) (h : x ∈ l) :
    x ∈ l.filter (fun y => y.alloc = x.alloc ∧ y.base = x.base) :=
  List.mem_filter.mpr ⟨h, by simp⟩

/-- A loan at a successor index has a predecessor at the preceding index. -/
private theorem exists_prev : ∀ {l : List Loan} {k : Nat} {m : Loan},
    l[k+1]? = some m → ∃ m', l[k]? = some m'
  | [], k, m, h => by simp at h
  | x :: xs, 0, m, h => ⟨x, rfl⟩
  | x :: xs, k+1, m, h => by
      simp only [List.getElem?_cons_succ] at h
      obtain ⟨m', hm'⟩ := exists_prev (l := xs) (k := k) (m := m) h
      exact ⟨m', by simpa using hm'⟩

/-- A later group loan has the same resource description as the first one. -/
private theorem resource_eq_index {loans : List Loan}
    (hadj : ∀ i l₁ l₂, loans[i]? = some l₁ → loans[i+1]? = some l₂ →
      l₂.lender = l₁.borrower)
    (hagree : ∀ l₁ ∈ loans, ∀ l₂ ∈ loans,
      (l₂.lender = l₁.borrower ∨ l₂.borrower = l₁.lender) →
      l₂.alloc = l₁.alloc ∧ l₂.lo = l₁.lo ∧ l₂.hi = l₁.hi ∧
        l₂.q = l₁.q ∧ l₂.ceiling = l₁.ceiling)
    {l0 : Loan} (h0 : loans[0]? = some l0) :
    ∀ (i : Nat) (m : Loan), loans[i]? = some m →
      m.alloc = l0.alloc ∧ m.lo = l0.lo ∧ m.hi = l0.hi ∧ m.q = l0.q ∧
        m.ceiling = l0.ceiling := by
  intro i
  induction i with
  | zero =>
      intro m hm
      rw [h0] at hm
      simp only [Option.some.injEq] at hm
      subst hm
      exact ⟨rfl, rfl, rfl, rfl, rfl⟩
  | succ k ih =>
      intro m hm
      obtain ⟨m', hm'⟩ := exists_prev hm
      have hadjk := hadj k m' m hm' hm
      have hres := hagree m' (List.mem_iff_getElem?.mpr ⟨k, hm'⟩)
        m (List.mem_iff_getElem?.mpr ⟨k+1, hm⟩) (Or.inl hadjk)
      have ihres := ih m' hm'
      exact ⟨by rw [hres.1, ihres.1], by rw [hres.2.1, ihres.2.1],
        by rw [hres.2.2.1, ihres.2.2.1], by rw [hres.2.2.2.1, ihres.2.2.2.1],
        by rw [hres.2.2.2.2, ihres.2.2.2.2]⟩

/-- The group's assembled chain lists exactly that group. -/
private theorem filter_toLoans {w : World} (h : w.BorrowOK)
    (hord : w.LoansChainOrderOK) (a : AllocId) (b : CapId) :
    (Delegation.Chain.ofPath
      (w.ctx.loans.loans.filter (fun l => decide (l.alloc = a ∧ l.base = b))) a b).toLoans =
      w.ctx.loans.loans.filter (fun l => decide (l.alloc = a ∧ l.base = b)) := by
  obtain ⟨hd, hna, _, _, _, _, _, _, _, _, _⟩ := h
  exact Delegation.Chain.toLoans_ofPath
    (fun l hl => of_decide_eq_true (List.mem_filter.mp hl).2)
    (List.Nodup.sublist
      (List.Sublist.map (fun l : Loan => l.id)
        (List.filter_sublist (p := fun l : Loan => decide (l.alloc = a ∧ l.base = b)))) hd.1)
    (List.Nodup.sublist
      (List.Sublist.map (fun l : Loan => l.lender)
        (List.filter_sublist (p := fun l : Loan => decide (l.alloc = a ∧ l.base = b)))) hd.2.1)
    (List.Nodup.sublist
      (List.Sublist.map (fun l : Loan => l.borrower)
        (List.filter_sublist (p := fun l : Loan => decide (l.alloc = a ∧ l.base = b)))) hd.2.2.1)
    (fun l hl => hna l (List.mem_filter.mp hl).1)
    (hord.1 a b) (hord.2 a b)

/-- Walking a group in chain order strictly decreases the issued-order index. -/
private theorem idx_borrower_lt_base {g : List Loan} {b : CapId} {issued : List CapId}
    (hord : ∀ l ∈ g, issued.idxOf l.borrower < issued.idxOf l.lender)
    (hadj : ∀ i l₁ l₂, g[i]? = some l₁ → g[i+1]? = some l₂ → l₂.lender = l₁.borrower)
    (hhead : ∀ l, g.head? = some l → l.lender = b) :
    ∀ (k : Nat) (x : Loan), g[k]? = some x →
      issued.idxOf x.borrower < issued.idxOf b := by
  intro k
  induction k with
  | zero =>
      intro x hx
      have hx' : g.head? = some x := by
        rw [List.head?_eq_getElem?]
        exact hx
      rw [← hhead x hx']
      exact hord x (List.mem_iff_getElem?.mpr ⟨0, hx⟩)
  | succ k ih =>
      intro x hx
      obtain ⟨x0, hx0⟩ := exists_prev hx
      have h1 := hord x (List.mem_iff_getElem?.mpr ⟨k+1, hx⟩)
      rw [hadj k x0 x hx0 hx] at h1
      exact Nat.lt_trans h1 (ih x0 hx0)

/-- A group's base is not one of its borrowers. An occurrence would make the
issued-order constraint descend along the chain and then close on itself, which
the acyclicity of the issue order forbids. -/
private theorem base_not_mem_borrowers {g : List Loan} {b : CapId} {issued : List CapId}
    (hord : ∀ l ∈ g, issued.idxOf l.borrower < issued.idxOf l.lender)
    (hadj : ∀ i l₁ l₂, g[i]? = some l₁ → g[i+1]? = some l₂ → l₂.lender = l₁.borrower)
    (hhead : ∀ l, g.head? = some l → l.lender = b) :
    b ∉ g.map (·.borrower) := by
  intro hmem
  obtain ⟨m, hm, hmb⟩ := List.mem_map.mp hmem
  obtain ⟨i, hi⟩ := List.mem_iff_getElem?.mp hm
  have hidx := idx_borrower_lt_base hord hadj hhead i m hi
  rw [hmb] at hidx
  exact absurd hidx (Nat.lt_irrefl _)

/-- The group's assembled chain is a valid chain. -/
private theorem filter_chain_OK {w : World} {a : AllocId} {b : CapId} {g : List Loan}
    (h : w.BorrowOK) (hord : w.LoansChainOrderOK)
    (hg : g = w.ctx.loans.loans.filter (fun l => decide (l.alloc = a ∧ l.base = b)))
    (hne : g ≠ []) : (Delegation.Chain.ofPath g a b).OK := by
  obtain ⟨hd, hna, _, _, _, _, _, _, hagree, horder, _⟩ := h
  have hgmem : ∀ l ∈ g, l ∈ w.ctx.loans.loans := by
    intro l hl
    rw [hg] at hl
    exact (List.mem_filter.mp hl).1
  have hloc : ∀ l ∈ g, l.alloc = a := by
    intro l hl
    rw [hg] at hl
    exact (of_decide_eq_true (List.mem_filter.mp hl).2).1
  have hbaseg : ∀ l ∈ g, l.base = b := by
    intro l hl
    rw [hg] at hl
    exact (of_decide_eq_true (List.mem_filter.mp hl).2).2
  have hids : (g.map (fun l : Loan => l.id)).Nodup := by
    rw [hg]
    exact List.Nodup.sublist
      (List.Sublist.map (fun l : Loan => l.id)
        (List.filter_sublist (p := fun l : Loan => decide (l.alloc = a ∧ l.base = b)))) hd.1
  have hlend : (g.map (fun l : Loan => l.lender)).Nodup := by
    rw [hg]
    exact List.Nodup.sublist
      (List.Sublist.map (fun l : Loan => l.lender)
        (List.filter_sublist (p := fun l : Loan => decide (l.alloc = a ∧ l.base = b)))) hd.2.1
  have hborr : (g.map (fun l : Loan => l.borrower)).Nodup := by
    rw [hg]
    exact List.Nodup.sublist
      (List.Sublist.map (fun l : Loan => l.borrower)
        (List.filter_sublist (p := fun l : Loan => decide (l.alloc = a ∧ l.base = b)))) hd.2.2.1
  have hnaG : ∀ l ∈ g, l.lender ≠ l.borrower := fun l hl => hna l (hgmem l hl)
  have hadj : ∀ i l₁ l₂, g[i]? = some l₁ → g[i+1]? = some l₂ →
      l₂.lender = l₁.borrower := by
    intro i l₁ l₂ h1 h2
    rw [hg] at h1 h2
    exact hord.1 a b i l₁ l₂ h1 h2
  have hhead : ∀ l, g.head? = some l → l.lender = b := by
    intro l hl
    rw [hg] at hl
    exact hord.2 a b l hl
  have hordG : ∀ l ∈ g,
      w.ctx.issued.idxOf l.borrower < w.ctx.issued.idxOf l.lender :=
    fun l hl => horder l (hgmem l hl)
  have hedges := Delegation.Chain.ofPath_edges (loans := g) (alloc := a) (base := b)
    (fun l hl => ⟨hloc l hl, hbaseg l hl⟩) hids hlend hborr hnaG hadj hhead
  cases g with
  | nil => exact absurd rfl hne
  | cons l0 rest =>
    have hresEq : ∀ (i : Nat) (m : Loan), (l0 :: rest)[i]? = some m →
        m.alloc = l0.alloc ∧ m.lo = l0.lo ∧ m.hi = l0.hi ∧ m.q = l0.q ∧
          m.ceiling = l0.ceiling :=
      resource_eq_index (loans := l0 :: rest) hadj
        (fun x hx y hy hc => (hagree x (hgmem x hx) y (hgmem y hy) hc).2) rfl
    have hbase : (Delegation.Chain.ofPath (l0 :: rest) a b).base = b := rfl
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · -- the capability path is simple
      have hpathEq : (Delegation.Chain.ofPath (l0 :: rest) a b).path =
          b :: (l0 :: rest).map (·.borrower) := by
        simp [Delegation.Chain.path, hedges, hbase, Delegation.Chain.edgeOf,
          List.map_map, Function.comp_def]
      rw [hpathEq]
      exact List.nodup_cons.mpr
        ⟨base_not_mem_borrowers hordG hadj hhead, hborr⟩
    · -- the first edge is lent by the base
      have hfirstG : l0.lender = b := hhead l0 rfl
      simp [Delegation.Chain.firstLenderOK, hedges, hbase, Delegation.Chain.edgeOf,
        hfirstG]
    · -- the stored holder is the derived holder
      have hder : (Delegation.Chain.ofPath (l0 :: rest) a b).derivedHolder =
          (match (l0 :: rest).getLast? with
            | none => b
            | some l => l.borrower) := by
        unfold Delegation.Chain.derivedHolder
        rw [hedges, List.getLast?_map]
        cases hl : (l0 :: rest).getLast? with
        | none => rfl
        | some l => simp [Delegation.Chain.edgeOf]
      rw [hder]
      cases hl : (l0 :: rest).getLast? with
      | none => simp [Delegation.Chain.ofPath, hl]
      | some l => simp [Delegation.Chain.ofPath, hl]
    · -- loan identities distinct
      rw [hedges]
      simpa [Delegation.Chain.edgeOf, List.map_map, Function.comp_def] using hids
    · -- lenders distinct
      rw [hedges]
      simpa [Delegation.Chain.edgeOf, List.map_map, Function.comp_def] using hlend
    · -- borrowers distinct
      rw [hedges]
      simpa [Delegation.Chain.edgeOf, List.map_map, Function.comp_def] using hborr
    · -- resource agreement
      intro e he
      rw [hedges] at he
      rcases List.mem_map.mp he with ⟨m, hm, rfl⟩
      obtain ⟨i, hi⟩ := List.mem_iff_getElem?.mp hm
      obtain ⟨hallocM, hloM, hhiM, hqM, hceilM⟩ := hresEq i m hi
      have hloc0 : l0.alloc = a := hloc l0 (by simp)
      simp [Delegation.Chain.edgeOf, Delegation.Chain.ofPath, hallocM, hloM, hhiM,
        hqM, hceilM, hloc0]
    · -- no self edge
      intro e he
      rw [hedges] at he
      rcases List.mem_map.mp he with ⟨m, hm, rfl⟩
      simpa [Delegation.Chain.edgeOf] using hnaG m hm
    · -- adjacency
      intro i e1 e2 h1 h2
      rw [hedges] at h1 h2
      rw [List.getElem?_map] at h1 h2
      cases hg1 : (l0 :: rest)[i]? with
      | none => simp [hg1] at h1
      | some l1 =>
        cases hg2 : (l0 :: rest)[i+1]? with
        | none => simp [hg2] at h2
        | some l2 =>
          rw [hg1] at h1
          rw [hg2] at h2
          simp only [Option.map, Option.some.injEq] at h1 h2
          rw [← h1, ← h2]
          simpa [Delegation.Chain.edgeOf] using hadj i l1 l2 hg1 hg2
    · -- each lender is the base or a previous borrower
      intro e he
      rw [hedges] at he
      rcases List.mem_map.mp he with ⟨m, hm, rfl⟩
      have hhead0 : l0.lender = b := hhead l0 rfl
      obtain ⟨i, hi⟩ := List.mem_iff_getElem?.mp hm
      cases i with
      | zero =>
        left
        have hm0 : m = l0 := by
          simpa [eq_comm] using hi
        subst hm0
        simpa [Delegation.Chain.edgeOf, Delegation.Chain.ofPath] using hhead0
      | succ k =>
        right
        obtain ⟨m', hm'⟩ := exists_prev (l := l0 :: rest) hi
        refine ⟨Delegation.Chain.edgeOf b m', ?_, ?_⟩
        · rw [hedges]
          exact List.mem_map.mpr ⟨m', List.mem_iff_getElem?.mpr ⟨k, hm'⟩, rfl⟩
        · have hadjk := hadj k m' m hm' hi
          simpa [Delegation.Chain.edgeOf] using hadjk.symm
    · -- the holder is the last borrower
      rw [hedges, List.getLast?_map]
      have hne' : l0 :: rest ≠ [] := by simp
      simp [Delegation.Chain.ofPath, Delegation.Chain.edgeOf,
        List.getLast?_eq_some_getLast hne']

/-- Grouping a list by the distinct keys of a key list is a permutation of the
list. -/
private theorem flatten_filter_pairs_perm {α β : Type} [DecidableEq β] (l : List α)
    (pairs : List β) (key : α → β)
    (hcover : ∀ a ∈ l, key a ∈ pairs) (hnd : pairs.Nodup) :
    (pairs.map (fun p => l.filter (fun a => decide (key a = p)))).flatten.Perm l := by
  induction pairs generalizing l with
  | nil =>
      have hl : l = [] := by
        cases l with
        | nil => rfl
        | cons a as => exact absurd (hcover a (by simp)) (by simp)
      subst hl
      simp
  | cons p ps ih =>
      have hpnd : ps.Nodup := (List.nodup_cons.mp hnd).2
      have hpnot : p ∉ ps := (List.nodup_cons.mp hnd).1
      let l1 := l.filter (fun a => decide (key a = p))
      let l2 := l.filter (fun a => !decide (key a = p))
      have hcover2 : ∀ a ∈ l2, key a ∈ ps := by
        intro a ha
        have ha' : a ∈ l := (List.mem_filter.mp ha).1
        have hneq : ¬ key a = p := by
          have := (List.mem_filter.mp ha).2
          simpa using this
        rcases List.mem_cons.mp (hcover a ha') with h | h
        · exact absurd h hneq
        · exact h
      have ih2 := ih l2 hcover2 hpnd
      have hfilters : (ps.map (fun q => l2.filter (fun a => decide (key a = q)))) =
          (ps.map (fun q => l.filter (fun a => decide (key a = q)))) := by
        apply List.map_congr_left
        intro q hq
        have hqp : q ≠ p := fun h => hpnot (h ▸ hq)
        simp only [l2]
        rw [List.filter_filter]
        apply List.filter_congr
        intro a ha
        by_cases hq' : key a = q
        · have hnp : ¬ key a = p := fun hp' => hqp (hq'.symm.trans hp')
          simp [hq', hnp, hqp, decide_eq_true_eq]
        · simp [hq', decide_eq_true_eq]
      have hsplit : List.Perm (l1 ++ l2) l := by
        simpa [l1, l2] using List.filter_append_perm (fun a => decide (key a = p)) l
      have hgoal : List.Perm (l.filter (fun a => decide (key a = p)) ++
          (ps.map (fun q => l2.filter (fun a => decide (key a = q)))).flatten) l :=
        (List.Perm.append (List.Perm.refl _) ih2).trans hsplit
      simpa [List.map_cons, List.flatten_cons, hfilters, l1] using hgoal

/-- Every `BorrowOK` world corresponds to its delegation chains: each chain is
valid, every world loan is represented, each chain is exactly its `(alloc, base)`
subsequence, and the flattened projection is a permutation of the loan list. -/
theorem delegationChains_ok {w : World} (h : w.BorrowOK)
    (hord : w.LoansChainOrderOK) :
    (∀ c ∈ w.delegationChains, c.OK)
    ∧ (∀ l ∈ w.ctx.loans.loans, ∃ c ∈ w.delegationChains,
        c.toLoans.find? (fun x => x.id = l.id) = some l)
    ∧ (∀ c ∈ w.delegationChains, c.toLoans =
        w.ctx.loans.loans.filter (fun l => l.alloc = c.alloc ∧ l.base = c.base))
    ∧ (w.delegationChains.map Delegation.Chain.toLoans).flatten.Perm
        w.ctx.loans.loans := by
  have hB : w.BorrowOK := h
  obtain ⟨hd, _, _, _, _, _, _, _, _, _, _⟩ := h
  have hpairs : ∀ p ∈ loanPairs w, ∃ l ∈ w.ctx.loans.loans,
      (l.alloc, l.base) = p := by
    intro p hp
    have := (distinctPairsAux_mem.mp hp)
    rcases this with h | ⟨l, hl, hp'⟩
    · simp at h
    · exact ⟨l, hl, hp'⟩
  have hgroup_ne : ∀ p ∈ loanPairs w,
      w.ctx.loans.loans.filter (fun l => decide (l.alloc = p.1 ∧ l.base = p.2)) ≠ [] := by
    intro p hp
    obtain ⟨l, hl, hlp⟩ := hpairs p hp
    intro hnil
    have hpair : l.alloc = p.1 ∧ l.base = p.2 := by
      cases p with
      | mk a b => simpa using hlp
    have hmem : l ∈ w.ctx.loans.loans.filter
        (fun x => decide (x.alloc = p.1 ∧ x.base = p.2)) :=
      List.mem_filter.mpr ⟨hl, by simpa using hpair⟩
    rw [hnil] at hmem
    simp at hmem
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro c hc
    rcases List.mem_map.mp hc with ⟨p, hp, rfl⟩
    exact filter_chain_OK hB hord rfl (hgroup_ne p hp)
  · intro l hl
    let p : AllocId × CapId := (l.alloc, l.base)
    have hp : p ∈ loanPairs w := by
      rw [loanPairs, distinctPairsAux_mem]
      exact Or.inr ⟨l, hl, rfl⟩
    refine ⟨Delegation.Chain.ofPath
      (w.ctx.loans.loans.filter (fun x => decide (x.alloc = p.1 ∧ x.base = p.2))) p.1 p.2,
      List.mem_map.mpr ⟨p, hp, rfl⟩, ?_⟩
    have hgl : l ∈ w.ctx.loans.loans.filter
        (fun x => decide (x.alloc = p.1 ∧ x.base = p.2)) := by
      refine List.mem_filter.mpr ⟨hl, ?_⟩
      simp [p]
    rw [filter_toLoans hB hord p.1 p.2]
    exact find?_eq_some_of_unique hgl (by simp) (fun y hy hyp =>
      List.nodup_map_inj hd.1 y (List.mem_filter.mp hy).1 l
        (List.mem_filter.mp hgl).1 (of_decide_eq_true hyp))
  · intro c hc
    rcases List.mem_map.mp hc with ⟨p, hp, rfl⟩
    exact filter_toLoans hB hord p.1 p.2
  · -- the flattened grouping is a permutation of the loan list
    have hmap : (loanPairs w).map (fun p =>
        (Delegation.Chain.ofPath
          (w.ctx.loans.loans.filter (fun l => decide (l.alloc = p.1 ∧ l.base = p.2)))
          p.1 p.2).toLoans) =
        (loanPairs w).map (fun p =>
          w.ctx.loans.loans.filter (fun l => decide (l.alloc = p.1 ∧ l.base = p.2))) := by
      apply List.map_congr_left
      intro p hp
      exact filter_toLoans hB hord p.1 p.2
    unfold delegationChains
    rw [List.map_map]
    simp only [Function.comp_def]
    rw [hmap]
    exact flatten_filter_pairs_perm w.ctx.loans.loans (loanPairs w)
      (fun l => (l.alloc, l.base))
      (fun a ha => by
        rw [loanPairs, distinctPairsAux_mem]
        exact Or.inr ⟨a, ha, rfl⟩)
      (distinctPairsAux_nodup w.ctx.loans.loans [] (by simp))

end World

namespace Discipline

/-- A world coupled to a delegation chain. -/
structure State where
  world : World
  chain : Delegation.Chain

/-- The correspondence invariant. -/
def State.OK (s : State) : Prop :=
  s.world.FullInv
  ∧ s.chain.OK
  ∧ s.chain.toLoans = s.world.ctx.loans.loans
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
  refine ⟨⟨uWorld_top, World.uWorld_borrowOK⟩, ?_, rfl, ?_⟩
  · unfold Delegation.Chain.OK
    refine ⟨by simp [Delegation.Chain.path, initialState],
      by simp [Delegation.Chain.firstLenderOK, initialState],
      by simp [Delegation.Chain.derivedHolder, initialState],
      by simp [initialState], by simp [initialState], by simp [initialState],
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
  obtain ⟨hfull, hchain, hloans, hcorr⟩ := hok
  obtain ⟨o, c, hfind, hleaf, hactive, halloc, hlo, hhi, hq, hceil⟩ := hcorr
  unfold State.write at h
  cases hw : s.world.writeChecked s.chain.alloc s.chain.holder 0 v with
  | error e => simp [hw] at h
  | ok w' =>
    simp [hw] at h
    cases h
    obtain ⟨_, _, _, _, _, _, _, hctx, _⟩ := World.writeChecked_sound hw
    refine ⟨⟨⟨World.writeChecked_wf hw hfull.1.1,
      World.historyOK_write hw hfull.1.2⟩, World.borrowOK_write hw hfull.2⟩,
      hchain, ?_, ?_⟩
    · rw [hctx]
      exact hloans
    · refine ⟨o, c, ?_, hleaf, hactive, halloc, hlo, hhi, hq, hceil⟩
      rw [hctx]
      exact hfind

/-- Begin a borrow through the chain holder. The resulting world loan is
appended to the chain through the checked route, which refuses anything the
admissibility predicate does not admit. -/
def State.beginBorrow (s : State) (borrower : CapId) (loanId : LoanId) :
    Option State :=
  match s.world.beginBorrowChecked s.chain.alloc s.chain.holder borrower loanId with
  | .error _ => none
  | .ok w' =>
      match w'.ctx.loans.loans.getLast? with
      | none => none
      | some loan =>
          match s.chain.begin? w'.ctx.loans
              (Delegation.Chain.edgeOf s.chain.base loan) with
          | none => none
          | some c' => some { world := w', chain := c' }

/-- End a borrow through the chain holder, removing the innermost chain edge
through the checked route. -/
def State.endBorrow (s : State) (loanId : LoanId) : Option State :=
  match s.world.endBorrowChecked s.chain.alloc loanId with
  | .error _ => none
  | .ok w' =>
      match s.chain.end? with
      | none => none
      | some c' => some { world := w', chain := c' }

/-- Beginning a borrow through the holder preserves the correspondence: the
world invariant by the checked transition, chain validity by the appended edge,
and the projection and active-holder agreement by the loan's place at the end of
the list. -/
theorem State.beginBorrow_OK {s s' : State} {borrower : CapId} {loanId : LoanId}
    (h : s.beginBorrow borrower loanId = some s') (hok : s.OK) : s'.OK := by
  obtain ⟨hfull, hchain, hloans, hcorr⟩ := hok
  obtain ⟨o0, c0, hfind0, hleaf0, hactive0, halloc0, hlo0, hhi0, hq0, hceil0⟩ := hcorr
  have hchainOK : s.chain.OK := hchain
  obtain ⟨_, _, _, _, _, _, _, _, _, _, hlastc⟩ := hchain
  unfold State.beginBorrow at h
  cases hw : s.world.beginBorrowChecked s.chain.alloc s.chain.holder borrower loanId with
  | error e => simp [hw] at h
  | ok w' =>
    cases hgl : w'.ctx.loans.loans.getLast? with
    | none => simp [hw, hgl] at h
    | some loan =>
      cases hb : s.chain.begin? w'.ctx.loans
          (Delegation.Chain.edgeOf s.chain.base loan) with
      | none => simp [hw, hgl, hb] at h
      | some c' =>
        obtain ⟨_, hc'eq⟩ := Delegation.Chain.begin?_sound hb
        have hchain' : c'.OK := Delegation.Chain.begin?_OK hchainOK hb
        obtain ⟨C, hC, hw'eq⟩ := World.beginBorrowChecked_sound hw
        obtain ⟨o, o', c, hfind, hretag, hiss, hroot, hloanfresh, hlive, hCeq⟩ :=
          Ctx.beginBorrow?_sound hC
        subst C
        subst w'
        simp only [hw, hgl, hb, Option.some.injEq] at h
        cases h
        let nl : Loan :=
          { id := loanId, alloc := s.chain.alloc,
            base := s.world.ctx.borrowBase s.chain.holder,
            lender := s.chain.holder, borrower := borrower,
            lifetime := ⟨s.world.ctx.loans.nextLifetime⟩,
            lo := c.lo, hi := c.hi, q := c.q, ceiling := c.ceiling }
        have hloan : loan = nl := by
          simp only [World.Ctx.beginBorrowNext_loanList, List.getLast?_concat] at hgl
          exact (Option.some.inj hgl).symm
        subst loan
        have hfull' : ({ s.world with
            ctx := Ctx.beginBorrowNext s.world.ctx s.chain.alloc o o' c s.chain.holder borrower
              loanId } : World).FullInv := World.fullInv_beginBorrowChecked hw hfull
        have hwf := hfull.1.1
        have hB : s.world.BorrowOK := hfull.2
        have hnewloans : ({ s.world with
            ctx := Ctx.beginBorrowNext s.world.ctx s.chain.alloc o o' c s.chain.holder borrower
              loanId } : World).ctx.loans.loans =
            s.world.ctx.loans.loans ++ [nl] := by
          simp [World.Ctx.beginBorrowNext_loanList, nl]
        -- the retagged leaf is the leaf the correspondence names
        have hcleaf : o.root.find? s.chain.holder = some c :=
          (Owner.retagLeafFind?_leaf hretag).1
        have hoeq : o0 = o :=
          World.Ctx.findOwner?_eq_of_shared_leaf hwf.1.2.2 hfind0 hfind hleaf0 hcleaf
        have hc0c : c0 = c := by
          rw [hoeq] at hleaf0
          exact Option.some.inj (hleaf0.symm.trans hcleaf)
        have hallocC : c.alloc = s.chain.alloc := hc0c ▸ halloc0
        have hloC : c.lo = s.chain.lo := hc0c ▸ hlo0
        have hhiC : c.hi = s.chain.hi := hc0c ▸ hhi0
        have hqC : c.q = s.chain.q := hc0c ▸ hq0
        have hceilC : c.ceiling = s.chain.ceiling := hc0c ▸ hceil0
        -- the loan's recorded base is the chain's base
        have hloanBase : nl.base = s.chain.base := by
          by_cases hempty : s.chain.edges = []
          · have hworldE : s.world.ctx.loans.loans = [] := by
              rw [← hloans]
              simp [Delegation.Chain.toLoans, hempty]
            have hholderBase : s.chain.holder = s.chain.base := by
              have hlast := hlastc
              simp only [hempty, List.getLast?_nil] at hlast
              exact hlast
            simp [nl, Ctx.borrowBase, hworldE, hholderBase]
          · have hne : s.chain.edges ≠ [] := hempty
            have hlast : s.chain.edges.getLast? = some (s.chain.edges.getLast hne) :=
              List.getLast?_eq_some_getLast hne
            have hholdere : s.chain.holder =
                (s.chain.edges.getLast hne).borrower := by
              have h := hlastc
              rw [hlast] at h
              exact h
            have hp : Delegation.Chain.edgeToLoan s.chain.base
                (s.chain.edges.getLast hne) ∈ s.world.ctx.loans.loans := by
              rw [← hloans]
              exact List.mem_map_of_mem
                (f := Delegation.Chain.edgeToLoan s.chain.base)
                (List.mem_of_getLast? hlast)
            have hbp : (Delegation.Chain.edgeToLoan s.chain.base
                (s.chain.edges.getLast hne)).borrower = s.chain.holder :=
              hholdere.symm
            obtain ⟨hbb, -⟩ := World.beginBorrow_newLoan_fields hwf hB hfind hretag hp hbp
            simp [nl, hbb, Delegation.Chain.edgeToLoan]
        -- the projection is the old list with the new loan appended
        have htoLoans : c'.toLoans =
            ({ s.world with
              ctx := Ctx.beginBorrowNext s.world.ctx s.chain.alloc o o' c s.chain.holder
                borrower loanId } : World).ctx.loans.loans := by
          rw [hc'eq]
          calc
            (s.chain.begin (Delegation.Chain.edgeOf s.chain.base nl)).toLoans
                = s.chain.toLoans ++ [Delegation.Chain.edgeToLoan s.chain.base
                    (Delegation.Chain.edgeOf s.chain.base nl)] := by
                  simp [Delegation.Chain.begin, Delegation.Chain.toLoans,
                    List.map_append]
            _ = s.chain.toLoans ++ [nl] := by
                  rw [Delegation.Chain.edgeToLoan_edgeOf hloanBase]
            _ = s.world.ctx.loans.loans ++ [nl] := by rw [hloans]
            _ = ({ s.world with
                  ctx := Ctx.beginBorrowNext s.world.ctx s.chain.alloc o o' c
                    s.chain.holder borrower loanId } : World).ctx.loans.loans := by
                  rw [hnewloans]
        -- the active holder is the retagged borrower leaf
        have ho'alloc : o'.alloc = o.alloc :=
          Owner.retagLeaf?_alloc (Owner.retagLeafFind?_fst hretag)
        have hoa : o.alloc = s.chain.alloc := by
          have := List.find?_some
            (p := fun x : Owner => decide (x.alloc = s.chain.alloc))
            (by simpa [Ctx.findOwner?] using hfind)
          simpa using this
        have hmemO : o ∈ s.world.ctx.owners := List.mem_of_find?_eq_some hfind
        have hmemUpdate : o' ∈ (s.world.ctx.update o.alloc o').owners := by
          unfold Ctx.update
          exact List.mem_map.mpr ⟨o, hmemO, by simp [ho'alloc]⟩
        have hfun := Ctx.update_functional ho'alloc hwf.1.1.2
        have hfindNew : (s.world.ctx.update o.alloc o').findOwner? o'.alloc = some o' :=
          Ctx.findOwner?_eq_some_of_mem_of_functional hfun hmemUpdate
        have hfindNew' : ({ s.world with
            ctx := Ctx.beginBorrowNext s.world.ctx s.chain.alloc o o' c s.chain.holder borrower
              loanId } : World).ctx.findOwner? s.chain.alloc = some o' := by
          change (s.world.ctx.update o.alloc o').findOwner? s.chain.alloc = some o'
          rw [← hoa]
          simpa only [ho'alloc] using hfindNew
        have hrect : o.retagLeaf? s.chain.holder borrower = some o' :=
          Owner.retagLeafFind?_fst hretag
        have hfresh : borrower ∉ o.root.ids := (Owner.retagLeafFind?_leaf hretag).2.2
        have hactiveC : c.state = .active := (Owner.retagLeafFind?_leaf hretag).2.1
        have hleafNew : o'.root.find? borrower = some { c with id := borrower } := by
          rw [Owner.retagLeaf?_eq hrect]
          exact Tree.find?_retag_new hcleaf hfresh
        refine ⟨hfull', hchain', htoLoans, ?_⟩
        rw [hc'eq]
        refine ⟨o', { c with id := borrower }, hfindNew', ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
        · rw [Delegation.Chain.holder_begin]
          exact hleafNew
        · simpa using hactiveC
        · simpa [Delegation.Chain.begin] using hallocC
        · simpa [Delegation.Chain.begin] using hloC
        · simpa [Delegation.Chain.begin] using hhiC
        · simpa [Delegation.Chain.begin] using hqC
        · simpa [Delegation.Chain.begin] using hceilC

/-- Dropping the last loan is filtering it out by identity, when identities are
distinct and the last loan is the one named. -/
private theorem dropLast_eq_filter {L : List Loan} {l : Loan}
    (hlast : L.getLast? = some l) (hnd : (L.map (·.id)).Nodup) :
    L.dropLast = L.filter (fun m => m.id ≠ l.id) := by
  obtain ⟨ys, rfl⟩ := List.getLast?_eq_some_iff.mp hlast
  have hnd' : (ys.map (·.id)).Nodup := by
    have := hnd
    rw [List.map_append, List.nodup_append] at this
    exact this.1
  have hdisj : ∀ a ∈ ys.map (·.id), a ≠ l.id := by
    have := hnd
    rw [List.map_append, List.nodup_append] at this
    intro a ha
    exact this.2.2 a ha l.id (by simp)
  have hfilter : ys.filter (fun m => m.id ≠ l.id) = ys := by
    rw [List.filter_eq_self]
    intro m hm
    have hm' : m.id ∈ ys.map (·.id) := List.mem_map_of_mem (f := (·.id)) hm
    simpa using hdisj m.id hm'
  rw [List.dropLast_concat, List.filter_append, hfilter]
  simp

/-- Ending a borrow through the holder preserves the correspondence: the world
invariant by the checked transition, chain validity by the removed innermost
edge, and the projection and active-holder agreement because the ended loan is
the last chain edge. -/
theorem State.endBorrow_OK {s s' : State} {loanId : LoanId}
    (h : s.endBorrow loanId = some s') (hok : s.OK) : s'.OK := by
  obtain ⟨hfull, hchain, hloans, hcorr⟩ := hok
  obtain ⟨o0, c0, hfind0, hleaf0, hactive0, halloc0, hlo0, hhi0, hq0, hceil0⟩ := hcorr
  have hchainOK : s.chain.OK := hchain
  obtain ⟨hpath, hfirst, hholderD, hids, hlends, hborrs, hres, hna, hadj, hsrc,
    hlastc⟩ := hchain
  unfold State.endBorrow at h
  cases hw : s.world.endBorrowChecked s.chain.alloc loanId with
  | error e => simp [hw] at h
  | ok w' =>
    obtain ⟨C, hC, hw'eq⟩ := World.endBorrowChecked_sound hw
    obtain ⟨loan, o, o', hloan, hfind, hret, hsuc, hdesc, hCeq⟩ :=
      Ctx.endBorrow?_sound hC
    subst C
    subst w'
    cases he : s.chain.end? with
    | none => simp [hw, he] at h
    | some c' =>
      have hchain' : c'.OK := Delegation.Chain.end?_OK hchainOK he
      have hend := Delegation.Chain.end?_sound he
      simp only [hw, he, Option.some.injEq] at h
      cases h
      obtain ⟨eLast, hlast, hc'holder⟩ := Delegation.Chain.holder_end hend
      obtain ⟨ys, hys⟩ := List.getLast?_eq_some_iff.mp hlast
      have hc'eq := by
        unfold Delegation.Chain.end at hend
        rw [hlast] at hend
        simp only [Option.some.injEq] at hend
        exact hend.symm
      have hc'edges : c'.edges = ys := by
        rw [hc'eq, hys]
        simp
      have hlastEnd : s.chain.holder = eLast.borrower := by
        have h := hlastc
        rw [hlast] at h
        exact h
      have hc'base : c'.base = s.chain.base := by rw [hc'eq]
      have hc'alloc : c'.alloc = s.chain.alloc := by rw [hc'eq]
      have hc'lo : c'.lo = s.chain.lo := by rw [hc'eq]
      have hc'hi : c'.hi = s.chain.hi := by rw [hc'eq]
      have hc'q : c'.q = s.chain.q := by rw [hc'eq]
      have hc'ceiling : c'.ceiling = s.chain.ceiling := by rw [hc'eq]
      have hfull' : ({ s.world with
          ctx := Ctx.endBorrowNext s.world.ctx o o' loan } : World).FullInv :=
        World.fullInv_endBorrowChecked hw hfull
      have hwf := hfull.1.1
      have hB : s.world.BorrowOK := hfull.2
      have hdistinct : World.LoansDistinctOK s.world := by
        obtain ⟨hd, _, _, _, _, _, _, _, _, _, _⟩ := hB
        exact hd
      -- the ended loan is the last loan of the list
      have hloanId : loan.id = loanId := by
        have := List.find?_some (p := fun x : Loan => x.id = loanId) hloan
        simpa using this
      have hmemLoan : loan ∈ s.chain.toLoans := by
        rw [hloans]
        exact List.mem_of_find?_eq_some hloan
      have hloanLast : s.chain.toLoans.getLast? = some loan := by
        obtain ⟨i, hi⟩ := List.mem_iff_getElem?.mp hmemLoan
        have hnone : s.chain.toLoans[i+1]? = none := by
          cases hs : s.chain.toLoans[i+1]? with
          | none => rfl
          | some m =>
            exfalso
            obtain ⟨e1, he1, hfe1⟩ : ∃ e1, s.chain.edges[i]? = some e1 ∧
                Delegation.Chain.edgeToLoan s.chain.base e1 = loan := by
              have h := hi
              rw [Delegation.Chain.toLoans, List.getElem?_map,
                Option.map_eq_some_iff] at h
              exact h
            obtain ⟨e2, he2, hfe2⟩ : ∃ e2, s.chain.edges[i+1]? = some e2 ∧
                Delegation.Chain.edgeToLoan s.chain.base e2 = m := by
              have h := hs
              rw [Delegation.Chain.toLoans, List.getElem?_map,
                Option.map_eq_some_iff] at h
              exact h
            have hlt1 : i < s.chain.edges.length :=
              (List.getElem?_eq_some_iff.mp he1).1
            have hlt1' : i < (s.chain.edges.map (·.id)).length := by
              simpa using hlt1
            have hmId : m.id ≠ loanId := by
              intro hmid
              have he1id : e1.id = loan.id := by rw [← hfe1]; rfl
              have he2id : e2.id = m.id := by rw [← hfe2]; rfl
              have hii : i = i + 1 := by
                apply hids.eq_of_getElem?_eq hlt1'
                rw [show (s.chain.edges.map (·.id))[i]? = some e1.id by simp [he1],
                  show (s.chain.edges.map (·.id))[i+1]? = some e2.id by simp [he2],
                  he2id, hmid, ← hloanId, ← he1id]
              omega
            have hmMem : m ∈ s.world.ctx.loans.loans := by
              rw [← hloans]
              exact List.mem_of_getElem? hs
            have hmL : m.lender = loan.borrower := by
              have hadj' := hadj i e1 e2 he1 he2
              rw [← hfe2, ← hfe1]
              simpa [Delegation.Chain.edgeToLoan] using hadj'
            exact hsuc m hmMem hmId hmL
        rw [List.getLast?_eq_getElem?]
        have hlen : s.chain.toLoans.length - 1 = i := by
          have hge := List.getElem?_eq_none_iff.mp hnone
          have hlt := (List.getElem?_eq_some_iff.mp hi).1
          omega
        rw [hlen]
        exact hi
      have hloanIsLast : Delegation.Chain.edgeToLoan s.chain.base eLast = loan := by
        have hm := hloanLast
        rw [Delegation.Chain.toLoans, List.getLast?_map, hlast] at hm
        simpa using hm
      have hloanBase : loan.base = s.chain.base := by
        rw [← hloanIsLast]
        rfl
      have hlastWorld : s.world.ctx.loans.loans.getLast? = some loan := by
        rw [← hloans]
        exact hloanLast
      have hnewloans : ({ s.world with
          ctx := Ctx.endBorrowNext s.world.ctx o o' loan } : World).ctx.loans.loans =
          s.world.ctx.loans.loans.filter (fun m => m.id ≠ loan.id) := by
        simp [Ctx.endBorrowNext, LoanCtx.endBorrowBookkeeping]
      have htoLoans : c'.toLoans = ({ s.world with
          ctx := Ctx.endBorrowNext s.world.ctx o o' loan } : World).ctx.loans.loans := by
        calc
          c'.toLoans = (s.chain.edges.dropLast).map
              (Delegation.Chain.edgeToLoan s.chain.base) := by
                rw [Delegation.Chain.toLoans, hc'edges, hc'base, hys]
                simp
          _ = s.chain.toLoans.dropLast := by
                simp [Delegation.Chain.toLoans, List.map_dropLast]
          _ = s.world.ctx.loans.loans.dropLast := by rw [hloans]
          _ = s.world.ctx.loans.loans.filter (fun m => m.id ≠ loan.id) :=
                dropLast_eq_filter hlastWorld hdistinct.1
          _ = ({ s.world with
                ctx := Ctx.endBorrowNext s.world.ctx o o' loan } :
                World).ctx.loans.loans := by
                rw [hnewloans]
      -- the restored holder is the leaf the return retagged
      obtain ⟨c1, hc1, hactive1⟩ := Owner.retagLeaf?_active hret
      have hloanBorrower : loan.borrower = eLast.borrower := by
        rw [← hloanIsLast]
        rfl
      have hleaf0' : o0.root.find? loan.borrower = some c0 := by
        rw [hloanBorrower, ← hlastEnd]
        exact hleaf0
      have hoeq : o0 = o :=
        World.Ctx.findOwner?_eq_of_shared_leaf hwf.1.2.2 hfind0 hfind hleaf0' hc1
      have hc1c0 : c1 = c0 := by
        rw [hoeq] at hleaf0'
        rw [hc1] at hleaf0'
        exact Option.some.inj hleaf0'
      have ho'alloc : o'.alloc = o.alloc := Owner.retagLeaf?_alloc hret
      have hoa : o.alloc = s.chain.alloc := by
        have := List.find?_some
          (p := fun x : Owner => decide (x.alloc = s.chain.alloc))
          (by simpa [Ctx.findOwner?] using hfind)
        simpa using this
      have hmemO : o ∈ s.world.ctx.owners := List.mem_of_find?_eq_some hfind
      have hmemUpdate : o' ∈ (s.world.ctx.update o.alloc o').owners := by
        unfold Ctx.update
        exact List.mem_map.mpr ⟨o, hmemO, by simp [ho'alloc]⟩
      have hfun := Ctx.update_functional ho'alloc hwf.1.1.2
      have hfindNew : (s.world.ctx.update o.alloc o').findOwner? o'.alloc = some o' :=
        Ctx.findOwner?_eq_some_of_mem_of_functional hfun hmemUpdate
      have hfindNew' : ({ s.world with
          ctx := Ctx.endBorrowNext s.world.ctx o o' loan } :
          World).ctx.findOwner? s.chain.alloc = some o' := by
        change (s.world.ctx.update o.alloc o').findOwner? s.chain.alloc = some o'
        rw [← hoa]
        simpa only [ho'alloc] using hfindNew
      have hfresh : loan.lender ∉ o.root.ids := Owner.retagLeaf?_fresh hret
      have hleafNew : o'.root.find? loan.lender =
          some { c1 with id := loan.lender } := by
        rw [Owner.retagLeaf?_eq hret]
        exact Tree.find?_retag_new hc1 hfresh
      refine ⟨hfull', hchain', htoLoans, ?_⟩
      refine ⟨o', { c1 with id := loan.lender }, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · simpa only [hc'alloc] using hfindNew'
      · have hlenderEq : eLast.lender = loan.lender := by
          rw [← hloanIsLast]
          rfl
        rw [hc'holder, hlenderEq]
        exact hleafNew
      · simpa using hactive1
      · simpa [hc1c0, hc'alloc] using halloc0
      · simpa [hc1c0, hc'lo] using hlo0
      · simpa [hc1c0, hc'hi] using hhi0
      · exact ⟨by simpa [hc1c0, hc'q] using hq0,
          by simpa [hc1c0, hc'ceiling] using hceil0⟩

end Discipline

end Cap
