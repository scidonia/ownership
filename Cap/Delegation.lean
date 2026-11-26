/-
A first-class nested-delegation chain.

The chain is the ownership state for one delegated allocation. Each edge records
the lender, the fresh borrower, the allocation and the resource description
carried down the chain. The chain stores one resource descriptor and every edge
must agree with it, so delegation never changes the allocation, footprint, share
or ceiling.

A valid chain is a rooted simple path. The capability path is
`base :: edges.map (·.borrower)`; it has no repeated name, the first edge is lent
by the base and every later edge by the previous borrower, and the stored holder
is derived from the edge list (the innermost borrower, or the base when there
are no edges). Distinct lender and borrower lists are not enough for this: the
two-edge cycle `a → b, b → a` has distinct lenders and borrowers and still
returns to its base, and the capability path rejects it. The stored holder is
not independent either, so an empty chain cannot name a holder other than its
base.

Raw `begin` and `end` are unchecked structural transformations, used inside
proofs. Executable callers use the checked `begin?` and `end?`: `beginCheck`
decides the edge preconditions (resource agreement, current-holder lending,
fresh identities against the path, and a live lifetime), and its soundness
theorem turns the executable check into the propositional admissibility needed
to preserve chain validity. Chain validity itself stays propositional; the
checked operations take it as the caller's proof.
-/
import Cap.Ledger
import Cap.Loans

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

/-- The capability path: the base name followed by each edge's borrower. -/
def Chain.path (c : Chain) : List CapId :=
  c.base :: c.edges.map (·.borrower)

/-- The holder the edge list implies: the innermost borrower, or the base when
there are no edges. -/
def Chain.derivedHolder (c : Chain) : CapId :=
  match c.edges.getLast? with
  | none => c.base
  | some e => e.borrower

/-- The first edge, when present, is lent by the chain's base. -/
def Chain.firstLenderOK (c : Chain) : Prop :=
  match c.edges with
  | [] => True
  | e :: _ => e.lender = c.base

/-- A valid chain is a rooted simple path with distinct loan identities, an
agreed resource descriptor, no self edge, adjacency, a base-or-previous-borrower
lender, and a holder derived from the edge list.

The path condition is what excludes cycles: distinct lender and borrower lists
alone admit `a → b, b → a`, whose capability path is `[a, b, a]`. -/
def Chain.OK (c : Chain) : Prop :=
  c.path.Nodup
  ∧ c.firstLenderOK
  ∧ c.holder = c.derivedHolder
  ∧ (c.edges.map (·.id)).Nodup
  ∧ (c.edges.map (·.lender)).Nodup
  ∧ (c.edges.map (·.borrower)).Nodup
  ∧ (∀ e ∈ c.edges, e.alloc = c.alloc ∧ e.lo = c.lo ∧ e.hi = c.hi ∧
      e.q = c.q ∧ e.ceiling = c.ceiling)
  ∧ (∀ e ∈ c.edges, e.lender ≠ e.borrower)
  ∧ (∀ i e₁ e₂, c.edges[i]? = some e₁ → c.edges[i+1]? = some e₂ →
      e₂.lender = e₁.borrower)
  ∧ (∀ e ∈ c.edges, e.lender = c.base ∨
      ∃ e' ∈ c.edges, e'.borrower = e.lender)
  ∧ (match c.edges.getLast? with
      | none => c.holder = c.base
      | some e => c.holder = e.borrower)

/-- Raw append: the unchecked structural transformation. It does not test
admissibility; callers use `Chain.begin?`. -/
def Chain.begin (c : Chain) (e : Edge) : Chain :=
  { c with edges := c.edges ++ [e], holder := e.borrower }

/-- Raw pop: the unchecked structural transformation. It does not test
admissibility; callers use `Chain.end?`. -/
def Chain.end (c : Chain) : Option Chain :=
  match c.edges.getLast? with
  | none => none
  | some e =>
      some { c with edges := c.edges.dropLast, holder := e.lender }

/-- The edge a loan contributes to the chain of its `(alloc, base)` group. -/
def Chain.edgeOf (base : CapId) (l : Loan) : Edge :=
  { id := l.id, alloc := l.alloc, lender := l.lender, borrower := l.borrower,
    lifetime := l.lifetime, lo := l.lo, hi := l.hi, q := l.q, ceiling := l.ceiling }

/-- The loan record an edge denotes at the chain's base. -/
def Chain.edgeToLoan (base : CapId) (e : Edge) : Loan :=
  { id := e.id, alloc := e.alloc, base := base, lender := e.lender,
    borrower := e.borrower, lifetime := e.lifetime, lo := e.lo, hi := e.hi,
    q := e.q, ceiling := e.ceiling }

/-- An edge assembled from a loan whose base is the chain's base maps back to
that loan. -/
theorem Chain.edgeToLoan_edgeOf {base : CapId} {l : Loan} (h : l.base = base) :
    Chain.edgeToLoan base (Chain.edgeOf base l) = l := by
  cases l with
  | mk id alloc lbase lender borrower lifetime lo hi q ceiling =>
    simp only [Chain.edgeOf, Chain.edgeToLoan] at h ⊢
    rw [h]

/-- The loan records represented by a delegation chain: one record per edge,
carrying the chain's base and the edge's allocation and resource description. -/
def Chain.toLoans (c : Chain) : List Loan :=
  c.edges.map (Chain.edgeToLoan c.base)

/-- Remove the loan with the given record's identity from a list. -/
def Chain.eraseLoan (loans : List Loan) (l : Loan) : List Loan :=
  loans.filter (fun m => m.id ≠ l.id)

/-- Walk a group of loans from the chain's base towards the holder, one borrower
at a time. `holder` is the lender the next edge must name; the walk stops when
no remaining loan is lent by it. The fuel bounds the walk by the group size. -/
def Chain.ofPathAux (loans : List Loan) (alloc : AllocId) (base : CapId) :
    Nat → CapId → List Edge
  | 0, _ => []
  | n + 1, holder =>
    match loans.find? (fun l =>
        decide (l.alloc = alloc) && decide (l.base = base) &&
          decide (l.lender = holder)) with
    | none => []
    | some l =>
        Chain.edgeOf base l ::
          Chain.ofPathAux (Chain.eraseLoan loans l) alloc base n l.borrower

/-- Assemble the chain of one `(alloc, base)` group. The walk starts at the
chain's base and follows each edge's borrower, so the produced edges are the
group in chain order. The fuel is `loans.length + 1`, enough for every edge. -/
def Chain.ofPath (loans : List Loan) (alloc : AllocId) (base : CapId) : Chain :=
  let frame := match loans.head? with
    | some l => (l.lo, l.hi, l.q, l.ceiling)
    | none => (0, 0, 0, Ceiling.readWrite)
  { base := base
    holder := match loans.getLast? with
      | some l => l.borrower
      | none => base
    alloc := alloc
    lo := frame.1
    hi := frame.2.1
    q := frame.2.2.1
    ceiling := frame.2.2.2
    edges := Chain.ofPathAux loans alloc base (loans.length + 1) base }

/-- A uniquely matching list element is the one `find?` returns. -/
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

/-- Erasing the head of a list with distinct identities leaves the tail. -/
private theorem Chain.eraseLoan_cons (l : Loan) (rest : List Loan)
    (h : ∀ m ∈ rest, m.id ≠ l.id) :
    Chain.eraseLoan (l :: rest) l = rest := by
  unfold Chain.eraseLoan
  rw [List.filter_cons_of_neg (by simp)]
  rw [List.filter_eq_self]
  intro m hm
  simpa using h m hm

/-- The walk assembles exactly the group, in list order, when the group is a
chain path: every edge is lent by the previous edge's borrower, and the first
edge is lent by the base. -/
private theorem Chain.ofPathAux_eq_map (loans : List Loan) (alloc : AllocId)
    (base : CapId) :
    ∀ (holder : CapId) (n : Nat),
      (∀ l ∈ loans, l.alloc = alloc ∧ l.base = base) →
      (loans.map (·.id)).Nodup →
      (loans.map (·.lender)).Nodup →
      (loans.map (·.borrower)).Nodup →
      (∀ l ∈ loans, l.lender ≠ l.borrower) →
      (∀ i l₁ l₂, loans[i]? = some l₁ → loans[i+1]? = some l₂ →
        l₂.lender = l₁.borrower) →
      (∀ l, loans.head? = some l → holder = l.lender) →
      loans.length < n →
      Chain.ofPathAux loans alloc base n holder = loans.map (Chain.edgeOf base) := by
  induction loans with
  | nil =>
      intro holder n _ _ _ _ _ _ _ hn
      cases n with
      | zero => omega
      | succ m => simp [Chain.ofPathAux]
  | cons l rest ih =>
      intro holder n halloc hids hlend hborr hna hadj hhead hn
      cases n with
      | zero => omega
      | succ m =>
        have hlen : rest.length < m := by simpa using hn
        have hpred : (fun x : Loan => decide (x.alloc = alloc) &&
            decide (x.base = base) && decide (x.lender = holder)) l = true := by
          obtain ⟨ha, hb⟩ := halloc l (by simp)
          have hh := hhead l rfl
          simp [ha, hb, hh]
        have huniq : ∀ y ∈ l :: rest,
            (fun x : Loan => decide (x.alloc = alloc) && decide (x.base = base) &&
              decide (x.lender = holder)) y = true → y = l := by
          intro y hy hp
          simp only [Bool.and_eq_true, decide_eq_true_eq] at hp
          exact List.nodup_map_inj hlend y hy l (by simp) (by rw [hp.2, hhead l rfl])
        have hfind : (l :: rest).find? (fun x => decide (x.alloc = alloc) &&
            decide (x.base = base) && decide (x.lender = holder)) = some l :=
          find?_eq_some_of_unique (by simp) hpred huniq
        have herase : Chain.eraseLoan (l :: rest) l = rest := by
          refine Chain.eraseLoan_cons l rest ?_
          intro x hx hxid
          have hxmem : x ∈ l :: rest := List.mem_cons_of_mem _ hx
          have hxl : x = l := List.nodup_map_inj hids x hxmem l (by simp) hxid
          subst hxl
          exact (List.nodup_cons.mp hids).1 (List.mem_map_of_mem (f := fun y => y.id) hx)
        rw [Chain.ofPathAux, hfind]
        simp only [herase]
        have hhead' : ∀ x, rest.head? = some x → l.borrower = x.lender := by
          intro x hx
          cases rest with
          | nil => simp at hx
          | cons r rs =>
              simp only [List.head?_cons, Option.some.injEq] at hx
              subst hx
              exact (hadj 0 l r (by simp) (by simp)).symm
        have ih' := ih l.borrower m
          (fun x hx => halloc x (by simp [hx]))
          (by simpa using (List.nodup_cons.mp (by simpa using hids)).2)
          (by simpa using (List.nodup_cons.mp (by simpa using hlend)).2)
          (by simpa using (List.nodup_cons.mp (by simpa using hborr)).2)
          (fun x hx => hna x (by simp [hx]))
          (fun i a b ha hb => hadj (i + 1) a b (by simp [ha]) (by simp [hb]))
          hhead' hlen
        rw [ih']
        simp [List.map_cons]

/-- Mapping an edge assembled from a group back to a loan recovers the group. -/
private theorem Chain.map_edgeToLoan_edgeOf (loans : List Loan) (base : CapId)
    (hbase : ∀ l ∈ loans, l.base = base) :
    (loans.map (Chain.edgeOf base)).map (Chain.edgeToLoan base) = loans := by
  induction loans with
  | nil => rfl
  | cons l rest ih =>
      simp only [List.map_cons]
      rw [ih (fun x hx => hbase x (by simp [hx]))]
      have hlb : l.base = base := hbase l (by simp)
      cases l with
      | mk id alloc base' lender borrower lifetime lo hi q ceiling =>
        simp only [Chain.edgeOf, Chain.edgeToLoan]
        have hb : base' = base := hlb
        simp [hb]

/-- In path order the walk assembles exactly the group's edges. -/
theorem Chain.ofPath_edges {loans : List Loan} {alloc : AllocId}
    {base : CapId}
    (halloc : ∀ l ∈ loans, l.alloc = alloc ∧ l.base = base)
    (hids : (loans.map (·.id)).Nodup)
    (hlend : (loans.map (·.lender)).Nodup)
    (hborr : (loans.map (·.borrower)).Nodup)
    (hna : ∀ l ∈ loans, l.lender ≠ l.borrower)
    (hadj : ∀ i l₁ l₂, loans[i]? = some l₁ → loans[i+1]? = some l₂ →
      l₂.lender = l₁.borrower)
    (hhead : ∀ l, loans.head? = some l → l.lender = base) :
    (Chain.ofPath loans alloc base).edges = loans.map (Chain.edgeOf base) := by
  unfold Chain.ofPath
  exact Chain.ofPathAux_eq_map loans alloc base base (loans.length + 1)
    halloc hids hlend hborr hna hadj (fun l h => (hhead l h).symm)
    (Nat.lt_succ_self _)

/-- The chain assembled from a group in path order lists exactly the group. -/
theorem Chain.toLoans_ofPath {loans : List Loan} {alloc : AllocId}
    {base : CapId}
    (halloc : ∀ l ∈ loans, l.alloc = alloc ∧ l.base = base)
    (hids : (loans.map (·.id)).Nodup)
    (hlend : (loans.map (·.lender)).Nodup)
    (hborr : (loans.map (·.borrower)).Nodup)
    (hna : ∀ l ∈ loans, l.lender ≠ l.borrower)
    (hadj : ∀ i l₁ l₂, loans[i]? = some l₁ → loans[i+1]? = some l₂ →
      l₂.lender = l₁.borrower)
    (hhead : ∀ l, loans.head? = some l → l.lender = base) :
    (Chain.ofPath loans alloc base).toLoans = loans := by
  have hedges := Chain.ofPath_edges (loans := loans) (alloc := alloc) (base := base)
    halloc hids hlend hborr hna hadj hhead
  unfold Chain.toLoans
  rw [hedges]
  have hbase : (Chain.ofPath loans alloc base).base = base := rfl
  rw [hbase, List.map_map]
  simpa [Function.comp_def] using
    Chain.map_edgeToLoan_edgeOf loans base (fun l hl => (halloc l hl).2)


/-- The authority a name carries in a chain: the holder carries the whole share
`D`, every other name zero. -/
def Chain.weight (c : Chain) (D : Nat) (x : CapId) : Nat :=
  if x = c.holder then D else 0

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

/-! ### Checked operations -/

/-- The admissibility predicate for appending an edge, apart from chain
validity: the edge agrees with the chain's resource descriptor, it is lent by
the current holder, its loan identity and lender are fresh against the edges and
its borrower against the capability path, it is not a self edge, and its
lifetime is live. Chain validity is a proof the caller supplies; this predicate
is what the executable check decides. -/
structure BeginAllowed (Γ : LoanCtx) (c : Chain) (e : Edge) : Prop where
  resource : e.alloc = c.alloc ∧ e.lo = c.lo ∧ e.hi = c.hi ∧ e.q = c.q ∧
    e.ceiling = c.ceiling
  lender : e.lender = c.holder
  freshId : e.id ∉ c.edges.map (·.id)
  freshLender : e.lender ∉ c.edges.map (·.lender)
  freshBorrower : e.borrower ∉ c.path
  distinct : e.lender ≠ e.borrower
  live : Γ.live e.lifetime = true

/-- The edge agrees with the chain's resource descriptor, as an executable
test. -/
private def Chain.resourceMatchB (c : Chain) (e : Edge) : Bool :=
  decide (e.alloc = c.alloc ∧ e.lo = c.lo ∧ e.hi = c.hi ∧ e.q = c.q ∧
    e.ceiling = c.ceiling)

private theorem Chain.resourceMatchB_sound {c : Chain} {e : Edge}
    (h : c.resourceMatchB e = true) :
    e.alloc = c.alloc ∧ e.lo = c.lo ∧ e.hi = c.hi ∧ e.q = c.q ∧
      e.ceiling = c.ceiling :=
  of_decide_eq_true h

/-- The executable form of `BeginAllowed`. -/
def Chain.beginCheck (Γ : LoanCtx) (c : Chain) (e : Edge) : Bool :=
  ((((((c.resourceMatchB e &&
    decide (e.lender = c.holder)) &&
    decide (e.id ∉ c.edges.map (·.id))) &&
    decide (e.lender ∉ c.edges.map (·.lender))) &&
    decide (e.borrower ∉ c.path)) &&
    decide (e.lender ≠ e.borrower)) &&
    Γ.live e.lifetime)

theorem Chain.beginCheck_sound {Γ : LoanCtx} {c : Chain} {e : Edge}
    (h : c.beginCheck Γ e = true) : BeginAllowed Γ c e := by
  unfold Chain.beginCheck at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  have hlive : Γ.live e.lifetime = true := h.2
  obtain ⟨⟨⟨⟨⟨hres, hlender⟩, hid⟩, hlend⟩, hborr⟩, hdist⟩ := h.1
  exact ⟨Chain.resourceMatchB_sound hres, hlender, hid, hlend, hborr, hdist, hlive⟩

/-- A predecessor of an indexing edge exists at the preceding index. -/
private theorem getElem?_succ_prev : ∀ {l : List Edge} {k : Nat} {m : Edge},
    l[k+1]? = some m → ∃ m', l[k]? = some m'
  | [], k, m, h => by simp at h
  | _ :: xs, 0, m, h => ⟨_, rfl⟩
  | _ :: xs, k+1, m, h => by
      simp only [List.getElem?_cons_succ] at h
      obtain ⟨m', hm'⟩ := getElem?_succ_prev (l := xs) (k := k) (m := m) h
      exact ⟨m', by simpa using hm'⟩

/-- Every edge's lender is the base or the borrower of an earlier edge. -/
private theorem Chain.lender_base_or_earlier {c : Chain} (h : c.OK) :
    ∀ (j : Nat) (e : Edge), c.edges[j]? = some e →
      e.lender = c.base ∨
        ∃ i, i < j ∧ ∃ e0, c.edges[i]? = some e0 ∧ e0.borrower = e.lender := by
  obtain ⟨_, hfirst, _, _, _, _, _, _, hadj, _, _⟩ := h
  intro j
  induction j with
  | zero =>
      intro e he
      left
      cases hE : c.edges with
      | nil => simp [hE] at he
      | cons e0 rest =>
          have hfl : e0.lender = c.base := by
            have := hfirst
            simpa [Chain.firstLenderOK, hE] using this
          simp only [hE, List.getElem?_cons_zero] at he
          rw [(Option.some.inj he).symm]
          exact hfl
  | succ k ih =>
      intro e he
      right
      obtain ⟨e0, he0⟩ := getElem?_succ_prev he
      have hadjk := hadj k e0 e he0 he
      exact ⟨k, Nat.lt_succ_self k, e0, he0, hadjk.symm⟩

/-- The holder of a valid chain is never a lender. The capability path is
simple, so the innermost borrower cannot be the lender of an earlier edge. -/
theorem Chain.holder_not_lender {c : Chain} (h : c.OK) :
    c.holder ∉ c.edges.map (·.lender) := by
  have hOK : c.OK := h
  obtain ⟨hpath, _, hholderD, _, _, hborrs, _, _, _, _, _⟩ := hOK
  intro hmem
  obtain ⟨e', he', hle⟩ := List.mem_map.mp hmem
  obtain ⟨j, hj⟩ := List.mem_iff_getElem?.mp he'
  have hne : c.edges ≠ [] := by
    intro hnil
    rw [hnil] at he'
    simp at he'
  have hlast := List.getLast?_eq_some_getLast hne
  have hlastIdx : c.edges[c.edges.length - 1]? = some (c.edges.getLast hne) := by
    rw [List.getLast?_eq_getElem?] at hlast
    exact hlast
  have hholderL : c.holder = (c.edges.getLast hne).borrower := by
    rw [hholderD]
    simp [Chain.derivedHolder, hlast]
  rcases Chain.lender_base_or_earlier h j e' hj with hb | ⟨i, hij, e0, he0, hb0⟩
  · have hbase : c.base = (c.edges.getLast hne).borrower := by
      rw [← hb, hle, hholderL]
    have hbaseNot : c.base ∉ c.edges.map (·.borrower) :=
      (List.nodup_cons.mp hpath).1
    apply hbaseNot
    rw [hbase]
    exact List.mem_map_of_mem (f := (·.borrower)) (List.mem_of_getLast? hlast)
  · have hbEq : e0.borrower = (c.edges.getLast hne).borrower := by
      rw [hb0, hle, hholderL]
    have hiLen : i < c.edges.length := (List.getElem?_eq_some_iff.mp he0).1
    have hiLen' : i < (c.edges.map (·.borrower)).length := by simpa using hiLen
    have hidx : i = c.edges.length - 1 := by
      apply hborrs.eq_of_getElem?_eq hiLen'
      rw [show (c.edges.map (·.borrower))[i]? = some e0.borrower by simp [he0],
        show (c.edges.map (·.borrower))[c.edges.length - 1]? =
          some (c.edges.getLast hne).borrower by simp [hlastIdx],
        hbEq]
    have hjLen : j < c.edges.length := (List.getElem?_eq_some_iff.mp hj).1
    have hpos : 0 < c.edges.length := by omega
    omega

/-- Beginning through the checked route appends only an admissible edge. -/
def Chain.begin? (Γ : LoanCtx) (c : Chain) (e : Edge) : Option Chain :=
  if c.beginCheck Γ e = true then some (c.begin e) else none

theorem Chain.begin?_sound {Γ : LoanCtx} {c : Chain} {e : Edge} {c' : Chain}
    (h : c.begin? Γ e = some c') : BeginAllowed Γ c e ∧ c' = c.begin e := by
  unfold Chain.begin? at h
  by_cases hchk : c.beginCheck Γ e = true
  · rw [if_pos hchk] at h
    simp only [Option.some.injEq] at h
    exact ⟨Chain.beginCheck_sound hchk, h.symm⟩
  · rw [if_neg hchk] at h
    simp at h

/-- Appending an edge lent by the current holder preserves chain validity. The
new edge must carry the chain's resource description, its identities must be
fresh against the existing edges and the path, and its lender and borrower must
differ. -/
theorem Chain.begin_OK {c : Chain} {e : Edge}
    (hok : c.OK)
    (hres : e.alloc = c.alloc ∧ e.lo = c.lo ∧ e.hi = c.hi ∧ e.q = c.q ∧
      e.ceiling = c.ceiling)
    (hlender : e.lender = c.holder)
    (hid : e.id ∉ c.edges.map (·.id))
    (hlendfresh : e.lender ∉ c.edges.map (·.lender))
    (hborrfresh : e.borrower ∉ c.path)
    (hna : e.lender ≠ e.borrower) :
    (c.begin e).OK := by
  obtain ⟨hpath, hfirst, hholderD, hids, hlends, hborrs, hresold, hnold, hadj,
    hsrc, hlastc⟩ := hok
  have hedges : (c.begin e).edges = c.edges ++ [e] := rfl
  have hborrfreshList : e.borrower ∉ c.edges.map (·.borrower) := by
    intro hm
    exact hborrfresh (List.mem_cons_of_mem _ hm)
  have hpath' : (c.begin e).path = c.path ++ [e.borrower] := by
    simp [Chain.path, Chain.begin, List.map_append]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- the capability path stays simple
    rw [hpath', List.nodup_append]
    refine ⟨hpath, by simp, ?_⟩
    intro x hx y hy
    simp only [List.mem_singleton] at hy
    subst y
    intro hxy
    exact hborrfresh (hxy ▸ hx)
  · -- the first edge is still lent by the base
    by_cases hnil : c.edges = []
    · have hhold : c.holder = c.base := by
        rw [hholderD]
        simp [Chain.derivedHolder, hnil]
      have hlendbase : e.lender = c.base := by rw [hlender, hhold]
      simp [Chain.firstLenderOK, Chain.begin, hnil, hlendbase]
    · obtain ⟨e0, rest, he⟩ : ∃ e0 rest, c.edges = e0 :: rest := by
        cases hE : c.edges with
        | nil => exact absurd hE hnil
        | cons e0 rest => exact ⟨e0, rest, rfl⟩
      have hfl : e0.lender = c.base := by
        have := hfirst
        simpa [Chain.firstLenderOK, he] using this
      simp [Chain.firstLenderOK, Chain.begin, he, hfl]
  · -- the stored holder is the derived one
    simp [Chain.begin, Chain.derivedHolder]
  · rw [hedges, List.map_append, List.nodup_append]
    refine ⟨hids, by simp, ?_⟩
    intro x hx y hy
    simp only [List.map_cons, List.map_nil, List.mem_singleton] at hy
    subst y
    intro hxy
    exact hid (hxy ▸ hx)
  · rw [hedges, List.map_append, List.nodup_append]
    refine ⟨hlends, by simp, ?_⟩
    intro x hx y hy
    simp only [List.map_cons, List.map_nil, List.mem_singleton] at hy
    subst y
    intro hxy
    exact hlendfresh (hxy ▸ hx)
  · rw [hedges, List.map_append, List.nodup_append]
    refine ⟨hborrs, by simp, ?_⟩
    intro x hx y hy
    simp only [List.map_cons, List.map_nil, List.mem_singleton] at hy
    subst y
    intro hxy
    exact hborrfreshList (hxy ▸ hx)
  · intro e' he'
    rw [hedges] at he'
    rcases List.mem_append.mp he' with he' | he'
    · exact hresold e' he'
    · simp only [List.mem_singleton] at he'
      subst he'
      exact hres
  · intro e' he'
    rw [hedges] at he'
    rcases List.mem_append.mp he' with he' | he'
    · exact hnold e' he'
    · simp only [List.mem_singleton] at he'
      subst he'
      exact hna
  · intro i e1 e2 h1 h2
    rw [hedges] at h1 h2
    by_cases hi : i < c.edges.length
    · rw [List.getElem?_append_left hi] at h1
      by_cases hi2 : i + 1 < c.edges.length
      · rw [List.getElem?_append_left hi2] at h2
        exact hadj i e1 e2 h1 h2
      · -- the next element is the appended edge
        rw [List.getElem?_append_right (by omega)] at h2
        have hz : i + 1 - c.edges.length = 0 := by omega
        rw [hz] at h2
        simp only [List.getElem?_cons_zero, Option.some.injEq] at h2
        subst e2
        have hlast : c.edges.getLast? = some e1 := by
          rw [List.getLast?_eq_getElem?]
          rw [show c.edges.length - 1 = i by omega]
          exact h1
        have hclause := hlastc
        simp only [hlast] at hclause
        rw [hlender, hclause]
    · exfalso
      obtain ⟨hlt, -⟩ := List.getElem?_eq_some_iff.mp h2
      simp only [List.length_append, List.length_singleton] at hlt
      omega
  · intro e' he'
    rw [hedges] at he'
    rcases List.mem_append.mp he' with he' | he'
    · rcases hsrc e' he' with hb | ⟨e2, he2, hborr⟩
      · exact Or.inl hb
      · exact Or.inr ⟨e2, List.mem_append_left _ he2, hborr⟩
    · simp only [List.mem_singleton] at he'
      subst he'
      rw [hlender]
      cases hl : c.edges.getLast? with
      | none =>
          left
          have := hlastc
          simp only [hl] at this
          exact this
      | some eL =>
          right
          refine ⟨eL, ?_, ?_⟩
          · exact List.mem_append_left _ (List.mem_of_getLast? hl)
          · have := hlastc
            simp only [hl] at this
            exact this.symm
  · simp [Chain.begin]

/-- A successful checked beginning preserves chain validity, given the validity
of the chain it appends to. -/
theorem Chain.begin?_OK {Γ : LoanCtx} {c : Chain} {e : Edge} {c' : Chain}
    (hok : c.OK) (h : c.begin? Γ e = some c') : c'.OK := by
  obtain ⟨ha, rfl⟩ := Chain.begin?_sound h
  exact Chain.begin_OK hok ha.resource ha.lender ha.freshId ha.freshLender
    ha.freshBorrower ha.distinct

/-- In a valid chain with a nonempty prefix, the last edge is lent by the
previous edge's borrower. -/
private theorem Chain.last_lender_eq {c : Chain} (hok : c.OK) {ys : List Edge}
    {e : Edge} (hedges : c.edges = ys ++ [e]) (hne : ys ≠ []) :
    ys.getLast?.map (·.borrower) = some e.lender := by
  obtain ⟨_, _, _, _, _, _, _, _, hadj, _, _⟩ := hok
  have hylast : ys[ys.length - 1]? = some (ys.getLast hne) := by
    rw [← List.getLast?_eq_getElem?]
    exact List.getLast?_eq_some_getLast hne
  have hpos : 0 < ys.length := List.length_pos_iff.mpr hne
  have hprev : c.edges[ys.length - 1]? = some (ys.getLast hne) := by
    rw [hedges, List.getElem?_append_left (by omega)]
    exact hylast
  have hlast : c.edges[ys.length]? = some e := by
    rw [hedges, List.getElem?_append_right (Nat.le_refl ys.length)]
    simp
  have hlast' : c.edges[(ys.length - 1) + 1]? = some e := by
    rw [show ys.length - 1 + 1 = ys.length by omega]
    exact hlast
  have hadj' := hadj (ys.length - 1) (ys.getLast hne) e hprev hlast'
  rw [List.getLast?_eq_some_getLast hne]
  simpa using hadj'.symm

/-- Removing the innermost edge preserves chain validity. The holder is the
active innermost name and is never a lender, so no remaining edge can have been
lent by the removed edge's borrower. -/
theorem Chain.end_OK {c c' : Chain} (h : c.end = some c')
    (hok : c.OK) : c'.OK := by
  have hOK : c.OK := hok
  obtain ⟨hpath, hfirst, hholderD, hids, hlends, hborrs, hres, hna, hadj, hsrc,
    hlastc⟩ := hOK
  obtain ⟨e, hlast, hc'holder⟩ := Chain.holder_end h
  obtain ⟨ys, hys⟩ := List.getLast?_eq_some_iff.mp hlast
  have hc'eq : c' = { c with edges := c.edges.dropLast, holder := e.lender } := by
    unfold Chain.end at h
    rw [hlast] at h
    simp only [Option.some.injEq] at h
    exact h.symm
  have hc'edges : c'.edges = ys := by
    rw [hc'eq, hys]
    simp
  have hlastE : c.holder = e.borrower := by
    have := hlastc
    rw [hlast] at this
    exact this
  have hc'base : c'.base = c.base := by rw [hc'eq]
  have hc'alloc : c'.alloc = c.alloc := by rw [hc'eq]
  have hc'lo : c'.lo = c.lo := by rw [hc'eq]
  have hc'hi : c'.hi = c.hi := by rw [hc'eq]
  have hc'q : c'.q = c.q := by rw [hc'eq]
  have hc'ceiling : c'.ceiling = c.ceiling := by rw [hc'eq]
  have hholderNot : c.holder ∉ c.edges.map (·.lender) := Chain.holder_not_lender hok
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- the remaining capability path stays simple
    have hsplit : c.path = c'.path ++ [e.borrower] := by
      simp [Chain.path, hc'eq, hys, List.map_append]
    have h' := hpath
    rw [hsplit, List.nodup_append] at h'
    exact h'.1
  · -- the first edge is unchanged
    cases ys with
    | nil => simp [Chain.firstLenderOK, hc'edges]
    | cons y0 rest =>
        have hthis : y0.lender = c.base := by
          simpa [Chain.firstLenderOK, hys] using hfirst
        simp [Chain.firstLenderOK, hc'edges, hc'base, hthis]
  · -- the restored holder is the previous edge's borrower, or the base
    rw [hc'holder]
    cases ys with
    | nil =>
        have hsingle : c.edges = [e] := by simpa using hys
        have hthis : e.lender = c.base := by
          simpa [Chain.firstLenderOK, hsingle] using hfirst
        simp [Chain.derivedHolder, hc'edges, hc'base, hthis]
    | cons y0 rest =>
        have hne : (y0 :: rest) ≠ [] := by simp
        have hmap := Chain.last_lender_eq hok hys hne
        have hder : c'.derivedHolder =
            (match (y0 :: rest).getLast? with
              | none => c'.base
              | some eL => eL.borrower) := by
          unfold Chain.derivedHolder
          rw [hc'edges]
        rw [hder]
        cases hl : (y0 :: rest).getLast? with
        | none =>
            simp only [hl, Option.map_none] at hmap
            exact absurd hmap (by simp)
        | some eL =>
            simp only [hl, Option.map_some, Option.some.injEq] at hmap
            exact hmap.symm
  · have h := hids
    rw [hys, List.map_append, List.nodup_append] at h
    rw [hc'edges]
    exact h.1
  · have h := hlends
    rw [hys, List.map_append, List.nodup_append] at h
    rw [hc'edges]
    exact h.1
  · have h := hborrs
    rw [hys, List.map_append, List.nodup_append] at h
    rw [hc'edges]
    exact h.1
  · intro e' he'
    have he'ys : e' ∈ ys := by rw [← hc'edges]; exact he'
    obtain ⟨ha, hlo, hhi, hq, hce⟩ := hres e'
      (by rw [hys]; exact List.mem_append_left _ he'ys)
    exact ⟨by rw [hc'alloc]; exact ha, by rw [hc'lo]; exact hlo,
      by rw [hc'hi]; exact hhi, by rw [hc'q]; exact hq,
      by rw [hc'ceiling]; exact hce⟩
  · intro e' he'
    have he'ys : e' ∈ ys := by rw [← hc'edges]; exact he'
    exact hna e' (by rw [hys]; exact List.mem_append_left _ he'ys)
  · intro i e1 e2 h1 h2
    rw [hc'edges] at h1 h2
    have hi : i < ys.length := (List.getElem?_eq_some_iff.mp h1).1
    have hi2 : i + 1 < ys.length := (List.getElem?_eq_some_iff.mp h2).1
    exact hadj i e1 e2
      (by rw [hys, List.getElem?_append_left hi]; exact h1)
      (by rw [hys, List.getElem?_append_left hi2]; exact h2)
  · intro e' he'
    have he'ys : e' ∈ ys := by rw [← hc'edges]; exact he'
    have he'c : e' ∈ c.edges := by rw [hys]; exact List.mem_append_left _ he'ys
    rcases hsrc e' he'c with hb | ⟨e2, he2, hborr⟩
    · exact Or.inl (by rw [hc'base]; exact hb)
    · refine Or.inr ⟨e2, ?_, hborr⟩
      have he2' : e2 ∈ ys ++ [e] := by rw [← hys]; exact he2
      rcases List.mem_append.mp he2' with hmem | hmem
      · rw [hc'edges]
        exact hmem
      · simp only [List.mem_singleton] at hmem
        subst e2
        exfalso
        apply hholderNot
        rw [hlastE, hborr]
        exact List.mem_map_of_mem (f := (·.lender)) he'c
  · rw [hc'edges]
    cases ys with
    | nil =>
        simp only [List.getLast?_nil]
        have hsingle : c.edges = [e] := by simpa using hys
        rcases hsrc e (by rw [hsingle]; simp) with hb | ⟨e2, he2, hborr⟩
        · rw [hc'holder, hc'base]
          exact hb
        · have he2e : e2 = e := by
            have : e2 ∈ [e] := by rw [← hsingle]; exact he2
            simpa using this
          rw [he2e] at hborr
          exact absurd hborr.symm (hna e (by rw [hsingle]; simp))
    | cons y0 rest =>
        have hne : (y0 :: rest) ≠ [] := by simp
        have hmap : (y0 :: rest).getLast?.map (·.borrower) = some e.lender :=
          Chain.last_lender_eq hok hys hne
        cases hl : (y0 :: rest).getLast? with
        | none =>
            simp only [hl, Option.map_none] at hmap
            exact absurd hmap (by simp)
        | some eL =>
            simp only [hl, Option.map_some, Option.some.injEq] at hmap
            rw [hc'holder]
            exact hmap.symm

/-- The executable return check: there is an innermost edge to pop. -/
def Chain.endCheck (c : Chain) : Bool := !c.edges.isEmpty

/-- Returning through the checked route pops only a nonempty chain. -/
def Chain.end? (c : Chain) : Option Chain :=
  if c.endCheck = true then c.end else none

theorem Chain.end?_sound {c c' : Chain} (h : c.end? = some c') :
    c.end = some c' := by
  unfold Chain.end? at h
  by_cases hc : c.endCheck = true
  · rw [if_pos hc] at h
    exact h
  · rw [if_neg hc] at h
    simp at h

/-- A successful checked return preserves chain validity, given the validity of
the chain it pops. -/
theorem Chain.end?_OK {c c' : Chain} (hok : c.OK) (h : c.end? = some c') :
    c'.OK :=
  Chain.end_OK (Chain.end?_sound h) hok

/-- A delegation moves the whole share to the new borrower; the previous holder
keeps it only if the borrower is the same name. -/
theorem Chain.delegate_conserved (c : Chain) (e : Edge) (D : Nat) :
    (c.begin e).weight D e.borrower = D ∧
    (c.begin e).weight D c.holder = (if c.holder = e.borrower then D else 0) := by
  constructor
  · simp [Chain.weight, Chain.holder_begin]
  · rfl

/-- After a delegation every name other than the borrower carries zero. -/
theorem Chain.delegate_zero_of_ne (c : Chain) (e : Edge) (D : Nat) {x : CapId}
    (hx : x ≠ e.borrower) : (c.begin e).weight D x = 0 := by
  simp [Chain.weight, Chain.holder_begin, hx]

/-- Ending the innermost delegation returns the whole share to the removed
edge's lender. -/
theorem Chain.retract_restores {c c' : Chain} (h : c.end = some c') :
    ∀ (D : Nat) (e : Edge), c.edges.getLast? = some e → c'.weight D e.lender = D := by
  obtain ⟨e0, hlast, hholder⟩ := Chain.holder_end h
  intro D e he
  have hee : e = e0 := by
    rw [he] at hlast
    exact Option.some.inj hlast
  subst hee
  simp [Chain.weight, hholder]

/-- After a return every name other than the restored lender carries zero. -/
theorem Chain.retract_zero_of_ne {c c' : Chain} (h : c.end = some c') :
    ∀ (D : Nat) (e : Edge) {x : CapId}, c.edges.getLast? = some e → x ≠ e.lender →
      c'.weight D x = 0 := by
  obtain ⟨e0, hlast, hholder⟩ := Chain.holder_end h
  intro D e x he hx
  have hee : e = e0 := by
    rw [he] at hlast
    exact Option.some.inj hlast
  subst hee
  simp [Chain.weight, hholder, hx]

end Delegation

end Cap
