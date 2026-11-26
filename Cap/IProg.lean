/-
The indexed program interface: `IProg Γ α Q`.

A program starts with permission context `Γ`, returns `a : α`, and ends with
permissions `Q a`. Context-changing constructors carry their evidence: an
`alloc` cannot be written without freshness, a `splitAt` without the ledger
transition's success, a `free` without the disposal check. Programs whose
operations are stale or refused do not typecheck — they are not programs. This
is the "syntax packaged with a typing derivation" architecture the handoff
selects; an elaborator that derives the evidence (`by decide` at concrete
contexts) is a separate, later layer.

The evaluator takes the realization hypothesis `w.ctx = Γ` and the command
carrier `w.CommandInv`, and is total by fuel (exhaustion is a visible `none`).
Its soundness theorem is:

  evalIProg_post : w.ctx = Γ → evalIProg fuel p w = some (a, w') →
    w'.ctx = Q a ∧ w'.CommandInv

— execution from a world that matches the typing context and satisfies the
command carrier ends in a world matching the postcondition that still carries
well-formedness, the issuance history and loan readiness, for every command in
the language.

Scope and limits: reads are observations of the pure backends; the context
index includes the loan context (`Ctx.loans`), so `beginBorrow`/`endBorrow`
carry the owner, active-leaf, borrower-freshness, loan-freshness and root
liveness evidence as fields. Termination is fuel; the negative/refusal side
lives at the type level (ill-evidenced programs do not exist) rather than as
runtime errors.
-/
import Cap.Unified
import Cap.Runner
import Cap.Access

namespace Cap

/-- An indexed program: context `Γ`, result `α`, postcondition `Q`. -/
inductive IProg : (Γ : Ctx) → (α : Type) → (α → Ctx) → Type 1 where
  | pure (a : α) : IProg Γ α (fun _ => Γ)
  | bind : IProg Γ α Q → ((a : α) → IProg (Q a) β R) → IProg Γ β R
  | read (a : AllocId) (id : CapId) (i : Nat) (h : Ctx.CanRead Γ a id i) :
      IProg Γ (Option UInt8) (fun _ => Γ)
  | write (a : AllocId) (id : CapId) (i : Nat) (v : UInt8)
      (h : Ctx.CanWrite Γ a id i) : IProg Γ Unit (fun _ => Γ)
  | alloc (n : Nat) (rootId disposal : CapId) (pos : 0 < Γ.D)
      (hf : (⟨Γ.nextAlloc⟩ : AllocId) ∉ Γ.owners.map (·.alloc))
      (hfr : rootId ∉ Γ.ids ∧ disposal ∉ Γ.ids ∧ rootId ≠ disposal
             ∧ rootId ∉ Γ.issued ∧ disposal ∉ Γ.issued) :
      IProg Γ AllocId (fun _ => Γ.alloc ⟨Γ.nextAlloc⟩ n pos rootId disposal hf)
  | splitAt (a : AllocId) (id id1 id2 : CapId) (k : Nat) (o : Owner)
      (hfind : Γ.findOwner? a = some o)
      (halloc : ∀ l ∈ Γ.loans.loans, l.alloc ≠ a) (hfids : o.FreshIds id1 id2)
      (hfresh1 : id1 ∉ Γ.ids) (hfresh2 : id2 ∉ Γ.ids)
      (hissued1 : id1 ∉ Γ.issued) (hissued2 : id2 ∉ Γ.issued)
      (hact : ∃ c, o.root.find? id = some c ∧ c.state = .active)
      (hs : (Γ.splitAtOwner? o id id1 id2 k).isSome) :
      IProg Γ Unit (fun _ => { (Γ.splitAtOwner? o id id1 id2 k).getD Γ with
                               issued := id1 :: id2 :: Γ.issued })
  | splitFraction (a : AllocId) (id id1 id2 : CapId) (q1 q2 : Nat)
      (p1 : 0 < q1) (p2 : 0 < q2) (o : Owner)
      (hfind : Γ.findOwner? a = some o)
      (halloc : ∀ l ∈ Γ.loans.loans, l.alloc ≠ a)
      (hfids : o.FreshIds id1 id2)
      (hfresh1 : id1 ∉ Γ.ids) (hfresh2 : id2 ∉ Γ.ids)
      (hissued1 : id1 ∉ Γ.issued) (hissued2 : id2 ∉ Γ.issued)
      (hact : ∃ c, o.root.find? id = some c ∧ c.state = .active)
      (hs : (Γ.splitFractionOwner? o id id1 id2 q1 q2 p1 p2).isSome) :
      IProg Γ Unit (fun _ => { (Γ.splitFractionOwner? o id id1 id2 q1 q2 p1 p2).getD Γ with
                               issued := id1 :: id2 :: Γ.issued })
  | join (a : AllocId) (node newId : CapId) (o : Owner)
      (hfind : Γ.findOwner? a = some o)
      (halloc : ∀ l ∈ Γ.loans.loans, l.alloc ≠ a)
      (hfresh : newId ∉ Γ.ids ∧ newId ∉ Γ.issued)
      (hs : (Γ.joinFractionOwner? o node newId).isSome) :
      IProg Γ Unit (fun _ => { (Γ.joinFractionOwner? o node newId).getD Γ with
                               issued := newId :: Γ.issued })
  | beginBorrow (a : AllocId) (lender borrower : CapId) (loanId : LoanId)
      (o : Owner) (hfind : Γ.findOwner? a = some o)
      (c : Leaf) (hleaf : o.root.find? lender = some c)
      (hact : c.state = .active)
      (hissued : borrower ∉ Γ.issued)
      (hroot : borrower ∉ o.root.ids)
      (hloanFresh : loanId ∉ Γ.loans.loans.map (·.id))
      (hlive : Γ.loans.live LoanCtx.rootLifetime = true)
      (o' : Owner) (hretag : o.retagLeaf? lender borrower = some o') :
      IProg Γ Unit (fun _ => Γ.beginBorrowNext a o o' c lender borrower loanId)
  | endBorrow (a : AllocId) (loanId : LoanId)
      (loan : Loan) (hloan : Γ.loans.findLoan? loanId = some loan)
      (o : Owner) (hfind : Γ.findOwner? a = some o)
      (hnoChild : ∀ l ∈ Γ.loans.loans, l.id ≠ loanId → l.lender ≠ loan.borrower)
      (hdesc : Γ.loans.hasDescendant loan.lifetime = false)
      (o' : Owner) (hretag : o.retagLeaf? loan.borrower loan.lender = some o') :
      IProg Γ Unit (fun _ => Γ.endBorrowNext o o' loan)
  | free (a : AllocId) (d : CapId)
      (halloc : ∀ o, Γ.findOwner? a = some o →
        ∀ l ∈ Γ.loans.loans, l.alloc ≠ a)
      (hloan : ∀ o, Γ.findOwner? a = some o →
        ∀ l ∈ Γ.loans.loans, l.lender ∉ o.ids)
      (h : (Γ.freeWith? a d).isSome) :
      IProg Γ Unit (fun _ => (Γ.freeWith? a d).getD Γ)

/-- A certified write cannot be refused: a matching world supplies the backend
and the ledger guard accepts, so the checked write succeeds. -/
theorem World.write_succeeds {w : World} {Γ : Ctx} {a : AllocId} {id : CapId}
    {i : Nat} {v : UInt8} (h : Ctx.CanWrite Γ a id i) (hΓ : w.ctx = Γ)
    (hwf : w.WellFormed) :
    ∃ w', w.writeChecked a id i v = .ok w' := by
  obtain ⟨o, hfind, hwb⟩ := h
  rw [← hΓ] at hfind hwb
  have hmem : o ∈ w.ctx.owners := List.mem_of_find?_eq_some hfind
  have hown : o.WellFormed w.ctx.D := hwf.1.2.1 o hmem
  obtain ⟨c, hfc, _hact, _hq, _hceil, _hlo, hhi⟩ := Owner.writableB_sound hwb
  have hle : c.hi ≤ o.len := (hown.2.1 id c hfc).2
  obtain ⟨b, hb, hlen⟩ := hwf.2.2 a o hfind
  have hlt : i < b.buf.length := by omega
  unfold World.writeChecked
  simp only [hfind, hb]
  rw [dif_pos hwb]
  unfold Backend.write
  rw [if_pos hlt]
  exact ⟨_, rfl⟩

/-- The fuelled evaluator. The permission evidence in the constructors is a
typing artifact: evaluation re-checks everything at runtime, and the soundness
theorem proves the checks never fire for a well-evidenced program. -/
def evalIProg (fuel : Nat) {Γ : Ctx} {α : Type} {Q : α → Ctx} (p : IProg Γ α Q)
    (w : World) : Option (α × World) :=
  match fuel, p with
  | 0, _ => none
  | fuel + 1, .pure a => some (a, w)
  | fuel + 1, .bind q k =>
    match evalIProg fuel q w with
    | none => none
    | some (a, w') => evalIProg fuel (k a) w'
  | fuel + 1, .read a _ i _ => some ((w.heaps a).bind (·.read i), w)
  | fuel + 1, .write a id i v _ =>
    match w.writeChecked a id i v with
    | .ok w' => some ((), w')
    | .error _ => none
  | fuel + 1, .alloc n rootId disposal _ _ _ =>
    if hpos : 0 < w.ctx.D then
      match w.allocChecked n rootId disposal hpos with
      | .ok w' => some (⟨Γ.nextAlloc⟩, w')
      | .error _ => none
    else none
  | fuel + 1, .splitAt a id id1 id2 k _ _ _ _ _ _ _ _ _ _ =>
    match w.splitAtChecked a id id1 id2 k with
    | .ok w' => some ((), w')
    | .error _ => none
  | fuel + 1, .splitFraction a id id1 id2 q1 q2 p1 p2 _ _ _ _ _ _ _ _ _ _ =>
    match w.splitFractionChecked a id id1 id2 q1 q2 p1 p2 with
    | .ok w' => some ((), w')
    | .error _ => none
  | fuel + 1, .join a node newId _ _ _ _ _ =>
    match w.joinChecked a node newId with
    | .ok w' => some ((), w')
    | .error _ => none
  | fuel + 1, .beginBorrow a lender borrower loanId o hfind c hleaf hact hissued hroot
      hloanFresh hlive o' hretag =>
    match w.beginBorrowChecked a lender borrower loanId with
    | .ok w' => some ((), w')
    | .error _ => none
  | fuel + 1, .endBorrow a loanId loan hloan o hfind hnoChild hdesc o' hretag =>
    match w.endBorrowChecked a loanId with
    | .ok w' => some ((), w')
    | .error _ => none
  | fuel + 1, .free a d _ _ _ =>
    match w.freeChecked a d with
    | .ok w' => some ((), w')
    | .error _ => none

/-- The evaluator's explicit outcome: a completed value and world, fuel
exhaustion, or a refused world check. Refusal is a constructor so that "a typed
program is never refused" is a statement about the machine rather than about a
missing `Option` cause. -/
inductive IOutcome (α : Type) where
  | done (a : α) (w : World)
  | exhausted
  | refused (msg : String)

/-- The evaluator with its outcome made explicit. It differs from `evalIProg`
only in preserving the refusal's message; the completed and exhausted cases
agree. -/
def runIProg (fuel : Nat) {Γ : Ctx} {α : Type} {Q : α → Ctx} (p : IProg Γ α Q)
    (w : World) : IOutcome α :=
  match fuel, p with
  | 0, _ => .exhausted
  | fuel + 1, .pure a => .done a w
  | fuel + 1, .bind q k =>
    match runIProg fuel q w with
    | .done a w' => runIProg fuel (k a) w'
    | .exhausted => .exhausted
    | .refused msg => .refused msg
  | fuel + 1, .read a _ i _ => .done ((w.heaps a).bind (·.read i)) w
  | fuel + 1, .write a id i v _ =>
    match w.writeChecked a id i v with
    | .ok w' => .done () w'
    | .error msg => .refused msg
  | fuel + 1, .alloc n rootId disposal _ _ _ =>
    if hpos : 0 < w.ctx.D then
      match w.allocChecked n rootId disposal hpos with
      | .ok w' => .done (⟨Γ.nextAlloc⟩) w'
      | .error msg => .refused msg
    else .exhausted
  | fuel + 1, .splitAt a id id1 id2 k _ _ _ _ _ _ _ _ _ _ =>
    match w.splitAtChecked a id id1 id2 k with
    | .ok w' => .done () w'
    | .error msg => .refused msg
  | fuel + 1, .splitFraction a id id1 id2 q1 q2 p1 p2 _ _ _ _ _ _ _ _ _ _ =>
    match w.splitFractionChecked a id id1 id2 q1 q2 p1 p2 with
    | .ok w' => .done () w'
    | .error msg => .refused msg
  | fuel + 1, .join a node newId _ _ _ _ _ =>
    match w.joinChecked a node newId with
    | .ok w' => .done () w'
    | .error msg => .refused msg
  | fuel + 1, .beginBorrow a lender borrower loanId o hfind c hleaf hact hissued hroot
      hloanFresh hlive o' hretag =>
    match w.beginBorrowChecked a lender borrower loanId with
    | .ok w' => .done () w'
    | .error msg => .refused msg
  | fuel + 1, .endBorrow a loanId loan hloan o hfind hnoChild hdesc o' hretag =>
    match w.endBorrowChecked a loanId with
    | .ok w' => .done () w'
    | .error msg => .refused msg
  | fuel + 1, .free a d _ _ _ =>
    match w.freeChecked a d with
    | .ok w' => .done () w'
    | .error msg => .refused msg

/-- The `Option` evaluator is the explicit-outcome evaluator with the refusal
cause erased. -/
theorem evalIProg_eq_run (w : World) (fuel : Nat) :
    ∀ {Γ : Ctx} {α : Type} {Q : α → Ctx} (p : IProg Γ α Q),
      evalIProg fuel p w = match runIProg fuel p w with
        | .done a w' => some (a, w')
        | .exhausted => none
        | .refused _ => none := by
  induction fuel generalizing w with
  | zero => intro Γ α Q p; cases p <;> simp [evalIProg, runIProg]
  | succ fuel ih =>
    intro Γ α Q p
    cases p with
    | pure a => rfl
    | bind q k =>
      simp only [evalIProg, runIProg]
      rw [ih w q]
      cases hq : runIProg fuel q w with
      | done a w' => exact ih w' (k a)
      | exhausted => rfl
      | refused msg => rfl
    | read a id i hc => rfl
    | write a id i v hc =>
      simp only [evalIProg, runIProg]
      cases w.writeChecked a id i v <;> rfl
    | alloc n rootId disposal pos hf hfr =>
      simp only [evalIProg, runIProg]
      by_cases hpos : 0 < w.ctx.D
      · simp only [dif_pos hpos]
        cases w.allocChecked n rootId disposal hpos <;> rfl
      · simp only [dif_neg hpos]
    | splitAt a id id1 id2 k o hfind hfids hfresh1 hfresh2 hissued1 hissued2 hact hs =>
      simp only [evalIProg, runIProg]
      cases w.splitAtChecked a id id1 id2 k <;> rfl
    | splitFraction a id id1 id2 q1 q2 p1 p2 _ _ _ _ _ _ _ _ _ =>
      simp only [evalIProg, runIProg]
      cases w.splitFractionChecked a id id1 id2 q1 q2 p1 p2 <;> rfl
    | join a node newId _ _ _ _ =>
      simp only [evalIProg, runIProg]
      cases w.joinChecked a node newId <;> rfl
    | beginBorrow a lender borrower loanId o hfind c hleaf hact hissued hroot hloanFresh
        hlive o' hretag =>
      simp only [evalIProg, runIProg]
      cases w.beginBorrowChecked a lender borrower loanId <;> rfl
    | endBorrow a loanId loan hloan o hfind hnoChild hdesc o' hretag =>
      simp only [evalIProg, runIProg]
      cases w.endBorrowChecked a loanId <;> rfl
    | free a d hloan hs =>
      simp only [evalIProg, runIProg]
      cases w.freeChecked a d <;> rfl

/-- Allocation realises its typed post-context. -/
theorem allocChecked_post {w w' : World} {Γ : Ctx} {n : Nat} {rootId disposal : CapId}
    {pos : 0 < Γ.D} (hf : (⟨Γ.nextAlloc⟩ : AllocId) ∉ Γ.owners.map (·.alloc))
    (hfr : rootId ∉ Γ.ids ∧ disposal ∉ Γ.ids ∧ rootId ≠ disposal
           ∧ rootId ∉ Γ.issued ∧ disposal ∉ Γ.issued)
    (hΓ : w.ctx = Γ) (hpos : 0 < w.ctx.D)
    (hw : w.allocChecked n rootId disposal hpos = .ok w') :
    w'.ctx = Γ.alloc ⟨Γ.nextAlloc⟩ n pos rootId disposal hf := by
  subst Γ
  unfold World.allocChecked at hw
  rw [dif_pos hf, dif_pos hfr] at hw
  cases hw
  rfl

/-- A typed split is never refused: the constructor's evidence discharges every
check the world-level split performs, including historical freshness. This is
the interface-side counterpart of the checker's history check. -/
theorem splitAtChecked_succeeds {w : World} {Γ : Ctx} {a : AllocId}
    {id id1 id2 : CapId} {k : Nat} {o : Owner}
    (hfind : Γ.findOwner? a = some o)
    (halloc : ∀ l ∈ Γ.loans.loans, l.alloc ≠ a) (hfids : o.FreshIds id1 id2)
    (hfresh1 : id1 ∉ Γ.ids) (hfresh2 : id2 ∉ Γ.ids)
    (hissued1 : id1 ∉ Γ.issued) (hissued2 : id2 ∉ Γ.issued)
    (hact : ∃ c, o.root.find? id = some c ∧ c.state = .active)
    (hs : (Γ.splitAtOwner? o id id1 id2 k).isSome)
    (hΓ : w.ctx = Γ) :
    (w.splitAtChecked a id id1 id2 k).isOk = true := by
  unfold World.splitAtChecked
  rw [hΓ]
  simp only [hfind]
  rw [if_pos halloc]
  rw [dif_pos ⟨hfids, hfresh1, hfresh2, hissued1, hissued2, hact⟩]
  split
  · rfl
  · rename_i hnone
    obtain ⟨C', hC'⟩ := Option.isSome_iff_exists.mp hs
    rw [hnone] at hC'
    nomatch hC'

/-- A checked spatial split realises its typed post-context. -/
theorem splitAtChecked_post {w w' : World} {Γ : Ctx} {a : AllocId}
    {id id1 id2 : CapId} {k : Nat} {o : Owner}
    (hfind : Γ.findOwner? a = some o)
    (hs : (Γ.splitAtOwner? o id id1 id2 k).isSome)
    (hΓ : w.ctx = Γ)
    (hw : w.splitAtChecked a id id1 id2 k = .ok w') :
    w'.ctx = { (Γ.splitAtOwner? o id id1 id2 k).getD Γ with
                issued := id1 :: id2 :: Γ.issued } := by
  obtain ⟨o', C', hfo', _, _, _, hs', hw'⟩ := World.splitAtChecked_sound hw
  rw [hΓ] at hfo'
  rw [hfind] at hfo'
  cases hfo'
  rw [hΓ] at hs'
  rw [hw', hΓ]
  show ({ C' with issued := id1 :: id2 :: Γ.issued } : Ctx)
      = { (Γ.splitAtOwner? o id id1 id2 k).getD Γ with issued := id1 :: id2 :: Γ.issued }
  rw [hs']
  rfl

/-- A typed fractional split is never refused: the constructor's evidence
discharges the world-level checks. -/
theorem splitFractionChecked_succeeds {w : World} {Γ : Ctx} {a : AllocId}
    {id id1 id2 : CapId} {q1 q2 : Nat} {p1 : 0 < q1} {p2 : 0 < q2} {o : Owner}
    (hfind : Γ.findOwner? a = some o)
    (halloc : ∀ l ∈ Γ.loans.loans, l.alloc ≠ a) (hfids : o.FreshIds id1 id2)
    (hfresh1 : id1 ∉ Γ.ids) (hfresh2 : id2 ∉ Γ.ids)
    (hissued1 : id1 ∉ Γ.issued) (hissued2 : id2 ∉ Γ.issued)
    (hact : ∃ c, o.root.find? id = some c ∧ c.state = .active)
    (hs : (Γ.splitFractionOwner? o id id1 id2 q1 q2 p1 p2).isSome)
    (hΓ : w.ctx = Γ) :
    (w.splitFractionChecked a id id1 id2 q1 q2 p1 p2).isOk = true := by
  unfold World.splitFractionChecked
  rw [hΓ]
  simp only [hfind]
  rw [if_pos halloc]
  rw [if_pos ⟨hfids, hfresh1, hfresh2, hissued1, hissued2, hact⟩]
  split
  · rfl
  · rename_i hnone
    obtain ⟨C', hC'⟩ := Option.isSome_iff_exists.mp hs
    rw [hnone] at hC'
    nomatch hC'

/-- A checked fractional split realises its typed post-context. -/
theorem splitFractionChecked_post {w w' : World} {Γ : Ctx} {a : AllocId}
    {id id1 id2 : CapId} {q1 q2 : Nat} {p1 : 0 < q1} {p2 : 0 < q2} {o : Owner}
    (hfind : Γ.findOwner? a = some o)
    (halloc : ∀ l ∈ Γ.loans.loans, l.alloc ≠ a) (hΓ : w.ctx = Γ)
    (hw : w.splitFractionChecked a id id1 id2 q1 q2 p1 p2 = .ok w') :
    w'.ctx = { (Γ.splitFractionOwner? o id id1 id2 q1 q2 p1 p2).getD Γ with
                issued := id1 :: id2 :: Γ.issued } := by
  unfold World.splitFractionChecked at hw
  rw [hΓ] at hw
  simp only [hfind] at hw
  rw [if_pos halloc] at hw
  by_cases hfr : o.FreshIds id1 id2 ∧ id1 ∉ Γ.ids ∧ id2 ∉ Γ.ids ∧
      id1 ∉ Γ.issued ∧ id2 ∉ Γ.issued ∧
      (∃ c, o.root.find? id = some c ∧ c.state = .active)
  · rw [if_pos hfr] at hw
    split at hw
    · rename_i C' hs'
      simp only [Except.ok.injEq] at hw
      cases hw
      rw [hs']
      rfl
    · nomatch hw
  · rw [if_neg hfr] at hw
    nomatch hw

/-- A typed fractional join is never refused. -/
theorem joinChecked_succeeds {w : World} {Γ : Ctx} {a : AllocId}
    {node newId : CapId} {o : Owner}
    (hfind : Γ.findOwner? a = some o)
    (halloc : ∀ l ∈ Γ.loans.loans, l.alloc ≠ a)
    (hfresh : newId ∉ Γ.ids ∧ newId ∉ Γ.issued)
    (hs : (Γ.joinFractionOwner? o node newId).isSome)
    (hΓ : w.ctx = Γ) :
    (w.joinChecked a node newId).isOk = true := by
  unfold World.joinChecked
  rw [hΓ]
  simp only [hfind]
  rw [if_pos halloc]
  rw [if_pos hfresh]
  split
  · rfl
  · rename_i hnone
    obtain ⟨C', hC'⟩ := Option.isSome_iff_exists.mp hs
    rw [hnone] at hC'
    nomatch hC'

/-- A checked fractional join realises its typed post-context. -/
theorem joinChecked_post {w w' : World} {Γ : Ctx} {a : AllocId}
    {node newId : CapId} {o : Owner}
    (hfind : Γ.findOwner? a = some o)
    (halloc : ∀ l ∈ Γ.loans.loans, l.alloc ≠ a) (hΓ : w.ctx = Γ)
    (hw : w.joinChecked a node newId = .ok w') :
    w'.ctx = { (Γ.joinFractionOwner? o node newId).getD Γ with
                issued := newId :: Γ.issued } := by
  unfold World.joinChecked at hw
  rw [hΓ] at hw
  simp only [hfind] at hw
  rw [if_pos halloc] at hw
  by_cases hfresh : newId ∉ Γ.ids ∧ newId ∉ Γ.issued
  · rw [if_pos hfresh] at hw
    split at hw
    · rename_i C' hs'
      simp only [Except.ok.injEq] at hw
      cases hw
      rw [hs']
      rfl
    · nomatch hw
  · rw [if_neg hfresh] at hw
    nomatch hw

/-- The typed borrow evidence drives `Ctx.beginBorrow?` to the exact transition
the constructor's postcondition names. -/
theorem Ctx.beginBorrow?_eq_next {C : Ctx} {a : AllocId} {lender borrower : CapId}
    {loanId : LoanId} {o : Owner} (hfind : C.findOwner? a = some o)
    {c : Leaf} (hleaf : o.root.find? lender = some c) (hact : c.state = .active)
    (hissued : borrower ∉ C.issued) (hroot : borrower ∉ o.root.ids)
    (hloanFresh : loanId ∉ C.loans.loans.map (·.id))
    (hlive : C.loans.live LoanCtx.rootLifetime = true)
    {o' : Owner} (hretag : o.retagLeaf? lender borrower = some o') :
    C.beginBorrow? a lender borrower loanId
      = .ok (C.beginBorrowNext a o o' c lender borrower loanId) := by
  have ho' : o' = { o with root := o.root.retag lender borrower } := by
    unfold Owner.retagLeaf? at hretag
    rw [hleaf] at hretag
    simp only at hretag
    rw [if_pos hact, if_pos hroot] at hretag
    exact (Option.some.inj hretag).symm
  have hrf : o.retagLeafFind? lender borrower = some (o', c) := by
    unfold Owner.retagLeafFind?
    rw [hleaf]
    simp only []
    rw [if_pos hact, if_pos hroot, ho']
  unfold Ctx.beginBorrow?
  rw [hfind]
  simp only []
  rw [hrf]
  simp only []
  rw [if_neg hissued, if_neg hroot, if_neg hloanFresh, if_pos hlive]

/-- The typed return evidence drives `Ctx.endBorrow?` to the exact transition
the constructor's postcondition names. -/
theorem Ctx.endBorrow?_eq_next {C : Ctx} {a : AllocId} {loanId : LoanId} {loan : Loan}
    (hloan : C.loans.findLoan? loanId = some loan)
    {o : Owner} (hfind : C.findOwner? a = some o)
    (hnoChild : ∀ l ∈ C.loans.loans, l.id ≠ loanId → l.lender ≠ loan.borrower)
    (hdesc : C.loans.hasDescendant loan.lifetime = false)
    {o' : Owner} (hretag : o.retagLeaf? loan.borrower loan.lender = some o') :
    C.endBorrow? a loanId = .ok (C.endBorrowNext o o' loan) := by
  have hno : ¬ ∃ l ∈ C.loans.loans, l.id ≠ loanId ∧ l.lender = loan.borrower := by
    rintro ⟨l, hl, hid, hle⟩
    exact hnoChild l hl hid hle
  unfold Ctx.endBorrow?
  rw [hloan, hfind]
  simp only []
  rw [if_neg hno]
  rw [if_neg (by simp [hdesc])]
  rw [hretag]

/-- A typed borrow is never refused. -/
theorem beginBorrowChecked_succeeds {w : World} {Γ : Ctx} {a : AllocId}
    {lender borrower : CapId} {loanId : LoanId} {o : Owner}
    (hfind : Γ.findOwner? a = some o) {c : Leaf}
    (hleaf : o.root.find? lender = some c) (hact : c.state = .active)
    (hissued : borrower ∉ Γ.issued) (hroot : borrower ∉ o.root.ids)
    (hloanFresh : loanId ∉ Γ.loans.loans.map (·.id))
    (hlive : Γ.loans.live LoanCtx.rootLifetime = true) {o' : Owner}
    (hretag : o.retagLeaf? lender borrower = some o') (hΓ : w.ctx = Γ) :
    (w.beginBorrowChecked a lender borrower loanId).isOk = true := by
  unfold World.beginBorrowChecked
  rw [hΓ, Ctx.beginBorrow?_eq_next hfind hleaf hact hissued hroot hloanFresh hlive hretag]
  rfl

/-- A checked borrow realises its typed post-context. -/
theorem beginBorrowChecked_post {w w' : World} {Γ : Ctx} {a : AllocId}
    {lender borrower : CapId} {loanId : LoanId} {o : Owner}
    (hfind : Γ.findOwner? a = some o) {c : Leaf}
    (hleaf : o.root.find? lender = some c) (hact : c.state = .active)
    (hissued : borrower ∉ Γ.issued) (hroot : borrower ∉ o.root.ids)
    (hloanFresh : loanId ∉ Γ.loans.loans.map (·.id))
    (hlive : Γ.loans.live LoanCtx.rootLifetime = true) {o' : Owner}
    (hretag : o.retagLeaf? lender borrower = some o') (hΓ : w.ctx = Γ)
    (hw : w.beginBorrowChecked a lender borrower loanId = .ok w') :
    w'.ctx = Γ.beginBorrowNext a o o' c lender borrower loanId := by
  obtain ⟨C, hC, hw'⟩ := World.beginBorrowChecked_sound hw
  rw [hΓ] at hC
  rw [Ctx.beginBorrow?_eq_next hfind hleaf hact hissued hroot hloanFresh hlive hretag] at hC
  cases hC
  rw [hw']

/-- A typed return is never refused. -/
theorem endBorrowChecked_succeeds {w : World} {Γ : Ctx} {a : AllocId}
    {loanId : LoanId} {loan : Loan}
    (hloan : Γ.loans.findLoan? loanId = some loan)
    {o : Owner} (hfind : Γ.findOwner? a = some o)
    (hnoChild : ∀ l ∈ Γ.loans.loans, l.id ≠ loanId → l.lender ≠ loan.borrower)
    (hdesc : Γ.loans.hasDescendant loan.lifetime = false)
    {o' : Owner} (hretag : o.retagLeaf? loan.borrower loan.lender = some o')
    (hΓ : w.ctx = Γ) :
    (w.endBorrowChecked a loanId).isOk = true := by
  unfold World.endBorrowChecked
  rw [hΓ, Ctx.endBorrow?_eq_next hloan hfind hnoChild hdesc hretag]
  rfl

/-- A checked return realises its typed post-context. -/
theorem endBorrowChecked_post {w w' : World} {Γ : Ctx} {a : AllocId}
    {loanId : LoanId} {loan : Loan}
    (hloan : Γ.loans.findLoan? loanId = some loan)
    {o : Owner} (hfind : Γ.findOwner? a = some o)
    (hnoChild : ∀ l ∈ Γ.loans.loans, l.id ≠ loanId → l.lender ≠ loan.borrower)
    (hdesc : Γ.loans.hasDescendant loan.lifetime = false)
    {o' : Owner} (hretag : o.retagLeaf? loan.borrower loan.lender = some o')
    (hΓ : w.ctx = Γ) (hw : w.endBorrowChecked a loanId = .ok w') :
    w'.ctx = Γ.endBorrowNext o o' loan := by
  obtain ⟨C, hC, hw'⟩ := World.endBorrowChecked_sound hw
  rw [hΓ] at hC
  rw [Ctx.endBorrow?_eq_next hloan hfind hnoChild hdesc hretag] at hC
  cases hC
  rw [hw']

/-- A checked disposal realises its typed post-context. -/
theorem freeChecked_post {w w' : World} {Γ : Ctx} {a : AllocId} {d : CapId}
    (halloc : ∀ o, Γ.findOwner? a = some o →
      ∀ l ∈ Γ.loans.loans, l.alloc ≠ a)
    (hloan : ∀ o, Γ.findOwner? a = some o →
      ∀ l ∈ Γ.loans.loans, l.lender ∉ o.ids)
    (hs : (Γ.freeWith? a d).isSome) (hΓ : w.ctx = Γ)
    (hw : w.freeChecked a d = .ok w') :
    w'.ctx = (Γ.freeWith? a d).getD Γ := by
  unfold World.freeChecked at hw
  split at hw
  · simp at hw
  · rename_i o hfind
    split at hw
    · rename_i hok
      split at hw
      · rename_i hok2
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
            rw [hΓ] at hc
            rw [hc]
            rfl
      · simp at hw
    · simp at hw

/-- Soundness: execution from a world matching the typing context and carrying
the command invariant ends in a world matching the postcondition that still
carries it. -/
theorem evalIProg_post (w : World) (fuel : Nat) :
    ∀ {Γ : Ctx} {α : Type} {Q : α → Ctx} (p : IProg Γ α Q) {a : α} {w' : World},
      w.ctx = Γ → evalIProg fuel p w = some (a, w') → w.CommandInv →
      w'.ctx = Q a ∧ w'.CommandInv := by
  induction fuel generalizing w with
  | zero => intro Γ α Q p a w' hΓ h hinv; simp [evalIProg] at h
  | succ fuel ih =>
    intro Γ α Q p a w' hΓ h hinv
    obtain ⟨hwf, hh, hlr⟩ := hinv
    cases p with
    | pure a' =>
      simp only [evalIProg] at h
      obtain ⟨rfl, rfl⟩ := Option.some.inj h
      exact ⟨hΓ, ⟨hwf, hh, hlr⟩⟩
    | bind q k =>
      cases hq : evalIProg fuel q w with
      | none =>
        simp only [evalIProg, hq] at h
        nomatch h
      | some r =>
        obtain ⟨a1, w1⟩ := r
        simp only [evalIProg, hq] at h
        obtain ⟨hctx1, hinv1⟩ := ih w q hΓ hq ⟨hwf, hh, hlr⟩
        exact ih w1 (k a1) hctx1 h hinv1
    | read a0 id0 i0 hc =>
      simp only [evalIProg] at h
      obtain ⟨-, rfl⟩ := Option.some.inj h
      exact ⟨hΓ, ⟨hwf, hh, hlr⟩⟩
    | write a0 id0 i0 v0 hc =>
      cases hw : w.writeChecked a0 id0 i0 v0 with
      | error e =>
        obtain ⟨w1, hok⟩ := World.write_succeeds hc hΓ hwf
        rw [hw] at hok
        nomatch hok
      | ok w1 =>
        simp only [evalIProg, hw] at h
        obtain ⟨-, rfl⟩ := Option.some.inj h
        obtain ⟨_, _, _, _, _, _, _, hctx, _⟩ := World.writeChecked_sound hw
        exact ⟨hctx.trans hΓ, ⟨World.writeChecked_wf hw hwf,
          World.historyOK_write hw hh, World.loansReady_writeChecked hw hlr⟩⟩
    | alloc n rootId disposal pos hf hfr =>
      by_cases hpos : 0 < w.ctx.D
      · cases hw : w.allocChecked n rootId disposal hpos with
        | error e =>
          simp only [evalIProg, hpos, hw] at h
          nomatch h
        | ok w1 =>
          simp only [evalIProg, hpos, hw] at h
          obtain ⟨-, rfl⟩ := Option.some.inj h
          -- w1.ctx = w.ctx.alloc ⟨w.ctx.nextAlloc⟩ n hpos rootId disposal _
          exact ⟨allocChecked_post hf hfr hΓ hpos hw, ⟨World.allocChecked_wf hw hwf,
            World.historyOK_allocChecked hw hh, World.loansReady_allocChecked hw hlr⟩⟩
      · simp only [evalIProg, hpos] at h
        nomatch h
    | splitAt a0 id0 id1 id2 k o hfind halloc hfids hfresh1 hfresh2 hissued1 hissued2 hact hs =>
      cases hw : w.splitAtChecked a0 id0 id1 id2 k with
      | error e =>
        simp only [evalIProg, hw] at h
        nomatch h
      | ok w1 =>
        simp only [evalIProg, hw] at h
        obtain ⟨-, rfl⟩ := Option.some.inj h
        exact ⟨splitAtChecked_post hfind hs hΓ hw, ⟨World.splitAtChecked_wf hw hwf,
          World.historyOK_splitAtChecked hw hwf hh,
          World.loansReady_splitAtChecked hw hwf hlr⟩⟩
    | splitFraction a0 id0 id1 id2 q1 q2 p1 p2 o hfind halloc hfids hf1 hf2 hi1 hi2 hact hs =>
      cases hw : w.splitFractionChecked a0 id0 id1 id2 q1 q2 p1 p2 with
      | error e =>
        simp only [evalIProg, hw] at h
        nomatch h
      | ok w1 =>
        simp only [evalIProg, hw] at h
        obtain ⟨-, rfl⟩ := Option.some.inj h
        exact ⟨splitFractionChecked_post hfind halloc hΓ hw,
          ⟨World.splitFractionChecked_wf hw hwf,
            World.historyOK_splitFractionChecked hw hwf hh,
            World.loansReady_splitFractionChecked hw hwf hlr⟩⟩
    | join a0 node newId o hfind halloc hfresh hs =>
      cases hw : w.joinChecked a0 node newId with
      | error e =>
        simp only [evalIProg, hw] at h
        nomatch h
      | ok w1 =>
        simp only [evalIProg, hw] at h
        obtain ⟨-, rfl⟩ := Option.some.inj h
        exact ⟨joinChecked_post hfind halloc hΓ hw, ⟨World.joinChecked_wf hw hwf,
          World.historyOK_joinChecked hw hh, World.loansReady_joinChecked hw hlr⟩⟩
    | beginBorrow a0 lender borrower loanId o hfind c hleaf hact hissued hroot hloanFresh
        hlive o' hretag =>
      cases hw : w.beginBorrowChecked a0 lender borrower loanId with
      | error e =>
        simp only [evalIProg, hw] at h
        nomatch h
      | ok w1 =>
        simp only [evalIProg, hw] at h
        obtain ⟨-, rfl⟩ := Option.some.inj h
        exact ⟨beginBorrowChecked_post hfind hleaf hact hissued hroot hloanFresh hlive
            hretag hΓ hw,
          ⟨World.beginBorrowChecked_wf hw ⟨hwf, hh, hlr⟩,
            World.historyOK_beginBorrow hw hh,
            World.loansReady_beginBorrow hw ⟨hwf, hh, hlr⟩⟩⟩
    | endBorrow a0 loanId loan hloan o hfind hnoChild hdesc o' hretag =>
      cases hw : w.endBorrowChecked a0 loanId with
      | error e =>
        simp only [evalIProg, hw] at h
        nomatch h
      | ok w1 =>
        simp only [evalIProg, hw] at h
        obtain ⟨-, rfl⟩ := Option.some.inj h
        exact ⟨endBorrowChecked_post hloan hfind hnoChild hdesc hretag hΓ hw,
          ⟨World.endBorrowChecked_wf hw ⟨hwf, hh, hlr⟩,
            World.historyOK_endBorrow hw hh hlr,
            World.loansReady_endBorrow hw hlr⟩⟩
    | free a0 d halloc hloan hs =>
      cases hw : w.freeChecked a0 d with
      | error e =>
        simp only [evalIProg, hw] at h
        nomatch h
      | ok w1 =>
        simp only [evalIProg, hw] at h
        obtain ⟨-, rfl⟩ := Option.some.inj h
        exact ⟨freeChecked_post halloc hloan hs hΓ hw, ⟨World.freeChecked_wf hw hwf,
          World.historyOK_freeChecked hw hh, World.loansReady_freeChecked hw hlr⟩⟩

/-- A typed program is never refused. From a matching world satisfying the
invariant, the explicit evaluator either completes or exhausts its fuel; every
world check a command performs is discharged by that command's own typing
evidence (`World.write_succeeds`, `World.allocChecked_succeeds`,
`splitAtChecked_succeeds`, `World.freeChecked_succeeds`). -/
theorem runIProg_no_refusal (w : World) (fuel : Nat) :
    ∀ {Γ : Ctx} {α : Type} {Q : α → Ctx} (p : IProg Γ α Q),
      w.ctx = Γ → w.CommandInv → ∀ msg, runIProg fuel p w ≠ .refused msg := by
  induction fuel generalizing w with
  | zero =>
    intro Γ α Q p hΓ hinv msg h
    cases h
  | succ fuel ih =>
    intro Γ α Q p hΓ hinv msg h
    obtain ⟨hwf, hh, hlr⟩ := hinv
    cases p with
    | pure a => cases h
    | read a id i hc => cases h
    | bind q k =>
      simp only [runIProg] at h
      cases hq : runIProg fuel q w with
      | done a w1 =>
        simp only [hq] at h
        have hsome : evalIProg fuel q w = some (a, w1) := by
          rw [evalIProg_eq_run w fuel q, hq]
        obtain ⟨hctx1, hinv1⟩ := evalIProg_post w fuel q hΓ hsome ⟨hwf, hh, hlr⟩
        exact ih w1 (k a) hctx1 hinv1 msg h
      | exhausted =>
        simp only [hq] at h
        cases h
      | refused mq =>
        exact absurd hq (ih w q hΓ ⟨hwf, hh, hlr⟩ mq)
    | write a id i v hc =>
      simp only [runIProg] at h
      cases hw : w.writeChecked a id i v with
      | error e =>
        simp only [hw] at h
        obtain ⟨w1, hok⟩ := World.write_succeeds hc hΓ hwf
        rw [hw] at hok
        nomatch hok
      | ok w1 =>
        simp only [hw] at h
        cases h
    | alloc n rootId disposal pos hf hfr =>
      simp only [runIProg] at h
      by_cases hpos : 0 < w.ctx.D
      · simp only [dif_pos hpos] at h
        cases ha : w.allocChecked n rootId disposal hpos with
        | error e =>
          simp only [ha] at h
          have hok := World.allocChecked_succeeds (w := w) (n := n) (rootId := rootId)
            (disposal := disposal) (po := hpos) (hΓ.symm ▸ hf) (hΓ.symm ▸ hfr)
          rw [ha] at hok
          cases hok
        | ok w1 =>
          simp only [ha] at h
          cases h
      · simp only [dif_neg hpos] at h
        cases h
    | splitAt a id id1 id2 k o hfind halloc hfids hfresh1 hfresh2 hissued1 hissued2 hact hs =>
      simp only [runIProg] at h
      cases hw : w.splitAtChecked a id id1 id2 k with
      | error e =>
        simp only [hw] at h
        have hok := splitAtChecked_succeeds hfind halloc hfids hfresh1 hfresh2
          hissued1 hissued2 hact hs hΓ
        rw [hw] at hok
        cases hok
      | ok w1 =>
        simp only [hw] at h
        cases h
    | splitFraction a id id1 id2 q1 q2 p1 p2 o hfind halloc hfids hf1 hf2 hi1 hi2 hact hs =>
      simp only [runIProg] at h
      cases hw : w.splitFractionChecked a id id1 id2 q1 q2 p1 p2 with
      | error e =>
        simp only [hw] at h
        have hok := splitFractionChecked_succeeds hfind halloc hfids hf1 hf2 hi1 hi2 hact hs hΓ
        rw [hw] at hok
        cases hok
      | ok w1 =>
        simp only [hw] at h
        cases h
    | join a node newId o hfind halloc hfresh hs =>
      simp only [runIProg] at h
      cases hw : w.joinChecked a node newId with
      | error e =>
        simp only [hw] at h
        have hok := joinChecked_succeeds hfind halloc hfresh hs hΓ
        rw [hw] at hok
        cases hok
      | ok w1 =>
        simp only [hw] at h
        cases h
    | beginBorrow a lender borrower loanId o hfind c hleaf hact hissued hroot hloanFresh
        hlive o' hretag =>
      simp only [runIProg] at h
      cases hw : w.beginBorrowChecked a lender borrower loanId with
      | error e =>
        simp only [hw] at h
        have hok := beginBorrowChecked_succeeds hfind hleaf hact hissued hroot hloanFresh
          hlive hretag hΓ
        rw [hw] at hok
        cases hok
      | ok w1 =>
        simp only [hw] at h
        cases h
    | endBorrow a loanId loan hloan o hfind hnoChild hdesc o' hretag =>
      simp only [runIProg] at h
      cases hw : w.endBorrowChecked a loanId with
      | error e =>
        simp only [hw] at h
        have hok := endBorrowChecked_succeeds hloan hfind hnoChild hdesc hretag hΓ
        rw [hw] at hok
        cases hok
      | ok w1 =>
        simp only [hw] at h
        cases h
    | free a d halloc hloan hs =>
      simp only [runIProg] at h
      cases hw : w.freeChecked a d with
      | error e =>
        simp only [hw] at h
        have hs' : (w.ctx.freeWith? a d).isSome = true := by
          rw [hΓ]
          exact hs
        have halloc' : ∀ o, w.ctx.findOwner? a = some o →
            ∀ l ∈ w.ctx.loans.loans, l.alloc ≠ a := by
          intro o ho l hl
          rw [hΓ] at ho hl
          exact halloc o ho l hl
        have hloan' : ∀ o, w.ctx.findOwner? a = some o →
            ∀ l ∈ w.ctx.loans.loans, l.lender ∉ o.ids := by
          intro o ho l hl
          rw [hΓ] at ho hl
          exact hloan o ho l hl
        have hsW : (w.freeWith? a d).isSome = true := by
          cases hc : w.ctx.freeWith? a d with
          | none =>
            rw [hc] at hs'
            cases hs'
          | some ctx' => simp [World.freeWith?, hc]
        have hok := World.freeChecked_succeeds (w := w) (a := a) (d := d) hsW halloc' hloan'
        rw [hw] at hok
        cases hok
      | ok w1 =>
        simp only [hw] at h
        cases h

/-- The context after allocating the 4-byte owner. -/
def ilCtx1 : Ctx :=
  uWorld.ctx.alloc ⟨uWorld.ctx.nextAlloc⟩ 4 (by decide) ⟨3⟩ ⟨4⟩ (by decide)

/-- The context after the spatial split. -/
def ilCtx3 : Ctx :=
  { (ilCtx1.splitAtOwner? (Owner.init ⟨1⟩ 4 64 (by decide) ⟨3⟩ ⟨4⟩) ⟨3⟩ ⟨5⟩ ⟨6⟩ 2).getD ilCtx1 with
    issued := ⟨5⟩ :: ⟨6⟩ :: ilCtx1.issued }

/-- The context after disposal. -/
def ilCtx5 : Ctx := (ilCtx3.freeWith? ⟨1⟩ ⟨4⟩).getD ilCtx3

theorem ilCtx3_loans : ilCtx3.loans.loans = [] := by
  unfold ilCtx3
  cases h : ilCtx1.splitAtOwner? (Owner.init ⟨1⟩ 4 64 (by decide) ⟨3⟩ ⟨4⟩) ⟨3⟩ ⟨5⟩ ⟨6⟩ 2
  · show ilCtx1.loans.loans = []
    rw [show ilCtx1.loans = uWorld.ctx.loans from rfl]
    rfl
  · unfold Ctx.splitAtOwner? at h
    cases ho : (Owner.init ⟨1⟩ 4 64 (by decide) ⟨3⟩ ⟨4⟩).splitAt? ⟨3⟩ ⟨5⟩ ⟨6⟩ 2 with
    | none => simp [ho] at h
    | some o' =>
      simp only [ho, Option.map_some, Option.some.injEq] at h
      subst h
      show (Ctx.update ilCtx1 ⟨1⟩ o').loans.loans = []
      rw [show (Ctx.update ilCtx1 ⟨1⟩ o').loans = ilCtx1.loans from rfl]
      rw [show ilCtx1.loans = uWorld.ctx.loans from rfl]
      rfl

def iAlloc : IProg uWorld.ctx AllocId (fun _ => ilCtx1) :=
  .alloc 4 ⟨3⟩ ⟨4⟩ (by decide) (by decide) (by decide)

/-- The first write. -/
def iWrite1 : IProg ilCtx1 Unit (fun _ => ilCtx1) :=
  .write ⟨1⟩ ⟨3⟩ 0 7 (by exact ⟨_, rfl, by decide⟩)

/-- The spatial split. -/
def iSplit : IProg ilCtx1 Unit (fun _ => ilCtx3) :=
  .splitAt ⟨1⟩ ⟨3⟩ ⟨5⟩ ⟨6⟩ 2 (Owner.init ⟨1⟩ 4 64 (by decide) ⟨3⟩ ⟨4⟩)
    (by rfl) (by intro l hl; rw [show ilCtx1.loans.loans = [] from rfl] at hl; cases hl) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by exact ⟨_, rfl, by decide⟩) (by decide)

/-- The write through the left half. -/
def iWrite2 : IProg ilCtx3 Unit (fun _ => ilCtx3) :=
  .write ⟨1⟩ ⟨5⟩ 0 8 (by exact ⟨_, rfl, by decide⟩)

/-- The disposal step. -/
def iFree : IProg ilCtx3 Unit (fun _ => ilCtx5) :=
  @IProg.free ilCtx3 ⟨1⟩ ⟨4⟩
    (by intro o _ l hl; rw [ilCtx3_loans] at hl; exact absurd hl (by simp))
    (by intro o _ l hl; rw [ilCtx3_loans] at hl; exact absurd hl (by simp))
    (by decide)

/-- The owner allocated at the start of the concrete context. -/
def ilOwner : Owner := Owner.init ⟨1⟩ 4 64 (by decide) ⟨3⟩ ⟨4⟩

/-- The context after splitting the root leaf fractionally into shares 32+32. -/
def ilFracCtx0 : Ctx :=
  (ilCtx1.splitFractionOwner? ilOwner ⟨3⟩ ⟨7⟩ ⟨8⟩ 32 32 (by decide) (by decide)).getD ilCtx1

/-- The owner in that context. -/
def ilFracOwner : Owner := (ilFracCtx0.findOwner? ⟨1⟩).getD ilOwner

/-- The context after joining the two fractional children. -/
def ilJoinCtx0 : Ctx :=
  (ilFracCtx0.joinFractionOwner? ilFracOwner ⟨7⟩ ⟨9⟩).getD ilFracCtx0

/-- The posted context of the fractional split. -/
def ilCtxFrac : Ctx :=
  { ilFracCtx0 with issued := ⟨7⟩ :: ⟨8⟩ :: ilCtx1.issued }

/-- The posted context of the join. -/
def ilCtxJoin : Ctx :=
  { ilJoinCtx0 with issued := ⟨9⟩ :: ilCtxFrac.issued }

/-- The fractional split of the allocated leaf. -/
def iFracSplit : IProg ilCtx1 Unit (fun _ => ilCtxFrac) :=
  .splitFraction ⟨1⟩ ⟨3⟩ ⟨7⟩ ⟨8⟩ 32 32 (by decide) (by decide) ilOwner
    (by rfl) (by intro l hl; rw [show ilCtx1.loans.loans = [] from rfl] at hl; cases hl) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by exact ⟨_, rfl, by decide⟩) (by decide)

/-- The fractional join of the two children. -/
def iJoin : IProg ilCtxFrac Unit (fun _ => ilCtxJoin) :=
  .join ⟨1⟩ ⟨7⟩ ⟨9⟩ ilFracOwner (by rfl)
    (by intro l hl; rw [show ilCtxFrac.loans.loans = [] from rfl] at hl; cases hl)
    (by decide) (by decide)

/-- Allocation, fractional split and join, all with evidence. -/
def iFracLifecycle : IProg uWorld.ctx Unit (fun _ => ilCtxJoin) :=
  .bind iAlloc fun _ =>
  .bind iFracSplit fun _ =>
  .bind iJoin fun _ =>
  .pure ()

/-- The fractional lifecycle's evaluator accepts it. -/
theorem iFracLifecycle_ok :
    (evalIProg 64 iFracLifecycle uWorld).isSome = true := by
  decide

/-- The active whole-share leaf the fixture's borrow starts from. -/
def ilRootLeaf : Leaf :=
  { id := ⟨3⟩, alloc := ⟨1⟩, lo := 0, hi := 4, ordered := by decide, q := 64,
    pos := by decide, ceiling := .readWrite, state := .active }

/-- The owner after retagging the lender's active leaf to the borrower's fresh
identity. -/
def ilBorrowed : Owner :=
  { ilOwner with root := ilOwner.root.retag ⟨3⟩ ⟨5⟩ }

/-- The loan record the begun borrow inserts: the borrower's lifetime is the
freshly minted one, and the chain base and resource description come from the
retagged leaf. -/
def ilLoan : Loan :=
  { id := ⟨10⟩, alloc := ⟨1⟩, base := ⟨3⟩, lender := ⟨3⟩, borrower := ⟨5⟩,
    lifetime := ⟨1⟩, lo := 0, hi := 4, q := 64, ceiling := .readWrite }

/-- The context after beginning the borrow. -/
def ilCtxLoan : Ctx :=
  ilCtx1.beginBorrowNext ⟨1⟩ ilOwner ilBorrowed ilRootLeaf ⟨3⟩ ⟨5⟩ ⟨10⟩

/-- The owner after returning the borrow: the borrower's name retags back to the
lender's. -/
def ilRestored : Owner :=
  { ilBorrowed with root := ilBorrowed.root.retag ⟨5⟩ ⟨3⟩ }

/-- The context after ending the borrow. -/
def ilCtxEnd : Ctx :=
  ilCtxLoan.endBorrowNext ilBorrowed ilRestored ilLoan

/-- The begin command with its context-level evidence. -/
def iBegin : IProg ilCtx1 Unit (fun _ => ilCtxLoan) :=
  @IProg.beginBorrow ilCtx1 ⟨1⟩ ⟨3⟩ ⟨5⟩ ⟨10⟩ ilOwner (by rfl)
    ilRootLeaf (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide)
    ilBorrowed (by rfl)

/-- The end command with its context-level evidence. -/
def iEnd : IProg ilCtxLoan Unit (fun _ => ilCtxEnd) :=
  @IProg.endBorrow ilCtxLoan ⟨1⟩ ⟨10⟩ ilLoan (by rfl) ilBorrowed (by rfl)
    (by
      intro l hl hid
      rw [show ilCtxLoan.loans.loans = [ilLoan] from rfl] at hl
      simp only [List.mem_singleton] at hl
      subst hl
      decide)
    (by decide) ilRestored (by rfl)

/-- Allocation, loan beginning and loan ending. -/
def iLoanLifecycle : IProg uWorld.ctx Unit (fun _ => ilCtxEnd) :=
  .bind iAlloc fun _ =>
  .bind iBegin fun _ =>
  .bind iEnd fun _ =>
  .pure ()

/-- The loan lifecycle's evaluator accepts it. -/
theorem iLoanLifecycle_ok :
    (evalIProg 64 iLoanLifecycle uWorld).isSome = true := by
  decide

/-- The indexed lifecycle, composed by `bind` with each stage's evidence. -/
def iLifecycle : IProg uWorld.ctx Unit (fun _ => ilCtx5) :=
  .bind iAlloc fun _ =>
  .bind iWrite1 fun _ =>
  .bind iSplit fun _ =>
  .bind iWrite2 fun _ =>
  .bind iFree fun _ =>
  .pure ()

/-- The indexed lifecycle is accepted. -/
theorem iLifecycle_ok : (evalIProg 64 iLifecycle uWorld).isSome = true := by
  decide

/-- The indexed lifecycle leaves the pre-existing 64-byte backend untouched. -/
theorem iLifecycle_snapshot :
    (evalIProg 64 iLifecycle uWorld).map
      (fun r => (r.2.heaps ⟨0⟩).map (·.buf)) = some (some (List.replicate 64 0)) := by
  decide

/-- The indexed lifecycle's final world is well formed. -/
theorem iLifecycle_sound {w' : World}
    (h : evalIProg 64 iLifecycle uWorld = some ((), w')) : w'.WellFormed :=
  (evalIProg_post uWorld 64 iLifecycle rfl h uWorld_commandInv).2.1

/-- The final context is the postcondition the type says it is. -/
theorem iLifecycle_ctx {w' : World}
    (h : evalIProg 64 iLifecycle uWorld = some ((), w')) : w'.ctx = ilCtx5 :=
  (evalIProg_post uWorld 64 iLifecycle rfl h uWorld_commandInv).1

/-- A split reusing the parent capability as a child id is not a program: the
freshness evidence is uninhabited. -/
theorem stale_child_refused :
    ¬ (Owner.init ⟨1⟩ 4 64 (by decide) ⟨3⟩ ⟨4⟩).FreshIds ⟨3⟩ ⟨5⟩ := by
  decide

/-- The empty world carries the command invariant. -/
theorem emptyWorld_commandInv : World.emptyWorld.CommandInv :=
  ⟨World.emptyWorld_wf, World.emptyWorld_historyOK, Ctx.loansReady_of_loans_nil rfl⟩

/-- The context after allocating the closed program's 4-byte owner. -/
def icCtx1 : Ctx :=
  World.emptyWorld.ctx.alloc ⟨0⟩ 4 (by decide) ⟨1⟩ ⟨2⟩ (by decide)

/-- The context after disposing it: no owners remain, fresh-id history is kept. -/
theorem icCtx1_loans : icCtx1.loans.loans = [] := by
  show uWorld.ctx.loans.loans = []
  rfl

def icCtx3 : Ctx := (icCtx1.freeWith? ⟨0⟩ ⟨2⟩).getD icCtx1

/-- A closed program: allocate a 4-byte owner, write, dispose. Its typed
post-context has no owners. -/
def iClosed : IProg World.emptyWorld.ctx Unit (fun _ => icCtx3) :=
  .bind (.alloc 4 ⟨1⟩ ⟨2⟩ (by decide) (by decide) (by decide)) fun _ =>
  .bind (.write ⟨0⟩ ⟨1⟩ 0 7 (by exact ⟨_, rfl, by decide⟩)) fun _ =>
  .bind (@IProg.free icCtx1 ⟨0⟩ ⟨2⟩
    (by intro o _ l hl; rw [icCtx1_loans] at hl; exact absurd hl (by simp))
    (by intro o _ l hl; rw [icCtx1_loans] at hl; exact absurd hl (by simp))
    (by decide)) fun _ =>
  .pure ()

/-- The closed program is accepted. -/
theorem iClosed_ok : (evalIProg 32 iClosed World.emptyWorld).isSome = true := by
  decide

/-- A successful closed run ends with no owners: no outstanding resources. -/
theorem iClosed_closed {w' : World}
    (h : evalIProg 32 iClosed World.emptyWorld = some ((), w')) : w'.ctx.owners = [] := by
  have hctx := (evalIProg_post World.emptyWorld 32 iClosed rfl h emptyWorld_commandInv).1
  rw [hctx]
  rfl

/-- The closed run's world is well formed. -/
theorem iClosed_sound {w' : World}
    (h : evalIProg 32 iClosed World.emptyWorld = some ((), w')) : w'.WellFormed :=
  (evalIProg_post World.emptyWorld 32 iClosed rfl h emptyWorld_commandInv).2.1

/-- After the closed run the disposed allocation's backend is gone. -/
theorem iClosed_freed :
    (evalIProg 32 iClosed World.emptyWorld).map
      (fun r => (r.2.heaps ⟨0⟩).isNone) = some true := by
  decide

/-! ### The delegation lifecycle on the 64-byte world -/

/-- The whole-share leaf of the concrete 64-byte owner. -/
def ildLeaf : Leaf :=
  { id := ⟨1⟩, alloc := ⟨0⟩, lo := 0, hi := 64, ordered := by decide, q := 64,
    pos := by decide, ceiling := .readWrite, state := .active }

/-- The owner after the lender's leaf is retagged to the borrower. -/
def ildBorrowed : Owner :=
  { uOwner with root := uOwner.root.retag ⟨1⟩ ⟨5⟩ }

/-- The loan record the begun borrow inserts: the borrower's lifetime is the
freshly minted one, and the chain base comes from the lender's own identity. -/
def ildLoan : Loan :=
  { id := ⟨10⟩, alloc := ⟨0⟩, base := ⟨1⟩, lender := ⟨1⟩, borrower := ⟨5⟩,
    lifetime := ⟨1⟩, lo := 0, hi := 64, q := 64, ceiling := .readWrite }

/-- The context after beginning the borrow. -/
def ildCtxBegin : Ctx :=
  uWorld.ctx.beginBorrowNext ⟨0⟩ uOwner ildBorrowed ildLeaf ⟨1⟩ ⟨5⟩ ⟨10⟩

/-- The owner after the borrower's name retags back to the lender. -/
def ildRestored : Owner :=
  { ildBorrowed with root := ildBorrowed.root.retag ⟨5⟩ ⟨1⟩ }

/-- The context after the return. -/
def ildCtxEnd : Ctx :=
  ildCtxBegin.endBorrowNext ildBorrowed ildRestored ildLoan

/-- The begin command with its context-level evidence. -/
def ildBegin : IProg uWorld.ctx Unit (fun _ => ildCtxBegin) :=
  @IProg.beginBorrow uWorld.ctx ⟨0⟩ ⟨1⟩ ⟨5⟩ ⟨10⟩ uOwner (by rfl)
    ildLeaf (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide)
    ildBorrowed (by rfl)

/-- A write through the borrowed capability. -/
def ildWriteBorrowed : IProg ildCtxBegin Unit (fun _ => ildCtxBegin) :=
  .write ⟨0⟩ ⟨5⟩ 0 7 (by exact ⟨_, rfl, by decide⟩)

/-- The return command with its context-level evidence. -/
def ildEnd : IProg ildCtxBegin Unit (fun _ => ildCtxEnd) :=
  @IProg.endBorrow ildCtxBegin ⟨0⟩ ⟨10⟩ ildLoan (by rfl) ildBorrowed (by rfl)
    (by
      intro l hl hid
      rw [show ildCtxBegin.loans.loans = [ildLoan] from rfl] at hl
      simp only [List.mem_singleton] at hl
      subst hl
      decide)
    (by decide) ildRestored (by rfl)

/-- A write through the lender's capability, restored by the return. -/
def ildWriteLender : IProg ildCtxEnd Unit (fun _ => ildCtxEnd) :=
  .write ⟨0⟩ ⟨1⟩ 1 9 (by exact ⟨_, rfl, by decide⟩)

/-- Borrow, write through the borrower, return, and write through the lender
again. -/
def iDelegationLifecycle : IProg uWorld.ctx Unit (fun _ => ildCtxEnd) :=
  .bind ildBegin fun _ =>
  .bind ildWriteBorrowed fun _ =>
  .bind ildEnd fun _ =>
  .bind ildWriteLender fun _ =>
  .pure ()

/-- The delegation lifecycle is accepted. -/
theorem iDelegationLifecycle_ok :
    (evalIProg 64 iDelegationLifecycle uWorld).isSome = true := by
  decide

/-- The run ends on the post-context the type names. -/
theorem iDelegationLifecycle_ctx {w' : World}
    (h : evalIProg 64 iDelegationLifecycle uWorld = some ((), w')) :
    w'.ctx = ildCtxEnd :=
  (evalIProg_post uWorld 64 iDelegationLifecycle rfl h uWorld_commandInv).1

/-- The return restored the lender: the borrower name is gone, and the lender
holds an active whole-share read--write leaf over the allocation again. -/
theorem iDelegationLifecycle_owner {w' : World}
    (h : evalIProg 64 iDelegationLifecycle uWorld = some ((), w')) :
    ∃ o, w'.ctx.findOwner? ⟨0⟩ = some o ∧ (o.root.find? ⟨5⟩).isNone = true ∧
      (o.root.find? ⟨1⟩).map (fun c => (c.state, c.lo, c.hi, c.q)) =
        some (.active, 0, 64, 64) := by
  have hctx := iDelegationLifecycle_ctx h
  rw [hctx]
  exact ⟨ildRestored, by rfl, by decide, by decide⟩

/-- The return discharges the loan: no loan record survives the run. -/
theorem iDelegationLifecycle_returned {w' : World}
    (h : evalIProg 64 iDelegationLifecycle uWorld = some ((), w')) :
    w'.ctx.loans.loans = [] := by
  rw [iDelegationLifecycle_ctx h]
  rfl

/-- The writes through the borrower and then through the restored lender both
land in the 64-byte backend. -/
theorem iDelegationLifecycle_snapshot :
    (evalIProg 64 iDelegationLifecycle uWorld).map
      (fun r => (r.2.heaps ⟨0⟩).map (·.buf)) =
      some (some ([7, 9] ++ List.replicate 62 (0 : UInt8))) := by
  decide

/-! ### The closed delegation lifecycle -/

/-- The owner allocation `icCtx1` records. -/
def icdLender : Owner := Owner.init ⟨0⟩ 4 64 (by decide) ⟨1⟩ ⟨2⟩

/-- The whole-share leaf of the closed program's 4-byte owner. -/
def icdLeaf : Leaf :=
  { id := ⟨1⟩, alloc := ⟨0⟩, lo := 0, hi := 4, ordered := by decide, q := 64,
    pos := by decide, ceiling := .readWrite, state := .active }

/-- The owner after the lender's leaf is retagged to the borrower. -/
def icdBorrowed : Owner :=
  { icdLender with root := icdLender.root.retag ⟨1⟩ ⟨3⟩ }

/-- The loan record the begun borrow inserts. -/
def icdLoan : Loan :=
  { id := ⟨10⟩, alloc := ⟨0⟩, base := ⟨1⟩, lender := ⟨1⟩, borrower := ⟨3⟩,
    lifetime := ⟨1⟩, lo := 0, hi := 4, q := 64, ceiling := .readWrite }

/-- The context after beginning the borrow. -/
def icdCtxBegin : Ctx :=
  icCtx1.beginBorrowNext ⟨0⟩ icdLender icdBorrowed icdLeaf ⟨1⟩ ⟨3⟩ ⟨10⟩

/-- The owner after the borrower's name retags back to the lender. -/
def icdRestored : Owner :=
  { icdBorrowed with root := icdBorrowed.root.retag ⟨3⟩ ⟨1⟩ }

/-- The context after the return. -/
def icdCtxEnd : Ctx :=
  icdCtxBegin.endBorrowNext icdBorrowed icdRestored icdLoan

/-- The context after disposal: the owner is gone, the free history remains. -/
def icdCtxFinal : Ctx := (icdCtxEnd.freeWith? ⟨0⟩ ⟨2⟩).getD icdCtxEnd

def icdAlloc : IProg World.emptyWorld.ctx AllocId (fun _ => icCtx1) :=
  .alloc 4 ⟨1⟩ ⟨2⟩ (by decide) (by decide) (by decide)

/-- The begin command with its context-level evidence. -/
def icdBegin : IProg icCtx1 Unit (fun _ => icdCtxBegin) :=
  @IProg.beginBorrow icCtx1 ⟨0⟩ ⟨1⟩ ⟨3⟩ ⟨10⟩ icdLender (by rfl)
    icdLeaf (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide)
    icdBorrowed (by rfl)

/-- A write through the borrowed capability. -/
def icdWriteBorrowed : IProg icdCtxBegin Unit (fun _ => icdCtxBegin) :=
  .write ⟨0⟩ ⟨3⟩ 0 7 (by exact ⟨_, rfl, by decide⟩)

/-- The return command with its context-level evidence. -/
def icdEnd : IProg icdCtxBegin Unit (fun _ => icdCtxEnd) :=
  @IProg.endBorrow icdCtxBegin ⟨0⟩ ⟨10⟩ icdLoan (by rfl) icdBorrowed (by rfl)
    (by
      intro l hl hid
      rw [show icdCtxBegin.loans.loans = [icdLoan] from rfl] at hl
      simp only [List.mem_singleton] at hl
      subst hl
      decide)
    (by decide) icdRestored (by rfl)

/-- A write through the lender's capability, restored by the return. -/
def icdWriteLender : IProg icdCtxEnd Unit (fun _ => icdCtxEnd) :=
  .write ⟨0⟩ ⟨1⟩ 1 9 (by exact ⟨_, rfl, by decide⟩)

/-- The disposal step, licensed by the discharged loan and the owner's recorded
disposal capability. -/
def icdFree : IProg icdCtxEnd Unit (fun _ => icdCtxFinal) :=
  @IProg.free icdCtxEnd ⟨0⟩ ⟨2⟩
    (by intro o _ l hl; rw [show icdCtxEnd.loans.loans = [] from rfl] at hl
        exact absurd hl (by simp))
    (by intro o _ l hl; rw [show icdCtxEnd.loans.loans = [] from rfl] at hl
        exact absurd hl (by simp))
    (by decide)

/-- Allocate, borrow, write through the borrower, return, write through the
lender, and dispose. -/
def iClosedDelegation : IProg World.emptyWorld.ctx Unit (fun _ => icdCtxFinal) :=
  .bind icdAlloc fun _ =>
  .bind icdBegin fun _ =>
  .bind icdWriteBorrowed fun _ =>
  .bind icdEnd fun _ =>
  .bind icdWriteLender fun _ =>
  .bind icdFree fun _ =>
  .pure ()

/-- The closed delegation lifecycle is accepted. -/
theorem iClosedDelegation_ok :
    (evalIProg 32 iClosedDelegation World.emptyWorld).isSome = true := by
  decide

/-- The run ends on the post-context the type names. -/
theorem iClosedDelegation_ctx {w' : World}
    (h : evalIProg 32 iClosedDelegation World.emptyWorld = some ((), w')) :
    w'.ctx = icdCtxFinal :=
  (evalIProg_post World.emptyWorld 32 iClosedDelegation rfl h emptyWorld_commandInv).1

/-- A successful closed delegation run ends with no owners: the allocation was
disposed after its loan was returned. -/
theorem iClosedDelegation_closed {w' : World}
    (h : evalIProg 32 iClosedDelegation World.emptyWorld = some ((), w')) :
    w'.ctx.owners = [] := by
  rw [iClosedDelegation_ctx h]
  rfl

/-- The owner and the loan are both gone at the end of the run. -/
theorem iClosedDelegation_owner {w' : World}
    (h : evalIProg 32 iClosedDelegation World.emptyWorld = some ((), w')) :
    w'.ctx.findOwner? ⟨0⟩ = none ∧ w'.ctx.loans.loans = [] := by
  rw [iClosedDelegation_ctx h]
  exact ⟨by rfl, by rfl⟩

/-- The disposed allocation's backend is gone. -/
theorem iClosedDelegation_snapshot :
    (evalIProg 32 iClosedDelegation World.emptyWorld).map
      (fun r => (r.2.heaps ⟨0⟩).isNone) = some true := by
  decide

end Cap
