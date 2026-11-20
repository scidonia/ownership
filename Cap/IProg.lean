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

The evaluator takes the realization hypothesis `w.ctx = Γ` and the invariant,
and is total by fuel (exhaustion is a visible `none`). Its soundness theorem is
the one the review's R1 asks for at this layer:

  evalIProg_post : evalIProg fuel p w hΓ = some (a, w') →
    w'.ctx = Q a ∧ w'.WellFormed

— execution from a well-formed world that matches the typing context ends in a
well-formed world that matches the postcondition, for every command in the
language.

Scope and limits: reads are observations of the pure backends; the context
index tracks owners, not the loan list (`w.loans` is world state outside the
index, so `beginLoan`/`endLoan` are not yet indexed constructors — they remain
in `UCmd`); termination is fuel; the negative/refusal side lives at the type
level (ill-evidenced programs do not exist) rather than as runtime errors.
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
      (hfind : Γ.findOwner? a = some o) (hfids : o.FreshIds id1 id2)
      (hfresh1 : id1 ∉ Γ.ids) (hfresh2 : id2 ∉ Γ.ids)
      (hissued1 : id1 ∉ Γ.issued) (hissued2 : id2 ∉ Γ.issued)
      (hact : ∃ c, o.root.find? id = some c ∧ c.state = .active)
      (hs : (Γ.splitAtOwner? o id id1 id2 k).isSome) :
      IProg Γ Unit (fun _ => { (Γ.splitAtOwner? o id id1 id2 k).getD Γ with
                               issued := id1 :: id2 :: Γ.issued })
  | free (a : AllocId) (d : CapId)
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
  | fuel + 1, .splitAt a id id1 id2 k _ _ _ _ _ _ _ _ _ =>
    match w.splitAtChecked a id id1 id2 k with
    | .ok w' => some ((), w')
    | .error _ => none
  | fuel + 1, .free a d _ _ =>
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
  | fuel + 1, .splitAt a id id1 id2 k _ _ _ _ _ _ _ _ _ =>
    match w.splitAtChecked a id id1 id2 k with
    | .ok w' => .done () w'
    | .error msg => .refused msg
  | fuel + 1, .free a d _ _ =>
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
  | zero => intro Γ α Q p; cases p <;> rfl
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
    (hfind : Γ.findOwner? a = some o) (hfids : o.FreshIds id1 id2)
    (hfresh1 : id1 ∉ Γ.ids) (hfresh2 : id2 ∉ Γ.ids)
    (hissued1 : id1 ∉ Γ.issued) (hissued2 : id2 ∉ Γ.issued)
    (hact : ∃ c, o.root.find? id = some c ∧ c.state = .active)
    (hs : (Γ.splitAtOwner? o id id1 id2 k).isSome)
    (hΓ : w.ctx = Γ) :
    (w.splitAtChecked a id id1 id2 k).isOk = true := by
  unfold World.splitAtChecked
  rw [hΓ]
  simp only [hfind]
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

/-- A checked disposal realises its typed post-context. -/
theorem freeChecked_post {w w' : World} {Γ : Ctx} {a : AllocId} {d : CapId}
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

/-- Soundness: execution from a world matching the typing context ends in a
world matching the postcondition, and preserves the world invariant. -/
theorem evalIProg_post (w : World) (fuel : Nat) :
    ∀ {Γ : Ctx} {α : Type} {Q : α → Ctx} (p : IProg Γ α Q) {a : α} {w' : World},
      w.ctx = Γ → evalIProg fuel p w = some (a, w') → w.WellFormed →
      w'.ctx = Q a ∧ w'.WellFormed := by
  induction fuel generalizing w with
  | zero => intro Γ α Q p a w' hΓ h hwf; simp [evalIProg] at h
  | succ fuel ih =>
    intro Γ α Q p a w' hΓ h hwf
    cases p with
    | pure a' =>
      simp only [evalIProg] at h
      obtain ⟨rfl, rfl⟩ := Option.some.inj h
      exact ⟨hΓ, hwf⟩
    | bind q k =>
      cases hq : evalIProg fuel q w with
      | none =>
        simp only [evalIProg, hq] at h
        nomatch h
      | some r =>
        obtain ⟨a1, w1⟩ := r
        simp only [evalIProg, hq] at h
        obtain ⟨hctx1, hwf1⟩ := ih w q hΓ hq hwf
        exact ih w1 (k a1) hctx1 h hwf1
    | read a0 id0 i0 hc =>
      simp only [evalIProg] at h
      obtain ⟨-, rfl⟩ := Option.some.inj h
      exact ⟨hΓ, hwf⟩
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
        exact ⟨hctx.trans hΓ, World.writeChecked_wf hw hwf⟩
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
          exact ⟨allocChecked_post hf hfr hΓ hpos hw, World.allocChecked_wf hw hwf⟩
      · simp only [evalIProg, hpos] at h
        nomatch h
    | splitAt a0 id0 id1 id2 k o hfind hfids hfresh1 hfresh2 hissued1 hissued2 hact hs =>
      cases hw : w.splitAtChecked a0 id0 id1 id2 k with
      | error e =>
        simp only [evalIProg, hw] at h
        nomatch h
      | ok w1 =>
        simp only [evalIProg, hw] at h
        obtain ⟨-, rfl⟩ := Option.some.inj h
        exact ⟨splitAtChecked_post hfind hs hΓ hw, World.splitAtChecked_wf hw hwf⟩
    | free a0 d hloan hs =>
      cases hw : w.freeChecked a0 d with
      | error e =>
        simp only [evalIProg, hw] at h
        nomatch h
      | ok w1 =>
        simp only [evalIProg, hw] at h
        obtain ⟨-, rfl⟩ := Option.some.inj h
        exact ⟨freeChecked_post hloan hs hΓ hw, World.freeChecked_wf hw hwf⟩

/-- A typed program is never refused. From a matching world satisfying the
invariant, the explicit evaluator either completes or exhausts its fuel; every
world check a command performs is discharged by that command's own typing
evidence (`World.write_succeeds`, `World.allocChecked_succeeds`,
`splitAtChecked_succeeds`, `World.freeChecked_succeeds`). -/
theorem runIProg_no_refusal (w : World) (fuel : Nat) :
    ∀ {Γ : Ctx} {α : Type} {Q : α → Ctx} (p : IProg Γ α Q),
      w.ctx = Γ → w.WellFormed → ∀ msg, runIProg fuel p w ≠ .refused msg := by
  induction fuel generalizing w with
  | zero =>
    intro Γ α Q p hΓ hwf msg h
    cases h
  | succ fuel ih =>
    intro Γ α Q p hΓ hwf msg h
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
        obtain ⟨hctx1, hwf1⟩ := evalIProg_post w fuel q hΓ hsome hwf
        exact ih w1 (k a) hctx1 hwf1 msg h
      | exhausted =>
        simp only [hq] at h
        cases h
      | refused mq =>
        exact absurd hq (ih w q hΓ hwf mq)
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
    | splitAt a id id1 id2 k o hfind hfids hfresh1 hfresh2 hissued1 hissued2 hact hs =>
      simp only [runIProg] at h
      cases hw : w.splitAtChecked a id id1 id2 k with
      | error e =>
        simp only [hw] at h
        have hok := splitAtChecked_succeeds hfind hfids hfresh1 hfresh2
          hissued1 hissued2 hact hs hΓ
        rw [hw] at hok
        cases hok
      | ok w1 =>
        simp only [hw] at h
        cases h
    | free a d hloan hs =>
      simp only [runIProg] at h
      cases hw : w.freeChecked a d with
      | error e =>
        simp only [hw] at h
        have hs' : (w.ctx.freeWith? a d).isSome = true := by
          rw [hΓ]
          exact hs
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
        have hok := World.freeChecked_succeeds (w := w) (a := a) (d := d) hsW hloan'
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
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by exact ⟨_, rfl, by decide⟩) (by decide)

/-- The write through the left half. -/
def iWrite2 : IProg ilCtx3 Unit (fun _ => ilCtx3) :=
  .write ⟨1⟩ ⟨5⟩ 0 8 (by exact ⟨_, rfl, by decide⟩)

/-- The disposal step. -/
def iFree : IProg ilCtx3 Unit (fun _ => ilCtx5) :=
  @IProg.free ilCtx3 ⟨1⟩ ⟨4⟩ (by intro o _ l hl; rw [ilCtx3_loans] at hl; exact absurd hl (by simp)) (by decide)

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
  (evalIProg_post uWorld 64 iLifecycle rfl h uWorld_wf).2

/-- The final context is the postcondition the type says it is. -/
theorem iLifecycle_ctx {w' : World}
    (h : evalIProg 64 iLifecycle uWorld = some ((), w')) : w'.ctx = ilCtx5 :=
  (evalIProg_post uWorld 64 iLifecycle rfl h uWorld_wf).1

/-- A split reusing the parent capability as a child id is not a program: the
freshness evidence is uninhabited. -/
theorem stale_child_refused :
    ¬ (Owner.init ⟨1⟩ 4 64 (by decide) ⟨3⟩ ⟨4⟩).FreshIds ⟨3⟩ ⟨5⟩ := by
  decide

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
  .bind (@IProg.free icCtx1 ⟨0⟩ ⟨2⟩ (by intro o _ l hl; rw [icCtx1_loans] at hl; exact absurd hl (by simp)) (by decide)) fun _ =>
  .pure ()

/-- The closed program is accepted. -/
theorem iClosed_ok : (evalIProg 32 iClosed World.emptyWorld).isSome = true := by
  decide

/-- A successful closed run ends with no owners: no outstanding resources. -/
theorem iClosed_closed {w' : World}
    (h : evalIProg 32 iClosed World.emptyWorld = some ((), w')) : w'.ctx.owners = [] := by
  have hctx := (evalIProg_post World.emptyWorld 32 iClosed rfl h World.emptyWorld_wf).1
  rw [hctx]
  rfl

/-- The closed run's world is well formed. -/
theorem iClosed_sound {w' : World}
    (h : evalIProg 32 iClosed World.emptyWorld = some ((), w')) : w'.WellFormed :=
  (evalIProg_post World.emptyWorld 32 iClosed rfl h World.emptyWorld_wf).2

/-- After the closed run the disposed allocation's backend is gone. -/
theorem iClosed_freed :
    (evalIProg 32 iClosed World.emptyWorld).map
      (fun r => (r.2.heaps ⟨0⟩).isNone) = some true := by
  decide

end Cap
