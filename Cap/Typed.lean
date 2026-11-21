/-
The context-preserving fragment, with evidence-bearing accesses.

`Owned Γ α` is ordinary monadic sequencing over a fixed permission context. Its
read and write constructors take the same access evidence the indexed interface
uses (`Ctx.CanRead`, `Ctx.CanWrite`), so an access the context does not permit is
not a program. The fragment has no raw accessor and no representation index; an
algorithm whose indices arrive at run time belongs to the certified interface
(`Cap/UFCertified.lean`), which derives the evidence from `UFRep`.

The evaluator has an explicit outcome: completion, fuel exhaustion or a refused
world check. Its no-refusal theorem is stated for a world matching the typing
context and satisfying the invariant: read evidence and the invariant make every
read succeed, and `World.write_succeeds` makes every write succeed, so no
well-typed program of this fragment is refused. Reads remain observations: the
fragment does not model read revocation or confidentiality beyond the evidence.
-/
import Cap.Access
import Cap.Unified
import Cap.IProg

namespace Cap

/-- A computation over a fixed permission context: reads, writes and monadic
sequencing. Accesses carry their evidence; no resource transition is
representable here. -/
inductive Owned (Γ : Ctx) : Type → Type 1 where
  | pure : α → Owned Γ α
  | bind : Owned Γ α → (α → Owned Γ β) → Owned Γ β
  | read (a : AllocId) (id : CapId) (i : Nat)
      (h : Ctx.CanRead Γ a id i) : Owned Γ (Option UInt8)
  | write (a : AllocId) (id : CapId) (i : Nat) (v : UInt8)
      (h : Ctx.CanWrite Γ a id i) : Owned Γ Unit

/-- The evaluator's explicit outcome. -/
inductive OOutcome (α : Type) where
  | done (a : α) (w : World)
  | exhausted
  | refused (msg : String)

/-- The fuelled evaluator. Fuel bounds `bind` expansion, so the definition is
total; exhaustion is visible and distinct from a refused check. -/
def runOwned (fuel : Nat) {Γ : Ctx} {α : Type} (p : Owned Γ α) (w : World) :
    OOutcome α :=
  match fuel, p with
  | 0, _ => .exhausted
  | fuel + 1, .pure a => .done a w
  | fuel + 1, .bind q k =>
    match runOwned fuel q w with
    | .done a w' => runOwned fuel (k a) w'
    | .exhausted => .exhausted
    | .refused msg => .refused msg
  | fuel + 1, .read a _id i _h =>
    .done ((w.heaps a).bind (·.read i)) w
  | fuel + 1, .write a id i v _h =>
    match w.writeChecked a id i v with
    | .ok w' => .done () w'
    | .error msg => .refused msg

/-- A completed run preserves the world invariant. -/
theorem runOwned_wf {Γ : Ctx} (w : World) (fuel : Nat) :
    ∀ {α : Type} (p : Owned Γ α) {a : α} {w' : World},
      runOwned fuel p w = .done a w' → w.WellFormed → w'.WellFormed := by
  induction fuel generalizing w with
  | zero => intro α p a w' h; cases h
  | succ fuel ih =>
    intro α p a w' h hwf
    cases p with
    | pure a' =>
      simp only [runOwned] at h
      cases h
      exact hwf
    | bind q k =>
      simp only [runOwned] at h
      cases hq : runOwned fuel q w with
      | done a1 w1 =>
        have h' : runOwned fuel (k a1) w1 = .done a w' := by simpa [hq] using h
        have hwf1 := ih w q hq hwf
        exact ih w1 (k a1) h' hwf1
      | exhausted => simp [hq] at h
      | refused m => simp [hq] at h
    | read a0 id0 i0 hc =>
      simp only [runOwned] at h
      cases h
      exact hwf
    | write a0 id0 i0 v0 hc =>
      simp only [runOwned] at h
      cases hw : w.writeChecked a0 id0 i0 v0 with
      | error e => simp [hw] at h
      | ok w1 =>
        have h' : OOutcome.done () w1 = .done a w' := by simpa [hw] using h
        cases h'
        exact World.writeChecked_wf hw hwf

/-- A completed run leaves the context (and therefore the permission ledger)
unchanged. -/
theorem runOwned_ctx {Γ : Ctx} (w : World) (fuel : Nat) :
    ∀ {α : Type} (p : Owned Γ α) {a : α} {w' : World},
      runOwned fuel p w = .done a w' → w'.ctx = w.ctx := by
  induction fuel generalizing w with
  | zero => intro α p a w' h; cases h
  | succ fuel ih =>
    intro α p a w' h
    cases p with
    | pure a' =>
      simp only [runOwned] at h
      cases h
      rfl
    | bind q k =>
      simp only [runOwned] at h
      cases hq : runOwned fuel q w with
      | done a1 w1 =>
        have h' : runOwned fuel (k a1) w1 = .done a w' := by simpa [hq] using h
        have hctx1 := ih w q hq
        have hctx2 := ih w1 (k a1) h'
        exact hctx2.trans hctx1
      | exhausted => simp [hq] at h
      | refused m => simp [hq] at h
    | read a0 id0 i0 hc =>
      simp only [runOwned] at h
      cases h
      rfl
    | write a0 id0 i0 v0 hc =>
      simp only [runOwned] at h
      cases hw : w.writeChecked a0 id0 i0 v0 with
      | error e => simp [hw] at h
      | ok w1 =>
        have h' : OOutcome.done () w1 = .done a w' := by simpa [hw] using h
        cases h'
        obtain ⟨-, -, -, -, -, -, -, hctx, -⟩ := World.writeChecked_sound hw
        exact hctx

/-- A typed program is never refused, from a world matching its context and
satisfying the invariant. Read evidence and the invariant make reads succeed;
`World.write_succeeds` makes writes succeed. -/
theorem runOwned_no_refusal {Γ : Ctx} (w : World) (fuel : Nat) :
    ∀ {α : Type} (p : Owned Γ α), w.ctx = Γ → w.WellFormed →
      ∀ msg, runOwned fuel p w ≠ .refused msg := by
  induction fuel generalizing w with
  | zero =>
    intro α p hΓ hwf msg h
    cases h
  | succ fuel ih =>
    intro α p hΓ hwf msg h
    cases p with
    | pure a => cases h
    | bind q k =>
      simp only [runOwned] at h
      cases hq : runOwned fuel q w with
      | done a1 w1 =>
        have h' : runOwned fuel (k a1) w1 = .refused msg := by simpa [hq] using h
        have hwf1 := runOwned_wf w fuel q hq hwf
        have hctx1 := runOwned_ctx w fuel q hq
        exact ih w1 (k a1) (hctx1.trans hΓ) hwf1 msg h'
      | exhausted => simp [hq] at h
      | refused mq => exact absurd hq (ih w q hΓ hwf mq)
    | read a0 id0 i0 hc =>
      simp only [runOwned] at h
      cases h
    | write a0 id0 i0 v0 hc =>
      simp only [runOwned] at h
      obtain ⟨w1, hok⟩ := World.write_succeeds hc hΓ hwf
      rw [hok] at h
      cases h

end Cap
