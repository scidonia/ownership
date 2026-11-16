/-
The context-preserving program fragment: a typed interface with reads, writes
and dependent control flow.

`Owned Γ α` is the fragment the handoff calls "the one that should carry most
algorithm code": ordinary monadic sequencing over a fixed permission context.
Reads are observations of the pure backends (the discipline constrains writes);
writes go through `World.writeChecked`. The evaluator is total by fuel, so a
data-dependent chase — union-find's `find` — is a *program*, not a host loop
around checked writes.

Proved: `evalOwned_wf` (a successful run preserves the world invariant) and
`evalOwned_ctx` (the fragment realises its constant context index: the final
context is the initial one). Not claimed: termination of the chase (fuel),
a read guard, or any context-changing transition (allocation, splits, loans and
disposal remain in `Cap/Unified.lean`'s `UCmd` for now).
-/
import Cap.Unified
import Cap.UFRun

namespace Cap

/-- A computation over a fixed permission context: reads, writes and monadic
sequencing. No resource transition is representable here. -/
inductive Owned (Γ : Ctx) : Type → Type 1 where
  | pure : α → Owned Γ α
  | bind : Owned Γ α → (α → Owned Γ β) → Owned Γ β
  | read (a : AllocId) (id : CapId) (i : Nat) : Owned Γ (Option UInt8)
  | write (a : AllocId) (id : CapId) (i : Nat) (v : UInt8) : Owned Γ Unit

/-- The fuelled evaluator. Fuel bounds the number of `bind` steps expanded, so
the definition is total; exhaustion is a visible `none`, not a silent answer. -/
def evalOwned (fuel : Nat) {Γ : Ctx} {α : Type} (p : Owned Γ α) (w : World) :
    Option (α × World) :=
  match fuel with
  | 0 => none
  | fuel + 1 =>
    match p with
    | .pure a => some (a, w)
    | .bind q k =>
      match evalOwned fuel q w with
      | none => none
      | some (a, w') => evalOwned fuel (k a) w'
    | .read a _id i => some ((w.heaps a).bind (·.read i), w)
    | .write a id i v =>
      match w.writeChecked a id i v with
      | .ok w' => some ((), w')
      | .error _ => none

/-- A successful run preserves the world invariant. -/
theorem evalOwned_wf {Γ : Ctx} (w : World) (fuel : Nat) :
    ∀ {α : Type} (p : Owned Γ α) {a : α} {w' : World},
      evalOwned fuel p w = some (a, w') → w.WellFormed → w'.WellFormed := by
  induction fuel generalizing w with
  | zero => intro α p a w' h hwf; simp [evalOwned] at h
  | succ fuel ih =>
    intro α p a w' h hwf
    cases p with
    | pure a' =>
      simp only [evalOwned] at h
      obtain ⟨-, rfl⟩ := Option.some.inj h
      exact hwf
    | bind q k =>
      cases hq : evalOwned fuel q w with
      | none =>
        simp only [evalOwned, hq] at h
        nomatch h
      | some r =>
        obtain ⟨a1, w1⟩ := r
        simp only [evalOwned, hq] at h
        exact ih w1 (k a1) h (ih w q hq hwf)
    | read a0 id0 i0 =>
      simp only [evalOwned] at h
      obtain ⟨-, rfl⟩ := Option.some.inj h
      exact hwf
    | write a0 id0 i0 v0 =>
      cases hw : w.writeChecked a0 id0 i0 v0 with
      | error e =>
        simp only [evalOwned, hw] at h
        nomatch h
      | ok w1 =>
        simp only [evalOwned, hw] at h
        obtain ⟨-, rfl⟩ := Option.some.inj h
        exact World.writeChecked_wf hw hwf

/-- A successful run leaves the context unchanged: the fragment realises its
constant index. -/
theorem evalOwned_ctx {Γ : Ctx} (w : World) (fuel : Nat) :
    ∀ {α : Type} (p : Owned Γ α) {a : α} {w' : World},
      evalOwned fuel p w = some (a, w') → w'.ctx = w.ctx := by
  induction fuel generalizing w with
  | zero => intro α p a w' h; simp [evalOwned] at h
  | succ fuel ih =>
    intro α p a w' h
    cases p with
    | pure a' =>
      simp only [evalOwned] at h
      obtain ⟨-, rfl⟩ := Option.some.inj h
      rfl
    | bind q k =>
      cases hq : evalOwned fuel q w with
      | none =>
        simp only [evalOwned, hq] at h
        nomatch h
      | some r =>
        obtain ⟨a1, w1⟩ := r
        simp only [evalOwned, hq] at h
        rw [ih w1 (k a1) h, ih w q hq]
    | read a0 id0 i0 =>
      simp only [evalOwned] at h
      obtain ⟨-, rfl⟩ := Option.some.inj h
      rfl
    | write a0 id0 i0 v0 =>
      cases hw : w.writeChecked a0 id0 i0 v0 with
      | error e =>
        simp only [evalOwned, hw] at h
        nomatch h
      | ok w1 =>
        simp only [evalOwned, hw] at h
        obtain ⟨-, rfl⟩ := Option.some.inj h
        obtain ⟨_, _, _, _, _, _, _, hctx, _⟩ := World.writeChecked_sound hw
        exact hctx

/-- The fuel-bounded find with path compression, as a program in the fragment:
on exhaustion or a missing parent the error is visible; on success the root is
returned and each chased node's parent is written to the root. -/
def findCompress (Γ : Ctx) (a : AllocId) (id : CapId) :
    Nat → Nat → Owned Γ (Except Unit Nat)
  | 0, _ => .pure (.error ())
  | fuel + 1, x =>
    .bind (.read a id x) fun
      | none => .pure (.error ())
      | some p =>
        if p.toNat = x then .pure (.ok x)
        else
          .bind (findCompress Γ a id fuel p.toNat) fun
            | .error e => .pure (.error e)
            | .ok root =>
              .bind (.write a id x root.toUInt8) fun _ => .pure (.ok root)

/-- The four-node union-find world after the trace's unions: parent
`[0,0,0,2]`, ranks zero. Same owner and invariant as `ufWorld`; only the
backend bytes differ. -/
def ufWorldC : World :=
  { ufWorld with
    heaps := fun a => if a = ⟨0⟩ then
      some { buf := [0, 0, 0, 2, 0, 0, 0, 0], len := 8, hlen := rfl } else none }

/-- `ufWorldC` is well formed. -/
theorem ufWorldC_wf : ufWorldC.WellFormed := by
  refine ⟨ufWorld_wf.1, ufWorld_wf.2.1, ?_⟩
  intro a o hfind
  by_cases ha : a = ⟨0⟩
  · subst ha
    have h := hfind
    simp [ufWorldC, ufWorld, Ctx.findOwner?] at h
    have ho : o = Owner.init ⟨0⟩ 8 64 (by decide) ⟨1⟩ ⟨2⟩ := h.2.symm
    subst o
    exact ⟨{ buf := [0, 0, 0, 2, 0, 0, 0, 0], len := 8, hlen := rfl }, rfl, rfl⟩
  · simp [ufWorldC, ufWorld, Ctx.findOwner?, Owner.init] at hfind
    exact absurd hfind.1.symm ha

/-- The chase from node 3 finds root 0 and compresses the path. -/
theorem findCompress_run_ok :
    (evalOwned 32 (findCompress ufWorldC.ctx ⟨0⟩ ⟨1⟩ 4 3) ufWorldC).isSome = true := by
  decide

/-- Whether a chase result is the root 0. -/
def rootIsZero (r : Option (Except Unit Nat × World)) : Bool :=
  match r with
  | some (.ok 0, _) => true
  | _ => false

/-- The chase returns root 0. -/
theorem findCompress_run_root :
    rootIsZero (evalOwned 32 (findCompress ufWorldC.ctx ⟨0⟩ ⟨1⟩ 4 3) ufWorldC) = true := by
  decide

/-- After the chase, the path is compressed: parent is `[0,0,0,0]`. -/
theorem findCompress_compresses :
    (evalOwned 32 (findCompress ufWorldC.ctx ⟨0⟩ ⟨1⟩ 4 3) ufWorldC).map
      (fun r => (r.2.heaps ⟨0⟩).map (fun b => (b.buf.take 4).map UInt8.toNat))
      = some (some [0, 0, 0, 0]) := by
  decide

/-- The chase's final world is well formed. -/
theorem findCompress_run_wf {root : Except Unit Nat} {w' : World}
    (h : evalOwned 32 (findCompress ufWorldC.ctx ⟨0⟩ ⟨1⟩ 4 3) ufWorldC = some (root, w')) :
    w'.WellFormed :=
  evalOwned_wf ufWorldC 32 _ h ufWorldC_wf

/-- The chase's final context is the initial one. -/
theorem findCompress_run_ctx {root : Except Unit Nat} {w' : World}
    (h : evalOwned 32 (findCompress ufWorldC.ctx ⟨0⟩ ⟨1⟩ 4 3) ufWorldC = some (root, w')) :
    w'.ctx = ufWorldC.ctx :=
  evalOwned_ctx ufWorldC 32 _ h

end Cap
