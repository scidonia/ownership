/-
A sealed program certificate.

This is the form the runner handoff calls acceptable: raw syntax packaged with a
typing derivation, where the derivation is the checker's result. A `Prog pre post`
cannot exist without a proof that `checkWorld` maps `pre` to `post`, and the only
public observation is an immutable snapshot taken from that post-world. There is no
constructor for arbitrary backend access and no function of type
`World -> World` exposed as execution.

`Ix` in `Cap/Indexed.lean` remains a specification type: its `run` field does not,
by itself, establish a post-relation. This module is the certificate-carrying form.
-/
import Cap.Unified

namespace Cap

/-- A checked program from `pre` to `post`: syntax plus the checker's derivation. -/
structure Prog (pre : World) where
  post : World
  cmds : List UCmd
  ok : checkWorld pre cmds = .ok post

/-- The immutable snapshot of an allocation in the program's post-world. -/
def Prog.snapshot (p : Prog pre) (a : AllocId) : Option (List UInt8) :=
  (p.post.heaps a).map (fun b => b.buf)

/-- The post-world of the concrete 64-byte program. -/
def post64 : World :=
  match checkWorld uWorld uProgram with
  | .ok w => w
  | .error _ => uWorld

theorem post64_ok : checkWorld uWorld uProgram = .ok post64 := by
  cases h : checkWorld uWorld uProgram with
  | ok w => simp [post64, h]
  | error e =>
    have hok := uProgram_ok
    have hfalse : (checkWorld uWorld uProgram).isOk = false := by
      rw [h]
      rfl
    rw [hfalse] at hok
    cases hok

/-- The concrete certificate: the 64-byte program with its checker derivation. -/
def p64 : Prog uWorld := ⟨post64, uProgram, post64_ok⟩

theorem p64_snapshot :
    p64.snapshot ⟨0⟩ =
      some (List.replicate 32 (1 : UInt8) ++ List.replicate 32 (2 : UInt8)) := by
  have hrun := uRun_snapshot
  simp only [uRun] at hrun
  rw [post64_ok] at hrun
  unfold Prog.snapshot p64
  exact hrun

/-- Running an appended command list continues from the first part's result. -/
theorem checkWorld_append : ∀ (cs ds : List UCmd) (w w' : World),
    checkWorld w cs = .ok w' → checkWorld w (cs ++ ds) = checkWorld w' ds := by
  intro cs
  induction cs with
  | nil =>
    intro ds w w' h
    simp [checkWorld] at h
    cases h
    rfl
  | cons c cs ih =>
    intro ds w w' h
    cases c with
    | nop =>
      simp only [List.cons_append, checkWorld] at h ⊢
      exact ih ds w w' h
    | write a id i v =>
      cases hw : w.writeChecked a id i v with
      | error e => simp [checkWorld, hw] at h
      | ok w'' =>
        simp only [List.cons_append, checkWorld, hw] at h ⊢
        exact ih ds w'' w' h
    | splitAt a id id1 id2 k =>
      cases hw : w.splitAtChecked a id id1 id2 k with
      | error e => simp [checkWorld, hw] at h
      | ok w'' =>
        simp only [List.cons_append, checkWorld, hw] at h ⊢
        exact ih ds w'' w' h
    | splitFraction a id id1 id2 q1 q2 =>
      by_cases hq : 0 < q1 ∧ 0 < q2
      · cases hw : w.splitFractionChecked a id id1 id2 q1 q2 hq.1 hq.2 with
        | error e => simp [checkWorld, hq, hw] at h
        | ok w'' =>
          simp only [List.cons_append, checkWorld, hq, hw] at h ⊢
          exact ih ds w'' w' h
      · simp [checkWorld, hq] at h
    | join a node newId =>
      cases hw : w.joinChecked a node newId with
      | error e => simp [checkWorld, hw] at h
      | ok w'' =>
        simp only [List.cons_append, checkWorld, hw] at h ⊢
        exact ih ds w'' w' h
    | free a d =>
      cases hw : w.freeChecked a d with
      | error e => simp [checkWorld, hw] at h
      | ok w'' =>
        simp only [List.cons_append, checkWorld, hw] at h ⊢
        exact ih ds w'' w' h
    | alloc n rootId disposal =>
      by_cases hpos : 0 < w.ctx.D
      · cases hw : w.allocChecked n rootId disposal hpos with
        | error e => simp [checkWorld, hpos, hw] at h
        | ok w'' =>
          simp only [List.cons_append, checkWorld, hpos, hw] at h ⊢
          exact ih ds w'' w' h
      · simp [checkWorld, hpos] at h

/-- Sequential composition of certificates: the second program starts in the first
program's post-world, and the commands are appended. -/
def Prog.seq (p : Prog pre) (q : Prog p.post) : Prog pre where
  post := q.post
  cmds := p.cmds ++ q.cmds
  ok := by
    rw [checkWorld_append p.cmds q.cmds pre p.post p.ok]
    exact q.ok

end Cap
