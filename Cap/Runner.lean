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

end Cap
