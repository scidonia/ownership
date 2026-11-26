/-
A kernel-checked certificate for a closed capability program.

`Cap.Surface` has both a checking form (`#own_prog`) and a proof-producing form
(`#own_cert`), which declares a `Checked` theorem. This module records a concrete
certificate directly: the checker's success is a decidable proposition
(`Cap.Checked`), so `by decide` produces a kernel-checked proof for the closed
program below. It is a second instance of the same certificate shape.
-/
import Cap.Core
import Cap.FullInv
import Cap.Runner

namespace Cap

/-- A closed 12-byte program: split at 6, write both halves, no-op. -/
def certifiedProgram : List Cmd :=
  [ .splitAt ⟨0⟩ ⟨1⟩ ⟨2⟩ 6
  , .write ⟨1⟩ 2
  , .write ⟨2⟩ 8
  , .nop ]

def certifiedOwner : Owner :=
  Owner.init ⟨0⟩ 12 12 (by decide) ⟨0⟩ ⟨9⟩

/-- The checker accepts the program, checked by the kernel. -/
theorem certifiedProgram_checked : Checked certifiedOwner 12 certifiedProgram := by
  unfold Checked
  decide

/-- The accepted program's final owner is covered at the whole share. -/
theorem certifiedProgram_covered :
    ∀ o', check certifiedOwner 12 certifiedProgram = .ok o' → o'.Covered 12 := by
  intro o' h
  exact check_covered certifiedProgram certifiedOwner o' 12 h
    (Owner.init_covered ⟨0⟩ 12 12 (by decide) ⟨0⟩ ⟨9⟩)

/-! ### A closed delegation certificate -/

/-- The closed delegation program: allocate a 4-byte owner, borrow its root for
a fresh borrower, write through the borrower, return it, and write through the
lender's restored capability. -/
def closedDelegationCmds : List UCmd :=
  [ .alloc 4 ⟨1⟩ ⟨2⟩,
    .beginBorrow ⟨0⟩ ⟨1⟩ ⟨3⟩ ⟨10⟩,
    .write ⟨0⟩ ⟨3⟩ 0 7,
    .endBorrow ⟨0⟩ ⟨10⟩,
    .write ⟨0⟩ ⟨1⟩ 1 9 ]

/-- The kernel checks the closed delegation program from the empty world. -/
theorem closedDelegation_ok :
    (checkWorld World.emptyWorld closedDelegationCmds).isOk = true := by
  decide

/-- The closed delegation certificate: the command list plus the checker's
derivation from the empty world. -/
def closedDelegation : ClosedProgram :=
  ⟨closedDelegationCmds, closedDelegation_ok⟩

/-- The certificate's post-world, named so its snapshot facts compute. -/
def closedDelegationPost : World :=
  match checkWorld World.emptyWorld closedDelegationCmds with
  | .ok w => w
  | .error _ => World.emptyWorld

theorem closedDelegationPost_ok :
    checkWorld World.emptyWorld closedDelegationCmds = .ok closedDelegationPost := by
  cases h : checkWorld World.emptyWorld closedDelegationCmds with
  | ok w => simp [closedDelegationPost, h]
  | error e =>
    have hfalse : (checkWorld World.emptyWorld closedDelegationCmds).isOk = false := by
      rw [h]
      rfl
    rw [closedDelegation_ok] at hfalse
    cases hfalse

/-- The certificate's abstract post-world is the one the checker returned. -/
theorem closedDelegation_post_eq :
    closedDelegation.post = closedDelegationPost := by
  have h := ClosedProgram.post_ok closedDelegation
  change checkWorld World.emptyWorld closedDelegationCmds = .ok closedDelegation.post at h
  rw [closedDelegationPost_ok] at h
  injection h with hpost
  exact hpost.symm

/-- The certificate's snapshot is the byte the borrower wrote and the byte the
restored lender wrote. -/
theorem closedDelegation_snapshot :
    closedDelegation.snapshot ⟨0⟩ = some ([7, 9, 0, 0] : List UInt8) := by
  unfold ClosedProgram.snapshot
  rw [closedDelegation_post_eq]
  decide

/-- The certificate's post-world is well formed through `ClosedProgram.wf`,
which still concludes `WellFormed` from the empty world's carrier. -/
theorem closedDelegation_wf : closedDelegation.post.WellFormed :=
  ClosedProgram.wf closedDelegation

/-- The closed delegation run carries the combined invariant. -/
theorem closedDelegation_fullInv : closedDelegation.post.FullInv :=
  World.checkWorld_fullInv _ _ _ closedDelegation.post_ok World.emptyWorld_fullInv

/-- The same certificate in the `Prog` form: syntax plus the checker's derivation
from the empty world. -/
def closedDelegationProg : Prog World.emptyWorld :=
  ⟨closedDelegationPost, closedDelegationCmds, closedDelegationPost_ok⟩

/-- The `Prog` certificate observes the same snapshot. -/
theorem closedDelegationProg_snapshot :
    closedDelegationProg.snapshot ⟨0⟩ = some ([7, 9, 0, 0] : List UInt8) := by
  unfold Prog.snapshot closedDelegationProg
  decide

end Cap
