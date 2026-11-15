/-
A kernel-checked certificate for a closed capability program.

`Cap.Surface` checks a program at elaboration time and emits no proof term. This
module records the certificate for a concrete program: the checker's success is a
decidable proposition (`Cap.Checked`), so `by decide` produces a kernel-checked
proof for the closed program below. This does not make the surface elaborator
proof-producing; it shows the certificate the elaborator would have to emit.
-/
import Cap.Core

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

end Cap
