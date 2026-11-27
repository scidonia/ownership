import CapCertified

open CapCertified

/-- The empty runtime program is certified by the trivial spec, and erasure
returns only the program. -/
def emptySpec : Spec := { pre := fun _ => True, post := fun _ _ => True }

def emptyCert : CertifiedProgram :=
  { program := [], spec := emptySpec,
    sound := by intro s _; exact ⟨s, rfl, trivial⟩ }

#guard erase emptyCert = []

def main : IO Unit :=
  IO.println "CapCertified: erase projection and proof-only soundness OK"
