import CapRuntime.Cmd

namespace CapCertified

/-- A runtime-level specification. The `sound` field below is a proof, not data
read by the executor. -/
structure Spec where
  pre : CapRuntime.State → Prop
  post : CapRuntime.State → CapRuntime.State → Prop

/-- The proof obligation behind a certificate. -/
def Spec.Sound (spec : Spec) (program : CapRuntime.Program) : Prop :=
  ∀ s, spec.pre s → ∃ s', CapRuntime.run s program = .ok s' ∧ spec.post s s'

/-- A certificate for a runtime program. `program` is the only field a runtime
entry point may read; `sound` is a proof. -/
structure CertifiedProgram where
  program : CapRuntime.Program
  spec : Spec
  sound : spec.Sound program

/-- The runtime program obtained from a certificate. -/
def erase (p : CertifiedProgram) : CapRuntime.Program := p.program

/-- Erasure is exactly the runtime program: no ghost or proof field is read. -/
theorem erase_program (p : CertifiedProgram) : erase p = p.program := rfl

end CapCertified
