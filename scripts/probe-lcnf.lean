/-
The acquisition probe, run as a `lean` script in its own process.

    nix develop -c bash -c 'lake build Ownership.Toy && lake env lean scripts/probe-lcnf.lean'

It runs the pinned toolchain's **full** LCNF pipeline on three toy declarations
and reads the final `Decl .impure` back with `getLocalImpureDecl?`. The full
pipeline matters: replaying a subset of the impure passes is not faithful.
`probeStruct` shows the difference — without `insertResetReuse` in the same
order the compiler runs it, the struct is copied and the array is `inc`'d;
with the full pipeline the reset/reuse pair is expanded to an `isShared` test
and an in-place `oset`.

This must **not** be run from a module that is itself being C-emitted: invoking
the compiler during elaboration mutates compiler state the C emitter later
assumes, and the build panics in `emitCForDecls`. A separate `lean` process is
the safe instrument; an executable `main` works too.
-/
import Lean.Elab.Command
import Lean.Compiler.Main
import Lean.Compiler.LCNF.PrettyPrinter
import Ownership.Toy

open Lean
open Lean.Elab.Command

def showImpure (n : Name) : CommandElabM Unit := do
  match (← liftCoreM <| Lean.Compiler.LCNF.getLocalImpureDecl? n) with
  | some d =>
    logInfo m!"===== {d.name} (size {d.size}) ====="
    let fmt ← liftCoreM <| Lean.Compiler.LCNF.ppDecl' d .impure
    logInfo fmt
  | none =>
    throwError "the full pipeline left no impure declaration for {n}"

run_cmd do
  liftCoreM <| Lean.Compiler.compile
    #[``Ownership.Toy.probeSet, ``Ownership.Toy.probeAlias, ``Ownership.Toy.probeStruct]
  showImpure ``Ownership.Toy.probeSet
  showImpure ``Ownership.Toy.probeAlias
  showImpure ``Ownership.Toy.probeStruct
