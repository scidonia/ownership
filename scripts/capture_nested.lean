/-
Step 3 capture: the pinned `setAt` nested (`Path.index`) alternative and the
helper declarations it calls.

Run from the sibling checkout so `lake env` supplies the sibling's oleans:

    cd ../lean-examples
    nix develop -c lake env lean ../ownership/scripts/capture_nested.lean

The replay uses the same pass sequence as `scripts/dump_executor.lean`: the
declaration's mono IR read from the olean, then the remainder of the mono
pipeline and the full impure pipeline. The compiler is invoked in a separate
`lean` process, not during the build of a C-emitted module.
-/
import Lean.Elab.Command
import Lean.Compiler.Main
import Lean.Compiler.LCNF.PrettyPrinter
import Lean.Compiler.LCNF.PhaseExt
import Lean.Compiler.LCNF.Passes
import Lean.Compiler.LCNF.PassManager
import Scidonia.FracPerm.StateVar.Layout5

open Lean
open Lean.Elab.Command

namespace CaptureNested

def privateName (mod decl : Name) : Name := mkPrivateNameCore mod decl

open Lean.Compiler.LCNF

/-- Replicate the compiler's private pass runner. -/
partial def runPassesGo (decls : (pu : Purity) × Array (Decl pu)) (passes : List Pass) :
    CompilerM ((pu : Purity) × Array (Decl pu)) := do
  match passes with
  | [] => return decls
  | pass :: rest =>
    let ds ← withPhase pass.phase do
      decls.1.withAssertPurity pass.phase.toPurity fun h =>
        pass.run (h ▸ decls.2)
    runPassesGo ⟨pass.phaseOut.toPurity, ds⟩ rest

def runPasses (inPhase outPhase : Purity) (passes : Array Pass)
    (decls : Array (Decl inPhase)) : CompilerM (Array (Decl outPhase)) := do
  let final ← runPassesGo ⟨inPhase, decls⟩ passes.toList
  return final.1.withAssertPurity outPhase fun h => h ▸ final.2

def impureOfMono (mono : Decl .pure) : CompilerM (Array (Decl .impure)) := do
  let pm ← getPassManager
  let afterSave := (pm.monoPassesNoLambda.toList.dropWhile (fun p => p.name != `saveMono)).drop 1 |>.toArray
  let ds ← runPasses .pure .impure afterSave #[mono]
  runPasses .impure .impure pm.impurePasses ds

def replayedDecl (n : Name) : CommandElabM (Option (Decl .impure)) := do
  match (← liftCoreM <| Lean.Compiler.LCNF.getMonoDecl? n) with
  | none => return none
  | some mono =>
    let ds ← liftCoreM <| CompilerM.run (impureOfMono mono) {} .base
    return ds.find? (fun d => d.name == n)

def showReplayed (label : String) (n : Name) : CommandElabM Bool := do
  match (← replayedDecl n) with
  | none =>
    logInfo m!"===== {label}: {n} -- no replayed declaration ====="
    return false
  | some d =>
    logInfo m!"===== {label}: replayed {d.name} (size {d.size}, params {d.params.size}) ====="
    let fmt ← liftCoreM <| ppDecl' d .impure
    logInfo fmt
    logInfo m!"replayed digest: {hash (toString fmt)}"
    return true

def showImpure (label : String) (n : Name) : CommandElabM Bool := do
  match (← liftCoreM <| Lean.Compiler.LCNF.getLocalImpureDecl? n) with
  | some d =>
    logInfo m!"===== {label}: {d.name} (size {d.size}, params {d.params.size}) ====="
    let fmt ← liftCoreM <| Lean.Compiler.LCNF.ppDecl' d .impure
    logInfo fmt
    logInfo m!"impure digest: {hash (toString fmt)}"
    return true
  | none => return false

def capture : CommandElabM Unit := do
  let pSetAt := (privateName `Scidonia.FracPerm.StateVar.Layout5
    `Scidonia.FracPerm.StateVar.Layout5.setAt) ++ `_redArg
  let pTakeOut := (privateName `Scidonia.FracPerm.StateVar.Layout5
    `Scidonia.FracPerm.StateVar.Layout5.takeOut) ++ `_redArg
  let pInBounds := (privateName `Scidonia.FracPerm.StateVar.Layout5
    `Scidonia.FracPerm.StateVar.Layout5.inBounds) ++ `_redArg
  for (label, n) in #[
      ("setAt (private)", pSetAt),
      ("takeOut (private)", pTakeOut),
      ("inBounds (private)", pInBounds)] do
    discard <| showReplayed label n
  for (label, n) in #[
      ("stateDefault", `Scidonia.FracPerm.StateVar.Layout5.stateDefault),
      ("stateDefault._redArg", `Scidonia.FracPerm.StateVar.Layout5.stateDefault ++ `_redArg),
      ("assertExclusiveArrayImpl", `Scidonia.FracPerm.assertExclusiveArrayImpl),
      ("assertExclusiveArrayImpl._redArg", `Scidonia.FracPerm.assertExclusiveArrayImpl ++ `_redArg),
      ("assertExclusiveImpl", `Scidonia.FracPerm.assertExclusiveImpl),
      ("assertExclusiveImpl._redArg", `Scidonia.FracPerm.assertExclusiveImpl ++ `_redArg)] do
    let replayed ← showReplayed label n
    unless replayed do
      discard <| showImpure label n

end CaptureNested

run_cmd CaptureNested.capture
