/-
Concrete projection check: replay the private `execP` declaration and run
`OwnershipLcnf.projectPrefix` on its actual `PTree.set` alternative.

Run from the sibling checkout with the ownership build on `LEAN_PATH`:

    cd ../lean-examples
    nix develop -c lake env bash -c \
      'export LEAN_PATH="../ownership/.lake/build/lib/lean:$LEAN_PATH"; \
       lean ../ownership/scripts/check_projection.lean'

The replay code is the same pass pipeline as `dump_executor.lean`; this script
exists so the projection is exercised on the real declaration, not only on the
projection API.
-/
import Lean.Elab.Command
import Lean.Compiler.Main
import Lean.Compiler.LCNF.PrettyPrinter
import Lean.Compiler.LCNF.PhaseExt
import Lean.Compiler.LCNF.Passes
import Lean.Compiler.LCNF.PassManager
import Scidonia.FracPerm.Structured.Executor
import OwnershipLcnf.Projection

open Lean
open Lean.Elab.Command

namespace CheckProjection

def privateName (mod decl : Name) : Name := mkPrivateNameCore mod decl

open Lean.Compiler.LCNF

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

def checkProjection : CommandElabM Unit := do
  let exMod : Name := `Scidonia.FracPerm.Structured.Executor
  let pExecP := (privateName exMod `Scidonia.FracPerm.Structured.execP) ++ `_redArg
  match (← replayedDecl pExecP) with
  | none => throwError "execP did not replay"
  | some d =>
    match d.value with
    | .code c =>
      match OwnershipLcnf.projectPrefix c with
      | some _ =>
        logInfo "projectPrefix accepted the replayed execP PTree.set branch"
      | none =>
        throwError "projectPrefix rejected the replayed execP PTree.set branch"
    | .extern _ => throwError "execP has no code body"

end CheckProjection

run_cmd CheckProjection.checkProjection
