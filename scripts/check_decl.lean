/-
Reflection bridge: run the ownership discipline's recognisers on a compiled Lean
declaration.

Run from the sibling checkout so `lake env` supplies the sibling's oleans:

    cd ../lean-examples
    nix develop -c lake env bash -c 'export LEAN_PATH="../ownership/.lake/build/lib/lean:$LEAN_PATH"; lean ../ownership/scripts/check_decl.lean'

The declaration is read from the imported olean as mono LCNF, the rest of the
compiler pipeline is replayed to impure LCNF (the same replay the capture scripts
use), and `projectPrefix` / `projectNested` are applied to the result. Nothing is
hand-shaped: a declaration either matches a recogniser or it does not, and the
report says which.

The recognisers are shape-specific. `projectPrefix` accepts the flat array-write
prefix; `projectNested` accepts the nested `setAt` shape and needs the private
names of the two captured callees. That a *different* real function is rejected is
the point of the second report: reflection is general, the discipline's fragment is
not.
-/
import Lean.Elab.Command
import Lean.Compiler.Main
import Lean.Compiler.LCNF.PrettyPrinter
import Lean.Compiler.LCNF.PhaseExt
import Lean.Compiler.LCNF.Passes
import Lean.Compiler.LCNF.PassManager
import OwnershipLcnf.Projection
import OwnershipLcnf.NestedProjection
import Scidonia.FracPerm.StateVar.Layout5

open Lean
open Lean.Elab.Command
open Lean.Compiler.LCNF

namespace CheckDecl

def privateName (mod decl : Name) : Name := mkPrivateNameCore mod decl

/-- The private name of the replayed `setAt._redArg`. -/
def setAtName : Name :=
  privateName `Scidonia.FracPerm.StateVar.Layout5 `Scidonia.FracPerm.StateVar.Layout5.setAt ++
    `_redArg

/-- The private name of the replayed `takeOut._redArg`. -/
def takeOutName : Name :=
  privateName `Scidonia.FracPerm.StateVar.Layout5 `Scidonia.FracPerm.StateVar.Layout5.takeOut ++
    `_redArg

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

/-- Replay the remainder of the mono pipeline and the full impure pipeline on a
mono declaration read from the olean. -/
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

/-- Report what the discipline makes of one compiled declaration. -/
def report (label : String) (n : Name) : CommandElabM Unit := do
  match (← replayedDecl n) with
  | none =>
    logInfo m!"{label} ({n}): no mono declaration in the imported olean; \
      the private constant's body is not saved there"
  | some d =>
    match d.value with
    | .code code =>
      let flat := OwnershipLcnf.projectPrefix code
      let nested := OwnershipLcnf.projectNested setAtName takeOutName code
      logInfo m!"{label} ({n}):"
      logInfo m!"  flat recogniser:   {if flat.isSome then "accepted" else "rejected"}"
      logInfo m!"  nested recogniser: {if nested.isSome then "accepted" else "rejected"}"
      if let some p := nested then
        logInfo m!"  recognised fragment: {p.fragment.length} operations"
    | _ => logInfo m!"{label} ({n}): the replayed declaration has no code value"

run_cmd do
  report "captured setAt" setAtName
  report "different shape (setLeaf)" `Scidonia.FracPerm.StateVar.Layout5.setLeaf

end CheckDecl
