/-
M1 measurement: dump the post-reference-counting LCNF of the sealed executor and
the layout write paths.

Run from the sibling checkout so `lake env` supplies the sibling's oleans:

    cd ../lean-examples
    nix develop -c lake env lean ../ownership/scripts/dump_executor.lean

The compiler is invoked in a separate `lean` process (not during the build of a
C-emitted module), for the reason recorded in PLAN.md §3.3.

`execP` and `execR` are private in the sibling. The script attempts the
mangled name, and also compiles a public copy of the same body (`probeExecP`)
so the emitted shape is available even when the private constant is not in the
imported kernel environment. The private constant's *IR* is read separately by
`ScidoniaTest/IRShape.lean` in the sibling.
-/
import Lean.Elab.Command
import Lean.Compiler.Main
import Lean.Compiler.LCNF.PrettyPrinter
import Lean.Compiler.LCNF.PhaseExt
import Lean.Compiler.LCNF.Passes
import Lean.Compiler.LCNF.PassManager
import Scidonia.FracPerm.Structured.Executor
import Scidonia.FracPerm.StateVar.Layout5

open Lean
open Lean.Elab.Command

namespace DumpExecutor

def privateName (mod decl : Name) : Name := mkPrivateNameCore mod decl


open Lean.Compiler.LCNF

/-- Replicate the compiler's private pass runner: run `passes` on `decls`,
carrying the purity index through each pass's `phase`/`phaseOut`. -/
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

def showReplayed (label : String) (n : Name) : CommandElabM Unit := do
  match (← replayedDecl n) with
  | none => logInfo m!"===== {label}: {n} -- no replayed declaration ====="
  | some d =>
    logInfo m!"===== {label}: replayed {d.name} (size {d.size}, params {d.params.size}) ====="
    let fmt ← liftCoreM <| ppDecl' d .impure
    logInfo fmt
    logInfo m!"replayed digest: {hash (toString fmt)}"

structure CallInfo where
  name : Name
  args : Array (Arg .impure)
  bound? : Option FVarId
  deriving Inhabited

structure Scan where
  calls : Array CallInfo := #[]
  incs : Array FVarId := #[]
  deriving Inhabited

partial def scanCode (c : Code .impure) (s : Scan) : Scan :=
  match c with
  | .let d k =>
      let s := match d.value with
        | .fap f args _ => { s with calls := s.calls.push ⟨f, args, some d.fvarId⟩ }
        | _ => s
      scanCode k s
  | .jp d k => scanCode k (scanCode d.value s)
  | .cases cs => cs.alts.foldl (fun s a => scanCode a.getCode s) s
  | .inc x _ _ _ k _ => scanCode k { s with incs := s.incs.push x }
  | .dec _ _ _ _ _ k _ | .oset _ _ _ k _ | .uset _ _ _ k _
  | .sset _ _ _ _ _ k _ | .del _ k _ | .setTag _ _ k _ => scanCode k s
  | .return _ | .jmp _ _ | .unreach _ => s

def findAlt (name : Name) (c : Code .impure) : Option (Code .impure) :=
  match c with
  | .cases cs =>
      cs.alts.findSome? fun a =>
        match a with
        | .ctorAlt info code => if info.name == name then some code else none
        | _ => none
  | _ => none

def argFvar? (a : Arg .impure) : Option FVarId :=
  match a with
  | .fvar x => some x
  | _ => none

def reportShape (d : Decl .impure) : CommandElabM Unit := do
  let code ← match d.value with
    | .code c => pure c
    | .extern _ => throwError "execP has no code body"
  let some alt := findAlt `Scidonia.FracPerm.Structured.PTree.set code
    | throwError "execP: no PTree.set alternative"
  let s := scanCode alt {}
  let chkIdx := s.calls.findIdx? fun c => c.name == `Scidonia.FracPerm.assertExclusiveArrayImpl._redArg
  let setIdx := s.calls.findIdx? fun c => c.name == `Array.set!
  let chkCall := chkIdx.bind (s.calls[·]?)
  let setCall := setIdx.bind (s.calls[·]?)
  let chkArr := chkCall.bind fun c => (c.args[1]?).bind argFvar?
  let chkBound := chkCall.bind (·.bound?)
  let setArr := setCall.bind fun c => (c.args[1]?).bind argFvar?
  let a := d.params[0]?.map (·.fvarId)
  let incA := match a with
    | some x => s.incs.any (· == x)
    | none => false
  let incChk := match chkBound with
    | some x => s.incs.any (· == x)
    | none => false
  let ordered := match chkIdx, setIdx with
    | some i, some j => i < j
    | _, _ => false
  let sameParam := chkArr == a
  let sameFlow := setArr == chkBound
  logInfo m!"execP set shape: check={chkCall.isSome}, set!={setCall.isSome}, check-array=param:{sameParam}, set-array=check-result:{sameFlow}, ordered:{ordered}, inc-param:{incA}, inc-check-result:{incChk}, calls={s.calls.size}, incs={s.incs.size}"
  unless chkCall.isSome && setCall.isSome && sameParam && sameFlow && ordered && !incA && !incChk do
    throwError "execP set alternative does not have the measured ownership shape"


def showImpure (label : String) (n : Name) : CommandElabM Unit := do
  match (← liftCoreM <| Lean.Compiler.LCNF.getLocalImpureDecl? n) with
  | some d =>
    logInfo m!"===== {label}: {d.name} (size {d.size}, params {d.params.size}) ====="
    let fmt ← liftCoreM <| Lean.Compiler.LCNF.ppDecl' d .impure
    logInfo fmt
  | none => logInfo m!"===== {label}: {n} -- no impure declaration ====="

/-- A public copy of the executor's read interpreter. -/
def probeExecR (a : @& Array UInt64) : Scidonia.FracPerm.Structured.RTree α → α
  | .pure x => x
  | .get i k => probeExecR a (k a[i]?)
  | .size k => probeExecR a (k a.size)
  | .fork l r k => probeExecR a (k (probeExecR a l, probeExecR a r))

/-- A public copy of the executor's program interpreter. -/
def probeExecP (a : Array UInt64) : Scidonia.FracPerm.Structured.PTree α → α
  | .pure x => x
  | .set i v k =>
      if i < a.size then
        probeExecP ((Scidonia.FracPerm.assertExclusiveArray
          "Scidonia.FracPerm.Structured.set" a).set! i v) (k true)
      else
        probeExecP a (k false)
  | .phase r k => probeExecP a (k (probeExecR a r))


def reportSetAtShape (d : Decl .impure) : CommandElabM Unit := do
  let code ← match d.value with
    | .code c => pure c
    | .extern _ => throwError "setAt has no code body"
  let some alt := findAlt `Scidonia.FracPerm.StateVar.Layout5.Path.index code
    | throwError "setAt: no Path.index alternative"
  let s := scanCode alt {}
  let idx (n : Name) := s.calls.findIdx? fun c => c.name == n
  let pTakeOut := (privateName `Scidonia.FracPerm.StateVar.Layout5 `Scidonia.FracPerm.StateVar.Layout5.takeOut) ++ `_redArg
  let pSetAt := (privateName `Scidonia.FracPerm.StateVar.Layout5 `Scidonia.FracPerm.StateVar.Layout5.setAt) ++ `_redArg
  let names : Array (String × Name) := #[
    ("checkArray", `Scidonia.FracPerm.assertExclusiveArrayImpl._redArg),
    ("takeOut", pTakeOut),
    ("checkElem", `Scidonia.FracPerm.assertExclusiveImpl._redArg),
    ("setAt", pSetAt),
    ("putBack", `Array.set)
  ]
  let mut positions : Array (String × Option Nat) := #[]
  for (label, n) in names do
    positions := positions.push (label, idx n)
  let vals := positions.toList.map fun (_, i) => i.getD 0
  let ordered := positions.toList.all (fun (_, i) => i.isSome) &&
    (vals.zip vals.tail).all (fun (a, b) => a < b)
  let order : Array String := positions.map fun (l, i) => s!"{l}={i}"
  logInfo m!"setAt index shape: {String.intercalate " " order.toList}, calls={s.calls.size}, incs={s.incs.size}"
  unless ordered do
    throwError "setAt Path.index does not have the measured take-out/check/recursive/put-back order"

def dump : CommandElabM Unit := do
  let exMod : Name := `Scidonia.FracPerm.Structured.Executor
  let pub : Array (String × Name) := #[
    ("runFresh", `Scidonia.FracPerm.Structured.runFresh),
    ("setLeaf", `Scidonia.FracPerm.StateVar.Layout5.setLeaf),
    ("probeExecP", ``probeExecP),
    ("probeExecR", ``probeExecR)
  ]
  liftCoreM <| Lean.Compiler.compile (pub.map (·.2))
  let exp : Array (String × Name) := pub.map fun (l, n) => (l ++ "._redArg", n ++ `_redArg)
  for (label, n) in exp do
    showImpure label n
  let pExecP := (privateName exMod `Scidonia.FracPerm.Structured.execP) ++ `_redArg
  let pExecR := (privateName exMod `Scidonia.FracPerm.Structured.execR) ++ `_redArg
  let pSetAt := (privateName `Scidonia.FracPerm.StateVar.Layout5 `Scidonia.FracPerm.StateVar.Layout5.setAt) ++ `_redArg
  showReplayed "execP (private)" pExecP
  showReplayed "execR (private)" pExecR
  showReplayed "setAt (private)" pSetAt
  match (← replayedDecl pExecP) with
  | some d => reportShape d
  | none => throwError "execP did not replay"
  match (← replayedDecl pSetAt) with
  | some d => reportSetAtShape d
  | none => throwError "setAt did not replay"

end DumpExecutor

run_cmd DumpExecutor.dump
