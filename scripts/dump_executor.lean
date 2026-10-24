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


/-! ## Branch-local pair report

The record the CLI prints for each `Path` constructor is written from the
`BranchFacts` value the inspector below returns. The inspector is a pure
function over one replayed alternative: it checks the selected/retained field
projections, the recursive child call's argument, the in-place `oset`, the
`Prod.mk` copy, and the false/true branches' joins, and it returns facts only
when those relations hold on that same alternative. -/

structure ProjInfo where
  result : FVarId
  idx : Nat
  src : FVarId

structure OsetInfo where
  obj : FVarId
  idx : Nat
  val : Arg .impure
  tag : Option (FVarId × Name)

structure CtorLet where
  result : FVarId
  name : Name
  args : Array (Arg .impure)
  tag : Option (FVarId × Name)

structure JpInfo where
  name : FVarId
  params : Array FVarId
  body : Code .impure

structure JmpInfo where
  target : FVarId
  args : Array (Arg .impure)
  tag : Option (FVarId × Name)

structure SharedInfo where
  result : FVarId
  src : FVarId

structure Facts where
  projs : Array ProjInfo := #[]
  calls : Array CallInfo := #[]
  osets : Array OsetInfo := #[]
  ctors : Array CtorLet := #[]
  jps : Array JpInfo := #[]
  jmps : Array JmpInfo := #[]
  shareds : Array SharedInfo := #[]

def altTag : Alt .impure → Name
  | .ctorAlt info _ _ => info.name
  | _ => .anonymous

partial def collectFacts (tag : Option (FVarId × Name)) (c : Code .impure)
    (s : Facts) : Facts :=
  match c with
  | .let d k =>
      let s := match d.value with
        | .oproj idx src _ => { s with projs := s.projs.push ⟨d.fvarId, idx, src⟩ }
        | .fap f args _ => { s with calls := s.calls.push ⟨f, args, some d.fvarId⟩ }
        | .ctor info args _ => { s with ctors := s.ctors.push ⟨d.fvarId, info.name, args, tag⟩ }
        | .isShared src _ => { s with shareds := s.shareds.push ⟨d.fvarId, src⟩ }
        | _ => s
      collectFacts tag k s
  | .jp d k =>
      let s := { s with jps := s.jps.push ⟨d.fvarId, d.params.map (·.fvarId), d.value⟩ }
      collectFacts tag k (collectFacts tag d.value s)
  | .cases cs =>
      cs.alts.foldl (fun s a => collectFacts (some (cs.discr, altTag a)) a.getCode s) s
  | .oset obj idx val k _ =>
      collectFacts tag k { s with osets := s.osets.push ⟨obj, idx, val, tag⟩ }
  | .inc _ _ _ _ k _ | .dec _ _ _ _ _ k _ | .uset _ _ _ k _
  | .sset _ _ _ _ _ k _ | .del _ k _ | .setTag _ _ k _ => collectFacts tag k s
  | .jmp f args => { s with jmps := s.jmps.push ⟨f, args, tag⟩ }
  | .return _ | .unreach _ => s

def isErased : Arg .impure → Bool
  | .erased => true
  | _ => false

/-- The branch-local pair facts. The inspector returns this value only when the
selected/retained projections, the child argument, the false branch's in-place
`oset` and joined pair, and the true branch's `Prod.mk` copy and joined copy all
belong to the same alternative and agree. -/
structure BranchFacts where
  ctor : Name
  selected : Nat
  retained : Nat
  exclusive : String
  shared : String
  osetObj : FVarId
  osetIdx : Nat
  child : FVarId
  retainedFvar : FVarId
  copied : FVarId
  reuseJoin : FVarId

def inspectBranch (ctorName : Name) (pairVar : FVarId) (recName : Name)
    (code : Code .impure) : Option BranchFacts := do
  let f := collectFacts none code {}
  let projs := f.projs.filter fun p => p.src == pairVar
  guard (projs.size = 2)
  guard (projs.any (fun p => p.idx = 0) && projs.any (fun p => p.idx = 1))
  let calls := f.calls.filter fun c => c.name == recName
  guard (calls.size = 1)
  let some call := calls[0]? | none
  guard (call.args.size = 3)
  let some selArg := call.args[2]? | none
  let some selField := argFvar? selArg | none
  let some selProj := projs.find? (fun p => p.result == selField) | none
  let some retProj := projs.find? (fun p => p.result != selField) | none
  guard (selProj.idx ≠ retProj.idx)
  guard (selProj.idx < 2)
  let theSel := selProj.idx
  let theRet := retProj.idx
  let some cres := call.bound? | none
  guard (f.osets.size = 1)
  let some os := f.osets[0]? | none
  guard (os.idx = theSel)
  guard (argFvar? os.val == some cres)
  guard (f.ctors.size = 1)
  let some ct := f.ctors[0]? | none
  guard (ct.name = `Prod.mk)
  guard (ct.args.size = 2)
  let some ctSel := ct.args[theSel]? | none
  let some ctRet := ct.args[theRet]? | none
  guard (argFvar? ctSel == some cres)
  guard (argFvar? ctRet == some retProj.result)
  let some (d1, a1) := os.tag | none
  let some (d2, a2) := ct.tag | none
  guard (d1 == d2 && a1 == `Bool.false && a2 == `Bool.true)
  let some reuseJp := f.jps.findSome? (fun j =>
      match j.params, j.body with
      | #[p], .return q => if p == q then some j else none
      | _, _ => none) | none
  let inReuse (jm : JmpInfo) (arg : FVarId) (branch : Name) : Bool :=
    jm.target == reuseJp.name &&
      (match jm.args, jm.tag with
       | #[a], some (d, n) => d == d1 && n == branch &&
           argFvar? a == some arg
       | _, _ => false)
  guard (f.jmps.any fun jm => inReuse jm os.obj `Bool.false)
  guard (f.jmps.any fun jm => inReuse jm ct.result `Bool.true)
  let some resetJp := f.jps.find? (fun j => j.params[0]? == some os.obj) | none
  guard (resetJp.params.size ≥ 2)
  let some sh := f.shareds.find? (fun s => s.src == pairVar) | none
  guard (f.jmps.any fun jm =>
      jm.target == resetJp.name &&
      (match jm.args, jm.tag with
       | #[a, _], some (d, n) => d == sh.result && n == `Bool.false &&
           argFvar? a == some pairVar
       | _, _ => false))
  guard (f.jmps.any fun jm =>
      jm.target == resetJp.name &&
      (match jm.args, jm.tag with
       | #[a, _], some (d, n) => d == sh.result && n == `Bool.true && isErased a
       | _, _ => false))
  return { ctor := ctorName, selected := theSel, retained := theRet,
           exclusive := "reuse", shared := "copy",
           osetObj := os.obj, osetIdx := os.idx, child := cres,
           retainedFvar := retProj.result, copied := ct.result, reuseJoin := reuseJp.name }

def shortCtor (n : Name) : String :=
  match n.components.getLast? with
  | some last => "Path." ++ toString last
  | none => toString n

def formatBranch (f : BranchFacts) : String :=
  s!"ctor={shortCtor f.ctor}; selected={f.selected}; retained={f.retained}; " ++
    s!"exclusive={f.exclusive}; shared={f.shared}"

/-! ### Near-miss mutations over the same alternative -/

partial def mapOsetIdx (obj val : FVarId) (newIdx : Nat) :
    Code .impure → Bool × Code .impure
  | .let d k =>
      let (b, k') := mapOsetIdx obj val newIdx k
      (b, .let d k')
  | .jp d k =>
      let (b1, body) := mapOsetIdx obj val newIdx d.value
      if b1 then (true, .jp (FunDecl.mk d.fvarId d.binderName d.params d.type body) k)
      else
        let (b2, k') := mapOsetIdx obj val newIdx k
        (b2, .jp d k')
  | .cases cs =>
      let step := fun (acc : Bool × Array (Alt .impure)) (a : Alt .impure) =>
        let (b, code) := mapOsetIdx obj val newIdx a.getCode
        (acc.1 || b, acc.2.push (a.updateCode code))
      let (b, alts) := cs.alts.foldl step (false, #[])
      (b, .cases (Cases.mk cs.typeName cs.resultType cs.discr alts))
  | .oset o i v k h =>
      if o == obj && argFvar? v == some val then
        (true, .oset o newIdx v k h)
      else (false, .oset o i v k h)
  | .inc x n p q k h =>
      let (b, k') := mapOsetIdx obj val newIdx k
      (b, .inc x n p q k' h)
  | .dec x n p q o k h =>
      let (b, k') := mapOsetIdx obj val newIdx k
      (b, .dec x n p q o k' h)
  | .uset x i y k h =>
      let (b, k') := mapOsetIdx obj val newIdx k
      (b, .uset x i y k' h)
  | .sset x i n y e k h =>
      let (b, k') := mapOsetIdx obj val newIdx k
      (b, .sset x i n y e k' h)
  | .del x k h =>
      let (b, k') := mapOsetIdx obj val newIdx k
      (b, .del x k' h)
  | .setTag x i k h =>
      let (b, k') := mapOsetIdx obj val newIdx k
      (b, .setTag x i k' h)
  | .jmp f args => (false, .jmp f args)
  | .return x => (false, .return x)
  | .unreach e => (false, .unreach e)

partial def mapJmpArgFvar (target old new : FVarId) :
    Code .impure → Bool × Code .impure
  | .let d k =>
      let (b, k') := mapJmpArgFvar target old new k
      (b, .let d k')
  | .jp d k =>
      let (b1, body) := mapJmpArgFvar target old new d.value
      if b1 then (true, .jp (FunDecl.mk d.fvarId d.binderName d.params d.type body) k)
      else
        let (b2, k') := mapJmpArgFvar target old new k
        (b2, .jp d k')
  | .cases cs =>
      let step := fun (acc : Bool × Array (Alt .impure)) (a : Alt .impure) =>
        let (b, code) := mapJmpArgFvar target old new a.getCode
        (acc.1 || b, acc.2.push (a.updateCode code))
      let (b, alts) := cs.alts.foldl step (false, #[])
      (b, .cases (Cases.mk cs.typeName cs.resultType cs.discr alts))
  | .jmp f args =>
      match args with
      | #[.fvar a] =>
          if f == target && a == old then (true, .jmp f #[.fvar new])
          else (false, .jmp f args)
      | _ => (false, .jmp f args)
  | .oset o i v k h =>
      let (b, k') := mapJmpArgFvar target old new k
      (b, .oset o i v k' h)
  | .inc x n p q k h =>
      let (b, k') := mapJmpArgFvar target old new k
      (b, .inc x n p q k' h)
  | .dec x n p q o k h =>
      let (b, k') := mapJmpArgFvar target old new k
      (b, .dec x n p q o k' h)
  | .uset x i y k h =>
      let (b, k') := mapJmpArgFvar target old new k
      (b, .uset x i y k' h)
  | .sset x i n y e k h =>
      let (b, k') := mapJmpArgFvar target old new k
      (b, .sset x i n y e k' h)
  | .del x k h =>
      let (b, k') := mapJmpArgFvar target old new k
      (b, .del x k' h)
  | .setTag x i k h =>
      let (b, k') := mapJmpArgFvar target old new k
      (b, .setTag x i k' h)
  | .return x => (false, .return x)
  | .unreach e => (false, .unreach e)

partial def mapCtorSwap (target : FVarId) :
    Code .impure → Bool × Code .impure
  | .let d k =>
      if d.fvarId == target then
        match d.value with
        | .ctor info args h =>
            match args with
            | #[a, b] => (true, .let { d with value := .ctor info #[b, a] h } k)
            | _ =>
                let (b, k') := mapCtorSwap target k
                (b, .let d k')
        | _ =>
            let (b, k') := mapCtorSwap target k
            (b, .let d k')
      else
        let (b, k') := mapCtorSwap target k
        (b, .let d k')
  | .jp d k =>
      let (b1, body) := mapCtorSwap target d.value
      if b1 then (true, .jp (FunDecl.mk d.fvarId d.binderName d.params d.type body) k)
      else
        let (b2, k') := mapCtorSwap target k
        (b2, .jp d k')
  | .cases cs =>
      let step := fun (acc : Bool × Array (Alt .impure)) (a : Alt .impure) =>
        let (b, code) := mapCtorSwap target a.getCode
        (acc.1 || b, acc.2.push (a.updateCode code))
      let (b, alts) := cs.alts.foldl step (false, #[])
      (b, .cases (Cases.mk cs.typeName cs.resultType cs.discr alts))
  | .jmp f args => (false, .jmp f args)
  | .oset o i v k h =>
      let (b, k') := mapCtorSwap target k
      (b, .oset o i v k' h)
  | .inc x n p q k h =>
      let (b, k') := mapCtorSwap target k
      (b, .inc x n p q k' h)
  | .dec x n p q o k h =>
      let (b, k') := mapCtorSwap target k
      (b, .dec x n p q o k' h)
  | .uset x i y k h =>
      let (b, k') := mapCtorSwap target k
      (b, .uset x i y k' h)
  | .sset x i n y e k h =>
      let (b, k') := mapCtorSwap target k
      (b, .sset x i n y e k' h)
  | .del x k h =>
      let (b, k') := mapCtorSwap target k
      (b, .del x k' h)
  | .setTag x i k h =>
      let (b, k') := mapCtorSwap target k
      (b, .setTag x i k' h)
  | .return x => (false, .return x)
  | .unreach e => (false, .unreach e)

/-- The focused AST gate: the replayed alternative must pass, and each
token-preserving near miss must change its targeted node and be rejected by the
same inspector. A changed node is asserted before the rejection, so the refusal
is not merely an unrelated malformed value. -/
def checkBranchAST (ctorName : Name) (pairVar : FVarId) (recName : Name)
    (code : Code .impure) : CommandElabM BranchFacts := do
  let some facts := inspectBranch ctorName pairVar recName code
    | throwError "setAt {ctorName}: branch-local pair relations do not hold on the replayed alternative"
  let tag := shortCtor ctorName

  let (changedOset, osetCode) := mapOsetIdx facts.osetObj facts.child facts.retained code
  unless changedOset do
    throwError "setAt {tag}: near miss did not find the targeted oset node"
  let osetFacts := collectFacts none osetCode {}
  unless osetFacts.osets.any (fun o =>
      o.obj == facts.osetObj && o.idx = facts.retained &&
        argFvar? o.val == some facts.child) do
    throwError "setAt {tag}: near miss did not alter the selected-field binding"
  if (inspectBranch ctorName pairVar recName osetCode).isSome then
    throwError "setAt {tag}: inspector accepted the altered selected-field binding"

  let (changedJmp, jmpCode) := mapJmpArgFvar facts.reuseJoin facts.osetObj facts.child code
  unless changedJmp do
    throwError "setAt {tag}: near miss did not find the false-reuse join node"
  let origJmpFacts := collectFacts none code {}
  unless !(origJmpFacts.jmps.any (fun jm =>
      jm.target == facts.reuseJoin &&
        (match jm.args with
         | #[a] => argFvar? a == some facts.child
         | _ => false))) do
    throwError "setAt {tag}: false-reuse join already carried the replacement argument"
  let jmpFacts := collectFacts none jmpCode {}
  unless jmpFacts.jmps.any (fun jm =>
      jm.target == facts.reuseJoin &&
        (match jm.args with
         | #[a] => argFvar? a == some facts.child
         | _ => false)) do
    throwError "setAt {tag}: near miss did not alter the false-reuse join binding"
  unless !(jmpFacts.jmps.any (fun jm =>
      jm.target == facts.reuseJoin &&
        (match jm.args with
         | #[a] => argFvar? a == some facts.osetObj
         | _ => false))) do
    throwError "setAt {tag}: false-reuse join still carries the old pair argument"
  if (inspectBranch ctorName pairVar recName jmpCode).isSome then
    throwError "setAt {tag}: inspector accepted the altered false-reuse join binding"

  let (changedCtor, ctorCode) := mapCtorSwap facts.copied code
  unless changedCtor do
    throwError "setAt {tag}: near miss did not find the true-copy constructor"
  let ctorFacts := collectFacts none ctorCode {}
  unless ctorFacts.ctors.any (fun c =>
      c.result == facts.copied &&
        ((c.args[facts.selected]?.bind argFvar?) == some facts.retainedFvar) &&
        ((c.args[facts.retained]?.bind argFvar?) == some facts.child)) do
    throwError "setAt {tag}: near miss did not swap the true-copy arguments"
  if (inspectBranch ctorName pairVar recName ctorCode).isSome then
    throwError "setAt {tag}: inspector accepted the swapped true-copy binding"

  return facts

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
  let some pairVar := d.params[2]?.map (·.fvarId)
    | throwError "setAt: no pair-state parameter"
  let leftCtor := `Scidonia.FracPerm.StateVar.Layout5.Path.left
  let rightCtor := `Scidonia.FracPerm.StateVar.Layout5.Path.right
  let some leftCode := findAlt leftCtor code
    | throwError "setAt: no Path.left alternative"
  let some rightCode := findAlt rightCtor code
    | throwError "setAt: no Path.right alternative"
  let leftFacts ← checkBranchAST leftCtor pairVar d.name leftCode
  let rightFacts ← checkBranchAST rightCtor pairVar d.name rightCode
  logInfo m!"setAt branch report: {formatBranch leftFacts}"
  logInfo m!"setAt branch report: {formatBranch rightFacts}"

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
