/-
Concrete pair-projection check: replay the private `setAt` declaration, run
`OwnershipLcnf.projectPair` on its actual `Path.left` and `Path.right`
alternatives, and check a reified transcription of the captured artifact in the
kernel.

Run from the sibling checkout with the ownership build on `LEAN_PATH`. The
sibling is `lean-examples` at `66e64334a1c968d829903b8aec8d22f7e3b9fd3f` (the
revision the artifact was captured at), and the ownership build is
`nix develop -c lake build OwnershipLcnf` run from the ownership checkout:

    cd ../lean-examples
    nix develop -c lake env bash -c \
      'export LEAN_PATH="../ownership/.lake/build/lib/lean:$LEAN_PATH"; \
       lean ../ownership/scripts/check_pair_projection.lean'

The replay code is the same pass pipeline as `dump_executor.lean`; this script
exists so the projection is exercised on the real declaration, not only on the
projection API.

## What is asserted about the replayed declaration

* the recognizer accepts both arms; the recognized path, replacement value and
  pair are the declaration's own three parameters, and the two arms read the
  same pair and pass the same replacement value to the child;
* the selected field is read from the `Path` constructor, not from a position:
  `Path.left`'s selected field is the `oproj[0]` binder and its retained field
  the `oproj[1]` binder, `Path.right`'s are the other way round, and the
  in-place write's index is the selected side's index in each arm (`0` and `1`);
* each arm's trace has the pinned nineteen operations, its binders are pairwise
  distinct, and the bound identities agree with an independent scan of the arm:
  the path is `oproj[2]` of the dispatch discriminant, the fields are its
  `oproj[0]` and `oproj[1]`, the child call reads the continuation, the value
  and the selected field, the in-place write targets the reset join's object at
  the selected index with the child result under the `Bool.false` label, the
  `Prod.mk` copy keeps the retained field at the other position and the child
  result at the selected one under the `Bool.true` label, the `isShared` test
  reads the pair, and the pair's dispatch joins the reset join with the pair
  itself on `Bool.false` and with the erased placeholder after incrementing both
  fields and decrementing the pair on `Bool.true`;
* the model term read from the arm is the pair write on the arm's side with the
  child call's result as the replacement — and the two arms' model terms differ
  only in the side and the two field references;
* each token-preserving near miss is rejected while the unmutated declaration is
  still accepted, so a refusal is not a wholesale rejection. The near misses,
  applied to each arm separately, are: the first field projection reading the
  second field, and the second reading the first (together, the swapped pair);
  the in-place write moved to the retained index; the child call reading the
  retained component; one field increment dropped; an extra increment of the
  pair added before the pair's decrement; the pair's decrement dropped; an extra
  pair decrement added; the flag's alternatives' bodies exchanged; their labels
  exchanged; the `Bool.false` join's pair argument replaced by the path; the
  `Bool.true` join's erased placeholder replaced by the pair; an extra argument
  appended to the reset join's jumps; and the copy's two arguments swapped. The
  label exchange is the fixture that a positional "first alternative is
  `Bool.false`" selection cannot survive; the extra argument keeps every call
  token and changes only the jump's arity.

## What is kernel-checked on a reified artifact

`docs/notes/artifacts/setAt-nested.lcnf.txt` records the replayed `setAt`
declaration (digest `17644656787385327013`). The captured text is transcribed
into a `Code .impure` value (`capturedDecl`) — the outer `cases` on the path with
its `here`, `left`, `right` and `index` alternatives and the captured binder
identities — and the following facts are proved by the kernel, not by the replay
pipeline: the recognizer accepts it and reads exactly `capturedPair`'s binders,
each arm's trace has the pinned nineteen operations, each arm's selected and
retained binders and in-place write index are the side's (`Path.left`: selected
`oproj[0]`, retained `oproj[1]`, write index `0`; `Path.right`: the mirror), and
each arm's model term is the pair write on that side. The replay assertions
below then check the same recognizer on the real declaration and that the
reified artifact decodes to the same prefix.
-/
import Lean.Elab.Command
import Lean.Compiler.Main
import Lean.Compiler.LCNF.PrettyPrinter
import Lean.Compiler.LCNF.PhaseExt
import Lean.Compiler.LCNF.Passes
import Lean.Compiler.LCNF.PassManager
import Scidonia.FracPerm.StateVar.Layout5
import OwnershipLcnf.PairProjection


open Lean
open Lean.Elab.Command

namespace CheckPairProjection

def privateName (mod decl : Name) : Name := mkPrivateNameCore mod decl

open Lean.Compiler.LCNF

/-! ## The replayed declaration -/

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

/-! ## A reified transcription of the captured artifact -/

/-- Expression placeholder for the fields the recognizer does not read. -/
def ty : Expr := .const ``Unit []

/-- A `stem.index` name, the form both the capture's printed names and the
compiler's `_uniq.N` names use. -/
def nm (stem : String) (idx : Nat) : Name := Name.mkNum (Name.str .anonymous stem) idx

/-- A binder identity: the compiler's `_uniq.N` name. -/
def u (idx : Nat) : FVarId := ⟨nm "_uniq" idx⟩

/-- A binder identity as a value argument. -/
def ua (idx : Nat) : Arg .impure := .fvar (u idx)

/-- A `let` binding: the `_uniq.N` identity, the capture's printed binder name,
and the bound value. -/
def uB (idx : Nat) (printed : Name) (v : LetValue .impure) : LetDecl .impure :=
  { fvarId := u idx, binderName := printed, type := ty, value := v }

/-- A join-point or function parameter: the `_uniq.N` identity and the capture's
printed binder name. -/
def uP (idx : Nat) (printed : Name) : Param .impure :=
  { fvarId := u idx, binderName := printed, type := ty, borrow := false }

/-- A constructor alternative's info: only the name is read. -/
def cinfo (n : Name) : CtorInfo := { name := n, cidx := 0, size := 0, usize := 0, ssize := 0 }

/-- The private name of the replayed `setAt._redArg`. -/
def setAtName : Name :=
  privateName `Scidonia.FracPerm.StateVar.Layout5 `Scidonia.FracPerm.StateVar.Layout5.setAt ++
    `_redArg

/-- The private name of the replayed `takeOut._redArg`. -/
def takeOutName : Name :=
  privateName `Scidonia.FracPerm.StateVar.Layout5 `Scidonia.FracPerm.StateVar.Layout5.takeOut ++
    `_redArg

/-- The captured `Path.here` alternative (binder identities `_uniq.1`–`_uniq.3`). -/
def hereAlt : Code .impure :=
  .dec (u 1) 1 false false (some 1) <|
  .dec (u 3) 1 true false none <|
  .inc (u 2) 1 true false <|
  .return (u 2)

/-- The captured `Path.left` alternative: the prelude, the reset join with the
child call and the reuse join, the flag's two-arm dispatch, then the outer
`isShared` test and the pair's own two-arm dispatch. -/
def leftAlt : Code .impure :=
  .let (uB 4 (nm "p" 4) (.oproj 2 (u 1))) <|
  .inc (u 4) 1 false false <|
  .dec (u 1) 1 false false (some 3) <|
  .let (uB 5 (nm "fst" 5) (.oproj 0 (u 3))) <|
  .let (uB 6 (nm "snd" 6) (.oproj 1 (u 3))) <|
  .jp (FunDecl.mk (u 13) (nm "resetjp" 7) #[uP 7 (nm "_x" 8), uP 8 (nm "isShared" 9)] ty <|
    .let (uB 9 (nm "_x" 10) (.fap setAtName #[ua 4, ua 2, ua 5])) <|
    .jp (FunDecl.mk (u 11) (nm "reusejp" 11) #[uP 10 (nm "_x" 12)] ty <|
      .return (u 10)) <|
    .cases (.mk `UInt8 ty (u 8) #[
      Alt.ctorAlt (cinfo `Bool.false) <|
        .oset (u 7) 0 (ua 9) <|
        .jmp (u 11) #[ua 7],
      Alt.ctorAlt (cinfo `Bool.true) <|
        .let (uB 12 (nm "reuseFailAlloc" 13) (.ctor (cinfo `Prod.mk) #[ua 9, ua 6])) <|
        .jmp (u 11) #[ua 12] ])) <|
  .let (uB 14 (nm "isSharedCheck" 14) (.isShared (u 3))) <|
  .cases (.mk `UInt8 ty (u 14) #[
    Alt.ctorAlt (cinfo `Bool.false) <| .jmp (u 13) #[ua 3, ua 14],
    Alt.ctorAlt (cinfo `Bool.true) <|
      .inc (u 6) 1 true false <|
      .inc (u 5) 1 true false <|
      .dec (u 3) 1 true false none <|
      .jmp (u 13) #[.erased, ua 14] ])

/-- The captured `Path.right` alternative, with the mirror roles. -/
def rightAlt : Code .impure :=
  .let (uB 15 (nm "p" 15) (.oproj 2 (u 1))) <|
  .inc (u 15) 1 false false <|
  .dec (u 1) 1 false false (some 3) <|
  .let (uB 16 (nm "fst" 16) (.oproj 0 (u 3))) <|
  .let (uB 17 (nm "snd" 17) (.oproj 1 (u 3))) <|
  .jp (FunDecl.mk (u 24) (nm "resetjp" 18) #[uP 18 (nm "_x" 19), uP 19 (nm "isShared" 20)] ty <|
    .let (uB 20 (nm "_x" 21) (.fap setAtName #[ua 15, ua 2, ua 17])) <|
    .jp (FunDecl.mk (u 22) (nm "reusejp" 22) #[uP 21 (nm "_x" 23)] ty <|
      .return (u 21)) <|
    .cases (.mk `UInt8 ty (u 19) #[
      Alt.ctorAlt (cinfo `Bool.false) <|
        .oset (u 18) 1 (ua 20) <|
        .jmp (u 22) #[ua 18],
      Alt.ctorAlt (cinfo `Bool.true) <|
        .let (uB 23 (nm "reuseFailAlloc" 24) (.ctor (cinfo `Prod.mk) #[ua 16, ua 20])) <|
        .jmp (u 22) #[ua 23] ])) <|
  .let (uB 25 (nm "isSharedCheck" 25) (.isShared (u 3))) <|
  .cases (.mk `UInt8 ty (u 25) #[
    Alt.ctorAlt (cinfo `Bool.false) <| .jmp (u 24) #[ua 3, ua 25],
    Alt.ctorAlt (cinfo `Bool.true) <|
      .inc (u 17) 1 true false <|
      .inc (u 16) 1 true false <|
      .dec (u 3) 1 true false none <|
      .jmp (u 24) #[.erased, ua 25] ])

/-- The captured `Path.index` alternative: the pre-bounds destructuring, the
bounds computation, the `Bool.false`/`Bool.true` alternatives in the captured
order, and the update tail through the put-back and the return. -/
def indexAlt : Code .impure :=
  .let (uB 26 (nm "a" 26) (.oproj 0 (u 1))) <|
  .inc (u 26) 1 false false <|
  .let (uB 27 (nm "i" 27) (.oproj 1 (u 1))) <|
  .inc (u 27) 1 true false <|
  .let (uB 28 (nm "p" 28) (.oproj 2 (u 1))) <|
  .inc (u 28) 1 false false <|
  .dec (u 1) 1 false false (some 3) <|
  .let (uB 29 (nm "_x" 29) (.fap `Array.size #[.erased, ua 3])) <|
  .let (uB 30 (nm "_x" 30) (.fap `Nat.decLt #[ua 27, ua 29])) <|
  .cases (.mk `UInt8 ty (u 30) #[
    Alt.ctorAlt (cinfo `Bool.false) <|
      .dec (u 28) 1 false false none <|
      .dec (u 27) 1 true false none <|
      .dec (u 26) 1 false false none <|
      .return (u 3),
    Alt.ctorAlt (cinfo `Bool.true) <|
      .let (uB 31 (nm "_x" 31) (.fap (setAtName ++ `_closed_0) #[])) <|
      .let (uB 32 (nm "_x" 32) (.fap
        `Scidonia.FracPerm.assertExclusiveArrayImpl._redArg #[ua 31, ua 3])) <|
      .let (uB 33 (nm "_x" 33) (.fap
        `Scidonia.FracPerm.StateVar.Layout5.stateDefault #[ua 26])) <|
      .let (uB 34 (nm "val" 34) (.fap takeOutName #[ua 32, ua 27, ua 33])) <|
      .let (uB 35 (nm "fst" 35) (.oproj 0 (u 34))) <|
      .inc (u 35) 1 true false <|
      .let (uB 36 (nm "snd" 36) (.oproj 1 (u 34))) <|
      .inc (u 36) 1 true false <|
      .dec (u 34) 1 false false none <|
      .let (uB 37 (nm "_x" 37) (.fap (setAtName ++ `_closed_1) #[])) <|
      .let (uB 38 (nm "_x" 38) (.fap
        `Scidonia.FracPerm.assertExclusiveImpl._redArg #[ua 37, ua 36])) <|
      .let (uB 39 (nm "_x" 39) (.fap setAtName #[ua 28, ua 2, ua 38])) <|
      .let (uB 40 (nm "xs'" 40) (.fap `Array.set #[.erased, ua 35, ua 27, ua 39, .erased])) <|
      .dec (u 27) 1 true false none <|
      .return (u 40) ])

/-- The reified captured declaration: the outer `cases` on the path. -/
def capturedDecl : Code .impure :=
  .cases (.mk `obj ty (u 1) #[
    Alt.ctorAlt (cinfo `Scidonia.FracPerm.StateVar.Layout5.Path.here) hereAlt,
    Alt.ctorAlt (cinfo `Scidonia.FracPerm.StateVar.Layout5.Path.left) leftAlt,
    Alt.ctorAlt (cinfo `Scidonia.FracPerm.StateVar.Layout5.Path.right) rightAlt,
    Alt.ctorAlt (cinfo `Scidonia.FracPerm.StateVar.Layout5.Path.index) indexAlt ])

/-- The arms the recognizer reads from `capturedDecl`. -/
def capturedPair : OwnershipLcnf.PairArms :=
  { node := u 1, pair := u 3, value := u 2,
    left :=
      { ctor := `Scidonia.FracPerm.StateVar.Layout5.Path.left, side := .left,
        node := u 1, pair := u 3, value := u 2, path := u 4, field0 := u 5,
        field1 := u 6, resetJp := u 13, resetObj := u 7, sharedFlag := u 8,
        recursive := u 9, reuseJp := u 11, joined := u 10, osetIdx := 0,
        copy := u 12, sharedCheck := u 14 },
    right :=
      { ctor := `Scidonia.FracPerm.StateVar.Layout5.Path.right, side := .right,
        node := u 1, pair := u 3, value := u 2, path := u 15, field0 := u 16,
        field1 := u 17, resetJp := u 24, resetObj := u 18, sharedFlag := u 19,
        recursive := u 20, reuseJp := u 22, joined := u 21, osetIdx := 1,
        copy := u 23, sharedCheck := u 25 } }

/-- Recognition on the reified captured artifact, checked by the kernel: the
recognizer accepts it and reads exactly `capturedPair`'s binders. -/
example : (OwnershipLcnf.projectPair setAtName capturedDecl).map
    OwnershipLcnf.PairArms.binderNames = some capturedPair.binderNames := by
  decide

/-- Each recognized arm's trace has the pinned nineteen operations. -/
example : (OwnershipLcnf.projectPair setAtName capturedDecl).map
    OwnershipLcnf.PairArms.opCounts = some [19, 19] := by
  decide

/-- The selected and retained binders and the in-place write's index are the
`Path` constructor's, not a position: `Path.left` selects `oproj[0]`, retains
`oproj[1]` and writes index `0`; `Path.right` is the mirror. -/
example : (OwnershipLcnf.projectPair setAtName capturedDecl).map
    (fun a => (a.left.selected.name, a.left.retained.name, a.left.osetIdx,
      a.right.selected.name, a.right.retained.name, a.right.osetIdx))
    = some (nm "_uniq" 5, nm "_uniq" 6, 0, nm "_uniq" 17, nm "_uniq" 16, 1) := by
  decide

/-- The kernel-checked arms' sides come from their constructors and disagree. -/
example : (OwnershipLcnf.projectPair setAtName capturedDecl).map
    (fun a => (a.left.side, a.right.side)) = some (.left, .right) := by
  decide

/-- Each arm's model term, read from its own operands, is the pair write on that
arm's side with the child call's result as the replacement reference. -/
example : (OwnershipLcnf.projectPair setAtName capturedDecl).map
    (fun a => OwnershipLcnf.PairWriteModel.ofPrefix (fun _ => 0) (fun _ => 0) a.left)
    = some { side := .left, pairVar := 0, pairRef := 0, rep := 0, retained := 0,
             result := 0 } := by
  decide

/-- The model program is the pair write followed by the return of the joined
handle, in `Ownership.Pair`'s `PCode` vocabulary. -/
example : (OwnershipLcnf.PairWriteModel.ofPrefix (fun _ => 1) (fun _ => 2)
    capturedPair.right).toCode = .pairWrite .right 1 2 1 (.ret 1) := by
  rfl

/-! ## Independent scans of one arm -/

/-- A call in the walked arm, with the binder it was bound to. -/
private structure Call where
  name : Name
  args : Array (Arg .impure)
  bound : Option FVarId

/-- A projection in the walked code. -/
private structure Proj where
  result : FVarId
  idx : Nat
  src : FVarId

/-- A jump in the walked code, with the alternative label it sits under. -/
private structure Jmp where
  target : FVarId
  args : Array (Arg .impure)
  tag : Name

/-- An in-place write in the walked code, with the label it sits under. -/
private structure Oset where
  obj : FVarId
  idx : Nat
  val : Arg .impure
  tag : Name

/-- A constructor allocation in the walked code, with its label. -/
private structure Ctor where
  result : FVarId
  name : Name
  args : Array (Arg .impure)
  tag : Name

/-- An increment in the walked code. -/
private structure Inc where
  x : FVarId
  n : Nat
  check : Bool
  deriving Inhabited

/-- A decrement in the walked code. -/
private structure Dec where
  x : FVarId
  n : Nat
  check : Bool
  objs : Option Nat
  deriving Inhabited

/-- A dispatch in the walked code: its discriminant and, per alternative, the
label and whether the alternative contains an in-place write. -/
private structure CaseShape where
  discr : FVarId
  alts : Array (Name × Bool)
  deriving Inhabited

/-- A join-point or function declaration in the walked code. -/
private structure Jp where
  name : FVarId
  params : Array FVarId
  body : Code .impure

/-- The facts a scan of one alternative reads, independent of the recognizer's
own comparisons. -/
private structure Scan where
  projs : Array Proj := #[]
  calls : Array Call := #[]
  jmps : Array Jmp := #[]
  osets : Array Oset := #[]
  ctors : Array Ctor := #[]
  jps : Array Jp := #[]
  incs : Array Inc := #[]
  decs : Array Dec := #[]
  shareds : Array (FVarId × FVarId) := #[]
  cases : Array CaseShape := #[]

private def altLabel : Alt .impure → Name
  | .ctorAlt info _ _ => info.name
  | .alt name _ _ _ => name
  | .default _ => .anonymous

private partial def scanCode (tag : Name) (c : Code .impure) (s : Scan) : Scan :=
  match c with
  | .let d k =>
      let s := match d.value with
        | .oproj i src _ => { s with projs := s.projs.push ⟨d.fvarId, i, src⟩ }
        | .fap f args _ => { s with calls := s.calls.push ⟨f, args, some d.fvarId⟩ }
        | .ctor info args _ => { s with ctors := s.ctors.push ⟨d.fvarId, info.name, args, tag⟩ }
        | .isShared src _ => { s with shareds := s.shareds.push ⟨d.fvarId, src⟩ }
        | _ => s
      scanCode tag k s
  | .jp d k =>
      let s := { s with jps := s.jps.push ⟨d.fvarId, d.params.map (·.fvarId), d.value⟩ }
      scanCode tag k (scanCode tag d.value s)
  | .cases cs =>
      let alts := cs.alts.map fun a =>
        (altLabel a, (scanCode (altLabel a) a.getCode {}).osets.size != 0)
      let s := { s with cases := s.cases.push ⟨cs.discr, alts⟩ }
      cs.alts.foldl (fun acc a => scanCode (altLabel a) a.getCode acc) s
  | .oset obj idx val k _ =>
      scanCode tag k { s with osets := s.osets.push ⟨obj, idx, val, tag⟩ }
  | .jmp f args => { s with jmps := s.jmps.push ⟨f, args, tag⟩ }
  | .inc x n check _ k _ => scanCode tag k { s with incs := s.incs.push ⟨x, n, check⟩ }
  | .dec x n check _ objs k _ =>
      scanCode tag k { s with decs := s.decs.push ⟨x, n, check, objs⟩ }
  | .return _ | .unreach _ => s
  | .fun d k _ => scanCode tag k (scanCode tag d.value s)
  | .uset _ _ _ k _ | .sset _ _ _ _ _ k _ | .setTag _ _ k _ | .del _ k _ => scanCode tag k s

private def argFvar? : Arg .impure → Option FVarId
  | .fvar x => some x
  | _ => none

private def isErased : Arg .impure → Bool
  | .erased => true
  | _ => false

/-- The arm's alternative code, selected by constructor name. -/
private def findArm (name : Name) (c : Code .impure) : Option (Code .impure) :=
  match c with
  | .cases cs =>
      cs.alts.findSome? fun a =>
        match a with
        | .ctorAlt info code => if info.name == name then some code else none
        | _ => none
  | _ => none

/-- Whether the code binds `result` to `oproj[idx]` of `src`. -/
private def isProj (ps : Array Proj) (idx : Nat) (src result : FVarId) : Bool :=
  ps.any fun q => q.idx == idx && q.src == src && q.result == result

/-- The jump whose target is `jp`, at the given branch label. -/
private def jmpsTo (js : Array Jmp) (jp : FVarId) (tag : Name) : Array Jmp :=
  js.filter fun j => j.target == jp && j.tag == tag

/-- The binders a prefix records are pairwise distinct fvar names. -/
private def distinctBinders (p : OwnershipLcnf.ArmPrefix) : Bool :=
  let bs := OwnershipLcnf.ArmPrefix.binderNames p
  bs.eraseDups.length == bs.length

/-! ## Token-preserving near misses

Each mutation is a single-node rewrite: `rewriteTracked` applies it at the first
node whose shape it matches and reports whether it matched at all. Because the
mutations match a node kind — a projection, an `oset`, a call, an `inc`, a
`dec`, a `cases`, a jump, a constructor — and the arms' joins are join bodies the
mutation must reach, the traversal descends into `jp` and `fun` bodies as well as
into case alternatives. A mutation that matches nowhere yields `none` and is
reported, never counted as a rejection. -/

/-- Apply `f` at the first node it matches, otherwise rebuild the node with its
sub-code rewritten, reporting whether `f` matched anywhere. -/
private partial def rewriteTracked (f : Code .impure → Option (Code .impure))
    (c : Code .impure) : Bool × Code .impure :=
  match f c with
  | some c' => (true, c')
  | none =>
    match c with
    | .let d k =>
        let (b, k') := rewriteTracked f k
        (b, .let d k')
    | .jp d k =>
        let (b1, body) := rewriteTracked f d.value
        let (b2, k') := rewriteTracked f k
        (b1 || b2, .jp (FunDecl.mk d.fvarId d.binderName d.params d.type body) k')
    | .fun d k h =>
        let (b1, body) := rewriteTracked f d.value
        let (b2, k') := rewriteTracked f k
        (b1 || b2, .fun (FunDecl.mk d.fvarId d.binderName d.params d.type body) k' h)
    | .cases cs =>
        let step (acc : Bool × Array (Alt .impure)) (a : Alt .impure) :=
          let (b, code) := rewriteTracked f a.getCode
          (acc.1 || b, acc.2.push (a.updateCode code))
        let (b, alts) := cs.alts.foldl step (false, #[])
        (b, .cases (.mk cs.typeName cs.resultType cs.discr alts))
    | .inc x n ck p k h =>
        let (b, k') := rewriteTracked f k
        (b, .inc x n ck p k' h)
    | .dec x n ck p o k h =>
        let (b, k') := rewriteTracked f k
        (b, .dec x n ck p o k' h)
    | .oset x i y k h =>
        let (b, k') := rewriteTracked f k
        (b, .oset x i y k' h)
    | .uset x i y k h =>
        let (b, k') := rewriteTracked f k
        (b, .uset x i y k' h)
    | .sset x i o y t k h =>
        let (b, k') := rewriteTracked f k
        (b, .sset x i o y t k' h)
    | .setTag x ci k h =>
        let (b, k') := rewriteTracked f k
        (b, .setTag x ci k' h)
    | .del x k h =>
        let (b, k') := rewriteTracked f k
        (b, .del x k' h)
    | c => (false, c)

/-- Apply a mutation to one arm of the outer `cases`, keeping the dispatch and
the other alternatives. Every near miss below is applied this way, so what is
rejected is that arm and not an unrelated alternative. -/
private def mapArm (ctorName : Name) (f : Code .impure → Option (Code .impure)) :
    Code .impure → Option (Code .impure)
  | .cases cs@(.mk _ _ _ alts) =>
      (fun alts' => Code.cases (.mk cs.typeName cs.resultType cs.discr alts')) <$>
        alts.mapM fun a =>
          match a with
          | .ctorAlt info code h =>
              if info.name == ctorName then
                (fun c' => Alt.ctorAlt info c' h) <$> f code
              else some a
          | _ => some a
  | _ => none

/-- The first field projection reads the second field: `oproj[0]` of the pair
becomes `oproj[1]`. The walk pins the projection order, so this is rejected. -/
private def firstFieldReadsSecond (pair : FVarId) : Code .impure → Option (Code .impure)
  | .let d k =>
      match d.value with
      | .oproj 0 x h => if x == pair then some (.let { d with value := .oproj 1 x h } k) else none
      | _ => none
  | _ => none

/-- The second field projection reads the first field: `oproj[1]` of the pair
becomes `oproj[0]`. Together with the previous one this is the swapped pair. -/
private def secondFieldReadsFirst (pair : FVarId) : Code .impure → Option (Code .impure)
  | .let d k =>
      match d.value with
      | .oproj 1 x h => if x == pair then some (.let { d with value := .oproj 0 x h } k) else none
      | _ => none
  | _ => none

/-- Move the in-place write to another field index, keeping the object and the
stored value. -/
private def osetAt (obj : FVarId) (newIdx : Nat) : Code .impure → Option (Code .impure)
  | .oset o _ v k h => if o == obj then some (.oset o newIdx v k h) else none
  | _ => none

/-- Rewrite the child call's third operand, keeping the call and its other
arguments: the recursion now consumes some other component. -/
private def recChild (declName : Name) (old new : FVarId) : Code .impure → Option (Code .impure)
  | .let d k =>
      match d.value with
      | .fap f args h =>
          if f == declName && args.size == 3 && args[2]? == some (.fvar old) then
            some (.let { d with value := .fap f (args.set! 2 (.fvar new)) h } k)
          else none
      | _ => none
  | _ => none

/-- Drop an increment of `x`. -/
private def dropInc (x : FVarId) : Code .impure → Option (Code .impure)
  | .inc y _ _ _ k _ => if y == x then some k else none
  | _ => none

/-- Insert an increment of `target` immediately before the pair's checked
decrement: an extra handle across the shared branch. -/
private def insertIncBeforeDec (pair target : FVarId) : Code .impure → Option (Code .impure)
  | .dec x n c p o k h =>
      if x == pair && c && o.isNone then
        some (.dec x n c p o (.inc target 1 true false k rfl) h)
      else none
  | _ => none

/-- Drop the pair's checked decrement. -/
private def dropPairDec (pair : FVarId) : Code .impure → Option (Code .impure)
  | .dec x _ c _ o k _ => if x == pair && c && o.isNone then some k else none
  | _ => none

/-- Insert a second pair decrement immediately before the pair's checked
decrement. -/
private def insertDecBeforeDec (pair : FVarId) : Code .impure → Option (Code .impure)
  | .dec x n c p o k h =>
      if x == pair && c && o.isNone then
        some (.dec x n c p o (.dec x n c p o k rfl) h)
      else none
  | _ => none

/-- Exchange the two `Bool` alternatives' bodies of the dispatch on `discr`,
keeping both constructor labels and every instruction token. -/
private def swapBodies (discr : FVarId) : Code .impure → Option (Code .impure)
  | .cases cs@(.mk _ _ d alts) =>
      if d == discr then
        match alts with
        | #[.ctorAlt a ca ha, .ctorAlt b cb hb] =>
            if (a.name == `Bool.false && b.name == `Bool.true) ||
                (a.name == `Bool.true && b.name == `Bool.false) then
              some (.cases (.mk cs.typeName cs.resultType cs.discr
                #[Alt.ctorAlt a cb ha, Alt.ctorAlt b ca hb]))
            else none
        | _ => none
      else none
  | _ => none

/-- Exchange the two `Bool` alternatives' labels of the dispatch on `discr`,
keeping both bodies in place and every instruction token. This is the fixture a
positional selection cannot survive. -/
private def swapLabels (discr : FVarId) : Code .impure → Option (Code .impure)
  | .cases cs@(.mk _ _ d alts) =>
      if d == discr then
        match alts with
        | #[.ctorAlt a ca ha, .ctorAlt b cb hb] =>
            if (a.name == `Bool.false && b.name == `Bool.true) ||
                (a.name == `Bool.true && b.name == `Bool.false) then
              some (.cases (.mk cs.typeName cs.resultType cs.discr
                #[Alt.ctorAlt b ca ha, Alt.ctorAlt a cb hb]))
            else none
        | _ => none
      else none
  | _ => none

/-- Rewrite one argument of a jump to `target` that currently reads `old`,
keeping the target and the other arguments. -/
private def rewriteJmpArg (target : FVarId) (pos : Nat) (old new : Arg .impure) :
    Code .impure → Option (Code .impure)
  | .jmp f args =>
      if f == target && args[pos]? == some old then some (.jmp f (args.set! pos new)) else none
  | _ => none

/-- Append an erased argument to a jump to `target`: the same target and the
recorded arguments, at an arity the walk does not accept. -/
private def appendJmpArg (target : FVarId) : Code .impure → Option (Code .impure)
  | .jmp f args => if f == target then some (.jmp f (args.push .erased)) else none
  | _ => none

/-- Swap the two arguments of the `Prod.mk` bound to `copy`. -/
private def swapCtorArgs (copy : FVarId) : Code .impure → Option (Code .impure)
  | .let d k =>
      if d.fvarId == copy then
        match d.value with
        | .ctor info args h =>
            match args with
            | #[a, b] => some (.let { d with value := .ctor info #[b, a] h } k)
            | _ => none
        | _ => none
      else none
  | _ => none

/-! ## The assertions -/

/-- Assert that a mutation of one arm is rejected, that it changed the node it
targets, and that the unmutated declaration is still accepted. -/
private def expectRejectedArm (ctorName : Name) (orig : Code .impure) (arm : Code .impure)
    (label : String) (mutate : Code .impure → Option (Code .impure))
    (applied : Code .impure → Bool) : CommandElabM Unit := do
  let (matched, mutatedArm) := rewriteTracked mutate arm
  unless matched do
    throwError "the near miss did not find its target: {label}"
  unless applied mutatedArm do
    throwError "the near miss did not change the node it targets: {label}"
  let some mutated := mapArm ctorName (fun _ => some mutatedArm) orig
    | throwError "could not rebuild the declaration around the mutated arm: {label}"
  match OwnershipLcnf.projectPair setAtName mutated with
  | some _ => throwError "projectPair accepted a mutation: {label}"
  | none => pure ()
  match OwnershipLcnf.projectPair setAtName orig with
  | some _ => logInfo m!"projectPair rejected {label}"
  | none => throwError "projectPair rejected the unmutated declaration while {label} was checked"

/-- The arm's prelude, its joins and the child call, against an independent
scan: the path is `oproj[2]` of the dispatch discriminant, the fields are its
`oproj[0]` and `oproj[1]`, the `isShared` test reads the pair, the reset join
takes the object and the flag, the reuse join returns its parameter, and the
child call reads the continuation, the replacement value and the selected
field. -/
private def checkArmPrelude (a : OwnershipLcnf.PairArms) (p : OwnershipLcnf.ArmPrefix)
    (s : Scan) : CommandElabM Unit := do
  let tag := p.ctor
  unless isProj s.projs 2 a.node p.path do
    throwError "{tag}: the continuation is not oproj[2] of the dispatch discriminant"
  unless isProj s.projs 0 p.pair p.field0 do
    throwError "{tag}: the first field is not oproj[0] of the pair"
  unless isProj s.projs 1 p.pair p.field1 do
    throwError "{tag}: the second field is not oproj[1] of the pair"
  let some shared := s.shareds.find? (fun q => q.2 == p.pair)
    | throwError "{tag}: no isShared test on the pair"
  unless shared.1 == p.sharedCheck do
    throwError "{tag}: the isShared test's result is not the dispatch discriminant"
  let some reset := s.jps.find? (fun j => j.name == p.resetJp)
    | throwError "{tag}: no reset join"
  unless reset.params == #[p.resetObj, p.sharedFlag] do
    throwError "{tag}: the reset join's parameters are not the object and the flag"
  let some reuse := s.jps.find? (fun j => j.name == p.reuseJp)
    | throwError "{tag}: no reuse join"
  unless reuse.params == #[p.joined] do
    throwError "{tag}: the reuse join's parameter is not the joined handle"
  let some rec := s.calls.find? (fun q => q.name == setAtName)
    | throwError "{tag}: no recursive child call"
  unless rec.args.size == 3 do
    throwError "{tag}: the child call has {rec.args.size} arguments, expected 3"
  unless rec.args[0]?.bind argFvar? == some p.path do
    throwError "{tag}: the child call does not read the continuation"
  unless rec.args[1]?.bind argFvar? == some p.value do
    throwError "{tag}: the child call does not read the replacement value"
  unless rec.args[2]?.bind argFvar? == some p.selected do
    throwError "{tag}: the child call does not read the selected field"
  let some recResult := rec.bound
    | throwError "{tag}: the child call is not bound"
  unless recResult == p.recursive do
    throwError "{tag}: the child call's result is not the recorded one"

/-- The two writes and the joins' arguments, against an independent scan: the
in-place write is under `Bool.false` at the selected index with the child
result, the `Prod.mk` is under `Bool.true` with the child result at the selected
position and the retained field at the other, and the four jumps into the two
joins carry exactly the recorded operands. -/
private def checkArmWrites (p : OwnershipLcnf.ArmPrefix) (s : Scan) : CommandElabM Unit := do
  let tag := p.ctor
  let some os := s.osets.find? (fun o => o.obj == p.resetObj)
    | throwError "{tag}: no in-place write of the reset join's object"
  unless os.tag == `Bool.false do
    throwError "{tag}: the in-place write is not under the Bool.false label"
  unless os.idx == p.osetIdx && os.idx == p.side.idx do
    throwError "{tag}: the in-place write is not at the selected index"
  unless argFvar? os.val == some p.recursive do
    throwError "{tag}: the in-place write does not store the child result"
  let some ct := s.ctors.find? (fun q => q.result == p.copy)
    | throwError "{tag}: no copy constructor"
  unless ct.name == `Prod.mk do
    throwError "{tag}: the copy is not a Prod.mk"
  unless ct.tag == `Bool.true do
    throwError "{tag}: the copy is not under the Bool.true label"
  unless ct.args.size == 2 do
    throwError "{tag}: the copy has {ct.args.size} arguments, expected 2"
  unless ct.args[p.side.idx]?.bind argFvar? == some p.recursive do
    throwError "{tag}: the copy's selected position does not hold the child result"
  unless ct.args[p.side.other]?.bind argFvar? == some p.retained do
    throwError "{tag}: the copy's other position does not hold the retained field"
  let reuseJmps := jmpsTo s.jmps p.reuseJp `Bool.false
  let some reuseFalse := reuseJmps[0]?
    | throwError "{tag}: expected one Bool.false jump to the reuse join"
  unless reuseJmps.size == 1 && reuseFalse.args.size == 1 &&
      reuseFalse.args[0]?.bind argFvar? == some p.resetObj do
    throwError "{tag}: the Bool.false reuse join does not carry the object"
  let reuseTrue := jmpsTo s.jmps p.reuseJp `Bool.true
  let some reuseTrueJmp := reuseTrue[0]?
    | throwError "{tag}: expected one Bool.true jump to the reuse join"
  unless reuseTrue.size == 1 && reuseTrueJmp.args.size == 1 &&
      reuseTrueJmp.args[0]?.bind argFvar? == some p.copy do
    throwError "{tag}: the Bool.true reuse join does not carry the copy"
  let resetFalse := jmpsTo s.jmps p.resetJp `Bool.false
  let some resetFalseJmp := resetFalse[0]?
    | throwError "{tag}: expected one Bool.false jump to the reset join"
  unless resetFalse.size == 1 && resetFalseJmp.args.size == 2 &&
      resetFalseJmp.args[0]?.bind argFvar? == some p.pair &&
      resetFalseJmp.args[1]?.bind argFvar? == some p.sharedCheck do
    throwError "{tag}: the Bool.false reset join is not the pair and the flag"
  let resetTrue := jmpsTo s.jmps p.resetJp `Bool.true
  let some resetTrueJmp := resetTrue[0]?
    | throwError "{tag}: expected one Bool.true jump to the reset join"
  unless resetTrue.size == 1 && resetTrueJmp.args.size == 2 &&
      (resetTrueJmp.args[0]?.map isErased).getD false &&
      resetTrueJmp.args[1]?.bind argFvar? == some p.sharedCheck do
    throwError "{tag}: the Bool.true reset join is not the erased placeholder and the flag"

/-- The shared branch's own traffic, against an independent scan: the two
checked increments on `oproj[1]`'s binder and then `oproj[0]`'s, and one checked
decrement of the pair with no object count. -/
private def checkArmShared (p : OwnershipLcnf.ArmPrefix) (s : Scan) : CommandElabM Unit := do
  let tag := p.ctor
  let sharedIncs := s.incs.filter (fun q => q.check)
  unless sharedIncs.size == 2 do
    throwError "{tag}: expected two checked increments, found {sharedIncs.size}"
  unless sharedIncs[0]!.x == p.field1 && sharedIncs[1]!.x == p.field0 do
    throwError "{tag}: the checked increments are not oproj[1]'s then oproj[0]'s binder"
  let sharedDecs := s.decs.filter (fun q => q.check && q.objs.isNone)
  unless sharedDecs.size == 1 do
    throwError "{tag}: expected one checked decrement without an object count"
  unless sharedDecs[0]!.x == p.pair do
    throwError "{tag}: the checked decrement is not the pair"

/-- Check one recognized arm against an independent scan of the arm's code. -/
private def checkArmAgreement (a : OwnershipLcnf.PairArms) (p : OwnershipLcnf.ArmPrefix)
    (c : Code .impure) : CommandElabM Unit := do
  let some arm := findArm p.ctor c
    | throwError "setAt: no {p.ctor} alternative"
  let s := scanCode .anonymous arm {}
  checkArmPrelude a p s
  checkArmWrites p s
  checkArmShared p s

/-- Replay `setAt`, recognize its `Path.left` and `Path.right` alternatives, and
check the recognized arms against independent scans and near misses. -/
def checkPairProjection : CommandElabM Unit := do
  match (← replayedDecl setAtName) with
  | none => throwError "setAt did not replay"
  | some d =>
    match d.value with
    | .code c =>
      let some a := OwnershipLcnf.projectPair setAtName c
        | throwError "projectPair rejected the replayed setAt pair alternatives"
      logInfo "projectPair accepted the replayed setAt Path.left and Path.right alternatives"
      -- the recognized parameters
      let params := d.params.map (·.fvarId)
      unless params[0]? == some a.node do
        throwError "the recognized path node is not the declaration's first parameter"
      unless params[1]? == some a.value do
        throwError "the recognized value is not the declaration's second parameter"
      unless params[2]? == some a.pair do
        throwError "the recognized pair is not the declaration's third parameter"
      logInfo "the recognized path, value and pair are the declaration's parameters"
      unless a.left.pair == a.right.pair && a.left.value == a.right.value do
        throwError "the two arms do not read the same pair and value"
      logInfo "both arms read the same pair and replacement value"
      -- the sides come from the constructors
      unless a.left.side == .left && a.right.side == .right do
        throwError "the arms' sides are not their constructors' sides"
      unless a.left.ctor == `Scidonia.FracPerm.StateVar.Layout5.Path.left &&
          a.right.ctor == `Scidonia.FracPerm.StateVar.Layout5.Path.right do
        throwError "the arms' recorded constructors are not Path.left and Path.right"
      logInfo "the arms' sides are read from their Path constructors"
      -- the roles and the write index
      unless a.left.selected == a.left.field0 && a.left.retained == a.left.field1 do
        throwError "Path.left does not select oproj[0] and retain oproj[1]"
      unless a.right.selected == a.right.field1 && a.right.retained == a.right.field0 do
        throwError "Path.right does not select oproj[1] and retain oproj[0]"
      unless a.left.osetIdx == a.left.side.idx && a.right.osetIdx == a.right.side.idx do
        throwError "an in-place write is not at its own side's index"
      unless a.left.osetIdx == 0 && a.right.osetIdx == 1 do
        throwError "the in-place writes are not at indices 0 and 1"
      logInfo "the selected/retained fields and the write indices follow the constructors"
      -- The recognized arms, as the walk read them.
      let showArm (p : OwnershipLcnf.ArmPrefix) : CommandElabM Unit :=
        let binders := (OwnershipLcnf.ArmPrefix.binderNames p).map toString
        logInfo s!"{p.ctor}: side={repr p.side}, osetIdx={p.osetIdx}, \
          selected={toString p.selected.name}, retained={toString p.retained.name}, \
          ops={p.fragment.length}, binders=[{String.intercalate ", " binders}]"
      showArm a.left
      showArm a.right
      -- the traces
      unless a.opCounts == [19, 19] do
        throwError "the traces have {a.opCounts} operations, expected [19, 19]"
      unless distinctBinders a.left && distinctBinders a.right do
        throwError "an arm's recorded binders are not pairwise distinct"
      logInfo "each arm's trace has the pinned 19 operations; the binders are distinct"
      -- the model terms
      let model := fun (p : OwnershipLcnf.ArmPrefix) =>
        OwnershipLcnf.PairWriteModel.ofPrefix (fun _ => 0) (fun _ => 0) p
      unless (model a.left).side == .left && (model a.right).side == .right do
        throwError "an arm's model term is not on its own side"
      unless (model a.left).rep == 0 && (model a.right).rep == 0 do
        throwError "a model term does not read the child call's result"
      unless (model a.left).retained == 0 && (model a.right).retained == 0 do
        throwError "a model term does not read the retained field"
      logInfo "the model terms are the pair writes on the arms' own sides"
      -- independent agreement
      checkArmAgreement a a.left c
      logInfo "Path.left's bound identities agree with an independent scan"
      checkArmAgreement a a.right c
      logInfo "Path.right's bound identities agree with an independent scan"
      -- the reified artifact decodes to the replay's binders
      match OwnershipLcnf.projectPair setAtName capturedDecl with
      | none => throwError "the reified captured artifact is not recognized"
      | some q =>
        unless q.binderNames == a.binderNames do
          throwError "the reified captured artifact decodes to different binders than the replay"
        unless q.opCounts == a.opCounts do
          throwError "the reified captured artifact decodes to different traces than the replay"
        logInfo "the reified captured artifact decodes to the replayed arms"
      -- near misses, per arm
      let nearMiss (ctorName : Name) (p : OwnershipLcnf.ArmPrefix) : CommandElabM Unit := do
        let some arm := findArm ctorName c
          | throwError "no {ctorName} alternative to mutate"
        let tag := p.ctor
        let facts (code : Code .impure) : Scan := scanCode .anonymous code {}
        let expect (label : String) (f : Code .impure → Option (Code .impure))
            (applied : Code .impure → Bool) : CommandElabM Unit :=
          expectRejectedArm ctorName c arm s!"{tag}: {label}" f applied
        expect "the first field projection reading the second field"
          (firstFieldReadsSecond p.pair)
          (fun m => (facts m).projs.any fun q =>
            q.src == p.pair && q.idx == 1 && q.result == p.field0)
        expect "the second field projection reading the first field"
          (secondFieldReadsFirst p.pair)
          (fun m => (facts m).projs.any fun q =>
            q.src == p.pair && q.idx == 0 && q.result == p.field1)
        expect "the in-place write at the retained index"
          (osetAt p.resetObj p.side.other)
          (fun m => (facts m).osets.any fun o =>
            o.obj == p.resetObj && o.idx == p.side.other)
        expect "the child call on the retained component"
          (recChild setAtName p.selected p.retained)
          (fun m => (facts m).calls.any fun q =>
            q.name == setAtName && q.args[2]?.bind argFvar? == some p.retained)
        expect "a dropped field increment"
          (dropInc p.field1)
          (fun m => (facts m).incs.size == 2)
        expect "an extra pair increment"
          (insertIncBeforeDec p.pair p.pair)
          (fun m => (facts m).incs.any fun q => q.x == p.pair)
        expect "a dropped pair decrement"
          (dropPairDec p.pair)
          (fun m => (facts m).decs.size == 1)
        expect "an extra pair decrement"
          (insertDecBeforeDec p.pair)
          (fun m => (facts m).decs.size == 3)
        expect "the flag alternatives' bodies exchanged"
          (swapBodies p.sharedFlag)
          (fun m => (facts m).cases.any fun cs =>
            cs.discr == p.sharedFlag &&
              cs.alts == #[(`Bool.false, false), (`Bool.true, true)])
        expect "the flag alternatives' labels exchanged"
          (swapLabels p.sharedFlag)
          (fun m => (facts m).cases.any fun cs =>
            cs.discr == p.sharedFlag &&
              cs.alts == #[(`Bool.true, true), (`Bool.false, false)])
        expect "the false join carrying the path"
          (rewriteJmpArg p.resetJp 0 (.fvar p.pair) (.fvar p.path))
          (fun m => (facts m).jmps.any fun j =>
            j.target == p.resetJp && j.tag == `Bool.false &&
              j.args[0]? == some (.fvar p.path))
        expect "the true join carrying the pair"
          (rewriteJmpArg p.resetJp 0 .erased (.fvar p.pair))
          (fun m => (facts m).jmps.any fun j =>
            j.target == p.resetJp && j.tag == `Bool.true &&
              j.args[0]? == some (.fvar p.pair))
        expect "an extra reset-join argument"
          (appendJmpArg p.resetJp)
          (fun m => (facts m).jmps.any fun j =>
            j.target == p.resetJp && j.args.size == 3)
        expect "swapped copy arguments"
          (swapCtorArgs p.copy)
          (fun m => (facts m).ctors.any fun q =>
            q.result == p.copy && q.args[p.side.idx]?.bind argFvar? == some p.retained)
      nearMiss `Scidonia.FracPerm.StateVar.Layout5.Path.left a.left
      nearMiss `Scidonia.FracPerm.StateVar.Layout5.Path.right a.right
      -- the unmutated declaration is still accepted after the mutations
      match OwnershipLcnf.projectPair setAtName c with
      | some _ => logInfo "projectPair still accepts the unmutated declaration"
      | none => throwError "projectPair rejected the declaration after the near misses"
    | .extern _ => throwError "setAt has no code body"

end CheckPairProjection

run_cmd CheckPairProjection.checkPairProjection
