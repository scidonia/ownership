/-
Concrete nested-projection check: replay the private `setAt` declaration and run
`OwnershipLcnf.projectNested` on its actual `Path.index` alternative, plus a
kernel-checked check on a reified transcription of the captured artifact.

Run from the sibling checkout with the ownership build on `LEAN_PATH`:

    cd ../lean-examples
    nix develop -c lake env bash -c \
      'export LEAN_PATH="../ownership/.lake/build/lib/lean:$LEAN_PATH"; \
       lean ../ownership/scripts/check_nested_projection.lean'

The replay code is the same pass pipeline as `dump_executor.lean`; this script
exists so the projection is exercised on the real declaration, not only on the
projection API.

## What is asserted about the replayed declaration

* the recognizer accepts its `Path.index` alternative, the recognized path node,
  value and array are the declaration's own three parameters, and the recognized
  fragment has the pinned twenty-five operations;
* the bound identities agree with an independent scan of the update arm: the
  put-back's array is the `takeOut` pair's first projection, its index is the
  same selected scalar, its value is the recursive call's result, the child
  exclusivity check reads the pair's second projection, and the `takeOut` call
  reads the array check's result, the selected index and the default state;
* the binders the walk reads are pairwise distinct apart from the index
  decrement, which the recognizer requires to decrement the index itself;
* each token-preserving near miss is rejected while the unmutated declaration is
  still accepted, so a refusal is not a wholesale rejection. The near misses are
  an extra increment of the pair or of the extracted child across the update, a
  put-back through the path's array field instead of the extracted parent, a
  put-back at the bounds result instead of the selected index, a put-back of the
  extracted child instead of the recursive result, the pair projections swapped,
  the path's array-field increment's check flag flipped, the pair decrement
  dropped, the two bounds alternatives' bodies exchanged, the two bounds
  alternatives' constructor labels exchanged, and the recursive call reading the
  raw extracted child instead of the asserted one. The label exchange is the
  fixture that a positional "second alternative is `Bool.true`" selection cannot
  survive; the child-check bypass keeps every call token and changes only which
  binder the recursive call consumes.

## What is kernel-checked on a reified artifact

The captured text is transcribed into a `Code .impure` value (`capturedDecl`) —
the outer `cases` on the path with its `here`, `left`, `right` and `index`
alternatives and the captured binder names — and two facts about it are proved by
the kernel, not by the replay pipeline: the recognizer accepts it and reads
exactly `capturedPrefix`'s binders (`decide`), and the fragment it reads has the
pinned twenty-five operations (`decide`). The replay assertions below then check
the same recognizer on the real declaration and that the reified artifact decodes
to the same prefix.
-/
import Lean.Elab.Command
import Lean.Compiler.Main
import Lean.Compiler.LCNF.PrettyPrinter
import Lean.Compiler.LCNF.PhaseExt
import Lean.Compiler.LCNF.Passes
import Lean.Compiler.LCNF.PassManager
import Scidonia.FracPerm.StateVar.Layout5
import OwnershipLcnf.NestedProjection

open Lean
open Lean.Elab.Command

namespace CheckNestedProjection

def privateName (mod decl : Name) : Name := mkPrivateNameCore mod decl

open Lean.Compiler.LCNF

/-! ## Mutations: token-preserving near misses

Each mutation is applied to the `Path.index` arm only. A mutation whose target
is absent leaves the code unchanged, or returns `none` where the position itself
is required, and `expectRejected` then fails loudly: either the mutation was not
found, or the still-valid code is accepted. An unapplied mutation is therefore
never counted as a rejection. -/

/-- Recurse into every sub-code of a node, rebuilding it. Each mutation below
uses this for the nodes it does not rewrite. -/
private partial def descend (f : Code .impure → Option (Code .impure)) :
    Code .impure → Option (Code .impure)
  | .let d k => (fun k' => Code.let d k') <$> f k
  | .cases (.mk name ty discr alts) =>
      (fun alts' => Code.cases (.mk name ty discr alts')) <$> alts.mapM fun a =>
        match a with
        | .ctorAlt info code h => (fun c' => Alt.ctorAlt info c' h) <$> f code
        | .default code => Alt.default <$> f code
        | .alt nm params code h => (fun c' => Alt.alt nm params c' h) <$> f code
  | .jp d k => (fun k' => Code.jp d k') <$> f k
  | .fun d k h => (fun k' => Code.fun d k' h) <$> f k
  | .inc x n c p k h => (fun k' => Code.inc x n c p k' h) <$> f k
  | .dec x n c p o k h => (fun k' => Code.dec x n c p o k' h) <$> f k
  | .oset x i y k h => (fun k' => Code.oset x i y k' h) <$> f k
  | .uset x i y k h => (fun k' => Code.uset x i y k' h) <$> f k
  | .sset x i o y t k h => (fun k' => Code.sset x i o y t k' h) <$> f k
  | .setTag x ci k h => (fun k' => Code.setTag x ci k' h) <$> f k
  | .del x k h => (fun k' => Code.del x k' h) <$> f k
  | c => some c

/-- Apply a mutation to the outer `cases`' `Path.index` alternative, keeping the
dispatch and the other alternatives. Every near miss below is applied this way,
so what is rejected is the update path and not an unrelated arm. -/
private def mapIndexArm (f : Code .impure → Option (Code .impure)) :
    Code .impure → Option (Code .impure)
  | .cases cs@(.mk _ _ _ alts) =>
      (fun alts' => Code.cases (.mk cs.typeName cs.resultType cs.discr alts')) <$>
        alts.mapM fun a =>
          match a with
          | .ctorAlt info code h =>
              if info.name == `Scidonia.FracPerm.StateVar.Layout5.Path.index then
                (fun c' => Alt.ctorAlt info c' h) <$> f code
              else some a
          | _ => some a
  | _ => none

/-- Insert an increment of `target` immediately after the pair's decrement: an
extra handle across the update. The walk expects the child site constant there
instead, so this must be rejected. -/
private partial def insertIncAfterPairDec (pair target : FVarId) :
    Code .impure → Option (Code .impure)
  | .dec x n c p o k h =>
      if x == pair && o.isNone then
        some (Code.dec x n c p o (Code.inc target 1 true false k rfl) h)
      else (fun k' => Code.dec x n c p o k' h) <$> insertIncAfterPairDec pair target k
  | c => descend (insertIncAfterPairDec pair target) c

/-- Rewrite one operand of the `Array.set` put-back, keeping the call and the
other arguments. `pos` is the argument position (1 array, 2 index, 3 value); the
rewrite only fires when that position currently reads `old`. -/
private partial def rewriteSetArg (pos : Nat) (old new : FVarId) :
    Code .impure → Option (Code .impure)
  | .let d k =>
      let v : LetValue .impure := match d.value with
        | .fap f args h =>
            if f == `Array.set && args.size == 5 && args[pos]? == some (.fvar old) then
              LetValue.fap f (args.set! pos (.fvar new)) h
            else LetValue.fap f args h
        | v => v
      (fun k' => Code.let { d with value := v } k') <$> rewriteSetArg pos old new k
  | c => descend (rewriteSetArg pos old new) c

/-- Swap the pair's two projections: `oproj[0]` becomes `oproj[1]` and the
reverse. The recognizer pins the extracted parent to the first projection, so
this must be rejected. -/
private partial def swapPairProj (pair : FVarId) : Code .impure → Option (Code .impure)
  | .let d k =>
      let v : LetValue .impure := match d.value with
        | .oproj 0 x h => if x == pair then LetValue.oproj 1 x h else LetValue.oproj 0 x h
        | .oproj 1 x h => if x == pair then LetValue.oproj 0 x h else LetValue.oproj 1 x h
        | v => v
      (fun k' => Code.let { d with value := v } k') <$> swapPairProj pair k
  | c => descend (swapPairProj pair) c

/-- Flip the check flag of the increment on the path's array field. This is an
ownership-relevant refcount token: the emitted increment checks the reference on
that field, and the recognizer pins the flag. -/
private partial def flipIncCheck (x : FVarId) : Code .impure → Option (Code .impure)
  | .inc y n c p k h =>
      if y == x then
        some (Code.inc y n (!c) p k h)
      else (fun k' => Code.inc y n c p k' h) <$> flipIncCheck x k
  | c => descend (flipIncCheck x) c

/-- Drop the pair's decrement, keeping every other operation. The recognizer
requires it between the pair increments and the child site constant. -/
private partial def dropPairDec (pair : FVarId) : Code .impure → Option (Code .impure)
  | .dec x n c p o k h =>
      if x == pair && o.isNone then
        some k
      else (fun k' => Code.dec x n c p o k' h) <$> dropPairDec pair k
  | c => descend (dropPairDec pair) c

/-- Exchange the two `Bool` alternatives' bodies while keeping both constructor
labels and every instruction token. The recognizer selects `Bool.true` by
constructor identity, so with the update body on the `Bool.false` alternative the
walk must fail. -/
private partial def swapBoundsArms (bound : FVarId) : Code .impure → Option (Code .impure)
  | .cases cs@(.mk _ _ discr alts) =>
      if discr == bound then
        match alts with
        | #[.ctorAlt a ca ha, .ctorAlt b cb hb] =>
            if (a.name == `Bool.false && b.name == `Bool.true) ||
                (a.name == `Bool.true && b.name == `Bool.false) then
              return .cases (.mk cs.typeName cs.resultType cs.discr
                #[Alt.ctorAlt a cb ha, Alt.ctorAlt b ca hb])
            else none
        | _ => none
      else descend (swapBoundsArms bound) (.cases cs)
  | c => descend (swapBoundsArms bound) c

/-- Exchange the two `Bool` alternatives' constructor labels while keeping both
bodies in place and every instruction token. This is the fixture that a
positional selection cannot survive: the update body now sits on the alternative
labelled `Bool.false`. -/
private partial def swapBoundsLabels (bound : FVarId) : Code .impure → Option (Code .impure)
  | .cases cs@(.mk _ _ discr alts) =>
      if discr == bound then
        match alts with
        | #[.ctorAlt a ca ha, .ctorAlt b cb hb] =>
            if (a.name == `Bool.false && b.name == `Bool.true) ||
                (a.name == `Bool.true && b.name == `Bool.false) then
              return .cases (.mk cs.typeName cs.resultType cs.discr
                #[Alt.ctorAlt b ca ha, Alt.ctorAlt a cb hb])
            else none
        | _ => none
      else descend (swapBoundsLabels bound) (.cases cs)
  | c => descend (swapBoundsLabels bound) c

/-- Rewrite the recursive call's third operand so it reads the raw extracted
child instead of the asserted one: the child exclusivity check still runs, but
its result no longer reaches the recursive update. Every call token is kept. -/
private partial def bypassChildCheck (childCheck child : FVarId) :
    Code .impure → Option (Code .impure)
  | .let d k =>
      let v : LetValue .impure := match d.value with
        | .fap f args h =>
            if args.size == 3 && args[2]? == some (.fvar childCheck) then
              LetValue.fap f (args.set! 2 (.fvar child)) h
            else LetValue.fap f args h
        | v => v
      (fun k' => Code.let { d with value := v } k') <$> bypassChildCheck childCheck child k
  | c => descend (bypassChildCheck childCheck child) c

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

/-! ## A reified transcription of the captured artifact

`docs/notes/artifacts/setAt-nested.lcnf.txt` records the replayed `setAt`
declaration (digest `17644656787385327013`): an outer `cases` on the path with
`here`, `left`, `right` and `index` alternatives. The value below transcribes its
statements, binder identities and names; the `Path.index` alternative is the one
the projection models.

Two name layers are transcribed. The capture prints each binder's `binderName`
(`p.4`, `i.27`, `_x.30`, …); the `FVarId` the recognizer reads is the compiler's
unique `_uniq.N` name for the same binder. Both are kept below, so the reified
value decodes to the replay's own binders. The `Expr` fields (let types, case
result types) are placeholders: the recognizer never reads them, and the branch
and operand identities it does establish do not depend on them. -/

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

/-- A join-point or function parameter: the `_uniq.N` identity and the
capture's printed binder name. -/
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

/-- The captured `Path.left` alternative. -/
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

/-- The captured `Path.right` alternative. -/
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

/-- The prefix the recognizer reads from `capturedDecl`. -/
def capturedPrefix : OwnershipLcnf.NestedPrefix :=
  { node := u 1, array := u 3, value := u 2, childArray := u 26, index := u 27,
    path := u 28, sizeResult := u 29, bound := u 30, arraySite := u 31,
    arrayCheck := u 32, dflt := u 33, pair := u 34, parent := u 35,
    child := u 36, childSite := u 37, childCheck := u 38, recursive := u 39,
    restored := u 40, indexDec := u 27 }

/-- Recognition on the reified captured artifact, checked by the kernel: the
recognizer accepts it and reads exactly `capturedPrefix`'s binders. -/
example : (OwnershipLcnf.projectNested setAtName takeOutName capturedDecl).map
    OwnershipLcnf.NestedPrefix.binderNames = some capturedPrefix.binderNames := by
  decide

/-- The fragment the recognizer reads from the reified artifact has the pinned
twenty-five operations. -/
example : (OwnershipLcnf.projectNested setAtName takeOutName capturedDecl).map
    (fun p => p.fragment.length) = some 25 := by
  decide

/-! ## Assertions about the replayed declaration -/

/-- Assert that a mutation of the replayed declaration's update arm is rejected,
and that the mutation actually applied. -/
private def expectRejected (code : Code .impure) (label : String)
    (mutate : Code .impure → Option (Code .impure)) : CommandElabM Unit := do
  let some mutated ← pure (mutate code)
    | throwError "the near miss did not find its target: {label}"
  match OwnershipLcnf.projectNested setAtName takeOutName mutated with
  | some _ => throwError "projectNested accepted a mutation: {label}"
  | none => logInfo m!"projectNested rejected {label}"

/-- A call in the walked arm, with the binder it was bound to. -/
private structure Call where
  name : Name
  args : Array (Arg .impure)
  bound : Option FVarId

/-- Collect every application and projection in a code value, descending through
joins, cases and the effectful statements. Used for the independent agreement
checks below, which do not go through the recognizer's own comparisons. -/
private partial def collectCalls (c : Code .impure) (calls : Array Call) :
    Array Call :=
  match c with
  | .let d k =>
      let calls := match d.value with
        | .fap f args _ => calls.push ⟨f, args, some d.fvarId⟩
        | _ => calls
      collectCalls k calls
  | .jp d k => collectCalls k (collectCalls d.value calls)
  | .cases cs => cs.alts.foldl (fun acc a => collectCalls a.getCode acc) calls
  | .inc _ _ _ _ k _ | .dec _ _ _ _ _ k _ | .oset _ _ _ k _ | .uset _ _ _ k _
  | .sset _ _ _ _ _ k _ | .del _ k _ | .setTag _ _ k _ => collectCalls k calls
  | .fun d k _ => collectCalls k (collectCalls d.value calls)
  | .return _ | .jmp _ _ | .unreach _ => calls

/-- A projection in the walked code, with the binder it was bound to and the
constructor field it reads. -/
private structure Proj where
  result : FVarId
  idx : Nat
  src : FVarId

/-- Collect every projection in a code value, descending through joins, cases and
the effectful statements. -/
private partial def collectProjs (c : Code .impure) (projs : Array Proj) :
    Array Proj :=
  match c with
  | .let d k =>
      let projs := match d.value with
        | .oproj i src _ => projs.push ⟨d.fvarId, i, src⟩
        | _ => projs
      collectProjs k projs
  | .jp d k => collectProjs k (collectProjs d.value projs)
  | .cases cs => cs.alts.foldl (fun acc a => collectProjs a.getCode acc) projs
  | .inc _ _ _ _ k _ | .dec _ _ _ _ _ k _ | .oset _ _ _ k _ | .uset _ _ _ k _
  | .sset _ _ _ _ _ k _ | .del _ k _ | .setTag _ _ k _ => collectProjs k projs
  | .fun d k _ => collectProjs k (collectProjs d.value projs)
  | .return _ | .jmp _ _ | .unreach _ => projs

/-- Whether the code binds `result` to `oproj[idx]` of `src`. -/
private def isProj (ps : Array Proj) (idx : Nat) (src result : FVarId) : Bool :=
  ps.any fun q => q.idx == idx && q.src == src && q.result == result

/-- The `Bool.true` alternative of the bounds `cases` on `bound`. The bounds
`cases` sits after the arm's pre-bounds `let`/`inc`/`dec` chain, so the search
walks that chain and reads the alternatives' identities, not their bodies. -/
private def trueArmOf (bound : FVarId) (c : Code .impure) : Option (Code .impure) :=
  match c with
  | .cases cs =>
      if cs.discr == bound then
        match cs.alts with
        | #[.ctorAlt a ca _, .ctorAlt b cb _] =>
            if a.name == `Bool.true && b.name == `Bool.false then some ca
            else if a.name == `Bool.false && b.name == `Bool.true then some cb
            else none
        | _ => none
      else none
  | .let _ k => trueArmOf bound k
  | .inc _ _ _ _ k _ | .dec _ _ _ _ _ k _ | .oset _ _ _ k _ | .uset _ _ _ k _
  | .sset _ _ _ _ _ k _ | .del _ k _ | .setTag _ _ k _ => trueArmOf bound k
  | _ => none

/-- The `Path.index` alternative of the replayed declaration's outer `cases`. -/
private def findIndexArm (c : Code .impure) : Option (Code .impure) :=
  match c with
  | .cases cs =>
      cs.alts.findSome? fun a =>
        match a with
        | .ctorAlt info code =>
            if info.name == `Scidonia.FracPerm.StateVar.Layout5.Path.index then some code
            else none
        | _ => none
  | _ => none

private def argFvar? : Arg .impure → Option FVarId
  | .fvar x => some x
  | _ => none

/-- The binders the walk reads are pairwise distinct fvar names, apart from the
index decrement: the recognizer requires it to decrement the index binder
itself, so `indexDec` is the one repeated name. -/
private def distinctBinders (p : OwnershipLcnf.NestedPrefix) : Bool :=
  let bs := (OwnershipLcnf.NestedPrefix.binderNames p).dropLast
  bs.eraseDups.length == bs.length

def checkNestedProjection : CommandElabM Unit := do
  match (← replayedDecl setAtName) with
  | none => throwError "setAt did not replay"
  | some d =>
    match d.value with
    | .code c =>
      match OwnershipLcnf.projectNested setAtName takeOutName c with
      | none =>
        throwError "projectNested rejected the replayed setAt Path.index alternative"
      | some p =>
        logInfo "projectNested accepted the replayed setAt Path.index alternative"
        -- The recognized path, value and array are the declaration's own
        -- parameters: (x.1 : Path), (x.2 : value), (x.3 : array).
        let params := d.params.map (·.fvarId)
        unless params[0]? == some p.node do
          throwError "the recognized path node is not the declaration's first parameter"
        unless params[1]? == some p.value do
          throwError "the recognized value is not the declaration's second parameter"
        unless params[2]? == some p.array do
          throwError "the recognized array is not the declaration's third parameter"
        logInfo "the recognized path, value and array are the declaration's parameters"
        -- The recognized fragment has the pinned operation count.
        unless p.fragment.length == 25 do
          throwError "the recognized fragment has {p.fragment.length} operations, expected 25"
        logInfo "the recognized fragment has the pinned 25 operations"
        -- Fresh binders: the layout premise.
        unless distinctBinders p do
          throwError "the binders the projection reads are not pairwise distinct"
        unless p.indexDec == p.index do
          throwError "the index decrement is not the selected index"
        logInfo "the binders the projection reads are pairwise distinct"
        -- The bound identities agree with an independent scan of the update arm.
        let some arm := findIndexArm c | throwError "setAt: no Path.index alternative"
        let armProjs := collectProjs arm #[]
        unless isProj armProjs 0 p.node p.childArray do
          throwError "the array field is not oproj[0] of the path"
        unless isProj armProjs 1 p.node p.index do
          throwError "the index is not oproj[1] of the path"
        unless isProj armProjs 2 p.node p.path do
          throwError "the continuation is not oproj[2] of the path"
        logInfo "the path's array, index and continuation are its three projections"
        let some update := trueArmOf p.bound arm
          | throwError "the update arm is not the Bool.true alternative"
        let updateProjs := collectProjs update #[]
        unless isProj updateProjs 0 p.pair p.parent do
          throwError "the put-back array is not oproj[0] of the takeOut pair"
        unless isProj updateProjs 1 p.pair p.child do
          throwError "the extracted child is not oproj[1] of the takeOut pair"
        logInfo "the takeOut pair's projections are the parent and the extracted child"
        let calls := collectCalls update #[]
        let call (n : Name) : Option Call := calls.find? (·.name == n)
        let some set := call `Array.set | throwError "the update arm has no Array.set"
        unless set.args.size == 5 do
          throwError "Array.set has {set.args.size} arguments, expected 5"
        unless set.args[1]?.bind argFvar? == some p.parent do
          throwError "the put-back array is not the takeOut pair's first projection"
        unless set.args[2]?.bind argFvar? == some p.index do
          throwError "the put-back index is not the selected index"
        unless set.args[3]?.bind argFvar? == some p.recursive do
          throwError "the put-back value is not the recursive result"
        logInfo "the put-back uses the extracted parent, the selected index and the recursive result"
        let some take := call takeOutName | throwError "the update arm has no takeOut call"
        unless take.args.size == 3 do
          throwError "takeOut has {take.args.size} arguments, expected 3"
        unless take.args[0]?.bind argFvar? == some p.arrayCheck do
          throwError "the takeOut check result is not the array check's result"
        unless take.args[1]?.bind argFvar? == some p.index do
          throwError "the takeOut index is not the selected index"
        unless take.args[2]?.bind argFvar? == some p.dflt do
          throwError "the takeOut default is not the stateDefault result"
        logInfo "the takeOut call reads the check result, the selected index and the default state"
        let some childCheck := call `Scidonia.FracPerm.assertExclusiveImpl._redArg
          | throwError "the update arm has no child exclusivity check"
        unless childCheck.args.size == 2 do
          throwError "the child check has {childCheck.args.size} arguments, expected 2"
        unless childCheck.args[1]?.bind argFvar? == some p.child do
          throwError "the child check does not read the pair's second projection"
        logInfo "the child check reads the pair's second projection"
        let some rec := call setAtName | throwError "the update arm has no recursive call"
        unless rec.args.size == 3 do
          throwError "the recursive call has {rec.args.size} arguments, expected 3"
        unless rec.args[0]?.bind argFvar? == some p.path do
          throwError "the recursive call does not read the path's continuation"
        unless rec.args[1]?.bind argFvar? == some p.value do
          throwError "the recursive call does not read the original value parameter"
        unless rec.args[2]?.bind argFvar? == some p.childCheck do
          throwError "the recursive call does not read the asserted child"
        logInfo "the recursive call reads the continuation, the value and the asserted child"
        -- The reified artifact decodes to the same prefix as the replay. This
        -- ties the kernel-checked evidence above to the real declaration.
        match OwnershipLcnf.projectNested setAtName takeOutName capturedDecl with
        | none => throwError "the reified captured artifact is not recognized"
        | some q =>
          unless q.binderNames == p.binderNames do
            throwError "the reified captured artifact decodes to different binders \
              than the replay"
          logInfo "the reified captured artifact decodes to the replayed prefix"
        -- Near misses. Every one is token preserving: it keeps the operation
        -- tokens the recognized path is made of and changes only an argument
        -- identity, a flag, a projection index, an alternative's body or label,
        -- or adds a handle across the update.
        expectRejected c "an extra pair increment across the update"
          (mapIndexArm (insertIncAfterPairDec p.pair p.pair))
        expectRejected c "an extra extracted-child increment across the update"
          (mapIndexArm (insertIncAfterPairDec p.pair p.child))
        expectRejected c "a put-back through the path's array field"
          (mapIndexArm (rewriteSetArg 1 p.parent p.childArray))
        expectRejected c "a put-back at the bounds result"
          (mapIndexArm (rewriteSetArg 2 p.index p.bound))
        expectRejected c "a put-back of the extracted child"
          (mapIndexArm (rewriteSetArg 3 p.recursive p.child))
        expectRejected c "swapped pair projections"
          (mapIndexArm (swapPairProj p.pair))
        expectRejected c "a flipped check flag on the array field's increment"
          (mapIndexArm (flipIncCheck p.childArray))
        expectRejected c "a dropped pair decrement"
          (mapIndexArm (dropPairDec p.pair))
        expectRejected c "the update body moved onto the Bool.false alternative"
          (mapIndexArm (swapBoundsArms p.bound))
        expectRejected c "swapped Bool labels (the update body labelled Bool.false)"
          (mapIndexArm (swapBoundsLabels p.bound))
        expectRejected c "the recursive call reading the raw extracted child"
          (mapIndexArm (bypassChildCheck p.childCheck p.child))
    | .extern _ => throwError "setAt has no code body"

end CheckNestedProjection

run_cmd CheckNestedProjection.checkNestedProjection
