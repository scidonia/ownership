/-
Concrete projection check: replay the private `execP` declaration and run
`OwnershipLcnf.projectPrefix` on its actual `PTree.set` alternative, plus a
kernel-checked check on a reified transcription of the captured artifact.

Run from the sibling checkout with the ownership build on `LEAN_PATH`:

    cd ../lean-examples
    nix develop -c lake env bash -c \
      'export LEAN_PATH="../ownership/.lake/build/lib/lean:$LEAN_PATH"; \
       lean ../ownership/scripts/check_projection.lean'

The replay code is the same pass pipeline as `dump_executor.lean`; this script
exists so the projection is exercised on the real declaration, not only on the
projection API.

## What is asserted about the replayed declaration

* the recognizer accepts its `PTree.set` alternative, the recognized array
  argument is the declaration's own array parameter, and the recognized
  fragment has the pinned fourteen operations;
* the binders the projected model reads are pairwise distinct, which is the
  fresh-binder fact the layout premise relies on;
* each token-preserving near miss is rejected while the unmutated declaration is
  still accepted, so a refusal is not a wholesale rejection. The near misses are
  an increment inserted between the check and the write, the two pre-bounds
  projection indices swapped, the pre-bounds increments duplicated, the index
  increment dropped, the two-object node decrement dropped, the `Array.size` and
  `Nat.decLt` bindings' values exchanged, the `Nat.decLt` arguments swapped, the
  two bounds alternatives' bodies exchanged, and the write reading the box's
  scalar source instead of the boxed binder. The last two are this milestone's
  branch-association and operand-flow cases: the first keeps both `Bool` labels
  and every instruction token and moves the write body onto the `Bool.false`
  alternative; the second keeps every call token and bypasses the box chain. The
  `Array.size`/`Nat.decLt` exchange is a structure fixture, not a compilable
  program: it keeps every call and argument token and changes only which binder
  receives which call.

## What is kernel-checked on a reified artifact

The captured text is transcribed into a `Code .impure` value (`capturedDecl`) —
the outer `cases` on the node with its `pure`, `set` and `phase` alternatives and
the captured binder names — and three facts about it are proved by the kernel,
not by the replay pipeline: the recognizer accepts it and reads exactly
`capturedPrefix`'s binders (`decide`); the variable layout holds for
`capturedPrefix` under `assignOf` (`decide`); and `projected_check` accepts the
projected model from the concrete entry context. The replay assertions below
then check the same recognizer on the real declaration and that the reified
artifact decodes to the same prefix.
-/
import Lean.Elab.Command
import Lean.Compiler.Main
import Lean.Compiler.LCNF.PrettyPrinter
import Lean.Compiler.LCNF.PhaseExt
import Lean.Compiler.LCNF.Passes
import Lean.Compiler.LCNF.PassManager
import Scidonia.FracPerm.Structured.Executor
import OwnershipLcnf.Semantics

open Lean
open Lean.Elab.Command

namespace CheckProjection

def privateName (mod decl : Name) : Name := mkPrivateNameCore mod decl

open Lean.Compiler.LCNF

/-! ## Mutations: token-preserving near misses -/

/-- Recurse into every sub-code of a node, rebuilding it. Each mutation below
uses this for the nodes it does not rewrite. -/
private partial def descend (f : Code .impure → Code .impure) : Code .impure → Code .impure
  | .let d k => .let d (f k)
  | .cases (.mk name ty discr alts) =>
      .cases (.mk name ty discr (alts.map fun a =>
        match a with
        | .ctorAlt info code h => .ctorAlt info (f code) h
        | .default code => .default (f code)
        | .alt nm params code h => .alt nm params (f code) h))
  | .jp d k => .jp d (f k)
  | .fun d k h => .fun d (f k) h
  | .inc x n c p k h => .inc x n c p (f k) h
  | .dec x n c p o k h => .dec x n c p o (f k) h
  | .oset x i y k h => .oset x i y (f k) h
  | .uset x i y k h => .uset x i y (f k) h
  | .sset x i o y t k h => .sset x i o y t (f k) h
  | .setTag x ci k h => .setTag x ci (f k) h
  | .del x k h => .del x (f k) h
  | c => c

/-- Insert an `inc checked` immediately after the exclusivity check. This is the
rejection fixture: a path-preserving projector must not still see the check and
set as adjacent supported operations. -/
private partial def insertIncAfterCheck : Code .impure → Code .impure
  | .let d k =>
      let k' := insertIncAfterCheck k
      match d.value with
      | .fap f _ _ =>
          if f == `Scidonia.FracPerm.assertExclusiveArrayImpl ||
             f == `Scidonia.FracPerm.assertExclusiveArrayImpl._redArg then
            .let d (.inc d.fvarId 1 false false k' rfl)
          else .let d k'
      | _ => .let d k'
  | c => descend insertIncAfterCheck c

/-- Swap the two pre-bounds projection indices: `oproj[0]` becomes `oproj[1]` and
the reverse. The recognizer's index and continuation projections are pinned, so
this must be rejected. -/
private partial def swapProjIndices : Code .impure → Code .impure
  | .let d k =>
      let v := match d.value with
        | .oproj 0 var h => .oproj 1 var h
        | .oproj 1 var h => .oproj 0 var h
        | v => v
      .let { d with value := v } (swapProjIndices k)
  | c => descend swapProjIndices c

/-- Duplicate every increment. The exact walk expects one increment on the index
and one on the continuation, so this must be rejected. -/
private partial def duplicateInc : Code .impure → Code .impure
  | .inc x n check persistent k h =>
      .inc x n check persistent (.inc x n check persistent (duplicateInc k) h) h
  | c => descend duplicateInc c

/-- Drop the index increment (the one emitted with the reference-check flag),
keeping the continuation's increment. -/
private partial def dropIndexInc : Code .impure → Code .impure
  | .inc _ 1 true false k _ => dropIndexInc k
  | c => descend dropIndexInc c

/-- Drop the two-object decrement of the destructured node, keeping every other
operation. -/
private partial def dropTwoObjectDec : Code .impure → Code .impure
  | .dec _ 1 _ _ (some 2) k _ => dropTwoObjectDec k
  | c => descend dropTwoObjectDec c

/-- Swap the two consecutive bounds bindings' values: the `Array.size` result
binding receives the `Nat.decLt` call and the reverse. -/
private partial def swapBoundsFaps : Code .impure → Code .impure
  | .let d1 (.let d2 k) =>
      match d1.value, d2.value with
      | .fap f1 a1 h1, .fap f2 a2 h2 =>
          if f1 == `Array.size && f2 == `Nat.decLt then
            .let { d1 with value := .fap f2 a2 h2 } (.let { d2 with value := .fap f1 a1 h1 } k)
          else .let d1 (swapBoundsFaps (.let d2 k))
      | _, _ => .let d1 (swapBoundsFaps (.let d2 k))
  | c => descend swapBoundsFaps c

/-- Swap the two arguments of `Nat.decLt`. The recognizer requires the index and
the size result in that order. -/
private partial def swapDecLtArgs : Code .impure → Code .impure
  | .let d k =>
      let v := match d.value with
        | .fap f args h =>
            if f == `Nat.decLt && args.size == 2 then .fap f #[args[1]!, args[0]!] h
            else .fap f args h
        | v => v
      .let { d with value := v } (swapDecLtArgs k)
  | c => descend swapDecLtArgs c

/-- Exchange the two `Bool` alternatives' constructor labels while keeping both
bodies in place and every instruction token. This is the fixture that a
positional selection cannot survive: the write body now sits on the alternative
labelled `Bool.false`, and the alternative labelled `Bool.true` carries the
bounds-failure body. Selecting "the second alternative" would still find the
write body here (on this declaration `Bool.false` comes first), so only a
constructor-identity check refuses the mutation. -/
private partial def swapBoolLabels : Code .impure → Code .impure
  | .cases cs =>
      let alts' :=
        match cs.alts with
        | #[.ctorAlt a ca ha, .ctorAlt b cb hb] =>
            if (a.name == `Bool.false && b.name == `Bool.true) ||
                (a.name == `Bool.true && b.name == `Bool.false) then
              #[Alt.ctorAlt b ca ha, Alt.ctorAlt a cb hb]
            else cs.alts
        | _ => cs.alts
      .cases (.mk cs.typeName cs.resultType cs.discr (alts'.map fun alt =>
        match alt with
        | .ctorAlt info code h => .ctorAlt info (swapBoolLabels code) h
        | .default code => .default (swapBoolLabels code)
        | .alt ctorName ps code h => .alt ctorName ps (swapBoolLabels code) h))
  | c => descend swapBoolLabels c

/-- Exchange the two `Bool` alternatives' bodies while keeping both constructor
labels and every instruction token. The recognizer selects `Bool.true` by
constructor identity, so with the write body on the `Bool.false` alternative the
walk must fail; a recognizer that identified "second" with "true" would accept
the mutation on this declaration, whose `Bool.false` comes first. -/
private partial def swapBoolArms : Code .impure → Code .impure
  | .cases cs@(.mk _ _ _ alts) =>
      let alts' :=
        match alts with
        | #[.ctorAlt a ca ha, .ctorAlt b cb hb] =>
            if a.name == `Bool.false && b.name == `Bool.true then
              #[Alt.ctorAlt a cb ha, Alt.ctorAlt b ca hb]
            else if a.name == `Bool.true && b.name == `Bool.false then
              #[Alt.ctorAlt a cb ha, Alt.ctorAlt b ca hb]
            else alts
        | _ => alts
      .cases (.mk cs.typeName cs.resultType cs.discr (alts'.map fun a =>
        match a with
        | .ctorAlt info code h => .ctorAlt info (swapBoolArms code) h
        | .default code => .default (swapBoolArms code)
        | .alt ctorName ps code h => .alt ctorName ps (swapBoolArms code) h))
  | c => descend swapBoolArms c

/-- Rewrite the `Array.set!` in `k` so that its value argument is `src` instead of
the boxed binder `boxed`, keeping the call and every other argument token. -/
private partial def rewriteSetValue (boxed src : FVarId) : Code .impure → Code .impure
  | .let d k =>
      let v := match d.value with
        | .fap f args h =>
            if f == `Array.set! && args.size == 4 && args[3]! == .fvar boxed then
              .fap f (args.set! 3 (.fvar src)) h
            else .fap f args h
        | v => v
      .let { d with value := v } (rewriteSetValue boxed src k)
  | c => descend (rewriteSetValue boxed src) c

/-- The operand-flow near miss: the write reads the box's scalar source instead of
the boxed binder it actually reads. This is the emitted operand the box chain
produces being bypassed — the defect the fragment semantics no longer has. Every
call and argument token is kept; only which binder the write reads changes. -/
private partial def bypassBox : Code .impure → Code .impure
  | .let d k =>
      match d.value with
      | .box _ src => .let d (rewriteSetValue d.fvarId src (bypassBox k))
      | _ => .let d (bypassBox k)
  | c => descend bypassBox c

/-! ## The replayed declaration -/

/-- Give `Array.set!` an extra erased argument. Every recognized operand keeps its
position and identity, so only an explicit argument-count check rejects this; a
recognizer that read the operands by index alone would accept it. -/
private partial def extraSetArg : Code .impure → Code .impure
  | .let d k =>
      let v := match d.value with
        | .fap f args h =>
            if f == `Array.set! then .fap f (args.push .erased) h else .fap f args h
        | v => v
      .let { d with value := v } (extraSetArg k)
  | c => descend extraSetArg c

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

`docs/notes/artifacts/execP.lcnf.txt` records the replayed `execP` declaration
(digest `15626230893919229497`): an outer `cases` on the node with `pure`, `set`
and `phase` alternatives. The value below transcribes its statements and binders.
The `PTree.set` alternative is the one the projection models; the outer `cases`
keeps all three alternatives so the dispatch is the captured one.

Two name layers are transcribed. The capture prints each binder's `binderName`
(`x.1`, `i.3`, `_x.6`, …); the `FVarId` the recognizer reads is the compiler's
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

/-- A constructor alternative's info: only the name is read. -/
def cinfo (n : Name) : CtorInfo := { name := n, cidx := 0, size := 0, usize := 0, ssize := 0 }

/-- The nested `execP` call's name in the captured replay. -/
def execPName : Name :=
  privateName `Scidonia.FracPerm.Structured.Executor `Scidonia.FracPerm.Structured.execP ++
    `_redArg

/-- The nested `execR` call's name in the captured replay. -/
def execRName : Name :=
  privateName `Scidonia.FracPerm.Structured.Executor `Scidonia.FracPerm.Structured.execR ++
    `_redArg

/-- The captured `PTree.pure` alternative (array parameter `_uniq.1`, node
parameter `_uniq.2`, its extracted array `_uniq.3`). -/
def pureAlt : Code .impure :=
  .dec (u 1) 1 false false none <|
  .let (uB 3 (nm "a" 2) (.oproj 0 (u 2))) <|
  .inc (u 3) 1 true false <|
  .dec (u 2) 1 false false (some 1) <|
  .return (u 3)

/-- The captured `PTree.set` alternative: the pre-bounds destructuring, the bounds
computation, and the `Bool.false`/`Bool.true` alternatives in the captured
order, with the write body on `Bool.true`. Binder identities follow the capture's
printed order: index `i.3`, replacement `v.4`, continuation `k.5`, size `_x.6`,
bounds `_x.7`, site `_x.11`, check `_x.12`, box `_x.13`, write `_x.14`. -/
def setAlt : Code .impure :=
  .let (uB 4 (nm "i" 3) (.oproj 0 (u 2))) <|
  .inc (u 4) 1 true false <|
  .let (uB 5 (nm "v" 4) (.sproj 2 0 (u 2))) <|
  .let (uB 6 (nm "k" 5) (.oproj 1 (u 2))) <|
  .inc (u 6) 1 false false <|
  .dec (u 2) 1 false false (some 2) <|
  .let (uB 7 (nm "_x" 6) (.fap `Array.size #[.erased, ua 1])) <|
  .let (uB 8 (nm "_x" 7) (.fap `Nat.decLt #[ua 4, ua 7])) <|
  .cases (.mk `Bool ty (u 8) #[
    Alt.ctorAlt (cinfo `Bool.false) <|
      .dec (u 4) 1 true false none <|
      .let (uB 9 (nm "_x" 8) (.box ty (u 8))) <|
      .let (uB 10 (nm "_x" 9) (.fvar (u 6) #[ua 9])) <|
      .let (uB 11 (nm "_x" 10) (.fap execPName #[ua 1, ua 10])) <|
      .return (u 11),
    Alt.ctorAlt (cinfo `Bool.true) <|
      .let (uB 12 (nm "_x" 11) (.fap `DumpExecutor.probeExecP._redArg._closed_0 #[])) <|
      .let (uB 13 (nm "_x" 12) (.fap
        `Scidonia.FracPerm.assertExclusiveArrayImpl._redArg #[ua 12, ua 1])) <|
      .let (uB 14 (nm "_x" 13) (.box ty (u 5))) <|
      .let (uB 15 (nm "_x" 14) (.fap `Array.set! #[.erased, ua 13, ua 4, ua 14])) <|
      .dec (u 4) 1 true false none <|
      .let (uB 16 (nm "_x" 15) (.box ty (u 8))) <|
      .let (uB 17 (nm "_x" 16) (.fvar (u 6) #[ua 16])) <|
      .let (uB 18 (nm "_x" 17) (.fap execPName #[ua 1, ua 15, ua 17])) <|
      .return (u 18) ])

/-- The captured `PTree.phase` alternative. -/
def phaseAlt : Code .impure :=
  .let (uB 19 (nm "r" 18) (.oproj 0 (u 2))) <|
  .inc (u 19) 1 false false <|
  .let (uB 20 (nm "k" 19) (.oproj 1 (u 2))) <|
  .inc (u 20) 1 false false <|
  .dec (u 2) 1 false false (some 2) <|
  .let (uB 21 (nm "_x" 20) (.fap execRName #[ua 1, ua 19])) <|
  .let (uB 22 (nm "_x" 21) (.fvar (u 20) #[ua 21])) <|
  .let (uB 23 (nm "_x" 22) (.fap execPName #[ua 1, ua 22])) <|
  .return (u 23)

/-- The reified captured declaration: the outer `cases` on the node. -/
def capturedDecl : Code .impure :=
  .cases (.mk `Scidonia.FracPerm.Structured.PTree ty (u 2) #[
    Alt.ctorAlt (cinfo `Scidonia.FracPerm.Structured.PTree.pure) pureAlt,
    Alt.ctorAlt (cinfo `Scidonia.FracPerm.Structured.PTree.set) setAlt,
    Alt.ctorAlt (cinfo `Scidonia.FracPerm.Structured.PTree.phase) phaseAlt ])

/-- The prefix the recognizer reads from `capturedDecl`. -/
def capturedPrefix : OwnershipLcnf.Prefix :=
  { node := u 2, index := u 4, value := u 5, continuation := u 6,
    sizeResult := u 7, bound := u 8, array := u 1, site := u 12,
    checkResult := u 13, boxedValue := u 14, setResult := u 15,
    indexDec := u 4 }

/-- Recognition on the reified captured artifact, checked by the kernel: the
recognizer accepts it and reads exactly `capturedPrefix`'s binders. -/
example : (OwnershipLcnf.projectPrefix capturedDecl).map OwnershipLcnf.Prefix.binderNames
    = some capturedPrefix.binderNames := by
  decide

/-- The variable layout holds for the reified artifact's prefix under the
canonical assignment: the eight binders occupy the eight distinct slots. -/
example : OwnershipLcnf.Layout (OwnershipLcnf.assignOf capturedPrefix 0 1 2 3)
    capturedPrefix :=
  ⟨by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide⟩

/-- The checker accepts the projected model from the concrete entry context, on
the reified artifact's own prefix. This is `projected_check` instantiated at the
captured declaration, so its recognition and checker acceptance are both
kernel-checked. -/
example : Ownership.check (Ownership.Runner.initCtx 0)
    (capturedPrefix.toModel (OwnershipLcnf.assignOf capturedPrefix 0 1 2 3)) =
      some ((Ownership.Runner.initCtx 0).move 0 3) :=
  OwnershipLcnf.projected_check (OwnershipLcnf.assignOf capturedPrefix 0 1 2 3)
    capturedPrefix
    ⟨by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide⟩ 0

/-! ## Assertions about the replayed declaration -/

/-- Assert that a mutation of the replayed declaration is rejected, while the
unmutated declaration is accepted (checked once, before the mutations). -/
private def expectRejected (code : Code .impure) (label : String)
    (mutate : Code .impure → Code .impure) : CommandElabM Unit := do
  match OwnershipLcnf.projectPrefix (mutate code) with
  | some _ => throwError "projectPrefix accepted a mutation: {label}"
  | none => logInfo m!"projectPrefix rejected {label}"

/-- The binders the projection reads are pairwise distinct fvar names. The index
decrement is deliberately absent: the recognizer requires it to decrement the
index binder itself, so `indexDec` is the one repeated name. -/
private def binders (p : OwnershipLcnf.Prefix) : List Name :=
  [p.node.name, p.index.name, p.value.name, p.continuation.name, p.sizeResult.name,
   p.bound.name, p.array.name, p.site.name, p.checkResult.name, p.boxedValue.name,
   p.setResult.name]

def checkProjection : CommandElabM Unit := do
  let exMod : Name := `Scidonia.FracPerm.Structured.Executor
  let pExecP := (privateName exMod `Scidonia.FracPerm.Structured.execP) ++ `_redArg
  match (← replayedDecl pExecP) with
  | none => throwError "execP did not replay"
  | some d =>
    match d.value with
    | .code c =>
      match OwnershipLcnf.projectPrefix c with
      | none =>
        throwError "projectPrefix rejected the replayed execP PTree.set branch"
      | some p =>
        logInfo "projectPrefix accepted the replayed execP PTree.set branch"
        -- The bounds computation and the write use the declaration's own array
        -- parameter, not a local copy.
        unless d.params.any (fun param => param.fvarId == p.array) do
          throwError "the recognized array argument is not the declaration's parameter"
        logInfo "the recognized array argument is the declaration's array parameter"
        -- The recognized fragment has the pinned operation count.
        unless p.fragment.length == 14 do
          throwError "the recognized fragment has {p.fragment.length} operations, expected 14"
        logInfo "the recognized fragment has the pinned 14 operations"
        -- Fresh binders: the layout premise, instantiated.
        let bs := binders p
        unless bs.eraseDups.length == bs.length do
          throwError "the binders the projection reads are not pairwise distinct"
        logInfo "the binders the projection reads are pairwise distinct"
        -- The reified artifact decodes to the same prefix as the replay. This
        -- ties the kernel-checked evidence above to the real declaration.
        match OwnershipLcnf.projectPrefix capturedDecl with
        | none => throwError "the reified captured artifact is not recognized"
        | some q =>
          unless q.binderNames == bs ++ [p.indexDec.name] do
            throwError "the reified captured artifact decodes to different binders \
              than the replay"
          logInfo "the reified captured artifact decodes to the replayed prefix"
        -- The target theorem's checker-acceptance hypothesis, instantiated on the
        -- real declaration under the entry context.
        let model := p.toModel (OwnershipLcnf.assignOf p 0 1 2 3)
        unless (Ownership.check (Ownership.Runner.initCtx 0) model).isSome do
          throwError "the checker rejects the projected model from the entry context"
        logInfo "the checker accepts the projected model from the entry context"
        -- Near misses. Every one is token preserving: it keeps the operation
        -- tokens the recognized path is made of and changes only their order,
        -- their multiplicity, an argument identity, or which alternative carries
        -- the write body.
        expectRejected c "an intervening increment between check and set"
          insertIncAfterCheck
        expectRejected c "swapped pre-bounds projection indices" swapProjIndices
        expectRejected c "duplicated pre-bounds increments" duplicateInc
        expectRejected c "a dropped index increment" dropIndexInc
        expectRejected c "a dropped two-object node decrement" dropTwoObjectDec
        expectRejected c "swapped Array.size and Nat.decLt bindings" swapBoundsFaps
        expectRejected c "swapped Nat.decLt arguments" swapDecLtArgs
        expectRejected c "swapped Bool labels (the write body labelled Bool.false)"
          swapBoolLabels
        expectRejected c "the write body moved onto the Bool.false alternative"
          swapBoolArms
        expectRejected c "the write reading the box source instead of the boxed binder"
          bypassBox
        expectRejected c "an extra argument on Array.set!" extraSetArg
    | .extern _ => throwError "execP has no code body"

end CheckProjection

run_cmd CheckProjection.checkProjection
