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

The script asserts four things about the real declaration:

* the recognizer accepts its `PTree.set` alternative, and the recognized array
  argument is the declaration's own array parameter;
* each token-preserving near miss is rejected — an increment inserted between
  the check and the write, the two pre-bounds projection indices swapped, the
  pre-bounds increments duplicated, the index increment dropped, the two-object
  node decrement dropped, the `Array.size` and `Nat.decLt` bindings' values
  exchanged, and the `Nat.decLt` arguments swapped — while the unmutated
  declaration is still accepted, so a refusal is not a wholesale rejection. The
  exchange is a structure fixture, not a compilable program: it keeps every call
  and argument token and changes only which binder receives which call;
* the binders the projected model reads are pairwise distinct, which is the
  fresh-binder fact the correspondence theorem relies on;
* the checker accepts the projected model from the concrete entry context, which
  is the checker-acceptance hypothesis of the target theorem instantiated on the
  real declaration.
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
        -- Fresh binders: the correspondence theorem's hypothesis, instantiated.
        let bs := binders p
        unless bs.eraseDups.length == bs.length do
          throwError "the binders the projection reads are not pairwise distinct"
        logInfo "the binders the projection reads are pairwise distinct"
        -- The target theorem's checker-acceptance hypothesis, instantiated on the
        -- real declaration under the entry context.
        let model := p.toModel (OwnershipLcnf.assignOf p 0 1 2 3)
        unless (Ownership.check (Ownership.Runner.initCtx 0) model).isSome do
          throwError "the checker rejects the projected model from the entry context"
        logInfo "the checker accepts the projected model from the entry context"
        -- Near misses. Every one is token preserving: it keeps the operation
        -- tokens the recognized path is made of and changes only their order,
        -- their multiplicity, or an argument identity.
        expectRejected c "an intervening increment between check and set"
          insertIncAfterCheck
        expectRejected c "swapped pre-bounds projection indices" swapProjIndices
        expectRejected c "duplicated pre-bounds increments" duplicateInc
        expectRejected c "a dropped index increment" dropIndexInc
        expectRejected c "a dropped two-object node decrement" dropTwoObjectDec
        expectRejected c "swapped Array.size and Nat.decLt bindings" swapBoundsFaps
        expectRejected c "swapped Nat.decLt arguments" swapDecLtArgs
    | .extern _ => throwError "execP has no code body"

end CheckProjection

run_cmd CheckProjection.checkProjection
