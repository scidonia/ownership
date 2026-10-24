/-
A partial projection from the replayed `execP` scalar-array set branch into the
`Ownership.Code` prefix.

The supported shape is the one captured in
`docs/notes/artifacts/execP.lcnf.txt`. This module now recognizes that path
structurally instead of flattening the branch:

* it selects the `PTree.set` alternative;
* it walks the actual pre-bounds destructuring and its two increments and one
  decrement, rejecting anything else;
* it requires the bounds-success `Bool.true` alternative;
* inside that alternative it requires, in order, the site constant, the
  exclusivity check, the box of the replacement value, the `Array.set!` call on
  the check result, and the index decrement; any intervening operation is
  rejected;
* it binds the set array to the check result, the set value to the boxed value,
  and the decrement to the set index.

The pre-bounds counts and the box/index facts are fixed by the recognizer and
recorded in `Prefix`. The continuation after the index decrement is outside the
returned prefix. The model still needs the boxing and index-decrement
obligations and the continuation before the intended `project_sound`
correspondence can be proved; that statement is recorded below but is not
asserted as a theorem.
-/
import Lean.Compiler.LCNF.Basic
import Ownership.Runner

open Lean
open Lean.Compiler.LCNF

namespace OwnershipLcnf

/-- The recognized emitted prefix. -/
structure Prefix where
  site : FVarId
  array : FVarId
  checkResult : FVarId
  boxedValue : FVarId
  value : FVarId
  index : FVarId
  setResult : FVarId
  indexDec : FVarId

private def fvarArg? : Arg .impure → Option FVarId
  | .fvar x => some x
  | _ => none

private def findAlt (name : Name) (c : Code .impure) : Option (Code .impure) :=
  match c with
  | .cases cs =>
      cs.alts.findSome? fun a =>
        match a with
        | .ctorAlt info code => if info.name == name then some code else none
        | _ => none
  | _ => none

/-- Walk the pre-bounds path to the bounds case, accepting only the operation
kinds the emitted sequence uses. Counts/names are not flattened away: an
unexpected operation kind stops the walk. -/
private partial def findCasesPath (c : Code .impure) : Option (Cases .impure) :=
  match c with
  | .let d k =>
      match d.value with
      | .oproj _ _ | .sproj _ _ _ | .fap _ _ _ => findCasesPath k
      | _ => none
  | .inc _ _ _ _ k _ => findCasesPath k
  | .dec _ _ _ _ _ k _ => findCasesPath k
  | .cases cs => some cs
  | _ => none

/-- Recognizer for the captured `execP` `PTree.set` path. The pre-bounds path is
walked by operation kind; the bounds-success alternative and the check/box/set
tail are matched exactly. The box, the set result and the index decrement are
bound; any extra operation in the tail makes the projection fail. -/
private def recognizeSet (setAlt : Code .impure) : Option Prefix := do
  let cs ← findCasesPath setAlt
  let trueAlt ← match cs.alts with
    | #[_, second] => some second.getCode
    | _ => findAlt `Bool.true (.cases cs)
  let .let dsite ksite := trueAlt | none
  let .let dcheck kcheck := ksite | none
  let .fap checkFn checkArgs _ := dcheck.value | none
  unless checkFn == `Scidonia.FracPerm.assertExclusiveArrayImpl ||
    checkFn == `Scidonia.FracPerm.assertExclusiveArrayImpl._redArg do none
  let .let dbox kbox := kcheck | none
  let .box _ v := dbox.value | none
  let .let dset kset := kbox | none
  let .fap setFn setArgs _ := dset.value | none
  unless setFn == `Array.set! do none
  let .dec idxDec _ _ _ _ _ _ := kset | none
  let siteArg ← checkArgs[0]?.bind fvarArg?
  let arrayArg ← checkArgs[1]?.bind fvarArg?
  let setArray ← setArgs[1]?.bind fvarArg?
  let index ← setArgs[2]?.bind fvarArg?
  let setValue ← setArgs[3]?.bind fvarArg?
  unless siteArg == dsite.fvarId do none
  unless setArray == dcheck.fvarId do none
  unless setValue == dbox.fvarId do none
  unless idxDec == index do none
  return {
    site := dsite.fvarId
    array := arrayArg
    checkResult := dcheck.fvarId
    boxedValue := dbox.fvarId
    value := v
    index := index
    setResult := dset.fvarId
    indexDec := idxDec
  }

/-- Project the captured `execP` set path. The `PTree.set` alternative is
selected, then the recognizer walks its exact supported path. Anything else is
unsupported. -/
def projectPrefix (code : Code .impure) : Option Prefix := do
  let setAlt ← findAlt `Scidonia.FracPerm.Structured.PTree.set code
  recognizeSet setAlt

/-- The model prefix corresponding to the recognized call shape. The boxed value
is represented by its source variable; the `setResult` and `indexDec` facts are
recorded in `Prefix` for the simulation proof. -/
def Prefix.toModel (assign : FVarId → Ownership.Var) (p : Prefix) : Ownership.Code :=
  Ownership.Code.let (assign p.checkResult) (Ownership.LetF.checkAlias (assign p.array))
    (Ownership.Code.setArr (assign p.checkResult) (assign p.index) (assign p.value)
      (Ownership.Code.ret (assign p.checkResult)))

/-
Intended `project_sound` (not proved here):

For the captured `execP` declaration, if `projectPrefix` returns `some p` and
`p.toModel assign = c`, then the emitted `PTree.set` path recognized here — the
pre-bounds destructuring and its counts, the bounds-success alternative, the
check, the boxed replacement, the `Array.set!` on the check result, the index
decrement, and the continuation — is simulated by `Ownership.Code.run c`,
preserving faults, the designated in-place write, and the target address. The
pre-bounds operations are fixed by the recognizer; the box/index facts are
recorded in `Prefix`; the continuation is outside the returned prefix. These
remaining model and proof obligations are the next milestone.
-/
#check projectPrefix
#check Prefix.toModel

end OwnershipLcnf
