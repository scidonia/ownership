/-
A partial projection from the replayed `execP` scalar-array set branch into the
`Ownership.Code` prefix.

The supported shape is the one captured in
`docs/notes/artifacts/execP.lcnf.txt` (`execP`, replayed digest
`15626230893919229497`). This module recognizes that path structurally instead
of flattening the branch:

* it selects the `PTree.set` alternative;
* it walks the actual pre-bounds destructuring in the emitted order, and
  requires the exact operations and the exact argument identities: the index
  projection, its increment, the replacement-value projection, the continuation
  projection, its increment, the two-object decrement of the node, the
  `Array.size` call on the function's array parameter, the `Nat.decLt` call on
  the extracted index and that size, and the `cases` on its result;
* it requires the bounds-success `Bool.true` alternative;
* inside that alternative it requires, in order, the site constant, the
  exclusivity check, the box of the replacement value, the `Array.set!` call on
  the check result, and the index decrement; any intervening operation is
  rejected;
* it binds the set array to the check result, the set value to the boxed value,
  and the decrement to the set index.

The pre-bounds counts, the projections and the box/index facts are fixed by the
recognizer and recorded in `Prefix`. The module's `Semantics.lean` gives the
recognized node kinds an explicit meaning and proves the projection's
correspondence; `Prefix.toModel` is the model term that correspondence is
stated against.

## What is *not* modeled

Two parts of the emitted path are named non-claims, bound for provenance but
never threaded into the model:

* **The index's own `inc`/`dec` pair.** The index is a scalar, not part of the
  array's mutable footprint, and `Ownership.Code.dec` requires an owned
  reference (`Ownership/Code.lean:127-130`), so `dec` on it would fault in the
  model's own semantics. `Prefix.indexDec` records the emitted decrement only.
* **The continuation and the recursive call.** After the index decrement the
  emitted code boxes the bounds result, calls the extracted continuation `k.5`,
  and recurses into `execP` on the updated array. The certified prefix ends at
  the designated write's return, matching `Ownership.Runner.execSet`'s
  boundary; `Prefix.continuation` and `Prefix.bound` record what the
  continuation would consume.
-/
import Lean.Compiler.LCNF.Basic
import Ownership.Runner

open Lean
open Lean.Compiler.LCNF

namespace OwnershipLcnf

/-- The recognized emitted prefix. The first eight fields are the pre-bounds
destructuring and the bounds computation; the rest are the bounds-success tail.
`indexDec`, `continuation`, `bound` and `setResult` are recorded for provenance
and are outside the modeled prefix. -/
structure Prefix where
  /-- The `PTree.set` value the pre-bounds path destructures. -/
  node : FVarId
  /-- The extracted index (`oproj[0]`). -/
  index : FVarId
  /-- The extracted replacement value (`sproj[2,0]`). -/
  value : FVarId
  /-- The extracted continuation (`oproj[1]`); not modeled. -/
  continuation : FVarId
  /-- The `Array.size` result. -/
  sizeResult : FVarId
  /-- The `Nat.decLt` result, the `cases` discriminant. -/
  bound : FVarId
  /-- The array the bounds computation and the write use. -/
  array : FVarId
  /-- The constant site argument passed to the exclusivity check. -/
  site : FVarId
  /-- The exclusivity check's result. -/
  checkResult : FVarId
  /-- The boxed replacement value passed to `Array.set!`. -/
  boxedValue : FVarId
  /-- The `Array.set!` result. -/
  setResult : FVarId
  /-- The index decrement that follows the write; not modeled. -/
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

/-- The pre-bounds destructuring of the `PTree.set` node, in the emitted order.

The captured sequence is exactly `oproj[0] node` → `inc index` → `sproj[2,0]`
node → `oproj[1] node` → `inc continuation` → `dec[2 objs] node` →
`Array.size array` → `Nat.decLt index sizeResult` → `cases` on the `Nat.decLt`
result. Operation kinds, counts, and the fvar identities of every argument are
required; a duplicate, a dropped operation, an extra operation, a swapped
projection index, a swapped `Nat.decLt` argument or a reordered pair of
bindings all fail the walk. -/
private structure Pre where
  node : FVarId
  index : FVarId
  value : FVarId
  continuation : FVarId
  sizeResult : FVarId
  bound : FVarId
  array : FVarId
  cases : Cases .impure

private def recognizePre (c : Code .impure) : Option Pre := do
  let .let dIndex k0 := c | none
  let .oproj 0 node _ := dIndex.value | none
  let index := dIndex.fvarId
  let .inc incIndex 1 true false k1 _ := k0 | none
  unless incIndex == index do none
  let .let dValue k2 := k1 | none
  let .sproj 2 0 nodeValue _ := dValue.value | none
  unless nodeValue == node do none
  let value := dValue.fvarId
  let .let dCont k3 := k2 | none
  let .oproj 1 nodeCont _ := dCont.value | none
  unless nodeCont == node do none
  let continuation := dCont.fvarId
  let .inc incCont 1 false false k4 _ := k3 | none
  unless incCont == continuation do none
  let .dec decNode 1 false false (some 2) k5 _ := k4 | none
  unless decNode == node do none
  let .let dSize k6 := k5 | none
  let .fap sizeFn sizeArgs _ := dSize.value | none
  unless sizeFn == `Array.size do none
  let array ← sizeArgs[1]?.bind fvarArg?
  let .let dBound k7 := k6 | none
  let .fap boundFn boundArgs _ := dBound.value | none
  unless boundFn == `Nat.decLt do none
  unless boundArgs[0]?.bind fvarArg? == some index do none
  unless boundArgs[1]?.bind fvarArg? == some dSize.fvarId do none
  let .cases cs := k7 | none
  unless cs.discr == dBound.fvarId do none
  return { node, index, value, continuation, sizeResult := dSize.fvarId,
           bound := dBound.fvarId, array, cases := cs }

/-- Recognizer for the captured `execP` `PTree.set` path. The pre-bounds path is
matched op by op; the bounds-success alternative and the check/box/set/index-dec
tail are matched exactly. The box, the set result and the index decrement are
bound; any extra operation in the tail makes the projection fail. -/
private def recognizeSet (setAlt : Code .impure) : Option Prefix := do
  let pre ← recognizePre setAlt
  let trueAlt ← match pre.cases.alts with
    | #[_, second] => some second.getCode
    | _ => findAlt `Bool.true (.cases pre.cases)
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
  let .dec idxDec 1 true false none _ _ := kset | none
  let siteArg ← checkArgs[0]?.bind fvarArg?
  let arrayArg ← checkArgs[1]?.bind fvarArg?
  let setArray ← setArgs[1]?.bind fvarArg?
  let index ← setArgs[2]?.bind fvarArg?
  let setValue ← setArgs[3]?.bind fvarArg?
  unless siteArg == dsite.fvarId do none
  unless arrayArg == pre.array do none
  unless setArray == dcheck.fvarId do none
  unless setValue == dbox.fvarId do none
  unless index == pre.index do none
  unless idxDec == pre.index do none
  unless v == pre.value do none
  return { node := pre.node, index := pre.index, value := pre.value,
           continuation := pre.continuation, sizeResult := pre.sizeResult,
           bound := pre.bound, array := pre.array, site := dsite.fvarId,
           checkResult := dcheck.fvarId, boxedValue := dbox.fvarId,
           setResult := dset.fvarId, indexDec := idxDec }

/-- Project the captured `execP` set path. The `PTree.set` alternative is
selected, then the recognizer walks its exact supported path. Anything else is
unsupported. -/
def projectPrefix (code : Code .impure) : Option Prefix := do
  let setAlt ← findAlt `Scidonia.FracPerm.Structured.PTree.set code
  recognizeSet setAlt

/-- The model prefix corresponding to the recognized call shape: bind the
exclusivity check's result, write through it, and return it. The certified
prefix ends at that return, matching `Ownership.Runner.execSet`. The boxed
replacement is represented by its source variable; the `setResult`, `bound`,
`continuation` and `indexDec` facts are recorded in `Prefix` for provenance and
are outside the modeled prefix. -/
def Prefix.toModel (assign : FVarId → Ownership.Var) (p : Prefix) : Ownership.Code :=
  Ownership.Code.let (assign p.checkResult) (Ownership.LetF.checkAlias (assign p.array))
    (Ownership.Code.setArr (assign p.checkResult) (assign p.index) (assign p.value)
      (Ownership.Code.ret (assign p.checkResult)))

#check projectPrefix
#check Prefix.toModel

end OwnershipLcnf
