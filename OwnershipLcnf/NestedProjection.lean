/-
A recognizer for the pinned nested `setAt` `Path.index` alternative.

The supported shape is the one captured in
`docs/notes/artifacts/setAt-nested.lcnf.txt` (`setAt`, replayed digest
`17644656787385327013`), with provenance in
`docs/notes/OWNERSHIP_NESTED_CAPTURE.md`. This module recognizes that path by
walking the actual `Lean.Compiler.LCNF.Code .impure` value, and records what it
walked twice: as the `NestedPrefix`'s binder identities, and as
`NestedPrefix.fragment`, the operation trace each matched node contributes, in
emitted order.

The walk covers the alternative the `setAt` dispatch selects for a `Path.index`
node:

* it selects the `Path.index` alternative by constructor name from the outer
  `cases` on the path parameter, and requires the arm's projections to read that
  very discriminant, so the alternative is tied to the dispatch it belongs to;
* it walks the pre-bounds destructuring in the emitted order and requires the
  exact operations, argument identities and primitive arities: `oproj[0]`,
  `oproj[1]` and `oproj[2]` of the path with their increments, the three-object
  decrement of the path node, `Array.size` of the function's array parameter
  (`x.3`, not the path's array field), and `Nat.decLt` of the extracted index and
  that size;
* it requires the bounds `cases` to be exactly the two-arm `Bool.false` /
  `Bool.true` shape and selects `Bool.true` by constructor identity, never by the
  alternative's position. A declaration that moves the update body onto the
  `Bool.false` arm while keeping both labels and every instruction token is
  therefore rejected;
* inside that alternative it requires, in the emitted order: the array site
  constant (`setAt._redArg._closed_0`), the array exclusivity check on the
  function's array parameter, `stateDefault` of the path's array field, the
  `takeOut` call on the check result, the index and the default state, the pair's
  two projections and their increments, the pair decrement, the child site
  constant (`setAt._redArg._closed_1`), the child exclusivity check on the pair's
  second projection, the recursive `setAt` call on the path's continuation, the
  original value parameter and the asserted child, the `Array.set` put-back, the
  index decrement and the return;
* it binds the put-back's array to the extracted parent (the pair's first
  projection), its index to the selected index scalar, and its value to the
  recursive call's result. Restoring through any other array, at any other
  index, or with the extracted child instead of the recursive result is
  therefore rejected;
* the recursive call is identified by the declaration's own pinned private name,
  so self-recursion on the path's continuation is a checked identity, and the
  `takeOut` helper is identified by the name the caller supplies; the two closed
  constants are the declaration's own `_closed_0` and `_closed_1`.

The primitive arities are checked explicitly: `Array.size` takes its type
argument and the array, `Nat.decLt` two scalars, the array exclusivity check its
site and array, `stateDefault` its array, `takeOut` its check result, index and
default state, the child exclusivity check its site and child, the recursive call
its path, value and child, and `Array.set` its type argument, array, index,
value and proof argument. Both call conventions of the exclusivity checks are
matched as named alternatives — `assertExclusiveArrayImpl`/`assertExclusiveImpl`
and their specialized `._redArg` forms — at the two-operand arity the pinned
capture emits; a differently shaped call with the right head symbol is rejected
by the arity check, not only by the destructuring pattern failing to bind.

## What is *not* constrained

* **The bounds-failure arm.** The recognizer requires the arm to exist and to be
  the second `Bool` alternative; it does not walk the `Bool.false` body. The
  update path is the `Bool.true` arm.
* **The other outer alternatives** (`Path.here`, `Path.left`, `Path.right`).
  They are left unconstrained; the recognizer selects the `Path.index` arm by
  name.
* **The recursive callee's body and the helper bodies.** The walk stops at the
  call and checks its operands; the callee's own code is a separate question.
* **The reference-counting effects of the index's `inc`/`dec` pair.** The trace
  records the emitted operations and their check flags; no runtime counter claim
  is made.

This module is a recognizer and a trace only: it states no model, no
correspondence theorem and no compiler semantics for the primitives it matches.
-/
import Lean.Compiler.LCNF.Basic

open Lean
open Lean.Compiler.LCNF

namespace OwnershipLcnf

/-- The recognized `setAt` `Path.index` path. Every field is a binder identity
read from the node that bound it — or, for `value`, an operand identity read from
the recursive call — which is what makes `NestedPrefix.fragment` the trace of the
walked code rather than a separate description of it. The signature's three
parameters are `node` (the path), `value` and `array`; the walk finds the array
through `Array.size` and the value through the recursive call's second operand. -/
structure NestedPrefix where
  /-- The path value the outer `cases` dispatches on. -/
  node : FVarId
  /-- The array parameter (`x.3`) the bounds computation and the array check
  read. -/
  array : FVarId
  /-- The original replacement-value parameter (`x.2`), read as the recursive
  call's second operand. -/
  value : FVarId
  /-- The path's array field (`oproj[0]`, `a.26`). -/
  childArray : FVarId
  /-- The selected index (`oproj[1]`, `i.27`). -/
  index : FVarId
  /-- The continuation sub-path (`oproj[2]`, `p.28`). -/
  path : FVarId
  /-- The `Array.size` result. -/
  sizeResult : FVarId
  /-- The `Nat.decLt` result, the bounds `cases` discriminant. -/
  bound : FVarId
  /-- The array site constant (`_closed_0`). -/
  arraySite : FVarId
  /-- The array exclusivity check's result. -/
  arrayCheck : FVarId
  /-- The `stateDefault` result. -/
  dflt : FVarId
  /-- The `takeOut` pair. -/
  pair : FVarId
  /-- The pair's first projection (`oproj[0]`), the array the put-back writes. -/
  parent : FVarId
  /-- The pair's second projection (`oproj[1]`), the extracted child. -/
  child : FVarId
  /-- The child site constant (`_closed_1`). -/
  childSite : FVarId
  /-- The child exclusivity check's result. -/
  childCheck : FVarId
  /-- The recursive `setAt` result. -/
  recursive : FVarId
  /-- The `Array.set` result, the returned array. -/
  restored : FVarId
  /-- The index decrement that follows the put-back. -/
  indexDec : FVarId
  deriving Repr

/-- The binder identities a `NestedPrefix` records, in field order. `FVarId`
carries only a name and its identity is that name, so comparing these lists
compares the prefixes' binder identities. -/
def NestedPrefix.binderNames (p : NestedPrefix) : List Name :=
  [p.node.name, p.array.name, p.value.name, p.childArray.name, p.index.name,
   p.path.name, p.sizeResult.name, p.bound.name, p.arraySite.name,
   p.arrayCheck.name, p.dflt.name, p.pair.name, p.parent.name, p.child.name,
   p.childSite.name, p.childCheck.name, p.recursive.name, p.restored.name,
   p.indexDec.name]

/-- The recognized fragment's operations, in emitted order: the trace the walk
emits, one operation per matched node. Each operation carries the binder
identities the walk read from that node, and the flags or closed-constant index
the walk required. -/
inductive NestedOp where
  /-- `oproj[0]` of the path: its array field. -/
  | projArray (dst node : FVarId)
  /-- `inc` of the array field, with its check flag. -/
  | incArray (x : FVarId) (check : Bool)
  /-- `oproj[1]` of the path: the selected index. -/
  | projIndex (dst node : FVarId)
  /-- `inc` of the index, with its check flag. -/
  | incIndex (x : FVarId) (check : Bool)
  /-- `oproj[2]` of the path: the continuation sub-path. -/
  | projPath (dst node : FVarId)
  /-- `inc` of the continuation sub-path, with its check flag. -/
  | incPath (x : FVarId) (check : Bool)
  /-- `dec` of the path with its object count. -/
  | decNode (x : FVarId) (objs : Nat)
  /-- `Array.size` of the array parameter. -/
  | arraySize (dst arr : FVarId)
  /-- `Nat.decLt` of the index and the size. -/
  | decLt (dst idx size : FVarId)
  /-- The recognizer's selected `Bool.true` alternative. -/
  | boundsTrue (discr : FVarId)
  /-- A closed site constant, with the index of the `_closed_N` it reads. -/
  | siteConst (dst : FVarId) (closed : Nat)
  /-- The array exclusivity check. -/
  | checkArray (dst site arr : FVarId)
  /-- `stateDefault` of the path's array field. -/
  | stateDefault (dst arr : FVarId)
  /-- `takeOut` of the check result, the index and the default state. -/
  | takeOut (dst check index dflt : FVarId)
  /-- `oproj[0]` of the pair: the extracted parent array. -/
  | projParent (dst pair : FVarId)
  /-- `inc` of the extracted parent. -/
  | incParent (x : FVarId)
  /-- `oproj[1]` of the pair: the extracted child. -/
  | projChild (dst pair : FVarId)
  /-- `inc` of the extracted child. -/
  | incChild (x : FVarId)
  /-- `dec` of the pair. -/
  | decPair (x : FVarId)
  /-- The child exclusivity check. -/
  | checkChild (dst site child : FVarId)
  /-- The recursive `setAt` call. -/
  | recurse (dst path value child : FVarId)
  /-- `Array.set` of the extracted parent, the index and the recursive result. -/
  | setArray (dst arr idx val : FVarId)
  /-- `dec` of the index. -/
  | decIndex (x : FVarId)
  /-- `return` of the put-back result. -/
  | retVar (x : FVarId)
  deriving Repr

/-- The recognized fragment, as the recognizer's own bindings read it. The
pre-bounds steps keep their emitted order; the tail is the update path through the
put-back and the return. The put-back's value operand is the recursive call's
result and its array operand is the extracted parent, not the array the
extraction was taken from. -/
def NestedPrefix.fragment (p : NestedPrefix) : List NestedOp :=
  [ .projArray p.childArray p.node
  , .incArray p.childArray false
  , .projIndex p.index p.node
  , .incIndex p.index true
  , .projPath p.path p.node
  , .incPath p.path false
  , .decNode p.node 3
  , .arraySize p.sizeResult p.array
  , .decLt p.bound p.index p.sizeResult
  , .boundsTrue p.bound
  , .siteConst p.arraySite 0
  , .checkArray p.arrayCheck p.arraySite p.array
  , .stateDefault p.dflt p.childArray
  , .takeOut p.pair p.arrayCheck p.index p.dflt
  , .projParent p.parent p.pair
  , .incParent p.parent
  , .projChild p.child p.pair
  , .incChild p.child
  , .decPair p.pair
  , .siteConst p.childSite 1
  , .checkChild p.childCheck p.childSite p.child
  , .recurse p.recursive p.path p.value p.childCheck
  , .setArray p.restored p.parent p.index p.recursive
  , .decIndex p.index
  , .retVar p.restored ]

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

/-- The supported bounds `cases`: exactly two constructor alternatives, named
`Bool.false` and `Bool.true`, selected by identity. A third alternative, a
`.default` alternative, an `.alt` alternative or any other constructor name is
unsupported, so which alternative carries the update body is a checked fact and
not a position. -/
private def trueArm? (cs : Cases .impure) : Option (Code .impure) :=
  match cs.alts with
  | #[.ctorAlt a ca _, .ctorAlt b cb _] =>
      if a.name == `Bool.true && b.name == `Bool.false then some ca
      else if a.name == `Bool.false && b.name == `Bool.true then some cb
      else none
  | _ => none

/-- The pre-bounds destructuring of the `Path.index` arm, in the emitted order.

The captured sequence is exactly `oproj[0] path` → `inc array` →
`oproj[1] path` → `inc index` → `oproj[2] path` → `inc continuation` →
`dec[3 objs] path` → `Array.size array` → `Nat.decLt index size` → `cases` on the
`Nat.decLt` result. Operation kinds, counts, primitive arities, the `inc`/`dec`
check flags and object count, and the fvar identities of every argument are
required. -/
private structure Pre where
  node : FVarId
  array : FVarId
  childArray : FVarId
  index : FVarId
  path : FVarId
  sizeResult : FVarId
  bound : FVarId
  cases : Cases .impure

private def recognizePre (node : FVarId) (c : Code .impure) : Option Pre := do
  let .let dArray k0 := c | none
  let .oproj 0 nodeArray _ := dArray.value | none
  unless nodeArray == node do none
  let .inc incArray 1 false false k1 _ := k0 | none
  unless incArray == dArray.fvarId do none
  let .let dIndex k2 := k1 | none
  let .oproj 1 nodeIndex _ := dIndex.value | none
  unless nodeIndex == node do none
  let .inc incIndex 1 true false k3 _ := k2 | none
  unless incIndex == dIndex.fvarId do none
  let .let dPath k4 := k3 | none
  let .oproj 2 nodePath _ := dPath.value | none
  unless nodePath == node do none
  let .inc incPath 1 false false k5 _ := k4 | none
  unless incPath == dPath.fvarId do none
  let .dec decNode 1 false false (some 3) k6 _ := k5 | none
  unless decNode == node do none
  let .let dSize k7 := k6 | none
  let .fap sizeFn sizeArgs _ := dSize.value | none
  unless sizeFn == `Array.size do none
  unless sizeArgs.size == 2 do none
  let array ← sizeArgs[1]?.bind fvarArg?
  let .let dBound k8 := k7 | none
  let .fap boundFn boundArgs _ := dBound.value | none
  unless boundFn == `Nat.decLt do none
  unless boundArgs.size == 2 do none
  unless boundArgs[0]?.bind fvarArg? == some dIndex.fvarId do none
  unless boundArgs[1]?.bind fvarArg? == some dSize.fvarId do none
  let .cases cs := k8 | none
  unless cs.discr == dBound.fvarId do none
  return { node, array, childArray := dArray.fvarId, index := dIndex.fvarId,
           path := dPath.fvarId, sizeResult := dSize.fvarId,
           bound := dBound.fvarId, cases := cs }

/-- Recognize the captured `setAt` `Path.index` arm. The pre-bounds path is
matched op by op; the bounds-success alternative is selected by constructor
identity and the update tail is matched exactly, including the put-back's
operands and the return. `declName` is the private name of the declaration being
recognized (the recursive call's target and the two closed constants' stem);
`takeOut` is the private name of the `takeOut` helper. -/
private def recognizeIndex (declName takeOut : Name) (node : FVarId)
    (arm : Code .impure) : Option NestedPrefix := do
  let pre ← recognizePre node arm
  let trueAlt ← trueArm? pre.cases
  let .let dArraySite k1 := trueAlt | none
  let .fap arraySiteFn arraySiteArgs _ := dArraySite.value | none
  unless arraySiteFn == declName ++ `_closed_0 do none
  unless arraySiteArgs.size == 0 do none
  let .let dArrayCheck k2 := k1 | none
  let .fap arrayCheckFn arrayCheckArgs _ := dArrayCheck.value | none
  unless arrayCheckFn == `Scidonia.FracPerm.assertExclusiveArrayImpl ||
    arrayCheckFn == `Scidonia.FracPerm.assertExclusiveArrayImpl._redArg do none
  unless arrayCheckArgs.size == 2 do none
  let .let dDflt k3 := k2 | none
  let .fap dfltFn dfltArgs _ := dDflt.value | none
  unless dfltFn == `Scidonia.FracPerm.StateVar.Layout5.stateDefault do none
  unless dfltArgs.size == 1 do none
  let .let dPair k4 := k3 | none
  let .fap takeFn takeArgs _ := dPair.value | none
  unless takeFn == takeOut do none
  unless takeArgs.size == 3 do none
  let .let dParent k5 := k4 | none
  let .oproj 0 pairParent _ := dParent.value | none
  unless pairParent == dPair.fvarId do none
  let .inc incParent 1 true false k6 _ := k5 | none
  unless incParent == dParent.fvarId do none
  let .let dChild k7 := k6 | none
  let .oproj 1 pairChild _ := dChild.value | none
  unless pairChild == dPair.fvarId do none
  let .inc incChild 1 true false k8 _ := k7 | none
  unless incChild == dChild.fvarId do none
  let .dec decPair 1 false false none k9 _ := k8 | none
  unless decPair == dPair.fvarId do none
  let .let dChildSite k10 := k9 | none
  let .fap childSiteFn childSiteArgs _ := dChildSite.value | none
  unless childSiteFn == declName ++ `_closed_1 do none
  unless childSiteArgs.size == 0 do none
  let .let dChildCheck k11 := k10 | none
  let .fap childCheckFn childCheckArgs _ := dChildCheck.value | none
  unless childCheckFn == `Scidonia.FracPerm.assertExclusiveImpl ||
    childCheckFn == `Scidonia.FracPerm.assertExclusiveImpl._redArg do none
  unless childCheckArgs.size == 2 do none
  let .let dRec k12 := k11 | none
  let .fap recFn recArgs _ := dRec.value | none
  unless recFn == declName do none
  unless recArgs.size == 3 do none
  let .let dSet k13 := k12 | none
  let .fap setFn setArgs _ := dSet.value | none
  unless setFn == `Array.set do none
  unless setArgs.size == 5 do none
  let .dec decIndex 1 true false none k14 _ := k13 | none
  let .return ret := k14 | none
  unless ret == dSet.fvarId do none
  -- The array the exclusivity check and the default state read.
  let arrayCheckArray ← arrayCheckArgs[1]?.bind fvarArg?
  let dfltArray ← dfltArgs[0]?.bind fvarArg?
  -- The take-out's operands.
  let takeCheck ← takeArgs[0]?.bind fvarArg?
  let takeIndex ← takeArgs[1]?.bind fvarArg?
  let takeDflt ← takeArgs[2]?.bind fvarArg?
  -- The child check's operands.
  let childCheckSite ← childCheckArgs[0]?.bind fvarArg?
  let childCheckChild ← childCheckArgs[1]?.bind fvarArg?
  -- The recursive call's operands.
  let recPath ← recArgs[0]?.bind fvarArg?
  let value ← recArgs[1]?.bind fvarArg?
  let recChild ← recArgs[2]?.bind fvarArg?
  -- The put-back's operands.
  let setArray ← setArgs[1]?.bind fvarArg?
  let setIndex ← setArgs[2]?.bind fvarArg?
  let setValue ← setArgs[3]?.bind fvarArg?
  unless arrayCheckArgs[0]?.bind fvarArg? == some dArraySite.fvarId do none
  unless arrayCheckArray == pre.array do none
  unless dfltArray == pre.childArray do none
  unless takeCheck == dArrayCheck.fvarId do none
  unless takeIndex == pre.index do none
  unless takeDflt == dDflt.fvarId do none
  unless childCheckSite == dChildSite.fvarId do none
  unless childCheckChild == dChild.fvarId do none
  unless recPath == pre.path do none
  unless recChild == dChildCheck.fvarId do none
  unless setArray == dParent.fvarId do none
  unless setIndex == pre.index do none
  unless setValue == dRec.fvarId do none
  unless decIndex == pre.index do none
  return { node := pre.node, array := pre.array, value, childArray := pre.childArray,
           index := pre.index, path := pre.path, sizeResult := pre.sizeResult,
           bound := pre.bound, arraySite := dArraySite.fvarId,
           arrayCheck := dArrayCheck.fvarId, dflt := dDflt.fvarId,
           pair := dPair.fvarId, parent := dParent.fvarId,
           child := dChild.fvarId, childSite := dChildSite.fvarId,
           childCheck := dChildCheck.fvarId, recursive := dRec.fvarId,
           restored := dSet.fvarId, indexDec := decIndex }

/-- Project the captured `setAt` `Path.index` alternative. The alternative is
selected by constructor name from the outer `cases` on the path parameter, then
the recognizer walks its exact supported path, requiring the arm's projections to
read that dispatch's discriminant. Anything else is unsupported. The returned
`NestedPrefix` is the walk's own record: every field is a binder or operand the
walk read from the node it matched, so `NestedPrefix.fragment` is the trace of
this code. -/
def projectNested (declName takeOut : Name) (code : Code .impure) : Option NestedPrefix := do
  let .cases cs := code | none
  let alt ← findAlt `Scidonia.FracPerm.StateVar.Layout5.Path.index code
  recognizeIndex declName takeOut cs.discr alt

#check projectNested
#check NestedPrefix.fragment

end OwnershipLcnf
