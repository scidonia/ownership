/-
A projection from the replayed `execP` scalar-array set branch into the
`Ownership.Code` prefix.

The supported shape is the one captured in
`docs/notes/artifacts/execP.lcnf.txt` (`execP`, replayed digest
`15626230893919229497`). This module recognizes that path by walking the actual
`Lean.Compiler.LCNF.Code .impure` value, and records what it walked twice: as the
`Prefix`'s binder identities, and as `Prefix.fragment`, the operation trace each
matched node contributes, in emitted order.

* it selects the `PTree.set` alternative by constructor name;
* it walks the actual pre-bounds destructuring in the emitted order, and
  requires the exact operations, the exact argument identities and the exact
  primitive arities: the index projection, its increment, the
  replacement-value projection, the continuation projection, its increment, the
  two-object decrement of the node, the `Array.size` call on the function's
  array parameter, the `Nat.decLt` call on the extracted index and that size,
  and the `cases` on its result;
* it requires the bounds `cases` to be exactly the two-arm `Bool.false` /
  `Bool.true` shape and selects `Bool.true` by constructor identity, never by
  the alternative's position. A declaration that moves the write body onto the
  `Bool.false` arm while keeping both labels and every instruction token is
  therefore rejected;
* inside that alternative it requires, in order, the site constant, the
  exclusivity check, the box of the replacement value, the `Array.set!` call on
  the check result, and the index decrement; any intervening operation is
  rejected, and the index decrement must immediately follow the write. What
  follows the decrement — the boxed bounds result, the call of the extracted
  continuation and the recursive `execP` call — is outside the recognized prefix
  (A9) and is deliberately not constrained here;
* it binds the set array to the check result, the set value to the boxed value,
  and the decrement to the set index.

The primitive arities are checked explicitly: `Array.size` takes its array
argument (one type argument plus one value), `Nat.decLt` two scalars, the
exclusivity check its site and array, and `Array.set!` its array, index and
boxed value after its type argument. Both call conventions of the exclusivity
check are matched — `assertExclusiveArrayImpl` and its specialized
`assertExclusiveArrayImpl._redArg` form — so the specialized-versus-unspecialized
choice is a stated alternative rather than an implicit one. A differently shaped
call with the right head symbol is rejected by the arity check, not only by the
destructuring pattern failing to bind.

The pre-bounds counts, the projections and the box/index facts are fixed by the
recognizer and recorded in `Prefix`. The module's `Semantics.lean` gives the
recognized node kinds an explicit meaning, executes the recognized code, and
proves the correspondence; `Prefix.toModel` is the model term that
correspondence is stated against.

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
and are outside the modeled prefix. Every field is a binder identity read from
the node that bound it, which is what makes `Prefix.fragment` the trace of the
walked code rather than a separate description of it. -/
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
  deriving Repr

/-- The binder identities a `Prefix` records, in field order. `FVarId` carries
only a name and its identity is that name, so comparing these lists compares the
prefixes' binder identities (used by `Semantics.lean` to check that a decoded
prefix is the expected one). -/
def Prefix.binderNames (p : Prefix) : List Name :=
  [p.node.name, p.index.name, p.value.name, p.continuation.name, p.sizeResult.name,
   p.bound.name, p.array.name, p.site.name, p.checkResult.name, p.boxedValue.name,
   p.setResult.name, p.indexDec.name]

/-- The recognized fragment's operations, in emitted order: the trace the walk
emits, one operation per matched node. Each operation carries the binder
identities the walk read from that node. -/
inductive Op where
  /-- `oproj[0]` of the node: the extracted index (A1). -/
  | projIndex (dst node : FVarId)
  /-- `inc` of the index (A2, non-claim). -/
  | incIndex (x : FVarId) (n : Nat)
  /-- `sproj[2,0]` of the node: the extracted replacement value (A1). -/
  | projValue (dst node : FVarId)
  /-- `oproj[1]` of the node: the extracted continuation (A1, non-claim). -/
  | projCont (dst node : FVarId)
  /-- `inc` of the continuation (A2, non-claim). -/
  | incCont (x : FVarId) (n : Nat)
  /-- `dec` of the destructured node (A2, non-claim). -/
  | decNode (x : FVarId) (n objs : Nat)
  /-- `Array.size` of the array argument (A3). -/
  | arraySize (dst arr : FVarId)
  /-- `Nat.decLt` of the index and the size (A4). -/
  | decLt (dst idx size : FVarId)
  /-- The site constant (A5). -/
  | siteConst (dst : FVarId)
  /-- The recognizer's selected `Bool.true` alternative (A4). -/
  | boundsTrue (discr : FVarId)
  /-- `assertExclusiveArrayImpl` (A6). -/
  | checkExclusive (dst site arr : FVarId)
  /-- `box` of the replacement value (A7). -/
  | boxValue (dst src : FVarId)
  /-- `Array.set!` of the boxed replacement (A8). -/
  | setBang (dst arr idx val : FVarId)
  /-- `return` of the checked handle. -/
  | retVar (x : FVarId)
  deriving Repr

/-- The recognized fragment, as the recognizer's own bindings read it: the
operation trace of the walked code. The pre-bounds steps keep their emitted
order; the tail is the site constant, the exclusivity check, the box, the write
and the return. The write's value operand is the *boxed* binder the emitted
`Array.set!` reads, not its scalar source.

The final `.retVar` is the observation the model inserts — the emitted code does
not return the checked handle, it continues into the continuation and the
recursive call — so it is the certified prefix's boundary, not a transcribed
node. The emitted path's index decrement, the boxing of the bounds result, the
call of the continuation and the recursive `execP` call are outside the fragment
(A9). -/
def Prefix.fragment (p : Prefix) : List Op :=
  [ .projIndex p.index p.node
  , .incIndex p.index 1
  , .projValue p.value p.node
  , .projCont p.continuation p.node
  , .incCont p.continuation 1
  , .decNode p.node 1 2
  , .arraySize p.sizeResult p.array
  , .decLt p.bound p.index p.sizeResult
  , .boundsTrue p.bound
  , .siteConst p.site
  , .checkExclusive p.checkResult p.site p.array
  , .boxValue p.boxedValue p.value
  , .setBang p.setResult p.checkResult p.index p.boxedValue
  , .retVar p.checkResult ]

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
unsupported, so which alternative carries the write body is a checked fact and
not a position. -/
private def trueArm? (cs : Cases .impure) : Option (Code .impure) :=
  match cs.alts with
  | #[.ctorAlt a ca _, .ctorAlt b cb _] =>
      if a.name == `Bool.true && b.name == `Bool.false then some ca
      else if a.name == `Bool.false && b.name == `Bool.true then some cb
      else none
  | _ => none

/-- The pre-bounds destructuring of the `PTree.set` node, in the emitted order.

The captured sequence is exactly `oproj[0] node` → `inc index` → `sproj[2,0]`
node → `oproj[1] node` → `inc continuation` → `dec[2 objs] node` →
`Array.size array` → `Nat.decLt index sizeResult` → `cases` on the `Nat.decLt`
result. Operation kinds, counts, primitive arities and the fvar identities of
every argument are required; a duplicate, a dropped operation, an extra
operation, a swapped projection index, a swapped `Nat.decLt` argument or a
reordered pair of bindings all fail the walk. -/
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
  unless sizeArgs.size == 2 do none
  let array ← sizeArgs[1]?.bind fvarArg?
  let .let dBound k7 := k6 | none
  let .fap boundFn boundArgs _ := dBound.value | none
  unless boundFn == `Nat.decLt do none
  unless boundArgs.size == 2 do none
  unless boundArgs[0]?.bind fvarArg? == some index do none
  unless boundArgs[1]?.bind fvarArg? == some dSize.fvarId do none
  let .cases cs := k7 | none
  unless cs.discr == dBound.fvarId do none
  return { node, index, value, continuation, sizeResult := dSize.fvarId,
           bound := dBound.fvarId, array, cases := cs }

/-- Recognizer for the captured `execP` `PTree.set` path. The pre-bounds path is
matched op by op; the bounds-success alternative is selected by constructor
identity and the check/box/set/index-dec tail is matched exactly. The box, the
set result and the index decrement are bound; any extra operation in the tail
makes the projection fail. -/
private def recognizeSet (setAlt : Code .impure) : Option Prefix := do
  let pre ← recognizePre setAlt
  let trueAlt ← trueArm? pre.cases
  let .let dsite ksite := trueAlt | none
  let .let dcheck kcheck := ksite | none
  let .fap checkFn checkArgs _ := dcheck.value | none
  unless checkFn == `Scidonia.FracPerm.assertExclusiveArrayImpl ||
    checkFn == `Scidonia.FracPerm.assertExclusiveArrayImpl._redArg do none
  unless checkArgs.size == 2 do none
  let .let dbox kbox := kcheck | none
  let .box _ v := dbox.value | none
  let .let dset kset := kbox | none
  let .fap setFn setArgs _ := dset.value | none
  unless setFn == `Array.set! do none
  unless setArgs.size == 4 do none
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
selected by constructor name, then the recognizer walks its exact supported
path. Anything else is unsupported. The returned `Prefix` is the walk's own
record: every field is a binder the walk read from the node it matched, so
`Prefix.fragment` is the trace of this code. -/
def projectPrefix (code : Code .impure) : Option Prefix := do
  let setAlt ← findAlt `Scidonia.FracPerm.Structured.PTree.set code
  recognizeSet setAlt

/-- The model prefix corresponding to the recognized call shape: bind the
exclusivity check's result, write through it, and return it. The certified
prefix ends at that return, matching `Ownership.Runner.execSet`. The boxed
replacement is represented by its source variable — the box is
ownership-transparent (A7), and `Semantics.lean` proves the two binders hold the
same scalar at the write. The `setResult`, `bound`, `continuation` and
`indexDec` facts are recorded in `Prefix` for provenance and are outside the
modeled prefix. -/
def Prefix.toModel (assign : FVarId → Ownership.Var) (p : Prefix) : Ownership.Code :=
  Ownership.Code.let (assign p.checkResult) (Ownership.LetF.checkAlias (assign p.array))
    (Ownership.Code.setArr (assign p.checkResult) (assign p.index) (assign p.value)
      (Ownership.Code.ret (assign p.checkResult)))

#check projectPrefix
#check Prefix.toModel

end OwnershipLcnf
