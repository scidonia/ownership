/-
A recognizer for the two pair arms of the pinned `setAt` dispatch, the trace of
what it walks, and the branch model term those operands name.

The arms are the `Path.left` and `Path.right` alternatives of the `setAt`
declaration captured in `docs/notes/artifacts/setAt-nested.lcnf.txt` (`setAt`,
replayed digest `17644656787385327013`). `NestedProjection.lean` recognizes the
`Path.index` alternative of the same dispatch and leaves these two arms
unconstrained; this module recognizes them, and only them. Both are matched on
the actual `Lean.Compiler.LCNF.Code .impure` value, and what is matched is
recorded twice: as `ArmPrefix`'s binder identities, and as `ArmPrefix.fragment`,
the operation trace each matched node contributes, in emitted order.

## What the walk requires

* it selects `Path.left` and `Path.right` by constructor identity from the outer
  `cases`, and passes that `cases`' discriminant into each arm's walk, so the
  arm's `oproj[2]` of "the path" reads the very value the dispatch is on, and
  every other reference to the path is that same binder. An alternative that
  projects some other value is unsupported;
* the two arms are then tied to one another: both must read the same pair value
  and pass the same replacement-value operand to the child, which is the
  dispatch's own calling convention — both alternatives receive the same
  parameters;
* it walks the arm's prelude in the emitted order: `oproj[2]` of the path, its
  check-free increment, the three-object decrement of the path, and the pair's
  `oproj[0]` and `oproj[1]`. The projection order is pinned as `0` then `1`,
  which is the field order of the pair in the artifact; *which* of the two is
  the selected field is read off the `Path` constructor, never off a position;
* inside the reset join it requires the recursive child call on the path's
  continuation, the replacement-value operand and the selected field — the child
  call's third operand is what makes "selected" a checked identity rather than a
  name — then the reuse join returning its own parameter, then the `isShared`
  flag's `cases` with exactly the two `Bool` alternatives selected by identity.
  The `Bool.false` arm must be the in-place write: `oset` of the reset join's
  object at the arm's selected index with the child call's result, joined back
  into the reuse join with that same object. The `Bool.true` arm must be the
  copy: a `Prod.mk` whose argument at the selected index is the child call's
  result and whose argument at the other index is the retained projection,
  joined back with the constructor;
* after the joins it requires `isShared` of the *pair* value — the same binder
  the two projections read — and the outer `cases` on that flag, again with
  exactly two `Bool` alternatives: `Bool.false` joins the reset join with the
  pair itself and the flag, `Bool.true` increments the two projections in the
  emitted order (`oproj[1]`'s binder, then `oproj[0]`'s, both checked and
  non-persistent), decrements the pair (checked, non-persistent, no object
  count) and joins the reset join with the erased placeholder and the flag.

Every arm's `inc`/`dec` count, order, check flag, persistence flag and object
count is required, as are the call arities: the child call has three operands,
both joins take their recorded parameter counts, the `oset` is a single-field
write of the child result, and the `Prod.mk` has exactly two arguments. A
dropped or added increment, an exchanged increment order, a flipped flag, a
dropped decrement, an extra join argument, a recursive call on the retained
component, an `oset` at the retained index, exchanged `isShared` bodies or
labels, and swapped pair projections each fail the walk.

## What is *not* constrained

* **The `Path.here` and `Path.index` alternatives.** The recognizer selects
  `Path.left` and `Path.right` by name and does not walk the other alternatives.
* **The joins' other callers.** The walks pin each join's parameter count, the
  reuse join's `return` of its own parameter, and every recorded jump into them;
  they do not require the joins to have no other callers elsewhere in the
  declaration.
* **The recursive callee and the helper bodies.** The walk stops at the child
  call and checks its operands. The callee's own code — the `Path.index`
  alternative `NestedProjection.lean` recognizes, or the `here` case — is a
  separate question.
* **What the runtime `isShared` test computes.** The walk binds the variable the
  test reads (the pair value) and the dispatch on its result. That the runtime
  result is the model's exclusivity predicate is not established here; it is one
  of the premises the correspondence below would take.
* **The reference-counting effects of the recorded `inc`/`dec` operations.** The
  trace records them with their flags; no runtime counter claim is made. The
  child call's accounting for the pair's fields is the premise
  `Ownership/Pair.lean` already names for its branch entry.

## The model term, and what is not proved

`PairWriteModel` is the branch's model values read from the recognized operands:
the selected `Ownership.Pair.Side` (read from the `Path` constructor), the pair
handle and reference, the replacement child reference (the child call's result),
the retained sibling's reference and the returned handle. `PairWriteModel.toCode`
is the `Ownership.Pair.PCode` term — the pair write followed by the return of
the joined handle — and `reuseHeap`/`copyHeap` are the two branch transitions in
`Ownership.Pair`'s vocabulary, with `step_exclusive`/`step_shared` showing that
`Ownership.Pair.step` on the model's side selects exactly them. `fieldModel`
reads the pair's two fields off the two projections, and the lemmas below relate
its `get`/`retained`/`toArray` to the recognizer's selected and retained
binders and to `Ownership.Pair.reuse`/`copy`.

**The correspondence is not proved here.** That executing the recognized trace
reports the same outcome as `Ownership.Pair.runP` of the model term — the reuse
branch on the exclusive path, the copy branch on the shared one, with the
retained sibling's increment and the old handle's decrement — is a separate
result, in the shape `NestedSemantics.lean` gives the `Path.index` arm: a machine
for the fragment, an outcome relation and a layout, with the runtime `isShared`
predicate and the child call's contract as premises. This module states the
recognizer, the trace and the model term only; nothing below claims that
execution correspondence.
-/
import Lean.Compiler.LCNF.Basic
import Ownership.Pair

open Lean
open Lean.Compiler.LCNF

namespace OwnershipLcnf

/-! ## Field roles -/

/-- The other field, as a side. `Ownership.Pair.Side.other` gives the other
field's index; this gives the side, so a role can be named by the field it
reads. -/
def otherSide : Ownership.Pair.Side → Ownership.Pair.Side
  | .left => .right
  | .right => .left

@[simp] theorem otherSide_left : otherSide .left = .right := rfl

@[simp] theorem otherSide_right : otherSide .right = .left := rfl

@[simp] theorem otherSide_involutive (s : Ownership.Pair.Side) :
    otherSide (otherSide s) = s := by
  cases s <;> rfl

@[simp] theorem otherSide_idx (s : Ownership.Pair.Side) :
    (otherSide s).idx = s.other := by
  cases s <;> rfl

/-- The projection binder for one field of the pair: `oproj[0]`'s result for the
left field, `oproj[1]`'s for the right. -/
def fieldFor (side : Ownership.Pair.Side) (field0 field1 : FVarId) : FVarId :=
  if side = .left then field0 else field1

@[simp] theorem fieldFor_left (field0 field1 : FVarId) :
    fieldFor .left field0 field1 = field0 := rfl

@[simp] theorem fieldFor_right (field0 field1 : FVarId) :
    fieldFor .right field0 field1 = field1 := rfl

/-! ## The recognized arm -/

/-- The recognized pair arm. Every field is a binder identity read from the node
that bound it — or, for `sharedFlag` and `joined`, a join parameter the arm's
jumps carry — which is what makes `ArmPrefix.fragment` the trace of the walked
code rather than a separate description of it.

The signature's three parameters are the path, the replacement value and the
pair; the walk finds the path through the arm's `oproj[2]`, the pair through the
two field projections, and the replacement value through the child call, and
requires the child call's third operand and the `isShared` test to read the
values it bound. -/
structure ArmPrefix where
  /-- The `Path` constructor of this alternative. -/
  ctor : Name
  /-- The selected field's side, read from `ctor`. -/
  side : Ownership.Pair.Side
  /-- The path value the outer `cases` dispatches on. -/
  node : FVarId
  /-- The pair value the two field projections read. -/
  pair : FVarId
  /-- The replacement-value operand, passed to the child call. -/
  value : FVarId
  /-- The path's continuation sub-path (`oproj[2]`). -/
  path : FVarId
  /-- The pair's first field (`oproj[0]`). -/
  field0 : FVarId
  /-- The pair's second field (`oproj[1]`). -/
  field1 : FVarId
  /-- The reset join's name. -/
  resetJp : FVarId
  /-- The reset join's first parameter: the object the in-place write targets. -/
  resetObj : FVarId
  /-- The reset join's second parameter: the `isShared` flag it dispatches on. -/
  sharedFlag : FVarId
  /-- The recursive child call's result. -/
  recursive : FVarId
  /-- The reuse join's name. -/
  reuseJp : FVarId
  /-- The reuse join's parameter: the joined handle the arm returns. -/
  joined : FVarId
  /-- The field index the in-place write targets. -/
  osetIdx : Nat
  /-- The `Prod.mk` copy's result. -/
  copy : FVarId
  /-- The `isShared` test's result. -/
  sharedCheck : FVarId
  deriving Repr

/-- The selected field's binder: the field projection on the arm's side. -/
def ArmPrefix.selected (p : ArmPrefix) : FVarId :=
  fieldFor p.side p.field0 p.field1

/-- The retained field's binder: the field projection on the other side. -/
def ArmPrefix.retained (p : ArmPrefix) : FVarId :=
  fieldFor (otherSide p.side) p.field0 p.field1

@[simp] theorem ArmPrefix.selected_field (p : ArmPrefix) :
    p.selected = fieldFor p.side p.field0 p.field1 := rfl

@[simp] theorem ArmPrefix.retained_field (p : ArmPrefix) :
    p.retained = fieldFor (otherSide p.side) p.field0 p.field1 := rfl

/-- The binder identities an `ArmPrefix` records, in field order. The
constructor, the selected side and the `oset` index are not binders and are not
recorded. -/
def ArmPrefix.binderNames (p : ArmPrefix) : List Name :=
  [p.node.name, p.pair.name, p.value.name, p.path.name, p.field0.name,
   p.field1.name, p.resetJp.name, p.resetObj.name, p.sharedFlag.name,
   p.recursive.name, p.reuseJp.name, p.joined.name, p.copy.name,
   p.sharedCheck.name]

/-! ## The trace -/

/-- A jump argument as the walk reads it: a binder or the erased placeholder.
Recording the erased case explicitly keeps "the shared arm joins with the erased
placeholder" a checked token rather than an unread argument. -/
inductive JmpArg where
  | fvar (x : FVarId)
  | erased
  deriving Repr

/-- The recognized arm's operations, in emitted order: the trace the walk emits,
one operation per matched node. Each operation carries the binder identities and
flags the walk read from that node. -/
inductive ArmOp where
  /-- `oproj[2]` of the path: the continuation sub-path. -/
  | projPath (dst node : FVarId)
  /-- `inc` of the continuation sub-path. -/
  | incPath (x : FVarId)
  /-- `dec` of the path with its object count. -/
  | decNode (x : FVarId) (objs : Nat)
  /-- `oproj[0]` or `oproj[1]` of the pair, with the projected index. -/
  | projField (dst pair : FVarId) (idx : Nat)
  /-- The reset join, with its object and flag parameters. -/
  | resetJoin (jp obj flag : FVarId)
  /-- The recursive child call: the continuation, the value and the child. -/
  | recurse (dst path value child : FVarId)
  /-- The reuse join, with its joined parameter. -/
  | reuseJoin (jp result : FVarId)
  /-- `return` of the joined handle. -/
  | retJoin (x : FVarId)
  /-- The in-place write: the flag's `cases`, the object, the field and the value. -/
  | inPlace (flag obj : FVarId) (idx : Nat) (val : FVarId)
  /-- A jump to the reuse join, with the flag's branch tag and the argument. -/
  | jmpReuse (jp : FVarId) (tag : Bool) (arg : JmpArg)
  /-- The copy: the flag's `cases`, the constructor, and its selected- and
  retained-position arguments. -/
  | copy (flag : FVarId) (dst child retained : FVarId)
  /-- The `isShared` test of the pair. -/
  | isSharedCheck (dst pair : FVarId)
  /-- A jump to the reset join, with the flag's branch tag and its two arguments. -/
  | jmpReset (jp : FVarId) (tag : Bool) (obj flagArg : JmpArg)
  /-- An increment of one field, in the shared arm. -/
  | incField (x : FVarId) (side : Ownership.Pair.Side)
  /-- The pair's decrement in the shared arm, with its object count. -/
  | decShared (x : FVarId) (objs : Option Nat)
  deriving Repr

/-- The recognized arm's trace, as the walk's own bindings read it. The prelude
keeps its emitted order; the reset join's body follows — the child call, the
reuse join and the two-arm flag dispatch — and then the outer `isShared` test
with the pair's own two-arm dispatch. The selected field is the field projection
the child call reads and the retained field is the other projection: both are
recorded by the binder they were bound to, not by a role name.

The two field increments are recorded in the emitted order, which is the
projection order (`oproj[1]`'s binder, then `oproj[0]`'s), not a role order; the
`side` each increment carries is the field it increments, so the trace states
both the order and the roles. -/
def ArmPrefix.fragment (p : ArmPrefix) : List ArmOp :=
  [ .projPath p.path p.node
  , .incPath p.path
  , .decNode p.node 3
  , .projField p.field0 p.pair 0
  , .projField p.field1 p.pair 1
  , .resetJoin p.resetJp p.resetObj p.sharedFlag
  , .recurse p.recursive p.path p.value p.selected
  , .reuseJoin p.reuseJp p.joined
  , .retJoin p.joined
  , .inPlace p.sharedFlag p.resetObj p.osetIdx p.recursive
  , .jmpReuse p.reuseJp false (.fvar p.resetObj)
  , .copy p.sharedFlag p.copy p.recursive p.retained
  , .jmpReuse p.reuseJp true (.fvar p.copy)
  , .isSharedCheck p.sharedCheck p.pair
  , .jmpReset p.resetJp false (.fvar p.pair) (.fvar p.sharedCheck)
  , .incField p.field1 .right
  , .incField p.field0 .left
  , .decShared p.pair none
  , .jmpReset p.resetJp true .erased (.fvar p.sharedCheck) ]

/-! ## The walk -/

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

/-- The two alternatives of a dispatch, as the bodies of `Bool.false` and
`Bool.true`, selected by constructor identity. The alternatives may appear in
either order; a third alternative, a `.default` or `.alt` alternative, or any
other constructor name is unsupported. An exchange of the two labels is
therefore a checked rejection: the body labelled `Bool.false` must be the
`Bool.false` body. -/
private def boolBodies (cs : Cases .impure) : Option (Code .impure × Code .impure) :=
  match cs.alts with
  | #[.ctorAlt a ca _, .ctorAlt b cb _] =>
      if a.name == `Bool.false && b.name == `Bool.true then some (ca, cb)
      else if a.name == `Bool.true && b.name == `Bool.false then some (cb, ca)
      else none
  | _ => none

/-- The arm's prelude, in the emitted order: `oproj[2]` of the path and its
increment, the three-object decrement of the path, then the pair's two field
projections in field order. `rest` is the code after the prelude. -/
private structure ArmPre where
  pair : FVarId
  path : FVarId
  field0 : FVarId
  field1 : FVarId
  rest : Code .impure

private def recognizePre (node : FVarId) (c : Code .impure) : Option ArmPre := do
  let .let dPath k1 := c | none
  let .oproj 2 nodePath _ := dPath.value | none
  unless nodePath == node do none
  let path := dPath.fvarId
  let .inc incPath 1 false false k2 _ := k1 | none
  unless incPath == path do none
  let .dec decNode 1 false false (some 3) k3 _ := k2 | none
  unless decNode == node do none
  let .let dField0 k4 := k3 | none
  let .oproj 0 pair0 _ := dField0.value | none
  let field0 := dField0.fvarId
  let .let dField1 k5 := k4 | none
  let .oproj 1 pair1 _ := dField1.value | none
  let field1 := dField1.fvarId
  unless pair1 == pair0 do none
  return { pair := pair0, path, field0, field1, rest := k5 }

/-- Recognize one arm. The prelude is matched op by op; the reset join's body is
matched through the child call, the reuse join and its two-arm flag dispatch;
then the outer `isShared` test and its two-arm dispatch are matched. `side` is
the field the arm's `Path` constructor selects, and `declName` is the private
name of the declaration being recognized, which the child call must target.

`node` is the outer `cases`' discriminant: every read of the path must be that
binder, so the arm is tied to the dispatch it belongs to. -/
private def recognizeArm (declName : Name) (ctor : Name) (side : Ownership.Pair.Side)
    (node : FVarId) (arm : Code .impure) : Option ArmPrefix := do
  let pre ← recognizePre node arm
  let selField := fieldFor side pre.field0 pre.field1
  let retField := fieldFor (otherSide side) pre.field0 pre.field1
  let .jp resetDecl k6 := pre.rest | none
  unless resetDecl.params.size == 2 do none
  let resetJp := resetDecl.fvarId
  let resetObj := resetDecl.params[0]!.fvarId
  let sharedFlag := resetDecl.params[1]!.fvarId
  -- the child call, on the continuation, the value and the selected field
  let .let dRec k7 := resetDecl.value | none
  let .fap recFn recArgs _ := dRec.value | none
  unless recFn == declName do none
  unless recArgs.size == 3 do none
  unless recArgs[0]?.bind fvarArg? == some pre.path do none
  let value ← recArgs[1]?.bind fvarArg?
  unless recArgs[2]?.bind fvarArg? == some selField do none
  let recursive := dRec.fvarId
  -- the reuse join returns its own parameter
  let .jp reuseDecl k8 := k7 | none
  unless reuseDecl.params.size == 1 do none
  let reuseJp := reuseDecl.fvarId
  let joined := reuseDecl.params[0]!.fvarId
  let .return retJoined := reuseDecl.value | none
  unless retJoined == joined do none
  -- the flag's dispatch: the in-place write, then the copy
  let .cases inner := k8 | none
  unless inner.discr == sharedFlag do none
  let innerArms ← boolBodies inner
  let .oset obj idx val kInnerFalse _ := innerArms.1 | none
  unless obj == resetObj do none
  unless idx == side.idx do none
  unless val == .fvar recursive do none
  let .jmp t1 a1 := kInnerFalse | none
  unless t1 == reuseJp do none
  unless a1.size == 1 do none
  unless a1[0]? == some (.fvar obj) do none
  let .let dCopy kInnerTrue := innerArms.2 | none
  let .ctor info cargs _ := dCopy.value | none
  unless info.name == `Prod.mk do none
  unless cargs.size == 2 do none
  let copy := dCopy.fvarId
  let .jmp t2 a2 := kInnerTrue | none
  unless t2 == reuseJp do none
  unless a2.size == 1 do none
  unless a2[0]? == some (.fvar copy) do none
  unless cargs[side.idx]?.bind fvarArg? == some recursive do none
  unless cargs[side.other]?.bind fvarArg? == some retField do none
  -- the outer shared test, on the pair, and its dispatch
  let .let dShared k9 := k6 | none
  let .isShared sharedSrc _ := dShared.value | none
  unless sharedSrc == pre.pair do none
  let sharedCheck := dShared.fvarId
  let .cases outer := k9 | none
  unless outer.discr == sharedCheck do none
  let outerArms ← boolBodies outer
  let .jmp t3 a3 := outerArms.1 | none
  unless t3 == resetJp do none
  unless a3.size == 2 do none
  unless a3[0]? == some (.fvar pre.pair) do none
  unless a3[1]? == some (.fvar sharedCheck) do none
  let .inc i1 1 true false k10 _ := outerArms.2 | none
  unless i1 == pre.field1 do none
  let .inc i2 1 true false k11 _ := k10 | none
  unless i2 == pre.field0 do none
  let .dec dPair 1 true false none k12 _ := k11 | none
  unless dPair == pre.pair do none
  let .jmp t4 a4 := k12 | none
  unless t4 == resetJp do none
  unless a4.size == 2 do none
  unless a4[0]? == some .erased do none
  unless a4[1]? == some (.fvar sharedCheck) do none
  return { ctor, side, node, pair := pre.pair, value, path := pre.path,
           field0 := pre.field0, field1 := pre.field1, resetJp, resetObj, sharedFlag,
           recursive, reuseJp, joined, osetIdx := idx, copy, sharedCheck }

/-! ## The dispatch's two arms -/

/-- The two recognized pair alternatives of one dispatch, with the values they
agree on: the path the dispatch is on, and the pair and replacement-value
operands both alternatives read. -/
structure PairArms where
  /-- The path value the outer `cases` dispatches on. -/
  node : FVarId
  /-- The pair value both alternatives read. -/
  pair : FVarId
  /-- The replacement-value operand both alternatives pass to the child. -/
  value : FVarId
  /-- The `Path.left` alternative. -/
  left : ArmPrefix
  /-- The `Path.right` alternative. -/
  right : ArmPrefix
  deriving Repr

/-- Both arms' binder identities, in left/right order. -/
def PairArms.binderNames (a : PairArms) : List (List Name) :=
  [a.left.binderNames, a.right.binderNames]

/-- Both arms' trace lengths, in left/right order. -/
def PairArms.opCounts (a : PairArms) : List Nat :=
  [a.left.fragment.length, a.right.fragment.length]

/-- Project the two pair alternatives of the captured `setAt` dispatch. Both are
selected by constructor name from the outer `cases` on the path parameter, and
each walk requires its projections to read that dispatch's discriminant. The
returned arms are the walks' own records: every field is a binder or join
parameter the walk read from the node it matched, so `ArmPrefix.fragment` is the
trace of this code. Anything else is unsupported. -/
def projectPair (declName : Name) (code : Code .impure) : Option PairArms := do
  let .cases cs := code | none
  let leftArm ← findAlt `Scidonia.FracPerm.StateVar.Layout5.Path.left code
  let rightArm ← findAlt `Scidonia.FracPerm.StateVar.Layout5.Path.right code
  let left ← recognizeArm declName `Scidonia.FracPerm.StateVar.Layout5.Path.left
    .left cs.discr leftArm
  let right ← recognizeArm declName `Scidonia.FracPerm.StateVar.Layout5.Path.right
    .right cs.discr rightArm
  unless left.pair == right.pair do none
  unless left.value == right.value do none
  return { node := cs.discr, pair := left.pair, value := left.value, left, right }

/-! ## The branch model term -/

/-- The branch's model values, read off the recognized operands: the selected
side, the pair handle and reference, the replacement child reference (the child
call's result), the retained sibling's reference and the returned handle. -/
structure PairWriteModel where
  /-- The field the branch writes. -/
  side : Ownership.Pair.Side
  /-- The pair handle. -/
  pairVar : Ownership.Var
  /-- The reference the pair handle denotes. -/
  pairRef : Ownership.Ref
  /-- The reference the selected field receives: the child call's result. -/
  rep : Ownership.Ref
  /-- The retained sibling's reference. -/
  retained : Ownership.Ref
  /-- The handle the branch returns. -/
  result : Ownership.Var
  deriving DecidableEq, Repr

/-- The model values, read from the arm and from the caller's assignment of the
recognized binders to model variables and references. -/
def PairWriteModel.ofPrefix (v : FVarId → Ownership.Var) (ref : FVarId → Ownership.Ref)
    (p : ArmPrefix) : PairWriteModel :=
  { side := p.side, pairVar := v p.pair, pairRef := ref p.pair, rep := ref p.recursive,
    retained := ref p.retained, result := v p.joined }

/-- The model program: the pair write the arm implements, in `Ownership.Pair`'s
`PCode` vocabulary — the selected side, the pair handle, the replacement child
and the returned handle. `Ownership.Pair.runP` runs it; `Ownership.Pair.step`
selects `reuse` or `copy` from the pair's exclusivity. -/
def PairWriteModel.toCode (m : PairWriteModel) : Ownership.Pair.PCode :=
  .pairWrite m.side m.pairVar m.rep m.result (.ret m.result)

/-- The in-place branch's transition: the selected field becomes the child and
the pair cell keeps its address, count and persistence. -/
def PairWriteModel.reuseHeap (m : PairWriteModel) (H : Ownership.Heap)
    (o : Ownership.Obj) : Ownership.Heap :=
  Ownership.Pair.reuse H m.pairRef o m.side m.rep

/-- The shared branch's transition: the retained sibling is incremented for the
new pair's reference, the fresh pair is allocated with the selected field
replaced, and the old pair is decremented for the caller's consumed handle. -/
def PairWriteModel.copyHeap (m : PairWriteModel) (H : Ownership.Heap)
    (o : Ownership.Obj) : Ownership.Heap :=
  Ownership.Pair.copy H m.pairRef o m.side m.retained m.rep

/-- The fresh pair's address: the copy's allocation point. -/
def PairWriteModel.fresh (_m : PairWriteModel) (H : Ownership.Heap) : Ownership.Ref :=
  Ownership.Pair.copyRef H

/-- The branch's runtime selection, in `Ownership.Pair`'s vocabulary: the
exclusive pair reuses the cell, the shared pair copies it. -/
def PairWriteModel.step (m : PairWriteModel) (H : Ownership.Heap) (o : Ownership.Obj)
    (pf : Ownership.Pair.Fields) : Ownership.Pair.Step :=
  Ownership.Pair.step m.side H m.pairRef o pf m.rep

/-- The exclusive branch is the in-place write. -/
theorem PairWriteModel.step_exclusive (m : PairWriteModel) {H : Ownership.Heap}
    {o : Ownership.Obj} {pf : Ownership.Pair.Fields}
    (hex : H.exclusive? m.pairRef = true) :
    m.step H o pf =
      { ref := m.pairRef, heap := m.reuseHeap H o, write := (m.pairRef, true) } := by
  simpa [PairWriteModel.step, PairWriteModel.reuseHeap] using
    Ownership.Pair.step_reuse (sel := m.side) (H := H) (r := m.pairRef) (o := o)
      (pf := pf) (rep := m.rep) hex

/-- The shared branch is the copy. `Ownership.Pair.step` reads the retained
sibling off the pair object's fields, so the branch is the model's copy exactly
when those fields' retained component is the model's retained reference; with
the arm's own field model that premise is `fieldModel_retained`. -/
theorem PairWriteModel.step_shared (m : PairWriteModel) {H : Ownership.Heap}
    {o : Ownership.Obj} {pf : Ownership.Pair.Fields}
    (hret : pf.retained m.side = m.retained)
    (hex : H.exclusive? m.pairRef = false) :
    m.step H o pf =
      { ref := m.fresh H, heap := m.copyHeap H o, write := (m.pairRef, false) } := by
  simpa [PairWriteModel.step, PairWriteModel.copyHeap, PairWriteModel.fresh, hret] using
    Ownership.Pair.step_copy (sel := m.side) (H := H) (r := m.pairRef) (o := o)
      (pf := pf) (rep := m.rep) hex


/-- The pair's two fields as the arm reads them: the `oproj[0]` binder is the
left field and the `oproj[1]` binder the right one. -/
def fieldModel (ref : FVarId → Ownership.Ref) (p : ArmPrefix) : Ownership.Pair.Fields :=
  { left := ref p.field0, right := ref p.field1 }

/-- The model's selected field is the binder the child call reads. -/
@[simp] theorem fieldModel_get (ref : FVarId → Ownership.Ref) (p : ArmPrefix) :
    (fieldModel ref p).get p.side = ref p.selected := by
  cases h : p.side <;>
    simp [fieldModel, ArmPrefix.selected, Ownership.Pair.Fields.get, h]

/-- The model's retained field is the binder the copy keeps. -/
@[simp] theorem fieldModel_retained (ref : FVarId → Ownership.Ref) (p : ArmPrefix) :
    (fieldModel ref p).retained p.side = ref p.retained := by
  cases h : p.side <;>
    simp [fieldModel, ArmPrefix.retained, Ownership.Pair.Fields.retained, h]

/-- The model's field array is the two projections in field order. -/
@[simp] theorem fieldModel_toArray (ref : FVarId → Ownership.Ref) (p : ArmPrefix) :
    (fieldModel ref p).toArray = #[.ref (ref p.field0), .ref (ref p.field1)] := rfl

/-- The selected index of the model's field array holds the selected projection,
and the copy writes the child there. -/
@[simp] theorem fieldModel_toArray_selected (ref : FVarId → Ownership.Ref) (p : ArmPrefix) :
    (fieldModel ref p).toArray[p.side.idx]? = some (.ref (ref p.selected)) := by
  cases h : p.side <;> simp [fieldModel, ArmPrefix.selected, h]

/-- The copy's retained sibling is exactly the arm's retained projection: the
reference `Ownership.Pair.copy` increments is read off the other field. -/
theorem copy_retained_eq (ref : FVarId → Ownership.Ref) (p : ArmPrefix) :
    (fieldModel ref p).retained p.side = ref p.retained :=
  fieldModel_retained ref p

/-- The shared branch at the arm's own field model: the retained sibling is the
binder the copy's `Prod.mk` keeps. -/
theorem PairWriteModel.step_shared_fieldModel (v : FVarId → Ownership.Var)
    (ref : FVarId → Ownership.Ref) (p : ArmPrefix) {H : Ownership.Heap}
    {o : Ownership.Obj} (hex : H.exclusive? (PairWriteModel.ofPrefix v ref p).pairRef = false) :
    (PairWriteModel.ofPrefix v ref p).step H o (fieldModel ref p) =
      { ref := (PairWriteModel.ofPrefix v ref p).fresh H,
        heap := (PairWriteModel.ofPrefix v ref p).copyHeap H o,
        write := ((PairWriteModel.ofPrefix v ref p).pairRef, false) } :=
  PairWriteModel.step_shared _ (fieldModel_retained ref p) hex

/-- The in-place write's index is the model's selected side index, so
`Ownership.Pair.reuse` writes the selected field. -/
theorem reuse_selected_index (m : PairWriteModel) {o : Ownership.Obj}
    (pf : Ownership.Pair.Fields) (h : Ownership.Pair.pairOf? o = some pf)
    (rep : Ownership.Ref) :
    ∃ pf', Ownership.Pair.pairOf? { o with fields := o.fields.set! m.side.idx (.ref rep) } =
      some pf' :=
  Ownership.Pair.pairOf?_set_ref h (Ownership.Pair.Side.idx_lt_two m.side) rep

/-- The copy's fresh pair holds the old pair's fields with the selected field
replaced by the child. -/
theorem copy_fresh_fields (m : PairWriteModel) (H : Ownership.Heap) (o : Ownership.Obj)
    (h : m.fresh H ≠ m.pairRef) :
    ((m.copyHeap H o).cells (m.fresh H)).map (·.fields) =
      some (o.fields.set! m.side.idx (.ref m.rep)) := by
  have hc : (m.copyHeap H o).cells (m.fresh H) =
      some ⟨o.fields.set! m.side.idx (.ref m.rep), 1, false⟩ := by
    simpa [PairWriteModel.copyHeap, PairWriteModel.fresh] using
      Ownership.Pair.copy_cells_new H m.pairRef o m.side m.retained m.rep h
  rw [hc]
  rfl

/-- The copy increments the retained sibling's count by one. -/
theorem copy_retained_rc {m : PairWriteModel} {H : Ownership.Heap}
    {o os : Ownership.Obj} (hslive : H.cells m.retained = some os)
    (hsr : m.retained ≠ m.pairRef) (hsn : m.retained ≠ H.next) :
    (m.copyHeap H o).rc m.retained = H.rc m.retained + 1 := by
  simpa [PairWriteModel.copyHeap] using
    Ownership.Pair.copy_rc_retained (H := H) (r := m.pairRef) (o := o) (sel := m.side)
      (s := m.retained) (rep := m.rep) (os := os) hslive hsr hsn

/-- The old pair loses exactly one count in the copy. -/
theorem copy_old_rc {m : PairWriteModel} {H : Ownership.Heap} {o : Ownership.Obj}
    (hcell : H.cells m.pairRef = some o) (hsr : m.retained ≠ m.pairRef)
    (hnr : H.next ≠ m.pairRef) :
    (m.copyHeap H o).rc m.pairRef = o.rc - 1 := by
  simpa [PairWriteModel.copyHeap] using
    Ownership.Pair.copy_rc_old (H := H) (r := m.pairRef) (o := o) (sel := m.side)
      (s := m.retained) (rep := m.rep) hcell hsr hnr

#check projectPair
#check PairArms.binderNames
#check ArmPrefix.fragment
#check PairWriteModel.toCode
#check PairWriteModel.step_exclusive
#check PairWriteModel.step_shared
#check fieldModel_get
#check copy_fresh_fields

end OwnershipLcnf
