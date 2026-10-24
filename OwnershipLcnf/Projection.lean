/-
A partial projection from the replayed `execP` scalar-array set branch into the
`Ownership.Code` prefix.

The supported shape is the one captured in
`docs/notes/artifacts/execP.lcnf.txt`: inside `PTree.set`, the `Bool.true` bound
branch performs `assertExclusiveArrayImpl`, boxes the replacement value, calls
`Array.set!` on the check result, decrements the index, and continues into the
recursive `execP` call. This module projects the check/set prefix and rejects
anything whose call shape or array identity does not match.

The projection is partial. It does not yet model the boxed value, the index
decrement, or the recursive continuation, and it does not claim the emitted
branch is semantically represented by `Ownership.Code`. The intended
`project_sound` statement is recorded below; the simulation proof is the next
milestone.
-/
import Lean.Compiler.LCNF.Basic
import Ownership.Runner

open Lean
open Lean.Compiler.LCNF

namespace OwnershipLcnf

/-- The supported emitted prefix: the exclusivity check's result and the
`Array.set!` call on that result. `value` is the set call's value argument; the
current projection deliberately does not erase the `box` that produced it. -/
structure Prefix where
  array : FVarId
  checkResult : FVarId
  index : FVarId
  value : FVarId
  setResult : FVarId

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

private structure Call where
  name : Name
  args : Array (Arg .impure)
  result : FVarId

private partial def scanCalls (c : Code .impure) (out : Array Call) : Array Call :=
  match c with
  | .let d k =>
      let out := match d.value with
        | .fap f args _ => out.push ⟨f, args, d.fvarId⟩
        | _ => out
      scanCalls k out
  | .jp d k => scanCalls k (scanCalls d.value out)
  | .cases cs => cs.alts.foldl (fun out a => scanCalls a.getCode out) out
  | .inc _ _ _ _ k _ => scanCalls k out
  | .dec _ _ _ _ _ k _ => scanCalls k out
  | .oset _ _ _ k _ => scanCalls k out
  | .uset _ _ _ k _ => scanCalls k out
  | .sset _ _ _ _ _ k _ => scanCalls k out
  | .del _ k _ => scanCalls k out
  | .setTag _ _ k _ => scanCalls k out
  | .return _ | .jmp _ _ | .unreach _ => out

/-- Project the captured `execP` set-branch prefix. The check and set calls must
be present in the same `PTree.set` alternative, the set array must be the check
result, and the check's array argument must be the first set argument. Anything
else is unsupported. -/
def projectPrefix (code : Code .impure) : Option Prefix := do
  let setAlt ← findAlt `Scidonia.FracPerm.Structured.PTree.set code
  let calls := scanCalls setAlt #[]
  let checkCall ← calls.findSome? fun c =>
    if c.name == `Scidonia.FracPerm.assertExclusiveArrayImpl ||
       c.name == `Scidonia.FracPerm.assertExclusiveArrayImpl._redArg then
      some c
    else none
  let setCall ← calls.findSome? fun c =>
    if c.name == `Array.set! then some c else none
  let array ← checkCall.args[1]?.bind fvarArg?
  let setArray ← setCall.args[1]?.bind fvarArg?
  let index ← setCall.args[2]?.bind fvarArg?
  let value ← setCall.args[3]?.bind fvarArg?
  unless setArray == checkCall.result do none
  return {
    array := array
    checkResult := checkCall.result
    index := index
    value := value
    setResult := setCall.result
  }

/-- The model prefix corresponding to the projected call shape. This is the
`Runner.execSet` shape, parameterised by a variable assignment. -/
def Prefix.toModel (assign : FVarId → Ownership.Var) (p : Prefix) : Ownership.Code :=
  Ownership.Code.let (assign p.checkResult) (Ownership.LetF.checkAlias (assign p.array))
    (Ownership.Code.setArr (assign p.checkResult) (assign p.index) (assign p.value)
      (Ownership.Code.ret (assign p.checkResult)))

/-
Intended `project_sound` statement (not asserted as a theorem here):

For the captured `execP` declaration, if `projectPrefix` returns `some p` and
`p.toModel assign` is `c`, then every ownership-relevant execution of the emitted
`PTree.set`/`Bool.true` branch from a heap and environment matching `assign` is
simulated by `Ownership.Code.run c`, preserving faults, the designated
`Array.set!` write (in-place exactly when the model's `setArr` mutates), and the
target address. The box of the replacement value, the index decrement, and the
recursive continuation are not yet in the model and are the next proof work.
-/
#check projectPrefix
#check Prefix.toModel

end OwnershipLcnf
