/-
A compile-time aliasing check for a surface of real Lean terms.

The discipline requires that an array be held by exactly one owning binding at a
write. This analysis is the surface-level half: an array-typed binder introduced
by a `let` or a `fun` may occur at most once in its term. That refuses
duplication (`let b := a; … a … b`), capture (`fun _ => a` used beside `a`) and
pairing (`(a, a)`), because each shows up as a second occurrence of the same
owning variable. Arrays produced by an update are fresh binders, so the intended
pattern `let b := a.set! …; b.set! …` passes.

It is deliberately conservative and small:
* reads count as uses (the surface has no borrowing);
* a loop is a single occurrence of the array, which is correct for ownership
  across iterations, while duplication inside the loop body is still caught;
* it checks one term, not a module; it does not know which functions are pure,
  and it does not track arrays stored in structures or fields.

The semantic half is `Ownership.Accounted`: multiplicity one at the write, and
two owners at a count-one cell are refuted. This analysis is what discharges the
surface premise that the model checker assumes.
-/
import Lean

open Lean Elab Command

namespace Alias

/-- Count occurrences of the de Bruijn index `k` in `e`. -/
partial def countBVar (k : Nat) : Expr → Nat
  | .bvar i => if i == k then 1 else 0
  | .app f a => countBVar k f + countBVar k a
  | .lam _ _ b _ => countBVar (k + 1) b
  | .forallE _ _ b _ => countBVar (k + 1) b
  | .letE _ _ v b _ => countBVar k v + countBVar (k + 1) b
  | .mdata _ b => countBVar k b
  | .proj _ _ b => countBVar k b
  | _ => 0

def isArrayTy (ty : Expr) : Bool :=
  ty.getAppFn.constName? == some ``Array

/-- Every array-typed `fun` or `let` binder may occur at most once in its body. -/
partial def checkTerm (e : Expr) (bad : Array String) : Array String :=
  match e with
  | .lam name ty b _ =>
    let bad :=
      if isArrayTy ty then
        let n := countBVar 0 b
        if n > 1 then bad.push s!"'{name}' occurs {n} times" else bad
      else bad
    checkTerm b bad
  | .letE name ty v b _ =>
    let bad := checkTerm v bad
    let bad :=
      if isArrayTy ty then
        let n := countBVar 0 b
        if n > 1 then bad.push s!"'{name}' occurs {n} times" else bad
      else bad
    checkTerm b bad
  | .app f a => checkTerm a (checkTerm f bad)
  | .forallE _ _ b _ => checkTerm b bad
  | .mdata _ b => checkTerm b bad
  | .proj _ _ b => checkTerm b bad
  | _ => bad

syntax "#alias_check " term : command

elab_rules : command
  | `(#alias_check $t) => liftTermElabM do
      let e ← Term.elabTerm t none
      Term.synthesizeSyntheticMVarsNoPostponing
      let e ← instantiateMVars e
      let bad := checkTerm e #[]
      unless bad.isEmpty do
        throwError "aliasing check failed: {bad.toList}; an owning array may occur at most once"

end Alias
