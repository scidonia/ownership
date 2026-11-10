/-
A compile-time alias/linearity check for a surface of Lean terms.

The discipline needs two things at a write: the array is held by exactly one
owning binding, and that binding is not duplicated or captured. This is the
surface-level half:

* **borrow vs move.** A variable in a borrow position (receiver of a read:
  `size`, `getD`, `get!`, …) may occur any number of times. A variable in a move
  position (receiver of `set!`/`uset`/`swap`, argument to any other call, returned,
  or rebound) is a use, at most one per path.
* **path sensitivity.** An `if`/`ite` takes the maximum over its branches, not the
  sum, so `if c then (x, a) else (x, a.set! …)` moves `a` once on each path.
* **capture is an escape.** An owning array occurring under a `fun` is refused
  outright: the closure keeps a reference and can be called repeatedly.

Array-typed `fun`/`let` binders are tracked by de Bruijn index. The analysis is
deliberately small: only array-typed binders, no arrays in structures or fields,
one term rather than a module, and unknown functions are treated as consuming
(moves) because borrow inference is a backend property that the surface does not
carry. The semantic half remains `Ownership.Accounted`.
-/
import Lean

open Lean Elab Command

namespace Alias

def isArrayTy (ty : Expr) : Bool :=
  ty.getAppFn.constName? == some ``Array

/-- Functions that read the array without consuming it. -/
def borrowFns : List Name :=
  [``Array.size, ``Array.getD, ``Array.uget, ``Array.back?]

/-- Moves of the tracked variable `k` in `e`, at most one per path. -/
partial def uses (k : Nat) (borrowed : Bool) (e : Expr) : Nat :=
  if e.isApp then
    let fn := e.getAppFn
    let args := e.getAppArgs
    if fn.isConstOf ``ite && args.size ≥ 2 then
      let n := args.size
      max (uses k borrowed args[n - 2]!) (uses k borrowed args[n - 1]!)
    else
      let argBorrowed :=
        match fn.constName? with
        | some nm => borrowFns.contains nm
        | none => false
      uses k false fn + args.foldl (fun s a => s + uses k argBorrowed a) 0
  else
    match e with
    | .bvar i => if i == k && !borrowed then 1 else 0
    | .lam _ _ b _ => uses (k + 1) false b
    | .forallE _ _ b _ => uses (k + 1) false b
    | .letE _ _ v b _ => uses k false v + uses (k + 1) false b
    | .mdata _ b => uses k borrowed b
    | .proj _ _ b => uses k borrowed b
    | _ => 0

/-- Does the tracked variable `k` occur in `e` while `underLam` is set? -/
partial def capturedAt (k : Nat) (underLam : Bool) (e : Expr) : Bool :=
  if e.isApp then
    capturedAt k underLam e.getAppFn || e.getAppArgs.any (capturedAt k underLam)
  else
    match e with
    | .bvar i => underLam && i == k
    | .lam _ _ b _ => capturedAt (k + 1) true b
    | .forallE _ _ b _ => capturedAt (k + 1) underLam b
    | .letE _ _ v b _ => capturedAt k underLam v || capturedAt (k + 1) underLam b
    | .mdata _ b => capturedAt k underLam b
    | .proj _ _ b => capturedAt k underLam b
    | _ => false

/-- Skip the remaining parameters of the same `fun` chain, then look for a
capture in the body: a lambda after the parameter spine is a closure. -/
partial def captured (k : Nat) : Expr → Bool
  | .lam _ _ b _ => captured (k + 1) b
  | e => capturedAt k false e

private def checkBinder (name : Name) (b : Expr) (bad : Array String) : Array String :=
  if captured 0 b then
    bad.push s!"'{name}' is captured in a closure"
  else
    let n := uses 0 false b
    if n > 1 then bad.push s!"'{name}' is moved {n} times" else bad

partial def checkTerm (e : Expr) (bad : Array String) : Array String :=
  match e with
  | .lam name ty b _ =>
    let bad := if isArrayTy ty then checkBinder name b bad else bad
    checkTerm b bad
  | .letE name ty v b _ =>
    let bad := checkTerm v bad
    let bad := if isArrayTy ty then checkBinder name b bad else bad
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
        throwError "aliasing check failed: {bad.toList}"

end Alias
