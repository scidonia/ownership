/-
A restricted ownership surface and the check that polices its use.

The payload is a private field, so client code cannot read, rebuild or write the
array directly: the only entry points are `Owned.new`, `Owned.write` and
`Owned.read?`. That closes direct access, not duplication: Lean has no linear
typing, so `let b := a` is always legal and shares the buffer. The check therefore
reflects the elaborated definition and rejects a handle used more than once in its
scope, which is the usage violation the type cannot see. The fractional account of
why one use is the write's whole share is in `OwnedTyping`.
-/
import Lean

open Lean Elab Command

structure Owned (α : Type) where
  private mk ::
  private val : Array α

namespace Owned

def new (xs : Array α) : Owned α := ⟨xs⟩

def write (a : Owned α) (i : Nat) (v : α) : Owned α := ⟨a.val.set! i v⟩

def read? (a : Owned α) (i : Nat) : Option α := a.val[i]?

end Owned

namespace OwnedCheck

/-- Uses of the de Bruijn index `k` in `e`. -/
partial def uses (k : Nat) : Expr → Nat
  | .bvar i => if i == k then 1 else 0
  | .app f a => uses k f + uses k a
  | .lam _ t b _ => uses k t + uses (k + 1) b
  | .forallE _ t b _ => uses k t + uses (k + 1) b
  | .letE _ t v b _ => uses k t + uses k v + uses (k + 1) b
  | .mdata _ b => uses k b
  | .proj _ _ b => uses k b
  | _ => 0

/-- Every handle bound by a `let` is used at most once in its scope. -/
partial def go (e : Expr) : CommandElabM Unit := do
  match e with
  | .letE n t v b _ =>
    if t.getAppFn.constName? == some ``Owned then
      let k := uses 0 b
      if k > 1 then
        throwError "restricted ownership: handle '{n}' used {k} times in its scope; the discipline permits one transfer"
    go v; go b
  | .lam _ t b _ => go t; go b
  | .app f a => go f; go a
  | .mdata _ b => go b
  | .proj _ _ b => go b
  | _ => pure ()

end OwnedCheck

/-- Reflective check of a definition against the one-transfer rule. -/
syntax "#own_check " ident : command

elab_rules : command
  | `(#own_check $n:ident) => do
    let env ← getEnv
    match env.find? n.getId with
    | some (.defnInfo d) => OwnedCheck.go d.value
    | _ => throwError "unknown definition '{n}'"
