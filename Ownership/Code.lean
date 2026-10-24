/-
The straight-line fragment of the ownership core, its counted-heap semantics,
and the usage/exclusivity context the checker maintains.

The fragment is deliberately small and covers the executor's designated write
prefix: a scalar-array element write between a runtime exclusivity check and the
return. `inc` models a duplicated handle (the alias countermodel); `dec` models
a consumed handle. The nested path write (`takeOut`/pair destructuring) and
calls are added in `Nested.lean` / `Calls.lean`; this module's theorem is the
array-write artifact certificate.

The checker's context separates the facts the review asked to separate:

* `us`       — the reference-management obligation (`owned`, `borrow`, `scalar`);
* `refOf`    — which object a variable denotes (identity, not uniqueness);
* `mult`     — the estimated total handle count of an object.

`Inv.owned` does **not** say an owned variable's object is exclusive. It says
the variable denotes the object and contributes at least one handle. Exclusivity
is `mult r = 1` plus `Inv.rc_eq` plus non-persistence, proved in
`Inv.exclusive`. This is the correction to the earlier plan's false invariant.
-/
import Ownership.Heap

namespace Ownership

abbrev Var := Nat
abbrev Env := Var → Option Val

namespace Env

def set (env : Env) (x : Var) (v : Val) : Env :=
  fun y => if y = x then some v else env y

def erase (env : Env) (x : Var) : Env :=
  fun y => if y = x then none else env y

@[simp] theorem set_self (env : Env) (x : Var) (v : Val) : env.set x v x = some v := by
  simp [set]

@[simp] theorem set_other (env : Env) (x y : Var) (v : Val) (h : y ≠ x) :
    env.set x v y = env y := by
  simp [set, h]

@[simp] theorem erase_self (env : Env) (x : Var) : env.erase x x = none := by
  simp [erase]

@[simp] theorem erase_other (env : Env) (x y : Var) (h : y ≠ x) :
    env.erase x y = env y := by
  simp [erase, h]

end Env

inductive LetF where
  | lit (n : Nat)
  | size (a : Var)
  | isShared (x : Var)
  /-- The runtime exclusivity check: it returns its argument unchanged on the
  exclusive branch. The emitted `execP` binds that result and passes it on. -/
  | checkAlias (x : Var)
  deriving Repr

inductive Code where
  | let (x : Var) (v : LetF) (k : Code)
  | inc (x : Var) (n : Nat) (k : Code)
  | dec (x : Var) (n : Nat) (k : Code)
  | check (x : Var) (k : Code)
  | setArr (x : Var) (i : Var) (v : Var) (k : Code)
  | ret (x : Var)
  deriving Repr

inductive Fault where
  | badVar (x : Var)
  | noCell (r : Ref)
  | notExclusive (r : Ref)
  deriving Repr

abbrev Write := Ref × Bool

inductive Res where
  | done (H : Heap) (env : Env) (v : Val) (ws : List Write)
  | fault (H : Heap) (env : Env) (f : Fault) (ws : List Write)

namespace Res

def addWrite : Res → Write → Res
  | .done H env v ws, w => .done H env v (w :: ws)
  | .fault H env f ws, w => .fault H env f (w :: ws)

def writes : Res → List Write
  | .done _ _ _ ws => ws
  | .fault _ _ _ ws => ws

def ok : Res → Bool
  | .done .. => true
  | .fault .. => false

end Res

/-- The fragment's big-step semantics. It is total and structural on the code:
there is no loop and no fuel. `setArr` models both runtime branches; the theorem
in `Soundness.lean` proves accepted code selects the mutate branch. -/
def run : Code → Env → Heap → Res
  | .let x (.lit n) k, env, H => run k (env.set x (.scalar n)) H
  | .let x (.size a) k, env, H =>
      match env a with
      | some (.ref r) =>
          match H.cells r with
          | some o => run k (env.set x (.scalar o.fields.size)) H
          | none => .fault H env (.noCell r) []
      | _ => .fault H env (.badVar a) []
  | .let x (.isShared y) k, env, H =>
      match env y with
      | some (.ref r) => run k (env.set x (.scalar (if H.rc r > 1 then 1 else 0))) H
      | _ => .fault H env (.badVar y) []
  | .let y (.checkAlias x) k, env, H =>
      match env x with
      | some (.ref r) =>
          if H.exclusive? r then run k (env.set y (.ref r)) H
          else .fault H env (.notExclusive r) []
      | _ => .fault H env (.badVar x) []
  | .inc x n k, env, H =>
      match env x with
      | some (.ref r) => run k env (H.inc r n)
      | _ => .fault H env (.badVar x) []
  | .dec x n k, env, H =>
      match env x with
      | some (.ref r) => run k (env.erase x) (H.dec r n)
      | _ => .fault H env (.badVar x) []
  | .check x k, env, H =>
      match env x with
      | some (.ref r) =>
          if H.exclusive? r then run k env H
          else .fault H env (.notExclusive r) []
      | _ => .fault H env (.badVar x) []
  | .setArr x i v k, env, H =>
      match env x, env i, env v with
      | some (.ref r), some (.scalar idx), some (.scalar val) =>
          match H.cells r with
          | none => .fault H env (.noCell r) []
          | some o =>
              if H.exclusive? r then
                let H' := H.set r { o with fields := o.fields.set! idx (.scalar val) }
                (run k (env.set x (.ref r)) H').addWrite (r, true)
              else
                let (r', H1) := H.alloc (o.fields.set! idx (.scalar val))
                let H2 := H1.dec r 1
                (run k (env.set x (.ref r')) H2).addWrite (r, false)
      | _, _, _ => .fault H env (.badVar x) []
  | .ret x, env, H => .done H env (env x |>.getD .erased) []

/-! ## The checker's context and invariant -/

inductive U where
  | owned
  | borrow
  | scalar
  | dead
  deriving DecidableEq, Repr

structure Ctx where
  us : Var → U
  refOf : Var → Option Ref
  mult : Ref → Nat

namespace Ctx

def empty : Ctx :=
  { us := fun _ => .dead, refOf := fun _ => none, mult := fun _ => 0 }

def setUs (c : Ctx) (x : Var) (u : U) : Ctx :=
  { c with us := fun y => if y = x then u else c.us y }

def inc (c : Ctx) (r : Ref) (n : Nat) : Ctx :=
  { c with mult := fun r' => if r' = r then c.mult r' + n else c.mult r' }

def dec (c : Ctx) (r : Ref) (n : Nat) : Ctx :=
  { c with mult := fun r' => if r' = r then c.mult r' - n else c.mult r' }

def multOf (c : Ctx) (x : Var) : Nat :=
  match c.refOf x with
  | some r => c.mult r
  | none => 0

/-- Move the handle named by `x` to `y` (the runtime check returns its argument;
the result is the same handle, not a new one). `x` becomes dead. -/
def move (c : Ctx) (x y : Var) : Ctx :=
  { c with
      us := fun z => if z = y then c.us x else if z = x then .dead else c.us z
      refOf := fun z => if z = y then c.refOf x else c.refOf z }

@[simp] theorem move_us_y (c : Ctx) (x y : Var) : (c.move x y).us y = c.us x := by
  simp [move]

@[simp] theorem move_refOf_y (c : Ctx) (x y : Var) : (c.move x y).refOf y = c.refOf x := by
  simp [move]

@[simp] theorem move_refOf_other (c : Ctx) (x y z : Var) (h : z ≠ y) :
    (c.move x y).refOf z = c.refOf z := by
  simp [move, h]

@[simp] theorem move_mult (c : Ctx) (x y : Var) : (c.move x y).mult = c.mult := rfl

@[simp] theorem move_us_other (c : Ctx) (x y z : Var) (hy : z ≠ y) (hx : z ≠ x) :
    (c.move x y).us z = c.us z := by
  simp [move, hy, hx]

/-- Bind a fresh variable to an existing ref as an owned handle. The ref's
count is already in `mult` (the take-out element); no new reference is created. -/
def bindOwned (c : Ctx) (x : Var) (r : Ref) : Ctx :=
  { c with
      us := fun z => if z = x then .owned else c.us z
      refOf := fun z => if z = x then some r else c.refOf z }

@[simp] theorem bindOwned_us_self (c : Ctx) (x : Var) (r : Ref) :
    (c.bindOwned x r).us x = .owned := by
  simp [bindOwned]

@[simp] theorem bindOwned_us_other (c : Ctx) (x z : Var) (r : Ref) (h : z ≠ x) :
    (c.bindOwned x r).us z = c.us z := by
  simp [bindOwned, h]

@[simp] theorem bindOwned_refOf_self (c : Ctx) (x : Var) (r : Ref) :
    (c.bindOwned x r).refOf x = some r := by
  simp [bindOwned]

@[simp] theorem bindOwned_refOf_other (c : Ctx) (x z : Var) (r : Ref) (h : z ≠ x) :
    (c.bindOwned x r).refOf z = c.refOf z := by
  simp [bindOwned, h]

@[simp] theorem bindOwned_mult (c : Ctx) (x : Var) (r : Ref) :
    (c.bindOwned x r).mult = c.mult := rfl

@[simp] theorem setUs_self (c : Ctx) (x : Var) (u : U) : (c.setUs x u).us x = u := by
  simp [setUs]

@[simp] theorem setUs_other (c : Ctx) (x y : Var) (u : U) (h : y ≠ x) :
    (c.setUs x u).us y = c.us y := by
  simp [setUs, h]

@[simp] theorem setUs_refOf (c : Ctx) (x : Var) (u : U) : (c.setUs x u).refOf = c.refOf := rfl

@[simp] theorem setUs_mult (c : Ctx) (x : Var) (u : U) : (c.setUs x u).mult = c.mult := rfl

@[simp] theorem inc_us (c : Ctx) (r : Ref) (n : Nat) : (c.inc r n).us = c.us := rfl

@[simp] theorem inc_refOf (c : Ctx) (r : Ref) (n : Nat) : (c.inc r n).refOf = c.refOf := rfl

@[simp] theorem dec_us (c : Ctx) (r : Ref) (n : Nat) : (c.dec r n).us = c.us := rfl

@[simp] theorem dec_refOf (c : Ctx) (r : Ref) (n : Nat) : (c.dec r n).refOf = c.refOf := rfl

@[simp] theorem inc_self (c : Ctx) (r : Ref) (n : Nat) : (c.inc r n).mult r = c.mult r + n := by
  simp [inc]

@[simp] theorem inc_other (c : Ctx) (r r' : Ref) (n : Nat) (h : r' ≠ r) :
    (c.inc r n).mult r' = c.mult r' := by
  simp [inc, h]

@[simp] theorem dec_self (c : Ctx) (r : Ref) (n : Nat) : (c.dec r n).mult r = c.mult r - n := by
  simp [dec]

@[simp] theorem dec_other (c : Ctx) (r r' : Ref) (n : Nat) (h : r' ≠ r) :
    (c.dec r n).mult r' = c.mult r' := by
  simp [dec, h]

theorem multOf_eq_one {c : Ctx} {x : Var} (h : c.multOf x = 1) :
    ∃ r, c.refOf x = some r ∧ c.mult r = 1 := by
  unfold multOf at h
  split at h
  · rename_i r hr
    exact ⟨r, hr, h⟩
  · simp at h

end Ctx

/-- The invariant. `owned` is a handle obligation, not a uniqueness claim:
`Inv.owned` only says the variable denotes the object and contributes at least
one handle. `Inv.exclusive` derives exclusivity from `mult r = 1` and
`rc_eq`. -/
structure Inv (H : Heap) (env : Env) (c : Ctx) : Prop where
  rc_eq : ∀ r, H.rc r = c.mult r
  owned : ∀ x r, c.us x = .owned → c.refOf x = some r →
    env x = some (.ref r) ∧ 1 ≤ c.mult r
  borrow : ∀ x r, c.us x = .borrow → c.refOf x = some r →
    env x = some (.ref r) ∧ H.cells r ≠ none
  scalar : ∀ x, c.us x = .scalar → ∃ n, env x = some (.scalar n)
  nonPersistent : ∀ r o, H.cells r = some o → o.persistent = false

/-- Setting a cell preserves the non-persistence of every cell when the new
object is non-persistent. -/
theorem nonPersistent_set {H : Heap} {r : Ref} {o : Obj}
    (hinv : ∀ r' o', H.cells r' = some o' → o'.persistent = false)
    (h : o.persistent = false) :
    ∀ r' o', (H.set r o).cells r' = some o' → o'.persistent = false := by
  intro r' o' hcell
  by_cases hr : r' = r
  · subst hr
    have ho : o = o' := by simpa [Heap.set] using hcell
    rw [← ho]
    exact h
  · have hc : H.cells r' = some o' := by simpa [Heap.set, if_neg hr] using hcell
    exact hinv r' o' hc

namespace Inv

theorem exclusive {H : Heap} {env : Env} {c : Ctx} {r : Ref}
    (hi : Inv H env c) (hm : c.mult r = 1) : Heap.Exclusive H r := by
  have hrc : H.rc r = 1 := by rw [hi.rc_eq r, hm]
  cases hcell : H.cells r with
  | none => simp [Heap.rc, hcell] at hrc
  | some o =>
      exact ⟨o, hcell, by simpa [Heap.rc, hcell] using hrc, hi.nonPersistent r o hcell⟩

theorem isRef {H : Heap} {env : Env} {c : Ctx} {x : Var} {r : Ref}
    (hi : Inv H env c) (hu : c.us x = .owned ∨ c.us x = .borrow)
    (hr : c.refOf x = some r) : env x = some (.ref r) := by
  rcases hu with hu | hu
  · exact (hi.owned x r hu hr).1
  · exact (hi.borrow x r hu hr).1

theorem rc_ne_zero {H : Heap} {env : Env} {c : Ctx} {r : Ref}
    (hi : Inv H env c) (h : 1 ≤ c.mult r) : H.cells r ≠ none := by
  intro hnone
  have hrc : H.rc r = 0 := by simp [Heap.rc, hnone]
  rw [hi.rc_eq r] at hrc
  omega

theorem nonPersistent_inc {H : Heap} {r : Ref} {n : Nat}
    (hi : Inv H env c) :
    ∀ r' o, (H.inc r n).cells r' = some o → o.persistent = false := by
  intro r' o' hcell
  cases hcellH : H.cells r with
  | none =>
      exact hi.nonPersistent r' o' (by simpa [Heap.inc, hcellH] using hcell)
  | some o =>
      simp only [Heap.inc, hcellH] at hcell
      exact nonPersistent_set (H := H) (r := r) (o := { o with rc := o.rc + n })
        hi.nonPersistent (by simpa using hi.nonPersistent r o hcellH) r' o' hcell

theorem nonPersistent_dec {H : Heap} {r : Ref} {n : Nat}
    (hi : Inv H env c) :
    ∀ r' o, (H.dec r n).cells r' = some o → o.persistent = false := by
  intro r' o' hcell
  cases hcellH : H.cells r with
  | none =>
      exact hi.nonPersistent r' o' (by simpa [Heap.dec, hcellH] using hcell)
  | some o =>
      simp only [Heap.dec, hcellH] at hcell
      exact nonPersistent_set (H := H) (r := r) (o := { o with rc := o.rc - n })
        hi.nonPersistent (by simpa using hi.nonPersistent r o hcellH) r' o' hcell

end Inv

/-! ## The checker -/

def check : Ctx → Code → Option Ctx
  | c, .let x (.lit n) k => check (c.setUs x .scalar) k
  | c, .let x (.size a) k =>
      match c.refOf a with
      | some _ =>
          if c.us a = .owned ∨ c.us a = .borrow then
            check (c.setUs x .scalar) k
          else none
      | none => none
  | c, .let x (.isShared y) k =>
      match c.refOf y with
      | some _ =>
          if c.us y = .owned ∨ c.us y = .borrow then
            check (c.setUs x .scalar) k
          else none
      | none => none
  | c, .let y (.checkAlias x) k =>
      if c.us x = .owned ∧ c.multOf x = 1 then check (c.move x y) k else none
  | c, .inc x n k =>
      match c.refOf x with
      | some r => if c.us x = .owned then check (c.inc r n) k else none
      | none => none
  | c, .dec x n k =>
      match c.refOf x with
      | some r =>
          if c.us x = .owned ∧ n < c.mult r then
            check ((c.dec r n).setUs x .dead) k
          else none
      | none => none
  | c, .check x k =>
      if c.us x = .owned ∧ c.multOf x = 1 then check c k else none
  | c, .setArr x i v k =>
      if c.us x = .owned ∧ c.multOf x = 1 ∧ c.us i = .scalar ∧ c.us v = .scalar then
        check c k
      else none
  | c, .ret x => if c.us x = .owned ∨ c.us x = .scalar then some c else none

end Ownership
