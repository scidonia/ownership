/-
The trusted LCNF-fragment semantics, the projection's correspondence theorem, and
the milestone's target theorem.

`Projection.lean` recognizes the pinned `execP` `PTree.set` alternative
structurally. This module gives the recognized node kinds an explicit meaning
over `Ownership.Heap`/`Val`/`Env` and proves that the fragment, executed under
that meaning, is the projected model: `project_sound`. It then instantiates the
concrete entry invariant and states the steering note's completion result: for a
declaration the projection recognizes, checker acceptance and the entry
invariant imply the designated write is in place at the root address.

`Lean.Compiler.LCNF.Code` has no Lean-checked operational semantics, so the
meaning of each primitive is an *assumption* of this module, not a theorem about
the compiler. The assumptions are listed here in full; each is also named at the
definition implementing it. Nothing below claims that the C backend, the
runtime, or an arbitrary LCNF program behaves this way — only that these
primitives, on this recognized fragment, do.

## Assumption list

* **A1** `oproj[0]`, `oproj[1]` and `sproj[2,0]` on the `PTree.set` node read
  its reified index, continuation and replacement value. The constructor layout
  is not modeled; the caller supplies those three fields (`NodeFields`) and the
  recognizer is what pins which fields the path reads.
* **A2** `inc`/`dec` on the index, the continuation and the node are refcount
  traffic on values the model heap has no cell for. They leave the model's heap
  and environment untouched. This is the named non-claim for the index's own
  `inc`/`dec` pair, the continuation's handle, and the destructured node.
* **A3** `Array.size a` yields the array cell's length, which is what the
  model's `LetF.size` reads.
* **A4** `Nat.decLt i n` yields `true` exactly when `i < n`. The recognizer
  matched the `Bool.true` alternative; whether the runtime takes it is a fact
  about the index and the array's length, not about ownership state, so the
  interpreter records the branch selection as a step rather than deriving it.
* **A5** The site constant is opaque; the exclusivity check ignores it.
* **A6** `assertExclusiveArrayImpl site a` returns `a` on the exclusive branch
  and faults otherwise, and has no heap effect. This is the model's
  `LetF.checkAlias`; the returned handle is the same handle, not a new one.
* **A7** `box v` is ownership-transparent: the boxed temporary denotes the same
  scalar as its source. The write's replacement is therefore the model's
  `value` variable.
* **A8** `Array.set! arr i v` on an exclusive array mutates in place and returns
  the array; on a shared array it copies (`Heap.alloc` plus a count decrement on
  the source). This is the model's `Code.setArr`, both branches. The model
  records the returned handle by re-binding the checked variable, so the
  fragment's fresh result binder is bound as a local only.
* **A9** The certified prefix ends at the designated write's return. The
  index decrement that follows, the boxing of the bounds result, the call of the
  extracted continuation, and the recursive `execP` call are outside it.
* **A10** The captured replay is the backend input up to the sibling pin and
  digest recorded in `docs/notes/artifacts/execP.lcnf.txt`; relating the replay
  to what the backend receives is the named trust step of the repository's
  measurement, not a kernel theorem.
-/
import OwnershipLcnf.Projection
import Ownership.Entry

namespace OwnershipLcnf

open Lean
open Lean.Compiler.LCNF

/-! ## The fragment's machine -/

/-- A local value bound by a node kind that is not ownership-relevant. -/
inductive Local where
  | unknown
  | scalar (n : Nat)
  | ref (r : Ownership.Ref)
  | flag (b : Bool)
  deriving DecidableEq, Repr

/-- The reified `PTree.set` fields the pre-bounds path destructures (A1). -/
structure NodeFields where
  index : Local := .unknown
  value : Local := .unknown
  continuation : Local := .unknown
  deriving Inhabited, Repr

/-- The fragment's machine state: the auxiliary locals, the reified node fields,
the ownership heap and the model environment. -/
structure Machine where
  locals : FVarId → Local
  nodes : FVarId → NodeFields
  heap : Ownership.Heap
  env : Ownership.Env

/-- The recognized fragment's operations, in emitted order. -/
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

/-- The recognized fragment, as the recognizer's own bindings read it. The
pre-bounds steps keep their emitted order; the tail is the site constant, the
exclusivity check, the box, the write and the return. The pre-bounds
destructuring includes the continuation binding and its increment, because the
emitted path destructures them; what the fragment does not include is the index
decrement, the boxing of the bounds result, the call of the continuation and the
recursive `execP` call (A9). -/
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
  , .setBang p.setResult p.checkResult p.index p.value
  , .retVar p.checkResult ]

/-- The model program the fragment denotes: the ownership-relevant operations in
their emitted order. The auxiliary node kinds are ownership-transparent
(A1–A7) and are dropped, so `Ownership.run` on the result is exactly the
projected model. The terminal `.ret 0` is the interpreter's empty tail; a
recognized fragment always ends in `retVar`. -/
def toCode (assign : FVarId → Ownership.Var) : List Op → Ownership.Code
  | [] => .ret 0
  | .checkExclusive dst _ arr :: rest =>
      .let (assign dst) (.checkAlias (assign arr)) (toCode assign rest)
  | .setBang _ arr idx val :: rest =>
      .setArr (assign arr) (assign idx) (assign val) (toCode assign rest)
  | .retVar x :: _ => .ret (assign x)
  | _ :: rest => toCode assign rest

/-! ## The interpreter -/

/-- The machine after the exclusivity check returned its argument (A6). -/
def afterCheck (assign : FVarId → Ownership.Var) (dst : FVarId) (r : Ownership.Ref)
    (s : Machine) : Machine :=
  { locals := fun f => if f.name = dst.name then .ref r else s.locals f
    nodes := s.nodes
    heap := s.heap
    env := s.env.set (assign dst) (.ref r) }

/-- The machine after `Array.set!` took the mutate branch (A8). -/
def afterMutate (assign : FVarId → Ownership.Var) (dst arr : FVarId) (r : Ownership.Ref)
    (i v : Nat) (o : Ownership.Obj) (s : Machine) : Machine :=
  { locals := fun f => if f.name = dst.name then .ref r else s.locals f
    nodes := s.nodes
    heap := s.heap.set r { o with fields := o.fields.set! i (.scalar v) }
    env := s.env.set (assign arr) (.ref r) }

/-- The machine after `Array.set!` took the copy branch (A8): a fresh cell with
the replaced fields, and a count decrement on the source. -/
def afterCopy (assign : FVarId → Ownership.Var) (dst arr : FVarId) (r : Ownership.Ref)
    (i v : Nat) (o : Ownership.Obj) (s : Machine) : Machine :=
  let (r', H1) := s.heap.alloc (o.fields.set! i (.scalar v))
  { locals := fun f => if f.name = dst.name then .ref r' else s.locals f
    nodes := s.nodes
    heap := H1.dec r 1
    env := s.env.set (assign arr) (.ref r') }

/-- Execute the fragment. Each rule is the primitive's assumed meaning; the
ownership-relevant rules (A6, A8) are the model's own transitions. A `none`
result means the fragment left the recognized alternative: the bounds result is
not `true`, so the emitted code would take the `Bool.false` branch, whose
continuation is the named non-claim A9 — or the operands are not the scalars A3
and A4 describe, which the recognized path does not produce. -/
def exec (assign : FVarId → Ownership.Var) : List Op → Machine →
    Machine × Option Ownership.Res
  | [], s => (s, some (.done s.heap s.env (s.env 0 |>.getD .erased) []))
  | .projIndex dst node :: rest, s =>                       -- A1
      exec assign rest { s with locals := (fun f =>
        if f.name = dst.name then (s.nodes node).index else s.locals f) }
  | .projValue dst node :: rest, s =>                       -- A1
      exec assign rest { s with locals := (fun f =>
        if f.name = dst.name then (s.nodes node).value else s.locals f) }
  | .projCont dst node :: rest, s =>                        -- A1
      exec assign rest { s with locals := (fun f =>
        if f.name = dst.name then (s.nodes node).continuation else s.locals f) }
  | .incIndex _ _ :: rest, s => exec assign rest s          -- A2
  | .incCont _ _ :: rest, s => exec assign rest s           -- A2
  | .decNode _ _ _ :: rest, s => exec assign rest s         -- A2
  | .arraySize dst arr :: rest, s =>                        -- A3
      match s.env (assign arr) with
      | some (.ref r) =>
          match s.heap.cells r with
          | some o =>
              exec assign rest { s with locals := (fun f =>
                if f.name = dst.name then .scalar o.fields.size else s.locals f) }
          | none =>
              exec assign rest { s with locals := (fun f =>
                if f.name = dst.name then .unknown else s.locals f) }
      | _ =>
          exec assign rest { s with locals := (fun f =>
            if f.name = dst.name then .unknown else s.locals f) }
  | .decLt dst idx size :: rest, s =>                       -- A4
      match s.locals idx, s.locals size with
      | .scalar i, .scalar n =>
          exec assign rest { s with locals := (fun f =>
            if f.name = dst.name then (if i < n then .flag true else .flag false) else s.locals f) }
      | _, _ => (s, none)
  | .siteConst dst :: rest, s =>                            -- A5
      exec assign rest { s with locals := (fun f =>
        if f.name = dst.name then .unknown else s.locals f) }
  | .boundsTrue discr :: rest, s =>                         -- A4
      match s.locals discr with
      | .flag true => exec assign rest s
      | _ => (s, none)
  | .checkExclusive dst _ arr :: rest, s =>                 -- A6
      match s.env (assign arr) with
      | some (.ref r) =>
          if s.heap.exclusive? r then exec assign rest (afterCheck assign dst r s)
          else (s, some (.fault s.heap s.env (.notExclusive r) []))
      | _ => (s, some (.fault s.heap s.env (.badVar (assign arr)) []))
  | .boxValue dst src :: rest, s =>                         -- A7
      exec assign rest { s with locals := (fun f =>
        if f.name = dst.name then s.locals src else s.locals f) }
  | .setBang dst arr idx val :: rest, s =>                  -- A8
      match s.env (assign arr), s.env (assign idx), s.env (assign val) with
      | some (.ref r), some (.scalar i), some (.scalar v) =>
          match s.heap.cells r with
          | none => (s, some (.fault s.heap s.env (.noCell r) []))
          | some o =>
              if s.heap.exclusive? r then
                let out := exec assign rest (afterMutate assign dst arr r i v o s)
                (out.1, out.2.map (·.addWrite (r, true)))
              else
                let out := exec assign rest (afterCopy assign dst arr r i v o s)
                (out.1, out.2.map (·.addWrite (r, false)))
      | _, _, _ => (s, some (.fault s.heap s.env (.badVar (assign arr)) []))
  | .retVar x :: _, s =>
      (s, some (.done s.heap s.env (s.env (assign x) |>.getD .erased) []))

/-! ## The correspondence theorem -/

/-- The ownership-relevant reading of the recognized fragment is the projected
model: the auxiliary node kinds are dropped and the check, the write and the
return keep their emitted order. -/
theorem toCode_fragment (p : Prefix) (assign : FVarId → Ownership.Var) :
    toCode assign p.fragment = p.toModel assign := rfl

/-- Executing the fragment under the assumed primitive meanings is executing the
projected model, unless the fragment left the recognized alternative (the
`Bool.false` bounds branch, whose continuation is the named non-claim A9). -/
theorem exec_eq_run (assign : FVarId → Ownership.Var) (ops : List Op) (s : Machine) :
    (exec assign ops s).2 = none ∨
      (exec assign ops s).2 = some (Ownership.run (toCode assign ops) s.env s.heap) := by
  induction ops generalizing s with
  | nil => exact Or.inr (by simp [exec, toCode, Ownership.run])
  | cons op rest ih =>
    cases op with
    | projIndex dst node =>
        exact ih { s with locals := (fun f =>
          if f.name = dst.name then (s.nodes node).index else s.locals f) }
    | incIndex x n => exact ih s
    | projValue dst node =>
        exact ih { s with locals := (fun f =>
          if f.name = dst.name then (s.nodes node).value else s.locals f) }
    | projCont dst node =>
        exact ih { s with locals := (fun f =>
          if f.name = dst.name then (s.nodes node).continuation else s.locals f) }
    | incCont x n => exact ih s
    | decNode x n objs => exact ih s
    | arraySize dst arr =>
        cases h : s.env (assign arr) with
        | none =>
            simp only [h, exec, toCode]
            exact ih _
        | some v =>
            cases v with
            | ref r =>
                cases hc : s.heap.cells r with
                | none =>
                    simp only [h, hc, exec, toCode]
                    exact ih _
                | some o =>
                    simp only [h, hc, exec, toCode]
                    exact ih _
            | scalar n =>
                simp only [h, exec, toCode]
                exact ih _
            | erased =>
                simp only [h, exec, toCode]
                exact ih _
    | decLt dst idx size =>
        cases h1 : s.locals idx <;> cases h2 : s.locals size <;>
          simp only [h1, h2, exec, toCode]
        all_goals first
          | exact ih _
          | exact Or.inl trivial
    | siteConst dst =>
        exact ih { s with locals := (fun f =>
          if f.name = dst.name then .unknown else s.locals f) }
    | boundsTrue discr =>
        cases h : s.locals discr with
        | flag b =>
            cases b with
            | true =>
                simp only [h, exec, toCode]
                exact ih s
            | false =>
                simp only [h, exec, toCode]
                exact Or.inl trivial
        | unknown =>
            simp only [h, exec, toCode]
            exact Or.inl trivial
        | scalar n =>
            simp only [h, exec, toCode]
            exact Or.inl trivial
        | ref r =>
            simp only [h, exec, toCode]
            exact Or.inl trivial
    | checkExclusive dst site arr =>
        cases h : s.env (assign arr) with
        | none =>
            simp only [h, exec, toCode, Ownership.run]
            exact Or.inr trivial
        | some v =>
            cases v with
            | ref r =>
                cases hex : s.heap.exclusive? r with
                | true =>
                    simp only [h, hex, exec, toCode, Ownership.run]
                    exact ih (afterCheck assign dst r s)
                | false =>
                    simp [h, hex, exec, toCode, Ownership.run]
            | scalar n =>
                simp only [h, exec, toCode, Ownership.run]
                exact Or.inr trivial
            | erased =>
                simp only [h, exec, toCode, Ownership.run]
                exact Or.inr trivial
    | boxValue dst src =>
        exact ih { s with locals := (fun f =>
          if f.name = dst.name then s.locals src else s.locals f) }
    | setBang dst arr idx val =>
        cases h1 : s.env (assign arr) with
        | none =>
            simp only [h1, exec, toCode, Ownership.run]
            exact Or.inr trivial
        | some v1 =>
            cases v1 with
            | ref r =>
                cases h2 : s.env (assign idx) with
                | none =>
                    simp only [h1, h2, exec, toCode, Ownership.run]
                    exact Or.inr trivial
                | some v2 =>
                    cases v2 with
                    | scalar i =>
                        cases h3 : s.env (assign val) with
                        | none =>
                            simp only [h1, h2, h3, exec, toCode, Ownership.run]
                            exact Or.inr trivial
                        | some v3 =>
                            cases v3 with
                            | scalar v =>
                                cases hc : s.heap.cells r with
                                | none =>
                                    simp only [h1, h2, h3, hc, exec, toCode,
                                      Ownership.run]
                                    exact Or.inr trivial
                                | some o =>
                                    cases hex : s.heap.exclusive? r
                                    case false =>
                                      simp only [h1, h2, h3, hc, hex, exec, toCode,
                                        Ownership.run]
                                      rcases ih (afterCopy assign dst arr r i v o s)
                                        with hres | hres
                                      · exact Or.inl (by rw [hres]; rfl)
                                      · exact Or.inr (by rw [hres]; rfl)
                                    case true =>
                                      simp only [h1, h2, h3, hc, hex, exec, toCode,
                                        Ownership.run]
                                      rcases ih (afterMutate assign dst arr r i v o s)
                                        with hres | hres
                                      · exact Or.inl (by rw [hres]; rfl)
                                      · exact Or.inr (by rw [hres]; rfl)
                            | ref _ =>
                                simp only [h1, h2, h3, exec, toCode, Ownership.run]
                                exact Or.inr trivial
                            | erased =>
                                simp only [h1, h2, h3, exec, toCode, Ownership.run]
                                exact Or.inr trivial
                    | ref _ =>
                        simp only [h1, h2, exec, toCode, Ownership.run]
                        exact Or.inr trivial
                    | erased =>
                        simp only [h1, h2, exec, toCode, Ownership.run]
                        exact Or.inr trivial
            | scalar _ =>
                simp only [h1, exec, toCode, Ownership.run]
                exact Or.inr trivial
            | erased =>
                simp only [h1, exec, toCode, Ownership.run]
                exact Or.inr trivial
    | retVar x =>
        exact Or.inr (by simp [exec, toCode, Ownership.run])

/-- `project_sound`: the recognized fragment, executed under the assumed
primitive meanings from a machine state whose heap and environment are the
model's, produces the model's own outcome.

The two named non-claims of the certified prefix are stated here: the index's
own `inc`/`dec` pair (scalar bookkeeping outside the array's mutable footprint,
A2) and the continuation with its boxed bounds result and recursive call (A9)
are not part of the fragment, and the fragment stops at the designated write's
return. The hypothesis excludes the bounds-failure branch, which selects the
continuation the milestone does not model. -/
theorem project_sound (p : Prefix) (assign : FVarId → Ownership.Var) (s : Machine)
    (h : (exec assign p.fragment s).2 ≠ none) :
    (exec assign p.fragment s).2 =
      some (Ownership.run (p.toModel assign) s.env s.heap) := by
  rcases exec_eq_run assign p.fragment s with hnone | hsome
  · exact absurd hnone h
  · rwa [toCode_fragment] at hsome

/-! ## The concrete entry invariant -/

/-- The four binders the projected model reads. Emitted LCNF binds every `let`
and every call result to a fresh fvar; the recognizer's argument identities are
only meaningful under that structural fact, which is what this records (fvar
names are the identifiers). -/
structure DistinctBinders (p : Prefix) : Prop where
  array_index : p.array.name ≠ p.index.name
  array_value : p.array.name ≠ p.value.name
  array_check : p.array.name ≠ p.checkResult.name
  index_value : p.index.name ≠ p.value.name
  index_check : p.index.name ≠ p.checkResult.name
  value_check : p.value.name ≠ p.checkResult.name
  /-- The extracted index is a different binder from the continuation and the
  size result, so the pre-bounds local writes stay distinguishable. -/
  index_continuation : p.index.name ≠ p.continuation.name
  index_sizeResult : p.index.name ≠ p.sizeResult.name

/-- The assignment of the recognized binders to the model's variables: the array
to the entry invariant's owned root variable, the index and the replacement to
its two scalars, and the check result to the fresh result variable. -/
def assignOf (p : Prefix) (arrayVar indexVar valueVar checkVar : Ownership.Var) :
    FVarId → Ownership.Var :=
  fun f =>
    if f.name = p.array.name then arrayVar
    else if f.name = p.index.name then indexVar
    else if f.name = p.value.name then valueVar
    else if f.name = p.checkResult.name then checkVar
    else 0

theorem assignOf_array (p : Prefix) (a i v c : Ownership.Var) :
    assignOf p a i v c p.array = a := by
  simp [assignOf]

theorem assignOf_index (p : Prefix) (h : DistinctBinders p) (a i v c : Ownership.Var) :
    assignOf p a i v c p.index = i := by
  have h' : p.index.name ≠ p.array.name := Ne.symm h.array_index
  simp [assignOf, h']

theorem assignOf_value (p : Prefix) (h : DistinctBinders p) (a i v c : Ownership.Var) :
    assignOf p a i v c p.value = v := by
  have h1 : p.value.name ≠ p.array.name := Ne.symm h.array_value
  have h2 : p.value.name ≠ p.index.name := Ne.symm h.index_value
  simp [assignOf, h1, h2]

theorem assignOf_check (p : Prefix) (h : DistinctBinders p) (a i v c : Ownership.Var) :
    assignOf p a i v c p.checkResult = c := by
  have h1 : p.checkResult.name ≠ p.array.name := Ne.symm h.array_check
  have h2 : p.checkResult.name ≠ p.index.name := Ne.symm h.index_check
  have h3 : p.checkResult.name ≠ p.value.name := Ne.symm h.value_check
  simp [assignOf, h1, h2, h3]

/-- The projected model is the runner's measured write prefix when the array is
bound to the owned root, the index and the replacement to its scalars, and the
check result to the fresh result variable. -/
theorem toModel_assignOf (p : Prefix) (h : DistinctBinders p) :
    p.toModel (assignOf p 0 1 2 3) = Ownership.Runner.execSet 0 3 1 2 := by
  simp [Prefix.toModel, Ownership.Runner.execSet, assignOf_array, assignOf_index p h,
    assignOf_value p h, assignOf_check p h]

/-- The checker accepts the projected model from the concrete entry context,
with the array bound to the owned root. -/
theorem projected_check (p : Prefix) (h : DistinctBinders p) (r : Ownership.Ref) :
    Ownership.check (Ownership.Runner.initCtx r) (p.toModel (assignOf p 0 1 2 3)) =
      some ((Ownership.Runner.initCtx r).move 0 3) := by
  rw [toModel_assignOf p h]
  exact Ownership.Runner.execSet_check r

/-- The heap after the designated in-place write on the initializer's array:
slot `0` holds the replacement scalar and the root's count is unchanged. -/
def inPlaceHeap (n : Nat) : Ownership.Heap :=
  (Ownership.Runner.initHeap n).2.set (Ownership.Runner.initHeap n).1
    { fields := (Array.replicate n (.scalar 0)).set! 0 (.scalar 0)
      rc := 1, persistent := false }

/-- The model environment after the designated in-place write: the check result
variable names the checked root. -/
def inPlaceEnv (n : Nat) : Ownership.Env :=
  (Ownership.Runner.initEnv (Ownership.Runner.initHeap n).1).set 3
    (.ref (Ownership.Runner.initHeap n).1)

/-- The designated write's concrete in-place execution from the initializer's
state: the checked write mutates the owned root's slot `0` and returns the root
handle, and the trace's only write is `(root, true)`. -/
theorem execSet_run (n : Nat) :
    Ownership.run (Ownership.Runner.execSet 0 3 1 2)
        (Ownership.Runner.initEnv (Ownership.Runner.initHeap n).1)
        (Ownership.Runner.initHeap n).2 =
      .done (inPlaceHeap n) (inPlaceEnv n)
        (.ref (Ownership.Runner.initHeap n).1)
        [((Ownership.Runner.initHeap n).1, true)] := by
  simp [Ownership.Runner.execSet, Ownership.Runner.initEnv,
    Ownership.Runner.initHeap, inPlaceHeap, inPlaceEnv, Ownership.run,
    Ownership.Heap.exclusive?, Ownership.Heap.set, Ownership.Env.set,
    Ownership.Res.addWrite]

/-- The designated write's run from any state that meets the conditions the entry
condition supplies at `Runner.initCtx`'s layout: the owned root at variable `0`,
its two scalars at `1` and `2`, an exclusive root cell, and the check's result
variable `3` free. -/
theorem execSet_run_of {H : Ownership.Heap} {env : Ownership.Env} {root : Ownership.Ref}
    {i v : Nat} {o : Ownership.Obj}
    (h0 : env 0 = some (.ref root)) (h1 : env 1 = some (.scalar i))
    (h2 : env 2 = some (.scalar v)) (hcell : H.cells root = some o)
    (hex : H.exclusive? root = true) :
    Ownership.run (Ownership.Runner.execSet 0 3 1 2) env H =
      .done (H.set root { o with fields := o.fields.set! i (.scalar v) })
        (env.set 3 (.ref root)) (.ref root) [(root, true)] := by
  simp [Ownership.Runner.execSet, Ownership.run, h0, h1, h2, hcell, hex,
    Ownership.Env.set, Ownership.Res.addWrite]

/-- The steering note's completion statement: for a declaration whose replayed
`PTree.set` alternative the projection recognizes, from any state satisfying the
concrete entry condition at the projected variable layout, the checker accepts
the projected model, its run is fault-free, the designated write selects the
in-place branch, and the target address and the returned handle are the root.

The entry condition is what supplies the exclusivity the write needs: with
`multOf 0 = 1` and `rc_eq`, `Inv.exclusive` makes the root's cell exclusive, so
the model takes the mutate branch without copying. `hproj` records that `p` is a
projection of the declaration under consideration; `hbind` is the fresh-binder
fact the projected variable layout needs. -/
theorem designated_write_in_place {code : Code .impure} {p : Prefix}
    (_hproj : projectPrefix code = some p) (hbind : DistinctBinders p)
    {H : Ownership.Heap} {env : Ownership.Env} {root : Ownership.Ref}
    {client : List Ownership.Ref}
    (hEntry : Ownership.Entry.EntryInv H env (Ownership.Runner.initCtx root) root client) :
    Ownership.check (Ownership.Runner.initCtx root) (p.toModel (assignOf p 0 1 2 3)) =
        some ((Ownership.Runner.initCtx root).move 0 3) ∧
      (∃ H' env', Ownership.run (p.toModel (assignOf p 0 1 2 3)) env H =
        .done H' env' (.ref root) [(root, true)]) := by
  have hi : Ownership.Inv H env (Ownership.Runner.initCtx root) := hEntry.toInv
  obtain ⟨r, hr, hmul⟩ :=
    Ownership.Ctx.multOf_eq_one (Ownership.Runner.initCtx_multOf_zero root)
  have hrroot : r = root := by
    have h : (Ownership.Runner.initCtx root).refOf 0 = some r := hr
    rw [Ownership.Runner.initCtx_refOf_zero] at h
    exact (Option.some.inj h).symm
  have hmul' : (Ownership.Runner.initCtx root).mult root = 1 := by
    simpa [hrroot] using hmul
  have hex : H.exclusive? root = true :=
    (Ownership.Heap.exclusive?_eq_true).mpr (hi.exclusive hmul')
  obtain ⟨o, hcell, _, _⟩ := hi.exclusive hmul'
  have h0 : env 0 = some (.ref root) :=
    (hi.owned 0 root (by simp [Ownership.Runner.initCtx])
      (Ownership.Runner.initCtx_refOf_zero root)).1
  obtain ⟨i, h1⟩ := hi.scalar 1 (by simp [Ownership.Runner.initCtx])
  obtain ⟨v, h2⟩ := hi.scalar 2 (by simp [Ownership.Runner.initCtx])
  refine ⟨?_, ?_⟩
  · rw [toModel_assignOf p hbind]
    exact Ownership.Runner.execSet_check root
  · rw [toModel_assignOf p hbind]
    exact ⟨_, _, execSet_run_of h0 h1 h2 hcell hex⟩

/-- The target result at the initializer: `Entry.initEntryInv` supplies the entry
condition, and `Runner.initHeap`/`initEnv` are the state it describes. -/
theorem initializer_designated_write_in_place {code : Code .impure} {p : Prefix}
    (_hproj : projectPrefix code = some p) (hbind : DistinctBinders p) (n : Nat) :
    ∃ H' env', Ownership.run (p.toModel (assignOf p 0 1 2 3))
        (Ownership.Runner.initEnv (Ownership.Runner.initHeap n).1)
        (Ownership.Runner.initHeap n).2 =
      .done H' env' (.ref (Ownership.Runner.initHeap n).1)
        [((Ownership.Runner.initHeap n).1, true)] :=
  (designated_write_in_place _hproj hbind
    (Ownership.Entry.initEntryInv n)).2

/-! ## The fragment, from the concrete entry state -/

/-- The fragment's initial machine state for the concrete scalar-array update:
the initializer's heap and model environment, the reified node fields the caller
supplies (A1), and every other local unconstrained. -/
def initMachine (p : Prefix) (n : Nat) : Machine :=
  { locals := fun _ => .unknown
    nodes := fun f =>
      if f.name = p.node.name then ⟨.scalar 0, .scalar 0, .unknown⟩
      else ⟨.unknown, .unknown, .unknown⟩
    heap := (Ownership.Runner.initHeap n).2
    env := Ownership.Runner.initEnv (Ownership.Runner.initHeap n).1 }

/-- The recognized fragment, executed under the assumed primitive meanings from
the concrete entry state, performs the designated in-place write at the root
address: the same poststate the projected model reaches.

The index and the replacement come from the node's reified fields (A1) and equal
the initializer's two scalar variables; the bounds check passes because the
initializer's index `0` is below the array's length `n`. The hypothesis `hproj`
is what connects the statement to a declaration the recognizer accepts, and
`hbind` is the fresh-binder fact the projected model relies on. -/
theorem fragment_in_place {code : Code .impure} {p : Prefix}
    (_hproj : projectPrefix code = some p) (hbind : DistinctBinders p)
    {n : Nat} (hin : 0 < n) :
    (exec (assignOf p 0 1 2 3) p.fragment (initMachine p n)).2 =
      some (.done (inPlaceHeap n) (inPlaceEnv n)
        (.ref (Ownership.Runner.initHeap n).1)
        [((Ownership.Runner.initHeap n).1, true)]) := by
  simp [Prefix.fragment, exec, initMachine, afterCheck, afterMutate,
    inPlaceHeap, inPlaceEnv, assignOf_array p, assignOf_index p hbind,
    assignOf_value p hbind, assignOf_check p hbind, hbind.index_continuation,
    hbind.index_sizeResult, hin, Ownership.Runner.initEnv,
    Ownership.Runner.initHeap, Ownership.Heap.exclusive?, Ownership.Heap.set,
    Ownership.Env.set, Ownership.Res.addWrite]

#print axioms OwnershipLcnf.toCode_fragment
#print axioms OwnershipLcnf.exec_eq_run
#print axioms OwnershipLcnf.project_sound
#print axioms OwnershipLcnf.projected_check
#print axioms OwnershipLcnf.execSet_run
#print axioms OwnershipLcnf.execSet_run_of
#print axioms OwnershipLcnf.designated_write_in_place
#print axioms OwnershipLcnf.initializer_designated_write_in_place
#print axioms OwnershipLcnf.fragment_in_place

end OwnershipLcnf
