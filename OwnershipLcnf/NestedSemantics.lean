/-
The recognized nested `setAt` `Path.index` fragment's meaning, its model term,
and the correspondence between the two.

`NestedProjection.lean` walks the pinned `Path.index` alternative and returns a
`NestedPrefix` whose `fragment` is the twenty-five-operation trace of that walk.
This module gives those operations an explicit meaning over `Ownership.Heap` and
`Ownership.Env` (`execNested`), reads the model term off the recognizer's own
operand binders (`indexModelTerm`), and proves that executing the recognized
trace reports the same heap, result and write trace as
`Ownership.Nested.runN` of the model term (`index_prefix_simulates_model`), with
no fault — and, over the actual declaration, `index_code_simulates_model`.

`Lean.Compiler.LCNF.Code` has no Lean-checked operational semantics, so the
meaning of each primitive is an *assumption* of this module, not a theorem about
the compiler. Nothing below claims that the C backend, the runtime, or an
arbitrary LCNF program behaves this way.

The emitted recursive callee's body is **not** captured: the child call's
contract is a hypothesis about an admitted model body
(`ChildContract`), and the theorem must not be read as certification of the
emitted recursive declaration. That link is an outstanding obligation.

## Assumptions, premises and contracts

**Encoded in the definitions of this module** (checkable by reading the code):

* the fragment's machine (`NestedMachine`) has the ownership heap, the variable
  environment, the reified `Path.index` node fields, the scalar the model hands
  its callee as the continuation path, the model's variable for the extracted
  element, the take-out pair the take-out step stored, and the writes the callee
  recorded. There are no other components: every value the fragment reads back
  is read from `env` at the binder the emitted code bound it to, or from the
  pair the recognizeable take-out step stored at the pair binder;
* `execNested`'s rules are the transitions, over the recognizer's own
  `NestedPrefix.fragment` — not a separately supplied program;
* the bounds flag is `Bool`-as-scalar (`1`/`0`), the encoding the model's own
  `LetF.isShared` uses;
* the model term is built from the recognizer's operand binders: the take-out
  from the array parameter the assertion checked, the selected index, and the
  pair's two projections; the recursive call on the extracted element with the
  continuation path, the value parameter and the recursive result; the put-back
  into the extracted parent at the selected index with the recursive result; and
  the return of the put-back's result.

**Explicit theorem premises** (each named at the theorem that takes it):

* `NestedLayout`: the nineteen binders whose environment traffic the fragment
  performs occupy the nineteen distinct slots `0`–`18`. Slots `0`–`7` are the
  model's variables (array parameter, index, value, parent, child, path,
  recursive result, restored array); `8`–`18` are the projections, bounds,
  assertion, default, pair, site and decrement results the model has no variable
  for. This is the fresh-binder fact emitted LCNF supplies, and it is what keeps
  the auxiliary writes from touching a model variable.
* `NestedAgrees`: the initial-state relation between the machine and the model
  environment — the machine's array slot and the model's name the same
  reference, the model's index and value variables are the reified node field
  and the machine's value slot, the machine's call-path scalar is the model's
  path scalar, the machine's child variable is the model's, and the machine's
  heap is the model's.
* the array cell `o` at the root reference and its exclusivity, which is the
  array assertion's precondition;
* the expected child slot `o.fields[i]? = some (.ref childRef)`, i.e. the
  element the model's take-out expects is the one the heap holds there;
* the in-bounds fact `i < o.fields.size`;
* `hsep`: the parent array is not in the child's mutable footprint, so the
  child body's own confinement does not let it change the parent between the
  take-out and the put-back;
* `ChildContract`: the child-call contract, below.

**Named external contracts** (trusted for this milestone, not proved):

* **N1 (path projections).** `oproj[0]`, `oproj[1]` and `oproj[2]` of the
  `Path.index` node read its layout field, its selected index and its
  continuation. The layout field is opaque and only `stateDefault` consumes it;
  the continuation is abstracted as the scalar the model hands its callee, so
  `projPath` binds the model's path variable to that scalar. The recognizer
  pins which fields the path reads, so a layout change is a rejection, not a
  silent misinterpretation.
* **N2 (refcount traffic).** The `inc`/`dec` steps on the path, its array field,
  its index, its continuation, the extracted parent, the extracted child and
  the pair are refcount traffic on handles the model heap has no cell for: they
  leave the model's heap, environment and write trace untouched. This is the
  named non-claim for the fragment's own increments and decrements. Treating
  that traffic as disjoint from the array's and the child's cells is a
  **modeling premise**: this fragment represents neither the path nor the pair
  as a `Ref`, so there is no cell for their counts to collide with. The model's
  counts are the checker's `mult`, not these.
* **N3 (`Array.size`).** `Array.size a` yields the array cell's field count,
  which is what the model's `LetF.size` reads.
* **N4 (`Nat.decLt` and the bounds alternative).** `Nat.decLt i n` yields the
  bounds flag: true exactly when `i < n`. The recognizer selects the
  `Bool.true` alternative by constructor identity; whether the runtime takes it
  is a fact about the index and the array's length, so the interpreter records
  the branch selection as a step and fails if the flag is not `1`.
* **N5 (site constants).** The two site constants are opaque; the assertions
  ignore them, and the fragment neither writes nor reads them in `env`.
* **N6 (array exclusivity assertion).** `assertExclusiveArrayImpl site a`
  returns `a` on the exclusive branch and faults otherwise, with no heap
  effect: the returned handle is the same handle. Both call conventions the
  recognizer matches — the plain and the specialized `._redArg` form — are
  stated alternatives.
* **N7 (`stateDefault`).** `stateDefault` of the path's layout field yields the
  model's default state: the placeholder scalar `0` the model's take-out writes
  into the emptied slot. The model has no variable for the layout field, so this
  contract is what makes the emitted default the model's default.
* **N8 (take-out).** The `takeOut` helper reads the array's selected slot and
  returns the pair `(array with the placeholder in that slot, extracted
  element)`: the meaning of the model's `NCode.takeOut`, including the
  `setIfInBounds` placeholder write. The helper's own body is not captured; the
  call's operands are, and the recognizer checks them.
* **N9 (child exclusivity assertion).** `assertExclusiveImpl site s` returns
  `s` on the exclusive branch and faults otherwise, with no heap effect.
* **N10 (recursive call).** The recursive `setAt` call's meaning is the model's
  `NCode.callAt`: the admitted body runs on the environment that exposes only
  the call's own state, path and index, on the caller's heap, and the caller's
  continuation runs on the heap the body leaves. **The emitted callee's body is
  not captured**; `ChildContract` is a hypothesis about the admitted model body,
  and the correspondence below is conditional on it.
* **N11 (put-back).** `Array.set` writes the recursive result into the extracted
  parent's selected slot in place and returns that array: the meaning of the
  model's `NCode.putBack`. The runtime copy branch for a shared array is not
  modelled on this path. The fragment relies on the array exclusivity assertion
  that preceded the take-out; the correspondence does not prove that the
  assertion's verdict still holds when the put-back runs, so in-place is part of
  the contract, not a consequence of it.
* **N12 (call signatures).** The primitive arities the recognizer checks are the
  specialized forms the pinned compiler emits for this declaration.

## The child-call contract

`ChildContract` states what this module assumes about the admitted model body the
recursive call runs: the call's state is exclusive (the child assertion's
precondition), the body runs fault-free and returns the state reference, every
write in its trace selects the exclusive branch, and it leaves every cell
outside the state reference's mutable footprint unchanged. It is a hypothesis,
not a theorem about the emitted recursive declaration; the latter is an
outstanding obligation.

## What is not claimed

The emitted recursive callee, general recursion, joins, callbacks and the other
outer `Path` alternatives are outside this module. The bounds-failure arm is not
walked. No physical runtime reference count, backend input or memory claim is
made: the model's counts are the restricted semantics' counts.
-/
import OwnershipLcnf.NestedProjection
import Ownership.Entry

open Lean
open Lean.Compiler.LCNF

namespace OwnershipLcnf

/-! ## The fragment's machine -/

/-- A reified field of the `Path.index` node: the scalar the caller fixes for it,
or `unknown` when it fixes none. -/
inductive PathField where
  | unknown
  | scalar (n : Nat)
  deriving DecidableEq, Repr

/-- The reified `Path.index` node fields the fragment projects. Only the selected
index is a model operand; the layout field is consumed by `stateDefault` (N7)
and the continuation is abstracted as the machine's call-path scalar (N1). -/
structure PathFields where
  index : PathField := .unknown
  deriving Inhabited, Repr

/-- The fragment's machine state. `callPath` is the scalar the model hands its
callee as the continuation path (the continuation itself is opaque, N1);
`childVar` is the model variable the take-out binds the extracted element to,
which is the recursive call's state argument; `pairs` holds the take-out pair at
the binder the take-out bound it to; `writes` is the callee's recorded write
trace. -/
structure NestedMachine where
  heap : Ownership.Heap
  env : Ownership.Env
  nodes : FVarId → PathFields
  callPath : Nat
  childVar : Ownership.Var
  pairs : Name → Option (Ownership.Val × Ownership.Val)
  writes : List Ownership.Write

/-- The environment the model hands an admitted callee: only the call's three
arguments are visible, so the body cannot name a suspended frame's variables. -/
def callEnv (state : Ownership.Var) (sv : Ownership.Val) (path : Ownership.Var)
    (pv : Ownership.Val) (x : Ownership.Var) (xv : Ownership.Val) : Ownership.Env :=
  fun z => if z = state then some sv else if z = path then some pv
           else if z = x then some xv else none

/-- The model's callee environment is the isolated environment of the caller's
environment, pinned at the three arguments the call passes. -/
theorem isolateEnv_eq_callEnv {env : Ownership.Env} {state path x : Ownership.Var}
    {sv pv xv : Ownership.Val}
    (hs : env state = some sv) (hp : env path = some pv) (hx : env x = some xv) :
    Ownership.Nested.isolateEnv env state path x = callEnv state sv path pv x xv := by
  funext z
  by_cases h1 : z = state
  · subst h1; simp [Ownership.Nested.isolateEnv, callEnv, hs]
  · by_cases h2 : z = path
    · subst h2; simp [Ownership.Nested.isolateEnv, callEnv, h1, hp]
    · by_cases h3 : z = x
      · subst h3; simp [Ownership.Nested.isolateEnv, callEnv, h1, h2, hx]
      · simp [Ownership.Nested.isolateEnv, callEnv, h1, h2, h3]

/-- Store a pair at the binder a take-out bound it to. A binder's identity is
its name, so the pair is keyed by the name the recognizer recorded. -/
def setPair (pairs : Name → Option (Ownership.Val × Ownership.Val)) (k : Name)
    (v : Ownership.Val × Ownership.Val) : Name → Option (Ownership.Val × Ownership.Val) :=
  fun k' => if k' = k then some v else pairs k'

@[simp] theorem setPair_self (pairs : Name → Option (Ownership.Val × Ownership.Val))
    (k : Name) (v : Ownership.Val × Ownership.Val) : setPair pairs k v k = some v := by
  simp [setPair]

@[simp] theorem setPair_other (pairs : Name → Option (Ownership.Val × Ownership.Val))
    (k k' : Name) (v : Ownership.Val × Ownership.Val) (h : k' ≠ k) :
    setPair pairs k v k' = pairs k' := by
  simp [setPair, h]

/-- The heap the take-out leaves: the selected slot holds the model's placeholder
scalar. -/
def takeOutHeap (H : Ownership.Heap) (r : Ownership.Ref) (o : Ownership.Obj)
    (i : Nat) : Ownership.Heap :=
  H.set r { o with fields := o.fields.setIfInBounds i (.scalar 0) }

/-- The object the take-out leaves at the extracted array. -/
def takeOutObj (o : Ownership.Obj) (i : Nat) : Ownership.Obj :=
  { o with fields := o.fields.setIfInBounds i (.scalar 0) }

/-! ## Executing the recognized trace -/

/-- Execute the recognized operation trace. Each rule is the primitive's assumed
meaning; the ownership-relevant rules are the model's own transitions. A `none`
result means the fragment left the recognized path (an operand is not the value
the recognized path produces), and a fault is reported where the primitive
faults.

The rules that matter for the correspondence:

* `projIndex` writes the node's reified index into the model's index variable;
  `projPath` writes the machine's call-path scalar into the model's path
  variable; `projArray` binds the opaque layout value (N1);
* `arraySize`/`decLt`/`boundsTrue` establish and consume the bounds flag (N3,
  N4);
* `checkArray`/`checkChild` return their array argument on the exclusive branch
  and fault otherwise (N6, N9);
* `stateDefault` yields the model's placeholder scalar (N7);
* `takeOut` performs the model take-out: the old element leaves the slot, the
  placeholder enters it, and the pair is stored at the pair binder (N8);
* `projParent`/`projChild` read the pair's two components, so the model's
  parent and child variables are the projections' results (N1);
* `recurse` runs the admitted body on the call environment and records its
  writes (N10);
* `setArray` performs the model put-back and binds the returned array (N11);
* `retVar` observes the returned value from the machine's environment. -/
def execNested (assign : FVarId → Ownership.Var) (body : Ownership.Nested.NCode) :
    List NestedOp → NestedMachine → NestedMachine × Option Ownership.Res
  | [], s => (s, some (.done s.heap s.env .erased s.writes))
  | .projArray dst _ :: rest, s =>
      execNested assign body rest { s with env := s.env.set (assign dst) .erased }
  | .incArray _ _ :: rest, s => execNested assign body rest s
  | .projIndex dst node :: rest, s =>
      match (s.nodes node).index with
      | .scalar i => execNested assign body rest { s with env := s.env.set (assign dst) (.scalar i) }
      | .unknown => (s, none)
  | .incIndex _ _ :: rest, s => execNested assign body rest s
  | .projPath dst _ :: rest, s =>
      execNested assign body rest { s with env := s.env.set (assign dst) (.scalar s.callPath) }
  | .incPath _ _ :: rest, s => execNested assign body rest s
  | .decNode _ _ :: rest, s => execNested assign body rest s
  | .arraySize dst arr :: rest, s =>
      match s.env (assign arr) with
      | some (.ref r) =>
          match s.heap.cells r with
          | some o =>
              execNested assign body rest { s with env := s.env.set (assign dst) (.scalar o.fields.size) }
          | none => (s, none)
      | _ => (s, none)
  | .decLt dst idx size :: rest, s =>
      match s.env (assign idx), s.env (assign size) with
      | some (.scalar i), some (.scalar n) =>
          execNested assign body rest
            { s with env := s.env.set (assign dst) (.scalar (if i < n then 1 else 0)) }
      | _, _ => (s, none)
  | .boundsTrue discr :: rest, s =>
      match s.env (assign discr) with
      | some (.scalar 1) => execNested assign body rest s
      | _ => (s, none)
  | .siteConst _ _ :: rest, s => execNested assign body rest s
  | .checkArray dst _ arr :: rest, s =>
      match s.env (assign arr) with
      | some (.ref r) =>
          if s.heap.exclusive? r then
            execNested assign body rest { s with env := s.env.set (assign dst) (.ref r) }
          else (s, some (.fault s.heap s.env (.notExclusive r) s.writes))
      | _ => (s, some (.fault s.heap s.env (.badVar (assign arr)) s.writes))
  | .stateDefault dst arr :: rest, s =>
      match s.env (assign arr) with
      | some _ => execNested assign body rest { s with env := s.env.set (assign dst) (.scalar 0) }
      | none => (s, none)
  | .takeOut dst check idx dflt :: rest, s =>
      match s.env (assign check), s.env (assign idx), s.env (assign dflt) with
      | some (.ref r), some (.scalar i), some (.scalar d) =>
          match s.heap.cells r with
          | some o =>
              match o.fields[i]? with
              | some (.ref e) =>
                  execNested assign body rest
                    { s with
                      heap := s.heap.set r { o with fields := o.fields.setIfInBounds i (.scalar d) }
                      pairs := setPair s.pairs dst.name (.ref r, .ref e) }
              | _ => (s, none)
          | none => (s, some (.fault s.heap s.env (.noCell r) s.writes))
      | _, _, _ => (s, none)
  | .projParent dst pair :: rest, s =>
      match s.pairs pair.name with
      | some (a, _) => execNested assign body rest { s with env := s.env.set (assign dst) a }
      | none => (s, none)
  | .incParent _ :: rest, s => execNested assign body rest s
  | .projChild dst pair :: rest, s =>
      match s.pairs pair.name with
      | some (_, b) => execNested assign body rest { s with env := s.env.set (assign dst) b }
      | none => (s, none)
  | .incChild _ :: rest, s => execNested assign body rest s
  | .decPair _ :: rest, s => execNested assign body rest s
  | .checkChild dst _ child :: rest, s =>
      match s.env (assign child) with
      | some (.ref r) =>
          if s.heap.exclusive? r then
            execNested assign body rest { s with env := s.env.set (assign dst) (.ref r) }
          else (s, some (.fault s.heap s.env (.notExclusive r) s.writes))
      | _ => (s, some (.fault s.heap s.env (.badVar (assign child)) s.writes))
  | .recurse dst path value child :: rest, s =>
      match s.env (assign child), s.env (assign path), s.env (assign value) with
      | some (.ref r), some (.scalar pv), some (.scalar v) =>
          match Ownership.Nested.runN body
              (callEnv s.childVar (.ref r) (assign path) (.scalar pv) (assign value) (.scalar v))
              s.heap with
          | .done H' _ _ ws =>
              execNested assign body rest
                { s with heap := H', env := s.env.set (assign dst) (.ref r), writes := s.writes ++ ws }
          | .fault H' _ f ws => (s, some (.fault H' s.env f (s.writes ++ ws)))
      | _, _, _ => (s, none)
  | .setArray dst arr idx val :: rest, s =>
      match s.env (assign arr), s.env (assign idx), s.env (assign val) with
      | some (.ref r), some (.scalar i), some (.ref e) =>
          match s.heap.cells r with
          | some o =>
              execNested assign body rest
                { s with
                  heap := s.heap.set r { o with fields := o.fields.set! i (.ref e) }
                  env := s.env.set (assign dst) (.ref r) }
          | none => (s, some (.fault s.heap s.env (.noCell r) s.writes))
      | _, _, _ => (s, none)
  | .decIndex _ :: rest, s => execNested assign body rest s
  | .retVar x :: _, s =>
      (s, some (.done s.heap s.env (s.env (assign x) |>.getD .erased) s.writes))

/-! ## Executing the recognized AST -/

/-- Execute the recognized prefix of an actual LCNF code value. `projectNested`
walks `code`, and the result is returned only when the prefix it decoded is the
expected `p` (by binder identity); a code value that does not decode to `p` is
not executed at all. This is what makes the recognition hypothesis of the
theorems load-bearing: without it, nothing is known about `code`, and
`execNestedAST` may return `none`. -/
def execNestedAST (declName takeOut : Name) (assign : FVarId → Ownership.Var)
    (body : Ownership.Nested.NCode) (p : NestedPrefix) (code : Code .impure)
    (s : NestedMachine) : Option (NestedMachine × Option Ownership.Res) :=
  match projectNested declName takeOut code with
  | none => none
  | some p' =>
      if p'.binderNames = p.binderNames then some (execNested assign body p'.fragment s)
      else none

/-- The recognition hypothesis is consumed: for a code value the projection
decodes to `p`, `execNestedAST` executes that code's own trace. -/
theorem execNestedAST_recognized (declName takeOut : Name)
    (assign : FVarId → Ownership.Var) (body : Ownership.Nested.NCode)
    (p : NestedPrefix) (code : Code .impure) (s : NestedMachine)
    (hproj : projectNested declName takeOut code = some p) :
    execNestedAST declName takeOut assign body p code s =
      some (execNested assign body p.fragment s) := by
  simp [execNestedAST, hproj]

/-! ## The observation boundary -/

/-- The observation boundary of the recognized fragment: the heap the fragment
leaves, the value the return step observes, the fault status and the write
trace. The machine's environment is not part of the boundary. -/
structure NestedOutcome where
  /-- The ownership heap at the boundary. -/
  heap : Ownership.Heap
  /-- The returned value, when the fragment completed. -/
  result : Option Ownership.Val
  /-- The ownership fault, when the outcome is a fault. -/
  fault : Option Ownership.Fault
  /-- The write trace at the boundary. -/
  writes : List Ownership.Write

/-- The outcome the executed machine reports. The result is read from the
machine's own environment at the binder the return step observes, so it is the
value the return sees rather than an opaque completion value; the heap, fault
and trace are the interpreter's. -/
def NestedOutcome.ofMachine (assign : FVarId → Ownership.Var) (p : NestedPrefix)
    (M : NestedMachine) : Ownership.Res → NestedOutcome
  | .done H _ _ ws =>
      { heap := H, result := M.env (assign p.restored), fault := none, writes := ws }
  | .fault H _ f ws =>
      { heap := H, result := none, fault := some f, writes := ws }

/-- The outcome the ownership model's run reports. -/
def NestedOutcome.ofModel : Ownership.Res → NestedOutcome
  | .done H _ v ws => { heap := H, result := some v, fault := none, writes := ws }
  | .fault H _ f ws => { heap := H, result := none, fault := some f, writes := ws }

/-- The outcome an `execNested` result reports, when the execution produced a
result at all. -/
def NestedOutcome.ofExec (assign : FVarId → Ownership.Var) (p : NestedPrefix)
    (out : Option (NestedMachine × Option Ownership.Res)) : Option NestedOutcome :=
  match out with
  | some (M, some r) => some (NestedOutcome.ofMachine assign p M r)
  | _ => none

/-! ## The variable layout and the initial-state relation -/

/-- The variable layout the fragment and the model share: the nineteen binders
whose environment traffic the fragment performs occupy the nineteen distinct
slots `0`–`18`. Slots `0`–`7` are the model's variables (array parameter, index,
value, parent, child, path, recursive result, restored array); `8`–`18` are the
projections, bounds, assertion, default, pair and site results the model has no
variable for. Which binder takes which slot is the caller's choice; that the
slots are distinct is the fresh-binder fact emitted LCNF supplies. -/
structure NestedLayout (assign : FVarId → Ownership.Var) (p : NestedPrefix) : Prop where
  array : assign p.array = 0
  index : assign p.index = 1
  value : assign p.value = 2
  parent : assign p.parent = 3
  child : assign p.child = 4
  path : assign p.path = 5
  recursive : assign p.recursive = 6
  restored : assign p.restored = 7
  node : assign p.node = 8
  childArray : assign p.childArray = 9
  sizeResult : assign p.sizeResult = 10
  bound : assign p.bound = 11
  arraySite : assign p.arraySite = 12
  arrayCheck : assign p.arrayCheck = 13
  dflt : assign p.dflt = 14
  pair : assign p.pair = 15
  childSite : assign p.childSite = 16
  childCheck : assign p.childCheck = 17
  indexDec : assign p.indexDec = 18

/-- The initial-state agreement between the machine the fragment executes from
and the model environment: the machine's array slot and the model's name the
same reference, the model's index variable is the reified node field, the
model's value variable is the machine's value slot, the model's path variable is
the machine's call-path scalar, the machine's child variable is the model's, the
machine's heap is the model's, and the machine's write trace starts empty, so
the callee's writes are the whole trace the fragment reports. -/
structure NestedAgrees (assign : FVarId → Ownership.Var) (p : NestedPrefix)
    (s : NestedMachine) (mEnv : Ownership.Env) (H : Ownership.Heap)
    (rA : Ownership.Ref) (i v pv : Nat) : Prop where
  heap : s.heap = H
  array_machine : s.env (assign p.array) = some (.ref rA)
  array_model : mEnv (assign p.array) = some (.ref rA)
  index_model : mEnv (assign p.index) = some (.scalar i)
  value_machine : s.env (assign p.value) = some (.scalar v)
  value_model : mEnv (assign p.value) = some (.scalar v)
  path_model : mEnv (assign p.path) = some (.scalar pv)
  callPath : s.callPath = pv
  childVar : s.childVar = assign p.child
  nodes : s.nodes p.node = { index := .scalar i }
  writes : s.writes = []

/-- The child-call contract: what this module assumes about the admitted model
body the recursive call runs. The body is fault-free, returns the state
reference, writes only exclusively, and leaves every cell outside the state
reference's mutable footprint unchanged. The state's exclusivity is the child
assertion's precondition. -/
structure ChildContract (H : Ownership.Heap) (cenv : Ownership.Env)
    (body : Ownership.Nested.NCode) (r : Ownership.Ref) : Prop where
  /-- The call's state reference is exclusive at entry. -/
  exclusive : H.exclusive? r = true
  /-- The body's own outcome. -/
  outcome : ∃ H' envb ws,
      Ownership.Nested.runN body cenv H = .done H' envb (.ref r) ws ∧
      (∀ w ∈ ws, w.2 = true) ∧
      (∀ q, ¬ Ownership.Entry.MutableFootprint H r q → H'.cells q = H.cells q)

/-! ## The model term -/

/-- The model term, read off the recognizer's own operand binders. The take-out
is taken from the array parameter the assertion checked, at the selected index;
its pair's components are the projections' binders. The recursive call runs the
admitted body on the extracted element, with the continuation path, the value
parameter and the recursive result. The put-back writes the recursive result into
the extracted parent at the selected index, and the program returns the
put-back's result. -/
def indexModelTerm (assign : FVarId → Ownership.Var) (p : NestedPrefix)
    (childRef : Ownership.Ref) (body : Ownership.Nested.NCode) : Ownership.Nested.NCode :=
  .takeOut (assign p.array) (assign p.index) (assign p.parent) (assign p.child) childRef
    (.callAt (assign p.child) (assign p.path) (assign p.value) (assign p.recursive) body
      (.putBack (assign p.parent) (assign p.recursive) (assign p.index) (assign p.restored)
        (.ret (assign p.restored))))

/-! ## The correspondence -/

/-- The recognized fragment simulates the ownership model's nested instance.

From the layout, the initial-state agreement, the array's cell and exclusivity,
the expected child slot, the in-bounds fact, the parent/child separation and the
child-call contract, executing the recognized trace's own operations reports the
same outcome as `Ownership.Nested.runN` of the model term: the same heap, the
same returned value, no fault, and the same write trace, whose writes are all
exclusive.

The take-out's array is the array parameter the recognizer's `array` field
names — the one the exclusivity assertion checked and the take-out extracted
from; the model's other variables are the pair's projections, the continuation
path, the value parameter, the recursive result and the restored array. -/
theorem index_fragment_simulates_model
    (assign : FVarId → Ownership.Var) (p : NestedPrefix) (hl : NestedLayout assign p)
    (body : Ownership.Nested.NCode) (s : NestedMachine) (mEnv : Ownership.Env)
    (H : Ownership.Heap) (rA : Ownership.Ref) (o : Ownership.Obj) (i v pv : Nat)
    (childRef : Ownership.Ref)
    (hag : NestedAgrees assign p s mEnv H rA i v pv)
    (hcell : H.cells rA = some o)
    (hex : H.exclusive? rA = true)
    (hslot : o.fields[i]? = some (.ref childRef))
    (hin : i < o.fields.size)
    (hsep : ¬ Ownership.Entry.MutableFootprint (takeOutHeap H rA o i) childRef rA)
    (hchild : ChildContract (takeOutHeap H rA o i)
      (callEnv (assign p.child) (.ref childRef) (assign p.path) (.scalar pv)
        (assign p.value) (.scalar v)) body childRef) :
    NestedOutcome.ofExec assign p (execNested assign body p.fragment s) =
        some (NestedOutcome.ofModel
          (Ownership.Nested.runN (indexModelTerm assign p childRef body) mEnv H)) ∧
      (∃ H' env' ws,
        Ownership.Nested.runN (indexModelTerm assign p childRef body) mEnv H =
          .done H' env' (.ref rA) ws ∧ (∀ w ∈ ws, w.2 = true)) := by
  obtain ⟨Hb, envb, wsb, hrunb, hwsb, hconf⟩ := hchild.outcome
  -- the agreement, normalized to the layout's slots
  have hheap : s.heap = H := hag.heap
  have harr : s.env 0 = some (.ref rA) := by simpa [hl.array] using hag.array_machine
  have hval : s.env 2 = some (.scalar v) := by simpa [hl.value] using hag.value_machine
  have harrM : mEnv 0 = some (.ref rA) := by simpa [hl.array] using hag.array_model
  have hindexM : mEnv 1 = some (.scalar i) := by simpa [hl.index] using hag.index_model
  have hvalM : mEnv 2 = some (.scalar v) := by simpa [hl.value] using hag.value_model
  have hpathM : mEnv 5 = some (.scalar pv) := by simpa [hl.path] using hag.path_model
  have hchildVar : s.childVar = 4 := by simpa [hl.child] using hag.childVar
  have hcallPath : s.callPath = pv := hag.callPath
  have hwrites0 : s.writes = [] := hag.writes
  have hchildEx : (H.set rA { o with fields := o.fields.setIfInBounds i (.scalar 0) }).exclusive?
      childRef = true := hchild.exclusive
  -- the child body runs on the environment the model hands it
  have hrunb' : Ownership.Nested.runN body
      (callEnv 4 (.ref childRef) 5 (.scalar pv) 2 (.scalar v))
      (H.set rA { o with fields := o.fields.setIfInBounds i (.scalar 0) }) =
      .done Hb envb (.ref childRef) wsb := by
    simpa [hl.child, hl.path, hl.value, takeOutHeap] using hrunb
  -- the selected slot holds the expected element, read as a field
  have hslot' : o.fields[i] = .ref childRef := by
    have h1 : o.fields[i]? = some o.fields[i] := by simp [hin]
    have h2 : some o.fields[i] = some (.ref childRef) := by rw [← h1]; exact hslot
    exact Option.some.inj h2
  -- the body left the extracted parent's cell live
  have hcellHb : Hb.cells rA = some { o with fields := o.fields.setIfInBounds i (.scalar 0) } := by
    rw [hconf rA hsep, takeOutHeap]
    exact Ownership.Heap.set_self (H := H) rA { o with fields := o.fields.setIfInBounds i (.scalar 0) }
  -- the model's callee environment is the call environment
  have hiso : Ownership.Nested.isolateEnv
      ((mEnv.set 3 (.ref rA)).set 4 (.ref childRef)) 4 5 2 =
      callEnv 4 (.ref childRef) 5 (.scalar pv) 2 (.scalar v) := by
    refine isolateEnv_eq_callEnv ?_ ?_ ?_
    · simp [Ownership.Env.set]
    · simp [Ownership.Env.set, hpathM]
    · simp [Ownership.Env.set, hvalM]
  -- the model run, reduced
  have hmodelRun : Ownership.Nested.runN (indexModelTerm assign p childRef body) mEnv H =
      .done
        (Hb.set rA { o with fields := (o.fields.setIfInBounds i (.scalar 0)).set! i (.ref childRef) })
        ((((mEnv.set (assign p.parent) (.ref rA)).set (assign p.child) (.ref childRef)).set
          (assign p.recursive) (.ref childRef)).set (assign p.restored) (.ref rA))
        (.ref rA) wsb := by
    simp [indexModelTerm, Ownership.Nested.runN, hl.array, hl.index, hl.value, hl.parent,
      hl.child, hl.path, hl.recursive, hl.restored, harrM, hindexM, hvalM, hpathM,
      hcell, hslot, hchildEx, hiso, hrunb', hcellHb, Ownership.Env.set,
      Ownership.Nested.addWrites, List.append_nil]
  have hmodelOut : NestedOutcome.ofModel
      (Ownership.Nested.runN (indexModelTerm assign p childRef body) mEnv H) =
      { heap := Hb.set rA { o with fields := (o.fields.setIfInBounds i (.scalar 0)).set! i (.ref childRef) }
        result := some (.ref rA), fault := none, writes := wsb } := by
    rw [hmodelRun]
    rfl
  -- the execution, reduced
  have hexecOut : NestedOutcome.ofExec assign p (execNested assign body p.fragment s) =
      some { heap := Hb.set rA { o with fields := (o.fields.setIfInBounds i (.scalar 0)).set! i (.ref childRef) }
             result := some (.ref rA), fault := none, writes := wsb } := by
    simp [NestedOutcome.ofExec, NestedOutcome.ofMachine, execNested, NestedPrefix.fragment,
      hl.array, hl.index, hl.value, hl.parent, hl.child, hl.path, hl.recursive, hl.restored,
      hl.childArray, hl.sizeResult, hl.bound, hl.arrayCheck, hl.dflt, hl.childCheck,
      hheap, harr, hval, hcallPath, hchildVar, hwrites0, hag.nodes,
      hcell, hex, hslot', hin, hchildEx, hrunb', hcellHb,
      Ownership.Env.set, List.nil_append]
  refine ⟨?_, Hb.set rA { o with fields :=
    (o.fields.setIfInBounds i (.scalar 0)).set! i (.ref childRef) }, _, wsb, hmodelRun, hwsb⟩
  rw [hexecOut, hmodelOut]

/-- `index_prefix_simulates_model`: for a declaration whose `Path.index`
alternative the recognizer accepts, executing the recognized code's own trace
reports the model's outcome. The recognition hypothesis is consumed by
`execNestedAST_recognized`: `execNestedAST` executes the `p.fragment` the walk
emitted for `code`, so nothing is assumed about `code` beyond the recognizer's
verdict. -/
theorem index_prefix_simulates_model
    (declName takeOut : Name) (assign : FVarId → Ownership.Var) (p : NestedPrefix)
    (code : Code .impure) (hproj : projectNested declName takeOut code = some p)
    (hl : NestedLayout assign p) (body : Ownership.Nested.NCode) (s : NestedMachine)
    (mEnv : Ownership.Env) (H : Ownership.Heap) (rA : Ownership.Ref) (o : Ownership.Obj)
    (i v pv : Nat) (childRef : Ownership.Ref)
    (hag : NestedAgrees assign p s mEnv H rA i v pv)
    (hcell : H.cells rA = some o)
    (hex : H.exclusive? rA = true)
    (hslot : o.fields[i]? = some (.ref childRef))
    (hin : i < o.fields.size)
    (hsep : ¬ Ownership.Entry.MutableFootprint (takeOutHeap H rA o i) childRef rA)
    (hchild : ChildContract (takeOutHeap H rA o i)
      (callEnv (assign p.child) (.ref childRef) (assign p.path) (.scalar pv)
        (assign p.value) (.scalar v)) body childRef) :
    NestedOutcome.ofExec assign p (execNestedAST declName takeOut assign body p code s) =
        some (NestedOutcome.ofModel
          (Ownership.Nested.runN (indexModelTerm assign p childRef body) mEnv H)) ∧
      (∃ H' env' ws,
        Ownership.Nested.runN (indexModelTerm assign p childRef body) mEnv H =
          .done H' env' (.ref rA) ws ∧ (∀ w ∈ ws, w.2 = true)) := by
  rw [execNestedAST_recognized declName takeOut assign body p code s hproj]
  exact index_fragment_simulates_model assign p hl body s mEnv H rA o i v pv childRef
    hag hcell hex hslot hin hsep hchild

#print axioms index_fragment_simulates_model
#print axioms index_prefix_simulates_model
#print axioms execNestedAST_recognized

end OwnershipLcnf
