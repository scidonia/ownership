/-
The trusted LCNF-fragment semantics, the AST-execution correspondence, and the
milestone's target theorem.

`Projection.lean` recognizes the pinned `execP` `PTree.set` alternative by
walking the actual `Code .impure` value; the `Prefix` it returns and the
`Prefix.fragment` trace are that walk's own record. This module gives the
recognized node kinds an explicit meaning over `Ownership.Heap`/`Val`/`Env`,
executes the recognized code (`execAST`), and proves that the execution of the
tree the recognizer accepted is the projected model at the designated write's
return — `project_sound`. It then instantiates the concrete entry invariant and
states the milestone's completion result: for a declaration the projection
recognizes, checker acceptance, the entry invariant, and an in-bounds index
imply the designated write is in place at the root address, for arbitrary
supported index and replacement, with a nonzero value-changing corollary.

`Lean.Compiler.LCNF.Code` has no Lean-checked operational semantics, so the
meaning of each primitive is an *assumption* of this module, not a theorem about
the compiler. Nothing below claims that the C backend, the runtime, or an
arbitrary LCNF program behaves this way — only that these primitives, on this
recognized fragment, do.

## Assumptions, premises and contracts

The facts the result rests on are of three different kinds, and the distinction
matters: an axiom inventory alone would not establish runtime correspondence.

**Encoded in the definitions of this module** (a reader can check them by
reading the code, no trust needed):

* the fragment's machine (`Machine`) has exactly three components — the reified
  node fields, the ownership heap and the variable environment — and no
  auxiliary `locals`: every value the fragment reads back is read from `env` at
  the binder the emitted code bound it to;
* `exec`'s rules are the transitions, and the operation trace is the
  recognizer's record of the nodes it matched (`Prefix.fragment`), not a
  separately supplied program;
* the bounds flag is `Bool`-as-scalar (`1`/`0`), the same encoding the model's
  own `LetF.isShared` uses (`Ownership/Code.lean:183-190`).

**Explicit theorem premises** (each named at the theorem that takes it):

* `Layout`: the eight binders whose environment traffic the prefix performs
  occupy the eight distinct slots `0`–`7`. This is the fresh-binder fact emitted
  LCNF supplies; it is what keeps the projection and bounds writes from touching
  a model variable, and it is a premise, not an assumption about the compiler's
  behaviour.
* `Agrees`: the initial-state relation between the machine and the model
  environment — the array binder names the same reference, and the node's
  reified index and replacement are the model's operand scalars. This is the
  relation that replaces the old independently pre-populated model environment:
  the model's operands are the node's own fields, and `exec_fragment_outcome`
  shows the prefix's projection steps write exactly those values.
* the in-bounds premise `i < o.fields.size` for the target cell `o`.

**Named external contracts** (trusted for this milestone, not proved):

* **A1 (node fields).** `oproj[0]`, `oproj[1]` and `sproj[2,0]` of the
  `PTree.set` node read its reified index, continuation and replacement value.
  The constructor layout is not modeled; the caller supplies those fields
  (`NodeFields`) and the recognizer pins which fields the path reads. The
  projection indices themselves (`0`, `1`, `2,0`) are A11's layout contract.
* **A2 (refcount traffic).** `inc`/`dec` on the index, the continuation and the
  destructured node are refcount traffic on values the model heap has no cell
  for. They leave the model's heap and environment untouched. This is the named
  non-claim for the index's own `inc`/`dec` pair, the continuation's handle and
  the destructured node. Treating that traffic as disjoint from the array's cell
  is a **modeling premise**, not an inference from the omission: this fragment
  represents neither the node nor the continuation as a `Ref`, so there is no
  cell for their counts to collide with; a continuation that captured the array
  itself would need a separation argument this milestone does not make.
* **A3 (`Array.size`).** `Array.size a` yields the array cell's length, which is
  what the model's `LetF.size` reads.
* **A4 (`Nat.decLt`).** `Nat.decLt i n` yields the bounds flag: true exactly
  when `i < n`. The recognizer requires the `Bool.true` alternative; whether the
  runtime takes it is a fact about the index and the array's length, not about
  ownership state, so the interpreter records the branch selection as a step
  and fails if the flag is not `1`.
* **A5 (site constant).** The site constant is opaque; the exclusivity check
  ignores it, and the fragment neither writes nor reads it in `env`.
* **A6 (exclusivity check).** `assertExclusiveArrayImpl site a` returns `a` on
  the exclusive branch and faults otherwise, with no heap effect. This is the
  model's `LetF.checkAlias`: the returned handle is the same handle. Both call
  conventions are matched — the plain and the specialized `._redArg` form — as a
  stated alternative (A12).
* **A7 (boxing).** `box v` is ownership-transparent: the boxed temporary
  denotes the same scalar as its source and introduces no reference into the
  mutable footprint. The write's replacement operand is therefore the model's
  `value` variable, and `exec`'s `boxValue` rule is the copy that makes the two
  binders hold that scalar.
* **A8 (array update).** `Array.set! arr i v` on an exclusive array mutates in
  place and returns the array; on a shared array it copies (`Heap.alloc` plus a
  count decrement on the source). This is the model's `Code.setArr`, both
  branches. The emitted result binder receives the returned array, and the model
  records the returned handle by re-binding the checked variable. The model's
  stored count of one is a count in *this* heap; connecting it to physical
  counted references is the separate runtime bridge (A10, `PLAN.md`).
* **A9 (prefix boundary).** The certified prefix ends at the designated write's
  return. The index decrement that follows, the boxing of the bounds result, the
  call of the extracted continuation and the recursive `execP` call are outside
  it, and no theorem below mentions them.
* **A10 (replay identity).** The captured replay is the backend input up to the
  sibling pin and digest recorded in `docs/notes/artifacts/execP.lcnf.txt`;
  relating the replay to what the backend receives is the named trust step of
  the repository's measurement, not a kernel theorem.
* **A11 (constructor layout).** The projection indices the recognizer requires
  (`oproj[0]` index, `oproj[1]` continuation, `sproj[2,0]` replacement) follow
  the `PTree.set` constructor's field layout in the pinned compiler. The
  recognizer rejects any other projection index, so a layout change is a
  rejection, not a silent misinterpretation.
* **A12 (call signatures).** The primitive arities the recognizer checks
  (`Array.size` with its type argument and array, `Nat.decLt` with two scalars,
  the exclusivity check with site and array, `Array.set!` with its type
  argument, array, index and boxed value) are the specialized forms the pinned
  compiler emits for this declaration.
-/
import OwnershipLcnf.Projection
import Ownership.Entry

namespace OwnershipLcnf

open Lean
open Lean.Compiler.LCNF

/-! ## The fragment's machine -/

/-- A reified `PTree.set` field: the scalar value the caller's state fixes for it,
or `unknown` when it fixes none. -/
inductive Field where
  | unknown
  | scalar (n : Nat)
  deriving DecidableEq, Repr

/-- The reified `PTree.set` fields the pre-bounds path destructures (A1). -/
structure NodeFields where
  index : Field := .unknown
  value : Field := .unknown
  continuation : Field := .unknown
  deriving Inhabited, Repr

/-- The fragment's machine state: the reified node fields, the ownership heap and
the variable environment the emitted binders name. There are no auxiliary
`locals`: every operand the fragment reads was written into `env` at the binder
the emitted code bound it to. -/
structure Machine where
  nodes : FVarId → NodeFields
  heap : Ownership.Heap
  env : Ownership.Env

/-- The machine after the exclusivity check returned its argument (A6). -/
def afterCheck (assign : FVarId → Ownership.Var) (dst : FVarId) (r : Ownership.Ref)
    (s : Machine) : Machine :=
  { s with env := s.env.set (assign dst) (.ref r) }

/-- The machine after `Array.set!` took the mutate branch (A8): the checked
handle and the emitted result binder both name the array, which is the same
reference. -/
def afterMutate (assign : FVarId → Ownership.Var) (dst arr : FVarId) (r : Ownership.Ref)
    (i v : Nat) (o : Ownership.Obj) (s : Machine) : Machine :=
  { s with
    heap := s.heap.set r { o with fields := o.fields.set! i (.scalar v) }
    env := (s.env.set (assign arr) (.ref r)).set (assign dst) (.ref r) }

/-- The machine after `Array.set!` took the copy branch (A8): a fresh cell with
the replaced fields, and a count decrement on the source. `exec` gives the
primitive its full meaning, so this rule exists; within the recognized prefix it
is not reached, because the exclusivity check that precedes the write faults on a
shared array first. -/
def afterCopy (assign : FVarId → Ownership.Var) (dst arr : FVarId) (r : Ownership.Ref)
    (i v : Nat) (o : Ownership.Obj) (s : Machine) : Machine :=
  let (r', H1) := s.heap.alloc (o.fields.set! i (.scalar v))
  { s with
    heap := H1.dec r 1
    env := (s.env.set (assign arr) (.ref r')).set (assign dst) (.ref r') }

/-- Execute the recognized operation trace. Each rule is the primitive's assumed
meaning; the ownership-relevant rules (A6, A8) are the model's own transitions.
The index and replacement rules (A1) *write* the operands into `env` from the
node's reified fields, so the write's operands are the projections' results and
not a pre-populated state. A `none` result means the fragment left the
recognized alternative: the bounds flag is not `1`, so the emitted code would
take the `Bool.false` branch, whose continuation is the named non-claim A9 — or
an operand is not the scalar the recognized path produces. -/
def exec (assign : FVarId → Ownership.Var) : List Op → Machine →
    Machine × Option Ownership.Res
  | [], s => (s, some (.done s.heap s.env .erased []))
  | .projIndex dst node :: rest, s =>                       -- A1
      match (s.nodes node).index with
      | .scalar i => exec assign rest { s with env := s.env.set (assign dst) (.scalar i) }
      | .unknown => (s, none)
  | .projValue dst node :: rest, s =>                       -- A1
      match (s.nodes node).value with
      | .scalar v => exec assign rest { s with env := s.env.set (assign dst) (.scalar v) }
      | .unknown => (s, none)
  | .projCont _ _ :: rest, s => exec assign rest s          -- A1, A2 (non-claim)
  | .incIndex _ _ :: rest, s => exec assign rest s          -- A2
  | .incCont _ _ :: rest, s => exec assign rest s           -- A2
  | .decNode _ _ _ :: rest, s => exec assign rest s         -- A2
  | .arraySize dst arr :: rest, s =>                        -- A3
      match s.env (assign arr) with
      | some (.ref r) =>
          match s.heap.cells r with
          | some o =>
              exec assign rest { s with env := s.env.set (assign dst) (.scalar o.fields.size) }
          | none => (s, none)
      | _ => (s, none)
  | .decLt dst idx size :: rest, s =>                       -- A4
      match s.env (assign idx), s.env (assign size) with
      | some (.scalar i), some (.scalar n) =>
          exec assign rest
            { s with env := s.env.set (assign dst) (.scalar (if i < n then 1 else 0)) }
      | _, _ => (s, none)
  | .siteConst _ :: rest, s => exec assign rest s           -- A5
  | .boundsTrue discr :: rest, s =>                         -- A4
      match s.env (assign discr) with
      | some (.scalar 1) => exec assign rest s
      | _ => (s, none)
  | .checkExclusive dst _ arr :: rest, s =>                 -- A6
      match s.env (assign arr) with
      | some (.ref r) =>
          if s.heap.exclusive? r then exec assign rest (afterCheck assign dst r s)
          else (s, some (.fault s.heap s.env (.notExclusive r) []))
      | _ => (s, some (.fault s.heap s.env (.badVar (assign arr)) []))
  | .boxValue dst src :: rest, s =>                         -- A7
      match s.env (assign src) with
      | some v => exec assign rest { s with env := s.env.set (assign dst) v }
      | none => (s, none)
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

/-! ## Executing the recognized AST -/

/-- Execute the recognized prefix of an actual LCNF code value. `projectPrefix`
walks `code`, and the result is returned only when the prefix it decoded is the
expected `p` (by binder identity); a code value that does not decode to `p` is
not executed at all. This is what makes the recognition hypothesis of the
theorems load-bearing: without it, nothing is known about `code`, and `execAST`
may return `none`. The executed operations are the trace the walk emitted for
`code`. -/
def execAST (assign : FVarId → Ownership.Var) (p : Prefix) (code : Code .impure)
    (s : Machine) : Option (Machine × Option Ownership.Res) :=
  match projectPrefix code with
  | none => none
  | some p' =>
      if p'.binderNames = p.binderNames then some (exec assign p'.fragment s) else none

/-- The recognition hypothesis is consumed: for a code value the projection
decodes to `p`, `execAST` executes that code's own trace. Nothing here is
assumed about `code` beyond the recognition result. -/
theorem execAST_recognized (assign : FVarId → Ownership.Var) (p : Prefix)
    (code : Code .impure) (s : Machine) (hproj : projectPrefix code = some p) :
    execAST assign p code s = some (exec assign p.fragment s) := by
  simp [execAST, hproj]

/-! ## The observation boundary -/

/-- The last write a trace records, which `addWrite` prepends: the designated
write. -/
def designatedWrite (ws : List Ownership.Write) : Option Ownership.Write :=
  ws.head?

/-- The observation boundary of the certified prefix: the heap the prefix leaves,
the two local binders the emitted code reads back after the write — the
`Array.set!` result binder and the checked handle the return step observes —
plus the designated write's target, disposition, fault status and trace. The
subsequent index decrement, continuation call and recursive `execP` call are
outside this observation (A9): the outcome records nothing about them. -/
structure PrefixOutcome where
  /-- The ownership heap at the boundary. -/
  heap : Ownership.Heap
  /-- The `Array.set!` result binder's value. -/
  setResult : Option Ownership.Val
  /-- The checked handle the prefix's return step observes. -/
  result : Option Ownership.Val
  /-- The designated write's target reference, if a write was recorded. -/
  target : Option Ownership.Ref
  /-- Whether the designated write was in place. -/
  inPlace : Bool
  /-- The ownership fault, when the outcome is a fault. -/
  fault : Option Ownership.Fault
  /-- The write trace at the boundary. -/
  writes : List Ownership.Write

/-- The prefix outcome read from the executed machine and the interpreter's
result. On a completed prefix the two local binders are read back from the
machine's own environment, not taken from an opaque completion value; on a fault
they are absent, because the prefix never reached the binders. -/
def PrefixOutcome.ofMachine (assign : FVarId → Ownership.Var) (p : Prefix)
    (M : Machine) : Ownership.Res → PrefixOutcome
  | .done _ _ _ ws =>
      { heap := M.heap
        setResult := M.env (assign p.setResult)
        result := M.env (assign p.checkResult)
        target := (designatedWrite ws).map (·.1)
        inPlace := ((designatedWrite ws).map (·.2)).getD false
        fault := none
        writes := ws }
  | .fault _ _ f ws =>
      { heap := M.heap
        setResult := none
        result := none
        target := none
        inPlace := false
        fault := some f
        writes := ws }

/-- The prefix outcome the ownership model's run reports. The model has no
`Array.set!` result binder of its own, so its returned handle stands for both
the write's result and the checked handle — which is the claim being proved on
the in-place path, not an assumption. -/
def PrefixOutcome.ofModel : Ownership.Res → PrefixOutcome
  | .done H _ v ws =>
      { heap := H
        setResult := some v
        result := some v
        target := (designatedWrite ws).map (·.1)
        inPlace := ((designatedWrite ws).map (·.2)).getD false
        fault := none
        writes := ws }
  | .fault H _ f ws =>
      { heap := H
        setResult := none
        result := none
        target := none
        inPlace := false
        fault := some f
        writes := ws }

/-- The prefix outcome the expected in-place write reports: the mutated heap, the
checked handle at both binders, and the single exclusive write at `root`. -/
def inPlaceOutcome (root : Ownership.Ref) (i v : Nat) (o : Ownership.Obj)
    (H : Ownership.Heap) : PrefixOutcome :=
  { heap := H.set root { o with fields := o.fields.set! i (.scalar v) }
    setResult := some (.ref root)
    result := some (.ref root)
    target := some root
    inPlace := true
    fault := none
    writes := [(root, true)] }

/-- The prefix outcome an `execAST` result reports, when the execution produced a
result at all. -/
def PrefixOutcome.ofExec (assign : FVarId → Ownership.Var) (p : Prefix)
    (out : Option (Machine × Option Ownership.Res)) : Option PrefixOutcome :=
  match out with
  | some (M, some r) => some (PrefixOutcome.ofMachine assign p M r)
  | _ => none

/-! ## The variable layout and the initial-state relation -/

/-- The variable layout the fragment and the projected model share: the eight
binders whose environment traffic the prefix performs occupy the eight distinct
slots `0`–`7`. Slots `0`–`3` are the projected model's variables (array, index,
replacement, check result); `4`–`7` are the projection, bounds and write results
the model has no variable for. Which binder takes which slot is the caller's
choice (`assignOf`); that the slots are distinct is the fresh-binder fact the
emitted LCNF supplies, and it is what keeps the auxiliary writes from touching a
model variable. -/
structure Layout (assign : FVarId → Ownership.Var) (p : Prefix) : Prop where
  array : assign p.array = 0
  index : assign p.index = 1
  value : assign p.value = 2
  check : assign p.checkResult = 3
  sizeResult : assign p.sizeResult = 4
  bound : assign p.bound = 5
  boxedValue : assign p.boxedValue = 6
  setResult : assign p.setResult = 7

/-- The canonical layout: the array, index, replacement and check result take the
projected model's variables, and the auxiliary binders take four further slots.
That this is a `Layout` for a concrete recognized prefix is checked where the
prefix is concrete (`scripts/check_projection.lean`). -/
def assignOf (p : Prefix) (arrayVar indexVar valueVar checkVar : Ownership.Var) :
    FVarId → Ownership.Var :=
  fun f =>
    if f.name = p.array.name then arrayVar
    else if f.name = p.index.name then indexVar
    else if f.name = p.value.name then valueVar
    else if f.name = p.checkResult.name then checkVar
    else if f.name = p.sizeResult.name then 4
    else if f.name = p.bound.name then 5
    else if f.name = p.boxedValue.name then 6
    else if f.name = p.setResult.name then 7
    else 0

/-- The initial-state agreement between the machine the AST prefix executes from
and the model environment: the machine's array slot and the model's root
variable name the same reference, the model's operand variables are the node's
reified index and replacement, and the machine's heap is the model's. This is
the relation that replaces an independently pre-populated model environment; the
theorems below use it as one hypothesis. -/
structure Agrees (assign : FVarId → Ownership.Var) (p : Prefix) (s : Machine)
    (env : Ownership.Env) (H : Ownership.Heap) (r : Ownership.Ref) (i v : Nat) : Prop where
  heap : s.heap = H
  array_machine : s.env (assign p.array) = some (.ref r)
  array_model : env 0 = some (.ref r)
  index_model : env 1 = some (.scalar i)
  value_model : env 2 = some (.scalar v)
  nodes : s.nodes p.node = ⟨.scalar i, .scalar v, .unknown⟩

/-- Under the variable layout, the projected model is the runner's measured
write prefix. -/
theorem toModel_eq_execSet (assign : FVarId → Ownership.Var) (p : Prefix)
    (hl : Layout assign p) :
    p.toModel assign = Ownership.Runner.execSet 0 3 1 2 := by
  simp [Prefix.toModel, Ownership.Runner.execSet, hl.array, hl.index, hl.value,
    hl.check]

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

/-! ## The executed prefix's outcome -/

/-- Executing the recognized trace from a machine whose node fields hold `(i, v)`,
whose array slot holds `r`, whose heap holds the array at `r`, and whose bounds
flag is in bounds, writes in place at `r` and leaves the checked handle at both
the write's result binder and the returned handle.

The operand derivation is visible in the statement: nothing supplies the index
or the replacement to the machine's environment up front — `exec`'s `projIndex`
and `projValue` rules read them from `s.nodes p.node`, the box rule copies the
replacement to the emitted boxed-value binder, and the write reads those
binders. -/
theorem exec_fragment_outcome (assign : FVarId → Ownership.Var) (p : Prefix)
    (hl : Layout assign p) (s : Machine) (r : Ownership.Ref) (i v : Nat) (o : Ownership.Obj)
    (hnodes : s.nodes p.node = ⟨.scalar i, .scalar v, .unknown⟩)
    (harr : s.env (assign p.array) = some (.ref r))
    (hcell : s.heap.cells r = some o)
    (hex : s.heap.exclusive? r = true)
    (hin : i < o.fields.size) :
    PrefixOutcome.ofExec assign p (some (exec assign p.fragment s)) =
      some (inPlaceOutcome r i v o s.heap) := by
  have harr0 : s.env 0 = some (.ref r) := by
    rw [← hl.array]; exact harr
  simp [PrefixOutcome.ofExec, Prefix.fragment, exec, afterCheck, afterMutate,
    PrefixOutcome.ofMachine, inPlaceOutcome, designatedWrite,
    hl.array, hl.index, hl.value, hl.check, hl.sizeResult, hl.bound,
    hl.boxedValue, hl.setResult, hnodes, harr0, hcell, hex, hin,
    Ownership.Res.addWrite, List.head?]

/-- The recognized prefix simulates the ownership model: from the initial-state
agreement, the executed prefix and the model's own run report the same prefix
outcome — heap, the write's result binder, the returned handle, the target, the
write disposition, the fault status and the trace.

The case split is over the exclusivity check's verdict, which is where this
prefix's two dispositions are decided, on both sides at once: an exclusive array
takes the in-place write and reports the root at both binders; a shared array
faults at the check (`notExclusive`) with an empty trace, so the model's copy
branch — reachable in `Ownership.Code.setArr` for other programs — is not reached
through this prefix. `exec`'s own copy rule still gives `Array.set!` its full
meaning; the preceding check is what makes it unreachable here.

The model environment's operands are the node's fields by `hag` (`index_model`,
`value_model`); the fragment's are the same values because its projection and box
rules wrote them (`exec_fragment_outcome`). -/
theorem prefix_simulates_model (assign : FVarId → Ownership.Var) (p : Prefix)
    (hl : Layout assign p) (s : Machine) (env : Ownership.Env) (H : Ownership.Heap)
    (r : Ownership.Ref) (i v : Nat) (o : Ownership.Obj)
    (hag : Agrees assign p s env H r i v)
    (hcell : H.cells r = some o)
    (hin : i < o.fields.size) :
    PrefixOutcome.ofExec assign p (some (exec assign p.fragment s)) =
      some (PrefixOutcome.ofModel (Ownership.run (p.toModel assign) env H)) := by
  have hH : H = s.heap := hag.heap.symm
  subst hH
  have harr0 : s.env 0 = some (.ref r) := by
    rw [← hl.array]; exact hag.array_machine
  rw [toModel_eq_execSet assign p hl]
  cases hex : s.heap.exclusive? r with
  | true =>
      rw [exec_fragment_outcome assign p hl s r i v o hag.nodes hag.array_machine hcell hex hin,
        execSet_run_of hag.array_model hag.index_model hag.value_model hcell hex]
      rfl
  | false =>
      simp [PrefixOutcome.ofExec, Prefix.fragment, exec, PrefixOutcome.ofMachine,
        PrefixOutcome.ofModel, Ownership.Runner.execSet, Ownership.run,
        Ownership.Env.set, hl.array, hl.index, hl.value, hl.sizeResult, hl.bound,
        hag.nodes, hag.array_model, harr0, hcell, hex, hin]

/-- `project_sound`: for a declaration the projection recognizes, executing the
recognized code's own trace — not a separately supplied program — reports the
model's outcome at the designated write's return.

`hproj` is consumed: `execAST_recognized` is the only way to know what
`execAST assign p code s` does, and it exists only because the recognizer accepts
`code`.

The two named non-claims of the certified prefix are stated here: the index's
own `inc`/`dec` pair (scalar bookkeeping outside the array's mutable footprint,
A2) and the continuation with its boxed bounds result and recursive call (A9)
are not part of the fragment, and the prefix stops at the designated write's
return. -/
theorem project_sound (assign : FVarId → Ownership.Var) (p : Prefix)
    (code : Code .impure) (hproj : projectPrefix code = some p)
    (hl : Layout assign p) (s : Machine) (env : Ownership.Env) (H : Ownership.Heap)
    (r : Ownership.Ref) (i v : Nat) (o : Ownership.Obj)
    (hag : Agrees assign p s env H r i v)
    (hcell : H.cells r = some o)
    (hin : i < o.fields.size) :
    PrefixOutcome.ofExec assign p (execAST assign p code s) =
      some (PrefixOutcome.ofModel (Ownership.run (p.toModel assign) env H)) := by
  rw [execAST_recognized assign p code s hproj]
  exact prefix_simulates_model assign p hl s env H r i v o hag hcell hin

/-! ## The model side -/

/-- The checker accepts the projected model from the concrete entry context,
with the array bound to the owned root. -/
theorem projected_check (assign : FVarId → Ownership.Var) (p : Prefix)
    (hl : Layout assign p) (r : Ownership.Ref) :
    Ownership.check (Ownership.Runner.initCtx r) (p.toModel assign) =
      some ((Ownership.Runner.initCtx r).move 0 3) := by
  rw [toModel_eq_execSet assign p hl]
  exact Ownership.Runner.execSet_check r

/-- The model environment with a client's operands: the initializer's
environment, with the index and replacement variables bound to `i` and `v`. This
is how the model is supplied its operands; `Agrees` is what ties those values to
the node's reified fields, so the supply is not independent of the AST. -/
def operandEnv (root : Ownership.Ref) (i v : Nat) : Ownership.Env :=
  (Ownership.Runner.initEnv root).set 1 (.scalar i) |>.set 2 (.scalar v)

theorem operandEnv_zero (root : Ownership.Ref) (i v : Nat) :
    operandEnv root i v 0 = some (.ref root) := by
  simp [operandEnv, Ownership.Runner.initEnv]

theorem operandEnv_one (root : Ownership.Ref) (i v : Nat) :
    operandEnv root i v 1 = some (.scalar i) := by
  simp [operandEnv]

theorem operandEnv_two (root : Ownership.Ref) (i v : Nat) :
    operandEnv root i v 2 = some (.scalar v) := by
  simp [operandEnv]

/-- The entry invariant survives replacing the model's two scalar operands: the
initializer's context declares variables `1` and `2` as scalars, so substituting
other scalars there leaves the handle/count invariant and the footprint facts
unchanged. This is what lets the general result be instantiated at a client's
arbitrary index and replacement, not only at the initializer's zeros. -/
theorem operandEnv_inv (n i v : Nat) :
    Ownership.Inv (Ownership.Runner.initHeap n).2
      (operandEnv (Ownership.Runner.initHeap n).1 i v)
      (Ownership.Runner.initCtx (Ownership.Runner.initHeap n).1) := by
  have hbase := Ownership.Runner.initInv n
  have hfst : (Ownership.Runner.initHeap n).1 = 0 := rfl
  refine ⟨hbase.rc_eq, ?_, ?_, ?_, hbase.nonPersistent⟩
  · intro x r hx hr
    by_cases hx0 : x = 0
    · subst hx0
      have hr' : (Ownership.Runner.initHeap n).1 = r := by
        simpa [Ownership.Runner.initCtx] using hr
      have hr0 : r = 0 := by rw [← hr', hfst]
      subst hr0
      constructor
      · simp [operandEnv, Ownership.Runner.initEnv, hfst]
      · simp [Ownership.Runner.initCtx, hfst]
    · by_cases hx1 : x = 1
      · simp [Ownership.Runner.initCtx, hx1] at hx
      · by_cases hx2 : x = 2
        · simp [Ownership.Runner.initCtx, hx2] at hx
        · simp [Ownership.Runner.initCtx, hx0, hx1, hx2] at hx
  · intro x r hx hr
    by_cases hx0 : x = 0
    · subst hx0; simp [Ownership.Runner.initCtx] at hx
    · by_cases hx1 : x = 1
      · subst hx1; simp [Ownership.Runner.initCtx] at hx
      · by_cases hx2 : x = 2
        · subst hx2; simp [Ownership.Runner.initCtx] at hx
        · simp [Ownership.Runner.initCtx, hx0, hx1, hx2] at hx
  · intro x hx
    by_cases hx0 : x = 0
    · subst hx0; simp [Ownership.Runner.initCtx] at hx
    · by_cases hx1 : x = 1
      · subst hx1
        exact ⟨i, by simp [operandEnv]⟩
      · by_cases hx2 : x = 2
        · subst hx2
          exact ⟨v, by simp [operandEnv]⟩
        · simp [Ownership.Runner.initCtx, hx0, hx1, hx2] at hx

/-- The concrete entry condition at the client's operands: the initializer's
heap, context and footprint facts, with the two scalar variables bound to the
client's index and replacement. -/
theorem operandEnv_entryInv (n i v : Nat) :
    Ownership.Entry.EntryInv (Ownership.Runner.initHeap n).2
      (operandEnv (Ownership.Runner.initHeap n).1 i v)
      (Ownership.Runner.initCtx (Ownership.Runner.initHeap n).1)
      (Ownership.Runner.initHeap n).1 [] :=
  { toInv := operandEnv_inv n i v
    uniqueTree := (Ownership.Entry.initEntryInv n).uniqueTree
    separated := (Ownership.Entry.initEntryInv n).separated
    complete := (Ownership.Entry.initEntryInv n).complete }

/-- The milestone's target statement at the model level: for a declaration the
projection recognizes, from any state satisfying the concrete entry condition at
the projected variable layout, the checker accepts the projected model, its run
is fault-free, the designated write selects the in-place branch, and the target
address and the returned handle are the root.

The entry condition is what supplies the exclusivity the write needs: with
`multOf 0 = 1` and `rc_eq`, `Inv.exclusive` makes the root's cell exclusive, so
the model takes the mutate branch without copying. `hproj` records that `p` is a
projection of the declaration under consideration; `hl` is the layout fact the
projected variable layout needs. Both are premises here because the statement is
about the model program; `recognized_write_in_place` is the version that also
executes the AST. -/
theorem designated_write_in_place {code : Code .impure} {p : Prefix}
    {assign : FVarId → Ownership.Var} (_hproj : projectPrefix code = some p)
    (hl : Layout assign p)
    {H : Ownership.Heap} {env : Ownership.Env} {root : Ownership.Ref}
    {client : List Ownership.Ref}
    (hEntry : Ownership.Entry.EntryInv H env (Ownership.Runner.initCtx root) root client) :
    Ownership.check (Ownership.Runner.initCtx root) (p.toModel assign) =
        some ((Ownership.Runner.initCtx root).move 0 3) ∧
      (∃ H' env', Ownership.run (p.toModel assign) env H =
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
  refine ⟨projected_check assign p hl root, ?_⟩
  rw [toModel_eq_execSet assign p hl]
  exact ⟨_, _, execSet_run_of h0 h1 h2 hcell hex⟩

/-- The target result at the initializer: `Entry.initEntryInv` supplies the entry
condition, and `Runner.initHeap`/`initEnv` are the state it describes. -/
theorem initializer_designated_write_in_place {code : Code .impure} {p : Prefix}
    {assign : FVarId → Ownership.Var} (hproj : projectPrefix code = some p)
    (hl : Layout assign p) (n : Nat) :
    ∃ H' env', Ownership.run (p.toModel assign)
        (Ownership.Runner.initEnv (Ownership.Runner.initHeap n).1)
        (Ownership.Runner.initHeap n).2 =
      .done H' env' (.ref (Ownership.Runner.initHeap n).1)
        [((Ownership.Runner.initHeap n).1, true)] :=
  (designated_write_in_place hproj hl (Ownership.Entry.initEntryInv n)).2

/-! ## The AST-execution target theorem -/

/-- The fragment's starting machine for the concrete scalar-array update: the
array handle at the model's array slot, the node's fields carrying the index and
replacement the caller's client supplies, and nothing else in the environment.
The index and replacement slots are *not* pre-populated: the prefix's own
projection steps write them. -/
def initMachine (assign : FVarId → Ownership.Var) (p : Prefix) (H : Ownership.Heap)
    (root : Ownership.Ref) (i v : Nat) : Machine :=
  { nodes := fun f =>
      if f.name = p.node.name then ⟨.scalar i, .scalar v, .unknown⟩
      else ⟨.unknown, .unknown, .unknown⟩
    heap := H
    env := fun x => if x = assign p.array then some (.ref root) else none }

/-- The observed initial-state relation holds for `initMachine`: its array slot
is the model's root variable, its heap is the model heap, and its node fields
are the model's operands. Nothing pre-populates the index or replacement slots —
the agreement is with the fields the AST's own node node carries. -/
theorem initMachine_agrees (assign : FVarId → Ownership.Var) (p : Prefix)
    (H : Ownership.Heap) (root : Ownership.Ref) (i v : Nat) :
    Agrees assign p (initMachine assign p H root i v) (operandEnv root i v) H root i v := by
  refine ⟨rfl, ?_, operandEnv_zero root i v, operandEnv_one root i v,
    operandEnv_two root i v, ?_⟩
  · simp [initMachine]
  · simp [initMachine]

/-- The milestone's completion statement, over the actual AST: for a declaration
whose replayed `PTree.set` alternative the projection recognizes, from any state
satisfying the concrete entry condition at the projected layout, an in-bounds
index and the node fields the client supplies, executing the *recognized code's
own trace* reports the in-place outcome at the root address — and the model's
run reports the same outcome. Fault-free, no copy, target and returned handle
the root.

The index and replacement are arbitrary supported scalars; the in-bounds premise
is the only thing the bounds check needs. The prefix boundary is `PrefixOutcome`
(A9): the index decrement, the continuation call and the recursive `execP` call
are not part of the outcome. -/
theorem recognized_write_in_place {code : Code .impure} {p : Prefix}
    {assign : FVarId → Ownership.Var} (hproj : projectPrefix code = some p)
    (hl : Layout assign p) (s : Machine) (env : Ownership.Env) (H : Ownership.Heap)
    (root : Ownership.Ref) (client : List Ownership.Ref) (i v : Nat) (o : Ownership.Obj)
    (hEntry : Ownership.Entry.EntryInv H env (Ownership.Runner.initCtx root) root client)
    (hag : Agrees assign p s env H root i v)
    (hcell : H.cells root = some o)
    (hin : i < o.fields.size) :
    PrefixOutcome.ofExec assign p (execAST assign p code s) =
        some (inPlaceOutcome root i v o H) ∧
      PrefixOutcome.ofModel (Ownership.run (p.toModel assign) env H) =
        inPlaceOutcome root i v o H := by
  have hex : H.exclusive? root = true := by
    have hi : Ownership.Inv H env (Ownership.Runner.initCtx root) := hEntry.toInv
    obtain ⟨r, hr, hmul⟩ :=
      Ownership.Ctx.multOf_eq_one (Ownership.Runner.initCtx_multOf_zero root)
    have hrroot : r = root := by
      have h : (Ownership.Runner.initCtx root).refOf 0 = some r := hr
      rw [Ownership.Runner.initCtx_refOf_zero] at h
      exact (Option.some.inj h).symm
    have hmul' : (Ownership.Runner.initCtx root).mult root = 1 := by
      simpa [hrroot] using hmul
    exact (Ownership.Heap.exclusive?_eq_true).mpr (hi.exclusive hmul')
  constructor
  · rw [project_sound assign p code hproj hl s env H root i v o hag hcell hin]
    rw [toModel_eq_execSet assign p hl,
      execSet_run_of hag.array_model hag.index_model hag.value_model hcell hex]
    rfl
  · rw [toModel_eq_execSet assign p hl,
      execSet_run_of hag.array_model hag.index_model hag.value_model hcell hex]
    rfl

/-- The zero-index, zero-replacement initializer case, executed on the AST: the
state `Entry.initEntryInv` describes (its environment read as the client's
operands bound to `0` and `0`), with the node's fields at the same two zeros. -/
theorem initializer_prefix_in_place {code : Code .impure} {p : Prefix}
    {assign : FVarId → Ownership.Var} (hproj : projectPrefix code = some p)
    (hl : Layout assign p) {n : Nat} (hin : 0 < n) :
    PrefixOutcome.ofExec assign p
        (execAST assign p code
          (initMachine assign p (Ownership.Runner.initHeap n).2
            (Ownership.Runner.initHeap n).1 0 0)) =
      some (inPlaceOutcome (Ownership.Runner.initHeap n).1 0 0
        ⟨Array.replicate n (.scalar 0), 1, false⟩ (Ownership.Runner.initHeap n).2) := by
  have hcell : (Ownership.Runner.initHeap n).2.cells (Ownership.Runner.initHeap n).1 =
      some ⟨Array.replicate n (.scalar 0), 1, false⟩ := by
    simp [Ownership.Runner.initHeap]
  have hin' : 0 < (⟨Array.replicate n (.scalar 0), 1, false⟩ : Ownership.Obj).fields.size := by
    simpa using hin
  exact (recognized_write_in_place hproj hl
    (initMachine assign p (Ownership.Runner.initHeap n).2 (Ownership.Runner.initHeap n).1 0 0)
    (operandEnv (Ownership.Runner.initHeap n).1 0 0)
    (Ownership.Runner.initHeap n).2 (Ownership.Runner.initHeap n).1 [] 0 0
    ⟨Array.replicate n (.scalar 0), 1, false⟩
    (operandEnv_entryInv n 0 0) (initMachine_agrees assign p _ _ 0 0) hcell hin').1

/-- The nonzero, value-changing case: index `1`, replacement `7`, on an array of
length at least two. The heap is the initializer's, the model's operand variables
are `1` and `7`, and the node's fields carry the same pair; the executed prefix
writes `7` into slot `1` in place at the root, under entry and primitive
contracts — no copy, target and returned handle the root. -/
theorem nonzero_prefix_in_place {code : Code .impure} {p : Prefix}
    {assign : FVarId → Ownership.Var} (hproj : projectPrefix code = some p)
    (hl : Layout assign p) {n : Nat} (hn : 2 ≤ n) :
    PrefixOutcome.ofExec assign p
        (execAST assign p code
          (initMachine assign p (Ownership.Runner.initHeap n).2
            (Ownership.Runner.initHeap n).1 1 7)) =
      some (inPlaceOutcome (Ownership.Runner.initHeap n).1 1 7
        ⟨Array.replicate n (.scalar 0), 1, false⟩ (Ownership.Runner.initHeap n).2) := by
  have hcell : (Ownership.Runner.initHeap n).2.cells (Ownership.Runner.initHeap n).1 =
      some ⟨Array.replicate n (.scalar 0), 1, false⟩ := by
    simp [Ownership.Runner.initHeap]
  have hsize : (⟨Array.replicate n (.scalar 0), 1, false⟩ : Ownership.Obj).fields.size = n := by
    simp
  have hin' : 1 < (⟨Array.replicate n (.scalar 0), 1, false⟩ : Ownership.Obj).fields.size := by
    omega
  exact (recognized_write_in_place hproj hl
    (initMachine assign p (Ownership.Runner.initHeap n).2 (Ownership.Runner.initHeap n).1 1 7)
    (operandEnv (Ownership.Runner.initHeap n).1 1 7)
    (Ownership.Runner.initHeap n).2 (Ownership.Runner.initHeap n).1 [] 1 7
    ⟨Array.replicate n (.scalar 0), 1, false⟩
    (operandEnv_entryInv n 1 7) (initMachine_agrees assign p _ _ 1 7) hcell hin').1

#print axioms OwnershipLcnf.execAST_recognized
#print axioms OwnershipLcnf.exec_fragment_outcome
#print axioms OwnershipLcnf.prefix_simulates_model
#print axioms OwnershipLcnf.project_sound
#print axioms OwnershipLcnf.toModel_eq_execSet
#print axioms OwnershipLcnf.projected_check
#print axioms OwnershipLcnf.execSet_run_of
#print axioms OwnershipLcnf.designated_write_in_place
#print axioms OwnershipLcnf.initializer_designated_write_in_place
#print axioms OwnershipLcnf.operandEnv_inv
#print axioms OwnershipLcnf.operandEnv_entryInv
#print axioms OwnershipLcnf.initMachine_agrees
#print axioms OwnershipLcnf.recognized_write_in_place
#print axioms OwnershipLcnf.initializer_prefix_in_place
#print axioms OwnershipLcnf.nonzero_prefix_in_place

end OwnershipLcnf
