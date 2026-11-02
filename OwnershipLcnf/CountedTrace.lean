/-
The recognized trace's counted reading.

`OwnershipLcnf/NestedSemantics.lean` interprets the recognizer's 25-operation
trace over the model's heap (`execNested`), where the take-out is a field write,
the two projection increments and the pair decrement are no-ops, and the
restoration is an unconditional `set!`. `Ownership/CountedNested.lean` accounts
for what the captured code does instead: the take-out allocates the temporary
pair, the two projections increment their components, the pair's unique decrement
releases both edges, and the restoration takes a derived branch.

This module reads the trace's counted operations off the recognizer's own
`NestedPrefix.fragment` (`countedOp`, `countedOf_fragment`) and executes them
against the counted heap (`execCounted`). The counted interpreter mirrors
`execNested` clause for clause; only the five operations the counted protocol
performs touch the heap, and every other clause is identical.

## What is related, and where

`HeapCompat` is not a per-step invariant of the counted interpreter. Between the
take-out and the pair's decrement the counted heap carries the pair cell, whose
name is one past the entry cursor, and the two components are at their entry
counts plus one; `execNested`'s corresponding clauses are no-ops. The relation
recomposes only at the pair release (`decPair`), after which the cells coincide
again with the cursor one higher. `execCounted_protocol_boundary` states the
boundary fact that is available: the counted interpreter's heap at the end of the
fragment's counted prefix is `CountedPair.protocol`'s boundary heap.

Nothing here is a runtime or backend claim, and the emitted recursive callee is
not captured: the recursive clause runs the admitted model body, exactly as
`execNested` does.
-/
import OwnershipLcnf.NestedSemantics
import Ownership.CountedNested
import Ownership.PathConsolidation

open Lean.Compiler.LCNF
open Ownership

namespace OwnershipLcnf

/-! ## The counted operations of the recognized trace -/

/-- The trace operations the counted protocol performs: the take-out allocation,
the two projection increments, the pair's release, and the restoration. -/
def countedOp : NestedOp → Bool
  | .takeOut .. => true
  | .incParent .. => true
  | .incChild .. => true
  | .decPair .. => true
  | .setArray .. => true
  | _ => false

/-- The counted block of the recognizer's own trace, in emitted order. -/
theorem countedOf_fragment (p : NestedPrefix) :
    p.fragment.filter countedOp =
      [ .takeOut p.pair p.arrayCheck p.index p.dflt
      , .incParent p.parent
      , .incChild p.child
      , .decPair p.pair
      , .setArray p.restored p.parent p.index p.recursive ] := by
  rfl

/-- The counted interpreter's prefix index at which the pair has been released:
the operations up to and including `.decPair`. -/
def countedPrefix : List NestedOp → List NestedOp :=
  fun ops => (ops.take 19)

/-! ## Executing the recognized trace against the counted heap -/

/-- Execute the recognized operation trace against the counted heap. Every clause
is `execNested`'s except the five the counted protocol performs:

* `.takeOut` runs the captured take-out (`CountedPair.takeOut`): the pair is
  allocated at the heap's fresh name and the selected slot receives the model's
  placeholder;
* `.incParent` / `.incChild` increment the projected component (`Heap.inc`), as
  the emitted projections do;
* `.decPair` runs the restricted decrement on the pair, whose name is the most
  recent allocation, so it is `heap.next - 1` (the fragment allocates nothing
  else);
* `.setArray` runs `PutBack.putBack`, binding the projection's destination to the
  reference the branch returns, and faults like `execNested` when the target cell
  is gone.

A `none` result means the fragment left the recognized path; a fault is reported
where the primitive faults. -/
def execCounted (assign : Lean.FVarId → Ownership.Var) (body : Ownership.Nested.NCode) :
    List NestedOp → NestedMachine → NestedMachine × Option Ownership.Res
  | [], s => (s, some (.done s.heap s.env .erased s.writes))
  | .projArray dst _ :: rest, s =>
      execCounted assign body rest { s with env := s.env.set (assign dst) .erased }
  | .incArray _ _ :: rest, s => execCounted assign body rest s
  | .projIndex dst node :: rest, s =>
      match (s.nodes node).index with
      | .scalar i => execCounted assign body rest { s with env := s.env.set (assign dst) (.scalar i) }
      | .unknown => (s, none)
  | .incIndex _ _ :: rest, s => execCounted assign body rest s
  | .projPath dst _ :: rest, s =>
      execCounted assign body rest { s with env := s.env.set (assign dst) (.scalar s.callPath) }
  | .incPath _ _ :: rest, s => execCounted assign body rest s
  | .decNode _ _ :: rest, s => execCounted assign body rest s
  | .arraySize dst arr :: rest, s =>
      match s.env (assign arr) with
      | some (.ref r) =>
          match s.heap.cells r with
          | some o =>
              execCounted assign body rest
                { s with env := s.env.set (assign dst) (.scalar o.fields.size) }
          | none => (s, none)
      | _ => (s, none)
  | .decLt dst idx size :: rest, s =>
      match s.env (assign idx), s.env (assign size) with
      | some (.scalar i), some (.scalar n) =>
          execCounted assign body rest
            { s with env := s.env.set (assign dst) (.scalar (if i < n then 1 else 0)) }
      | _, _ => (s, none)
  | .boundsTrue discr :: rest, s =>
      match s.env (assign discr) with
      | some (.scalar 1) => execCounted assign body rest s
      | _ => (s, none)
  | .siteConst _ _ :: rest, s => execCounted assign body rest s
  | .checkArray dst _ arr :: rest, s =>
      match s.env (assign arr) with
      | some (.ref r) =>
          if s.heap.exclusive? r then
            execCounted assign body rest { s with env := s.env.set (assign dst) (.ref r) }
          else (s, some (.fault s.heap s.env (.notExclusive r) s.writes))
      | _ => (s, some (.fault s.heap s.env (.badVar (assign arr)) s.writes))
  | .stateDefault dst arr :: rest, s =>
      match s.env (assign arr) with
      | some _ => execCounted assign body rest { s with env := s.env.set (assign dst) (.scalar 0) }
      | none => (s, none)
  | .takeOut dst check idx dflt :: rest, s =>
      match s.env (assign check), s.env (assign idx), s.env (assign dflt) with
      | some (.ref r), some (.scalar i), some (.scalar _) =>
          match s.heap.cells r with
          | some o =>
              match o.fields[i]? with
              | some (.ref e) =>
                  execCounted assign body rest
                    { s with
                      heap := (CountedPair.takeOut s.heap r e i).2
                      pairs := setPair s.pairs dst.name (.ref r, .ref e) }
              | _ => (s, none)
          | none => (s, some (.fault s.heap s.env (.noCell r) s.writes))
      | _, _, _ => (s, none)
  | .projParent dst pair :: rest, s =>
      match s.pairs pair.name with
      | some (a, _) => execCounted assign body rest { s with env := s.env.set (assign dst) a }
      | none => (s, none)
  | .incParent x :: rest, s =>
      match s.env (assign x) with
      | some (.ref q) => execCounted assign body rest { s with heap := s.heap.inc q 1 }
      | _ => (s, none)
  | .projChild dst pair :: rest, s =>
      match s.pairs pair.name with
      | some (_, b) => execCounted assign body rest { s with env := s.env.set (assign dst) b }
      | none => (s, none)
  | .incChild x :: rest, s =>
      match s.env (assign x) with
      | some (.ref q) => execCounted assign body rest { s with heap := s.heap.inc q 1 }
      | _ => (s, none)
  /- The pair's name is the cursor the counted block started with: the prefix
  allocates exactly once (`.takeOut`), every other counted operation rewrites a
  cell or a count rather than a name, and the child body runs only after this
  release, so `heap.next - 1` is the pair's own name here. -/
  | .decPair _ :: rest, s =>
      execCounted assign body rest { s with heap := CountedPair.decRef s.heap (s.heap.next - 1) }
  | .checkChild dst _ child :: rest, s =>
      match s.env (assign child) with
      | some (.ref r) =>
          if s.heap.exclusive? r then
            execCounted assign body rest { s with env := s.env.set (assign dst) (.ref r) }
          else (s, some (.fault s.heap s.env (.notExclusive r) s.writes))
      | _ => (s, some (.fault s.heap s.env (.badVar (assign child)) s.writes))
  | .recurse dst path value child :: rest, s =>
      match s.env (assign child), s.env (assign path), s.env (assign value) with
      | some (.ref r), some (.scalar pv), some (.scalar v) =>
          match Ownership.Nested.runN body
              (callEnv s.childVar (.ref r) (assign path) (.scalar pv) (assign value) (.scalar v))
              s.heap with
          | .done H' _ _ ws =>
              execCounted assign body rest
                { s with heap := H', env := s.env.set (assign dst) (.ref r), writes := s.writes ++ ws }
          | .fault H' _ f ws => (s, some (.fault H' s.env f (s.writes ++ ws)))
      | _, _, _ => (s, none)
  | .setArray dst arr idx val :: rest, s =>
      match s.env (assign arr), s.env (assign idx), s.env (assign val) with
      | some (.ref r), some (.scalar i), some (.ref e) =>
          match PutBack.putBack s.heap r i e with
          | some (rr, H') =>
              execCounted assign body rest
                { s with heap := H', env := s.env.set (assign dst) (.ref rr) }
          | none => (s, some (.fault s.heap s.env (.noCell r) s.writes))
      | _, _, _ => (s, none)
  | .decIndex _ :: rest, s => execCounted assign body rest s
  | .retVar x :: _, s =>
      (s, some (.done s.heap s.env (s.env (assign x) |>.getD .erased) s.writes))

end OwnershipLcnf

namespace OwnershipLcnf

/-! ## Relating the trace to the model's nested correspondence -/

/-- The child-call contract's one accounting-dependent field: at an accounted
state a count-one owned handle's reference is exclusive, so the child
assertion's precondition is derived rather than assumed. The run, its exclusive
writes and its confinement stay the body's share, exactly as
`OwnershipLcnf.ChildContract` states them. -/
theorem childContract_of_accounted {support : List Ownership.Var} {H : Ownership.Heap}
    {envA : Ownership.Env} {cA : Ownership.Ctx}
    (hacc : Ownership.Accounted support H envA cA) {x : Ownership.Var} {r : Ownership.Ref}
    (hx : cA.us x = .owned) (hr : cA.refOf x = some r) (hm : cA.mult r = 1)
    {cenv : Ownership.Env} {body : Ownership.Nested.NCode}
    {H' : Ownership.Heap} {envb : Ownership.Env} {ws : List Ownership.Write}
    (hout : Ownership.Nested.runN body cenv H = .done H' envb (.ref r) ws)
    (hws : ∀ w ∈ ws, w.2 = true)
    (hconf : ∀ q, ¬ Ownership.Entry.MutableFootprint H r q → H'.cells q = H.cells q) :
    ChildContract H cenv body r :=
  ⟨Ownership.exclusive?_of_accounted hacc hx hr hm, ⟨H', envb, ws, hout, hws, hconf⟩⟩

/-- The nested correspondence with the array assertion's exclusivity and the
child assertion's exclusivity derived from accounting. The remaining premises are
the recognizer's own: the layout, the initial-state agreement, the parent cell and
slot, the bounds, the separation, and the child body's run, trace and
confinement. The original `index_fragment_simulates_model` stays unchanged. -/
theorem index_fragment_simulates_model_of_accounted
    (assign : Lean.FVarId → Ownership.Var) (p : NestedPrefix) (hl : NestedLayout assign p)
    (body : Ownership.Nested.NCode) (s : NestedMachine) (mEnv : Ownership.Env)
    (H : Ownership.Heap) (rA : Ownership.Ref) (o : Ownership.Obj) (i v pv : Nat)
    (childRef : Ownership.Ref)
    (hag : NestedAgrees assign p s mEnv H rA i v pv)
    (hcell : H.cells rA = some o)
    {supportA : List Ownership.Var} {envA : Ownership.Env} {cA : Ownership.Ctx}
    (haccA : Ownership.Accounted supportA H envA cA)
    {xA : Ownership.Var} (hxA : cA.us xA = .owned) (hrA : cA.refOf xA = some rA)
    (hmA : cA.mult rA = 1)
    (hslot : o.fields[i]? = some (.ref childRef))
    (hin : i < o.fields.size)
    (hsep : ¬ Ownership.Entry.MutableFootprint (takeOutHeap H rA o i) childRef rA)
    {supportB : List Ownership.Var} {envB : Ownership.Env} {cB : Ownership.Ctx}
    (haccB : Ownership.Accounted supportB (takeOutHeap H rA o i) envB cB)
    {xB : Ownership.Var} (hxB : cB.us xB = .owned) (hrB : cB.refOf xB = some childRef)
    (hmB : cB.mult childRef = 1)
    {H' : Ownership.Heap} {envb : Ownership.Env} {ws : List Ownership.Write}
    (hout : Ownership.Nested.runN body
      (callEnv (assign p.child) (.ref childRef) (assign p.path) (.scalar pv)
        (assign p.value) (.scalar v)) (takeOutHeap H rA o i) =
      .done H' envb (.ref childRef) ws)
    (hws : ∀ w ∈ ws, w.2 = true)
    (hconf : ∀ q, ¬ Ownership.Entry.MutableFootprint (takeOutHeap H rA o i) childRef q →
      H'.cells q = (takeOutHeap H rA o i).cells q) :
    NestedOutcome.ofExec assign p (execNested assign body p.fragment s) =
        some (NestedOutcome.ofModel
          (Ownership.Nested.runN (indexModelTerm assign p childRef body) mEnv H)) ∧
      (∃ H' env' ws,
        Ownership.Nested.runN (indexModelTerm assign p childRef body) mEnv H =
          .done H' env' (.ref rA) ws ∧ (∀ w ∈ ws, w.2 = true)) :=
  index_fragment_simulates_model assign p hl body s mEnv H rA o i v pv childRef hag hcell
    (Ownership.exclusive?_of_accounted haccA hxA hrA hmA) hslot hin hsep
    (childContract_of_accounted haccB hxB hrB hmB hout hws hconf)

/-- The same derivation through the recognizer: for a declaration whose
`Path.index` alternative the projection accepts, the array and child
exclusivity premises are both read off accounting. -/
theorem index_prefix_simulates_model_of_accounted
    (declName takeOut : Lean.Name) (assign : Lean.FVarId → Ownership.Var) (p : NestedPrefix)
    (code : Lean.Compiler.LCNF.Code .impure) (hproj : projectNested declName takeOut code = some p)
    (hl : NestedLayout assign p) (body : Ownership.Nested.NCode) (s : NestedMachine)
    (mEnv : Ownership.Env) (H : Ownership.Heap) (rA : Ownership.Ref) (o : Ownership.Obj)
    (i v pv : Nat) (childRef : Ownership.Ref)
    (hag : NestedAgrees assign p s mEnv H rA i v pv)
    (hcell : H.cells rA = some o)
    {supportA : List Ownership.Var} {envA : Ownership.Env} {cA : Ownership.Ctx}
    (haccA : Ownership.Accounted supportA H envA cA)
    {xA : Ownership.Var} (hxA : cA.us xA = .owned) (hrA : cA.refOf xA = some rA)
    (hmA : cA.mult rA = 1)
    (hslot : o.fields[i]? = some (.ref childRef))
    (hin : i < o.fields.size)
    (hsep : ¬ Ownership.Entry.MutableFootprint (takeOutHeap H rA o i) childRef rA)
    {supportB : List Ownership.Var} {envB : Ownership.Env} {cB : Ownership.Ctx}
    (haccB : Ownership.Accounted supportB (takeOutHeap H rA o i) envB cB)
    {xB : Ownership.Var} (hxB : cB.us xB = .owned) (hrB : cB.refOf xB = some childRef)
    (hmB : cB.mult childRef = 1)
    {H' : Ownership.Heap} {envb : Ownership.Env} {ws : List Ownership.Write}
    (hout : Ownership.Nested.runN body
      (callEnv (assign p.child) (.ref childRef) (assign p.path) (.scalar pv)
        (assign p.value) (.scalar v)) (takeOutHeap H rA o i) =
      .done H' envb (.ref childRef) ws)
    (hws : ∀ w ∈ ws, w.2 = true)
    (hconf : ∀ q, ¬ Ownership.Entry.MutableFootprint (takeOutHeap H rA o i) childRef q →
      H'.cells q = (takeOutHeap H rA o i).cells q) :
    NestedOutcome.ofExec assign p (execNestedAST declName takeOut assign body p code s) =
        some (NestedOutcome.ofModel
          (Ownership.Nested.runN (indexModelTerm assign p childRef body) mEnv H)) ∧
      (∃ H' env' ws,
        Ownership.Nested.runN (indexModelTerm assign p childRef body) mEnv H =
          .done H' env' (.ref rA) ws ∧ (∀ w ∈ ws, w.2 = true)) :=
  index_prefix_simulates_model declName takeOut assign p code hproj hl body s mEnv H rA o i v
    pv childRef hag hcell (Ownership.exclusive?_of_accounted haccA hxA hrA hmA) hslot hin hsep
    (childContract_of_accounted haccB hxB hrB hmB hout hws hconf)

end OwnershipLcnf

namespace OwnershipLcnf

/-- The counted block as a literal: the first nineteen operations of the
recogniser's trace, through the pair's release. -/
theorem countedPrefix_fragment (p : NestedPrefix) :
    countedPrefix p.fragment =
      [ .projArray p.childArray p.node
      , .incArray p.childArray false
      , .projIndex p.index p.node
      , .incIndex p.index true
      , .projPath p.path p.node
      , .incPath p.path false
      , .decNode p.node 3
      , .arraySize p.sizeResult p.array
      , .decLt p.bound p.index p.sizeResult
      , .boundsTrue p.bound
      , .siteConst p.arraySite 0
      , .checkArray p.arrayCheck p.arraySite p.array
      , .stateDefault p.dflt p.childArray
      , .takeOut p.pair p.arrayCheck p.index p.dflt
      , .projParent p.parent p.pair
      , .incParent p.parent
      , .projChild p.child p.pair
      , .incChild p.child
      , .decPair p.pair ] := rfl

end OwnershipLcnf

namespace OwnershipLcnf

/-- The counted block's boundary: its heap is the protocol boundary, it is
`HeapCompat` to the abstract take-out heap, and the non-heap machine fields agree
with `execNested`'s.

Premise suppliers: `hl` the recogniser's layout (`OwnershipLcnf.NestedLayout`);
`harr`/`hnode` `NestedAgrees.array_machine`/`nodes`; `hcell`/`hcc`/`hslot` the
take-out agreement; `hne` the checker's take-out guard (`Nested.checkNF` refuses
`e = r`), equivalently `PutBack.Boundary.distinct`; `hnext`
`Ownership.Accounted.domain`; `hex` `Ownership.exclusive?_of_accounted`. `hidx` is
derived by `.projIndex` from `hnode`; `rA ≠ s.heap.next` and `childRef ≠
s.heap.next` are derived from `hnext` with `hcell`/`hcc`. The cell comparison
reuses `Ownership.PathConsolidation.protocol_cells`, whose `blankLevel` is this
statement's abstract take-out heap definitionally. -/
theorem execCounted_protocol_boundary (assign : Lean.FVarId → Ownership.Var)
    (p : NestedPrefix) (body : Ownership.Nested.NCode) (s : NestedMachine)
    (rA childRef : Ownership.Ref) (idx : Nat) (o oc : Ownership.Obj)
    (hl : NestedLayout assign p)
    (harr : s.env (assign p.array) = some (.ref rA))
    (hnode : s.nodes p.node = { index := .scalar idx })
    (hcell : s.heap.cells rA = some o)
    (hcc : s.heap.cells childRef = some oc)
    (hslot : o.fields[idx]? = some (.ref childRef))
    (hne : rA ≠ childRef)
    (hnext : s.heap.cells s.heap.next = none)
    (hex : s.heap.exclusive? rA = true) :
    (execCounted assign body (countedPrefix p.fragment) s).1.heap =
        (CountedPair.protocol s.heap rA childRef idx).2
      ∧ HeapCompat (execCounted assign body (countedPrefix p.fragment) s).1.heap
          (s.heap.set rA { o with fields := o.fields.setIfInBounds idx (.scalar 0) })
      ∧ (execCounted assign body (countedPrefix p.fragment) s).1.env
          = (execNested assign body (countedPrefix p.fragment) s).1.env
      ∧ (execCounted assign body (countedPrefix p.fragment) s).1.nodes
          = (execNested assign body (countedPrefix p.fragment) s).1.nodes
      ∧ (execCounted assign body (countedPrefix p.fragment) s).1.pairs
          = (execNested assign body (countedPrefix p.fragment) s).1.pairs
      ∧ (execCounted assign body (countedPrefix p.fragment) s).1.callPath
          = (execNested assign body (countedPrefix p.fragment) s).1.callPath
      ∧ (execCounted assign body (countedPrefix p.fragment) s).1.childVar
          = (execNested assign body (countedPrefix p.fragment) s).1.childVar
      ∧ (execCounted assign body (countedPrefix p.fragment) s).1.writes
          = (execNested assign body (countedPrefix p.fragment) s).1.writes := by
  have hins : idx < o.fields.size := (Array.getElem?_eq_some_iff.mp hslot).1
  have harr0 : s.env 0 = some (.ref rA) := by simpa [hl.array] using harr
  have hslot' : o.fields[idx] = .ref childRef := by
    have h1 : o.fields[idx]? = some o.fields[idx] := by simp [hins]
    have h2 : some o.fields[idx] = some (.ref childRef) := by rw [← h1]; exact hslot
    exact Option.some.inj h2
  have hpn : rA ≠ s.heap.next := by
    intro hh
    rw [hh] at hcell
    rw [hnext] at hcell
    exact absurd hcell (by simp)
  have hcn : childRef ≠ s.heap.next := by
    intro hh
    rw [hh] at hcc
    rw [hnext] at hcc
    exact absurd hcc (by simp)
  let l : Ownership.Path.Level := ⟨rA, o, idx, childRef, 0, 0, 0, 0, 0, 0⟩
  have hblank : ∀ q, (Ownership.Path.blankLevel s.heap l).cells q =
      (s.heap.set rA { o with fields := o.fields.setIfInBounds idx (.scalar 0) }).cells q :=
    fun q => rfl
  have hpairNone : (CountedPair.protocol s.heap rA childRef idx).2.cells s.heap.next = none := by
    obtain ⟨-, -, -, hp, -, -, -, -⟩ :=
      CountedPair.protocol_boundary (H := s.heap) (p := rA) (c := childRef) (i := idx)
        (op := o) (oc := oc) hcell hcc hne hpn hcn
    have : (CountedPair.protocol s.heap rA childRef idx).1 = s.heap.next := rfl
    rw [← this]
    exact hp
  have hcompat : HeapCompat (CountedPair.protocol s.heap rA childRef idx).2
      (s.heap.set rA { o with fields := o.fields.setIfInBounds idx (.scalar 0) }) := by
    refine ⟨fun q => ?_, ?_⟩
    · by_cases hqn : q = s.heap.next
      · rw [hqn, hpairNone, Heap.set_other (H := s.heap) (r := rA) (r' := s.heap.next)
          { o with fields := o.fields.setIfInBounds idx (.scalar 0) } (Ne.symm hpn), hnext]
      · rw [show (CountedPair.protocol s.heap rA childRef idx).2.cells q =
            (Ownership.Path.blankLevel s.heap l).cells q
          from PathConsolidation.protocol_cells (H := s.heap) (l := l) (oc := oc)
            hcell hcc hne hpn hcn q hqn]
        exact hblank q
    · rw [protocol_next hpn hcn, Heap_set_next]
      exact Nat.le_succ s.heap.next
  have hnextChain :
      (((CountedPair.takeOut s.heap rA childRef idx).2.inc rA 1).inc childRef 1).next =
        (CountedPair.takeOut s.heap rA childRef idx).2.next := by
    rw [Heap_inc_next, Heap_inc_next]
  have hstep :
      CountedPair.decRef
        (((CountedPair.takeOut s.heap rA childRef idx).2.inc rA 1).inc childRef 1)
        ((CountedPair.takeOut s.heap rA childRef idx).2.next - 1) =
      CountedPair.pairTraffic (CountedPair.takeOut s.heap rA childRef idx).2 s.heap.next := by
    rw [takeOut_next s.heap rA childRef idx, Nat.succ_sub_one]
    show CountedPair.decRef
        (CountedPair.pairInc (CountedPair.takeOut s.heap rA childRef idx).2 rA childRef)
        s.heap.next =
      CountedPair.pairTraffic (CountedPair.takeOut s.heap rA childRef idx).2 s.heap.next
    rw [← CountedPair.incPairComponents_eq
      (H := (CountedPair.takeOut s.heap rA childRef idx).2)
      (pair := s.heap.next) (p := rA) (c := childRef)
      (o := ⟨CountedPair.pairFields rA childRef, 1, false⟩)
      (CountedPair.takeOut_cells_pair hpn) (by simp [CountedPair.pairFields])
      (by simp [CountedPair.pairFields]) (Ne.symm hpn)]
    rfl
  have hheap : (execCounted assign body (countedPrefix p.fragment) s).1.heap =
      (CountedPair.protocol s.heap rA childRef idx).2 := by
    rw [countedPrefix_fragment p]
    simpa [execCounted, harr0, hnode, hcell, hslot, hslot', hins, hex, hne, hpn,
      CountedPair.takeOut_cells_pair hpn, Ownership.Env.set, List.nil_append, hnextChain, CountedPair.protocol,
      hl.array, hl.index, hl.value, hl.parent, hl.child, hl.path, hl.recursive, hl.restored,
      hl.node, hl.childArray, hl.sizeResult, hl.bound, hl.arraySite, hl.arrayCheck, hl.dflt,
      hl.pair, hl.childSite, hl.childCheck, hl.indexDec, hcc] using hstep
  refine ⟨hheap, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hheap]; exact hcompat
  · rw [countedPrefix_fragment p]
    simp [execCounted, execNested, harr0, hnode, hcell, hslot, hslot', hins, hex, Ownership.Env.set,
      hl.array, hl.index, hl.value, hl.parent, hl.child, hl.path, hl.recursive, hl.restored,
      hl.node, hl.childArray, hl.sizeResult, hl.bound, hl.arraySite, hl.arrayCheck, hl.dflt,
      hl.pair, hl.childSite, hl.childCheck, hl.indexDec, hcc]
  · rw [countedPrefix_fragment p]
    simp [execCounted, execNested, harr0, hnode, hcell, hslot, hslot', hins, hex, Ownership.Env.set,
      hl.array, hl.index, hl.value, hl.parent, hl.child, hl.path, hl.recursive, hl.restored,
      hl.node, hl.childArray, hl.sizeResult, hl.bound, hl.arraySite, hl.arrayCheck, hl.dflt,
      hl.pair, hl.childSite, hl.childCheck, hl.indexDec, hcc]
  · rw [countedPrefix_fragment p]
    simp [execCounted, execNested, harr0, hnode, hcell, hslot, hslot', hins, hex, Ownership.Env.set,
      hl.array, hl.index, hl.value, hl.parent, hl.child, hl.path, hl.recursive, hl.restored,
      hl.node, hl.childArray, hl.sizeResult, hl.bound, hl.arraySite, hl.arrayCheck, hl.dflt,
      hl.pair, hl.childSite, hl.childCheck, hl.indexDec, hcc]
  · rw [countedPrefix_fragment p]
    simp [execCounted, execNested, harr0, hnode, hcell, hslot, hslot', hins, hex, Ownership.Env.set,
      hl.array, hl.index, hl.value, hl.parent, hl.child, hl.path, hl.recursive, hl.restored,
      hl.node, hl.childArray, hl.sizeResult, hl.bound, hl.arraySite, hl.arrayCheck, hl.dflt,
      hl.pair, hl.childSite, hl.childCheck, hl.indexDec, hcc]
  · rw [countedPrefix_fragment p]
    simp [execCounted, execNested, harr0, hnode, hcell, hslot, hslot', hins, hex, Ownership.Env.set,
      hl.array, hl.index, hl.value, hl.parent, hl.child, hl.path, hl.recursive, hl.restored,
      hl.node, hl.childArray, hl.sizeResult, hl.bound, hl.arraySite, hl.arrayCheck, hl.dflt,
      hl.pair, hl.childSite, hl.childCheck, hl.indexDec, hcc]
  · rw [countedPrefix_fragment p]
    simp [execCounted, execNested, harr0, hnode, hcell, hslot, hslot', hins, hex, Ownership.Env.set,
      hl.array, hl.index, hl.value, hl.parent, hl.child, hl.path, hl.recursive, hl.restored,
      hl.node, hl.childArray, hl.sizeResult, hl.bound, hl.arraySite, hl.arrayCheck, hl.dflt,
      hl.pair, hl.childSite, hl.childCheck, hl.indexDec, hcc]

end OwnershipLcnf

namespace OwnershipLcnf

end OwnershipLcnf

namespace OwnershipLcnf

end OwnershipLcnf
