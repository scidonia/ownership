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
recomposes at the pair release (`decPair`), after which the cells coincide again
with the cursor one higher. `execCounted_protocol_boundary` states the boundary
fact: the counted interpreter's heap at the end of the fragment's counted prefix
is `CountedPair.protocol`'s boundary heap.

The trace splits at that release — `countedPrefix` is the release-terminated span
and `countedSuffix` the rest — and the counted reading continues from the
boundary state. `execCounted_full_fragment` executes the whole of `p.fragment`:
the counted prefix, then the child check, the child call at that state, the
restoration at the call's output heap and the return. The call is the supplied
`Ownership.CountedChildCall`, consumed where the interpreter reaches it; the
restoration's `mutate` branch is derived there rather than assumed. The counted
outcome is related to the model's run of the same extraction/call/restoration term
by `NestedOutcome.Compat`: `HeapCompat` on the heaps — the same cell at every
name, with the model cursor no higher — and literal equality on the result, the
fault and the write trace. The statement is over `execCountedAST`, the counted
counterpart of `execNestedAST`, so the recogniser's verdict is spent by the
theorem: a code value that does not decode to `p` is not executed at all.

Nothing here is a runtime or backend claim, and the emitted recursive callee is
not captured: the recursive clause runs the admitted model body, exactly as
`execNested` does.
-/
import OwnershipLcnf.NestedSemantics
import OwnershipLcnf.PathRecursion
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

/-- The counted block's span: the recogniser's trace up to and including the
pair's release. The span is defined by the release, not by a position: the
take-out is the only operation in the block that allocates, so the pair's
decrement is the last counted operation of the block, and the trace stops there.
`fragment_decomp` records that nothing else separates the block from the rest of
the fragment. -/
def countedPrefix : List NestedOp → List NestedOp
  | [] => []
  | op :: rest =>
      match op with
      | .decPair _ => [op]
      | _ => op :: countedPrefix rest

/-- The post-release span of the recognised fragment, in emitted order: the child
site constant, the child assertion, the recursive call on the checked handle, the
put-back of the result, the index decrement and the return. -/
def countedSuffix (p : NestedPrefix) : List NestedOp :=
  [ .siteConst p.childSite 1
  , .checkChild p.childCheck p.childSite p.child
  , .recurse p.recursive p.path p.value p.childCheck
  , .setArray p.restored p.parent p.index p.recursive
  , .decIndex p.index
  , .retVar p.restored ]

/-- The recognised fragment is its counted block followed by the post-release
span. The split is the release's own position in the trace, so it is a fact about
the recognised shape rather than a numeric cutoff applied to it. -/
theorem fragment_decomp (p : NestedPrefix) :
    p.fragment = countedPrefix p.fragment ++ countedSuffix p := rfl

/-- The post-release span of the recognised fragment, as the literal six
operations the counted interpreter runs after the pair's release. -/
theorem countedSuffix_fragment (p : NestedPrefix) :
    countedSuffix p =
      [ .siteConst p.childSite 1
      , .checkChild p.childCheck p.childSite p.child
      , .recurse p.recursive p.path p.value p.childCheck
      , .setArray p.restored p.parent p.index p.recursive
      , .decIndex p.index
      , .retVar p.restored ] := rfl

/-- A step that ends a counted run: only `.retVar` does, so a trace with no return
is executed to its end before any trace appended to it. -/
def NestedOp.returns : NestedOp → Bool
  | .retVar _ => true
  | _ => false

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

/-! ## Composing counted runs -/

/-- Appending a trace to one that has no return. No clause of the interpreter ends
a run except `.retVar`, so the head's clause is the same in both traces and the
appended trace runs from the state the head's trace reaches. A plain "run `a`,
then run `b`" law is false — a `.retVar` in `a` ends the whole run — so the
no-return side condition is part of the statement, and `countedPrefix_noRet`
supplies it for the fragment's counted block. -/
theorem execCounted_append (assign : Lean.FVarId → Ownership.Var)
    (body : Ownership.Nested.NCode) :
    ∀ (a b : List NestedOp) (s : NestedMachine),
      (∀ op ∈ a, op.returns = false) →
        execCounted assign body (a ++ b) s =
          match execCounted assign body a s with
          | (s', some (.done H e v ws)) => execCounted assign body b s'
          | out => out := by
  intro a
  induction a with
  | nil =>
      intro b s _
      simp [execCounted]
  | cons op rest ih =>
      intro b s hno
      have hop : op.returns = false := hno op (by simp)
      have hrest : ∀ op' ∈ rest, op'.returns = false :=
        fun op' hop' => hno op' (List.mem_cons_of_mem _ hop')
      cases op with
      | retVar x => simp [NestedOp.returns] at hop
      | projArray dst node =>
          simpa [execCounted] using
            ih b { s with env := s.env.set (assign dst) .erased } hrest
      | incArray x check => simpa [execCounted] using ih b s hrest
      | projIndex dst node =>
          cases hn : (s.nodes node).index with
          | unknown => simp [execCounted, hn]
          | scalar i =>
              simpa [execCounted, hn] using
                ih b { s with env := s.env.set (assign dst) (.scalar i) } hrest
      | incIndex x check => simpa [execCounted] using ih b s hrest
      | projPath dst node =>
          simpa [execCounted] using
            ih b { s with env := s.env.set (assign dst) (.scalar s.callPath) } hrest
      | incPath x check => simpa [execCounted] using ih b s hrest
      | decNode x objs => simpa [execCounted] using ih b s hrest
      | arraySize dst arr =>
          cases h1 : s.env (assign arr) with
          | none => simp [execCounted, h1]
          | some v =>
              cases v with
              | ref r =>
                  cases h2 : s.heap.cells r with
                  | none => simp [execCounted, h1, h2]
                  | some o =>
                      simpa [execCounted, h1, h2] using
                        ih b { s with env := s.env.set (assign dst) (.scalar o.fields.size) }
                          hrest
              | scalar n => simp [execCounted, h1]
              | erased => simp [execCounted, h1]
      | decLt dst idx size =>
          cases h1 : s.env (assign idx) with
          | none => simp [execCounted, h1]
          | some v1 =>
              cases v1 with
              | scalar i =>
                  cases h2 : s.env (assign size) with
                  | none => simp [execCounted, h1, h2]
                  | some v2 =>
                      cases v2 with
                      | scalar n =>
                          simpa [execCounted, h1, h2] using
                            ih b { s with
                              env := s.env.set (assign dst)
                                (.scalar (if i < n then 1 else 0)) } hrest
                      | ref r2 => simp [execCounted, h1, h2]
                      | erased => simp [execCounted, h1, h2]
              | ref r1 => simp [execCounted, h1]
              | erased => simp [execCounted, h1]
      | boundsTrue discr =>
          cases h1 : s.env (assign discr) with
          | none => simp [execCounted, h1]
          | some v =>
              cases v with
              | ref r => simp [execCounted, h1]
              | erased => simp [execCounted, h1]
              | scalar n =>
                  cases n with
                  | zero => simp [execCounted, h1]
                  | succ k =>
                      cases k with
                      | zero => simpa [execCounted, h1] using ih b s hrest
                      | succ m => simp [execCounted, h1]
      | siteConst dst closed => simpa [execCounted] using ih b s hrest
      | checkArray dst site arr =>
          cases h1 : s.env (assign arr) with
          | none => simp [execCounted, h1]
          | some v =>
              cases v with
              | ref r =>
                  cases hex : s.heap.exclusive? r with
                  | false => simp [execCounted, h1, hex]
                  | true =>
                      simpa [execCounted, h1, hex] using
                        ih b { s with env := s.env.set (assign dst) (.ref r) } hrest
              | scalar n => simp [execCounted, h1]
              | erased => simp [execCounted, h1]
      | stateDefault dst arr =>
          cases h1 : s.env (assign arr) with
          | none => simp [execCounted, h1]
          | some v =>
              simpa [execCounted, h1] using
                ih b { s with env := s.env.set (assign dst) (.scalar 0) } hrest
      | takeOut dst check index dflt =>
          cases h1 : s.env (assign check) with
          | none => simp [execCounted, h1]
          | some v1 =>
              cases v1 with
              | ref r =>
                  cases h2 : s.env (assign index) with
                  | none => simp [execCounted, h1, h2]
                  | some v2 =>
                      cases v2 with
                      | scalar i =>
                          cases h3 : s.env (assign dflt) with
                          | none => simp [execCounted, h1, h2, h3]
                          | some v3 =>
                              cases v3 with
                              | scalar d =>
                                  cases h4 : s.heap.cells r with
                                  | none => simp [execCounted, h1, h2, h3, h4]
                                  | some o =>
                                      cases h5 : o.fields[i]? with
                                      | none => simp [execCounted, h1, h2, h3, h4, h5]
                                      | some v5 =>
                                          cases v5 with
                                          | ref e =>
                                              simpa [execCounted, h1, h2, h3, h4, h5] using
                                                ih b { s with
                                                  heap := (CountedPair.takeOut s.heap r e i).2
                                                  pairs := setPair s.pairs dst.name
                                                    (.ref r, .ref e) } hrest
                                          | scalar n =>
                                              simp [execCounted, h1, h2, h3, h4, h5]
                                          | erased =>
                                              simp [execCounted, h1, h2, h3, h4, h5]
                              | ref r3 => simp [execCounted, h1, h2, h3]
                              | erased => simp [execCounted, h1, h2, h3]
                      | ref r2 => simp [execCounted, h1, h2]
                      | erased => simp [execCounted, h1, h2]
              | scalar n => simp [execCounted, h1]
              | erased => simp [execCounted, h1]
      | projParent dst pair =>
          cases h1 : s.pairs pair.name with
          | none => simp [execCounted, h1]
          | some pr =>
              cases pr with
              | mk pa pb =>
                  simpa [execCounted, h1] using
                    ih b { s with env := s.env.set (assign dst) pa } hrest
      | incParent x =>
          cases h1 : s.env (assign x) with
          | none => simp [execCounted, h1]
          | some v =>
              cases v with
              | ref q =>
                  simpa [execCounted, h1] using ih b { s with heap := s.heap.inc q 1 } hrest
              | scalar n => simp [execCounted, h1]
              | erased => simp [execCounted, h1]
      | projChild dst pair =>
          cases h1 : s.pairs pair.name with
          | none => simp [execCounted, h1]
          | some pr =>
              cases pr with
              | mk pa pb =>
                  simpa [execCounted, h1] using
                    ih b { s with env := s.env.set (assign dst) pb } hrest
      | incChild x =>
          cases h1 : s.env (assign x) with
          | none => simp [execCounted, h1]
          | some v =>
              cases v with
              | ref q =>
                  simpa [execCounted, h1] using ih b { s with heap := s.heap.inc q 1 } hrest
              | scalar n => simp [execCounted, h1]
              | erased => simp [execCounted, h1]
      | decPair x =>
          simpa [execCounted] using
            ih b { s with heap := CountedPair.decRef s.heap (s.heap.next - 1) } hrest
      | checkChild dst site child =>
          cases h1 : s.env (assign child) with
          | none => simp [execCounted, h1]
          | some v =>
              cases v with
              | ref r =>
                  cases hex : s.heap.exclusive? r with
                  | false => simp [execCounted, h1, hex]
                  | true =>
                      simpa [execCounted, h1, hex] using
                        ih b { s with env := s.env.set (assign dst) (.ref r) } hrest
              | scalar n => simp [execCounted, h1]
              | erased => simp [execCounted, h1]
      | recurse dst path value child =>
          cases h1 : s.env (assign child) with
          | none => simp [execCounted, h1]
          | some v1 =>
              cases v1 with
              | ref r =>
                  cases h2 : s.env (assign path) with
                  | none => simp [execCounted, h1, h2]
                  | some v2 =>
                      cases v2 with
                      | scalar pv =>
                          cases h3 : s.env (assign value) with
                          | none => simp [execCounted, h1, h2, h3]
                          | some v3 =>
                              cases v3 with
                              | scalar xv =>
                                  cases h4 : Ownership.Nested.runN body
                                      (callEnv s.childVar (.ref r) (assign path) (.scalar pv)
                                        (assign value) (.scalar xv)) s.heap with
                                  | done H' envb vb ws =>
                                      simpa [execCounted, h1, h2, h3, h4] using
                                        ih b { s with
                                          heap := H'
                                          env := s.env.set (assign dst) (.ref r)
                                          writes := s.writes ++ ws } hrest
                                  | fault H' envb f ws => simp [execCounted, h1, h2, h3, h4]
                              | ref r3 => simp [execCounted, h1, h2, h3]
                              | erased => simp [execCounted, h1, h2, h3]
                      | ref r2 => simp [execCounted, h1, h2]
                      | erased => simp [execCounted, h1, h2]
              | scalar n => simp [execCounted, h1]
              | erased => simp [execCounted, h1]
      | setArray dst arr idx val =>
          cases h1 : s.env (assign arr) with
          | none => simp [execCounted, h1]
          | some v1 =>
              cases v1 with
              | ref r =>
                  cases h2 : s.env (assign idx) with
                  | none => simp [execCounted, h1, h2]
                  | some v2 =>
                      cases v2 with
                      | scalar i =>
                          cases h3 : s.env (assign val) with
                          | none => simp [execCounted, h1, h2, h3]
                          | some v3 =>
                              cases v3 with
                              | ref e =>
                                  cases h4 : PutBack.putBack s.heap r i e with
                                  | none => simp [execCounted, h1, h2, h3, h4]
                                  | some p =>
                                      cases p with
                                      | mk rr H' =>
                                          simpa [execCounted, h1, h2, h3, h4] using
                                            ih b { s with
                                              heap := H'
                                              env := s.env.set (assign dst) (.ref rr) } hrest
                              | scalar n => simp [execCounted, h1, h2, h3]
                              | erased => simp [execCounted, h1, h2, h3]
                      | ref r2 => simp [execCounted, h1, h2]
                      | erased => simp [execCounted, h1, h2]
              | scalar n => simp [execCounted, h1]
              | erased => simp [execCounted, h1]
      | decIndex x => simpa [execCounted] using ih b s hrest

/-- The append law in the form a composition uses: when the head's trace completes,
the appended trace runs from the state it reaches. -/
theorem execCounted_append_of_done (assign : Lean.FVarId → Ownership.Var)
    (body : Ownership.Nested.NCode) (a b : List NestedOp) (s M : NestedMachine)
    (H : Ownership.Heap) (e : Ownership.Env) (v : Ownership.Val)
    (ws : List Ownership.Write)
    (hnoRet : ∀ op ∈ a, op.returns = false)
    (h : execCounted assign body a s = (M, some (.done H e v ws))) :
    execCounted assign body (a ++ b) s = execCounted assign body b M := by
  rw [execCounted_append assign body a b s hnoRet, h]

/-- The fragment's counted block has no return: its last operation is the pair's
release, so the appended trace runs from the state the block reaches. -/
theorem countedPrefix_noRet (p : NestedPrefix) :
    ∀ op ∈ countedPrefix p.fragment, op.returns = false := by
  intro op hop
  have h : (countedPrefix p.fragment).all (fun op => !op.returns) = true := rfl
  have h' := List.all_eq_true.mp h op hop
  simpa using h'

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
      hl.pair, hl.childSite, hl.childCheck, hcc] using hstep
  refine ⟨hheap, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hheap]; exact hcompat
  · rw [countedPrefix_fragment p]
    simp [execCounted, execNested, harr0, hnode, hcell, hslot, hslot', hins, hex, Ownership.Env.set,
      hl.array, hl.index, hl.value, hl.parent, hl.child, hl.path, hl.recursive, hl.restored,
      hl.node, hl.childArray, hl.sizeResult, hl.bound, hl.arraySite, hl.arrayCheck, hl.dflt,
      hl.pair, hl.childSite, hl.childCheck, hcc]
  · rw [countedPrefix_fragment p]
    simp [execCounted, execNested, harr0, hnode, hcell, hslot, hslot', hins, hex, Ownership.Env.set,
      hl.array, hl.index, hl.value, hl.parent, hl.child, hl.path, hl.recursive, hl.restored,
      hl.node, hl.childArray, hl.sizeResult, hl.bound, hl.arraySite, hl.arrayCheck, hl.dflt,
      hl.pair, hl.childSite, hl.childCheck, hcc]
  · rw [countedPrefix_fragment p]
    simp [execCounted, execNested, harr0, hnode, hcell, hslot, hslot', hins, hex, Ownership.Env.set,
      hl.array, hl.index, hl.value, hl.parent, hl.child, hl.path, hl.recursive, hl.restored,
      hl.node, hl.childArray, hl.sizeResult, hl.bound, hl.arraySite, hl.arrayCheck, hl.dflt,
      hl.pair, hl.childSite, hl.childCheck, hcc]
  · rw [countedPrefix_fragment p]
    simp [execCounted, execNested, harr0, hnode, hcell, hslot, hslot', hins, hex, Ownership.Env.set,
      hl.array, hl.index, hl.value, hl.parent, hl.child, hl.path, hl.recursive, hl.restored,
      hl.node, hl.childArray, hl.sizeResult, hl.bound, hl.arraySite, hl.arrayCheck, hl.dflt,
      hl.pair, hl.childSite, hl.childCheck, hcc]
  · rw [countedPrefix_fragment p]
    simp [execCounted, execNested, harr0, hnode, hcell, hslot, hslot', hins, hex, Ownership.Env.set,
      hl.array, hl.index, hl.value, hl.parent, hl.child, hl.path, hl.recursive, hl.restored,
      hl.node, hl.childArray, hl.sizeResult, hl.bound, hl.arraySite, hl.arrayCheck, hl.dflt,
      hl.pair, hl.childSite, hl.childCheck, hcc]
  · rw [countedPrefix_fragment p]
    simp [execCounted, execNested, harr0, hnode, hcell, hslot, hslot', hins, hex, Ownership.Env.set,
      hl.array, hl.index, hl.value, hl.parent, hl.child, hl.path, hl.recursive, hl.restored,
      hl.node, hl.childArray, hl.sizeResult, hl.bound, hl.arraySite, hl.arrayCheck, hl.dflt,
      hl.pair, hl.childSite, hl.childCheck, hcc]

end OwnershipLcnf

namespace OwnershipLcnf

end OwnershipLcnf

namespace OwnershipLcnf

/-! ## The boundary state, the post-release run and the whole-fragment theorem -/

/-- The counted block's exit state. The block has no return, so its run ends at the
trace's end; the machine it leaves has the five environment lookups the child
check, the call and the restoration consume, and its non-heap fields are the
entry's. The clause evaluation is the one `execCounted_protocol_boundary`
performs for its environment row; the heap fact is that theorem's. -/
theorem execCounted_boundary_env (assign : Lean.FVarId → Ownership.Var)
    (p : NestedPrefix) (body : Ownership.Nested.NCode) (s : NestedMachine)
    (rA childRef : Ownership.Ref) (idx v : Nat) (o : Ownership.Obj)
    (hl : NestedLayout assign p)
    (harr : s.env (assign p.array) = some (.ref rA))
    (hnode : s.nodes p.node = { index := .scalar idx })
    (hcell : s.heap.cells rA = some o)
    (hslot : o.fields[idx]? = some (.ref childRef))
    (hval : s.env (assign p.value) = some (.scalar v))
    (hex : s.heap.exclusive? rA = true) :
    ∃ M,
      execCounted assign body (countedPrefix p.fragment) s =
          (M, some (.done M.heap M.env .erased M.writes)) ∧
        M.env (assign p.parent) = some (.ref rA) ∧
        M.env (assign p.child) = some (.ref childRef) ∧
        M.env (assign p.path) = some (.scalar s.callPath) ∧
        M.env (assign p.value) = some (.scalar v) ∧
        M.env (assign p.index) = some (.scalar idx) ∧
        M.childVar = s.childVar ∧
        M.writes = s.writes := by
  have hins : idx < o.fields.size := (Array.getElem?_eq_some_iff.mp hslot).1
  have hbound : (if idx < o.fields.size then (1 : Nat) else 0) = 1 := by rw [if_pos hins]
  have hslot' : o.fields[idx] = .ref childRef := by
    have h1 : o.fields[idx]? = some o.fields[idx] := by simp [hins]
    have h2 : some o.fields[idx] = some (.ref childRef) := by rw [← h1]; exact hslot
    exact Option.some.inj h2
  -- the layout's slots, so the interpreter's own binder expressions match
  have harr0 : s.env 0 = some (.ref rA) := by simpa [hl.array] using harr
  have hval0 : s.env 2 = some (.scalar v) := by simpa [hl.value] using hval
  refine ⟨(execCounted assign body (countedPrefix p.fragment) s).1, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp [countedPrefix_fragment p, execCounted, harr0, hnode, hval0, hcell, hslot, hslot', hins,
      hbound, hex, Ownership.Env.set, hl.array, hl.index, hl.value, hl.parent, hl.child, hl.path,
      hl.recursive, hl.restored, hl.node, hl.childArray, hl.sizeResult, hl.bound, hl.arraySite,
      hl.arrayCheck, hl.dflt, hl.pair, hl.childSite, hl.childCheck]

/-- The counted interpreter's post-release span, from the boundary state: the
child site constant, the child assertion over the child the take-out extracted,
the recursive call at that state, the put-back of the result at the call's output
heap, the index decrement and the return. The call is the caller's own contract
run, and the put-back's outcome is the restoration's, so the span's heap is the
restoration's final heap and its write trace is the call's. -/
theorem execCounted_suffix (assign : Lean.FVarId → Ownership.Var) (p : NestedPrefix)
    (body : Ownership.Nested.NCode) (M : NestedMachine)
    (Hout Hf : Ownership.Heap) (rA childRef : Ownership.Ref) (i v pv : Nat)
    (envb : Ownership.Env) (ws : List Ownership.Write)
    (hl : NestedLayout assign p)
    (hchild : M.env (assign p.child) = some (.ref childRef))
    (hparent : M.env (assign p.parent) = some (.ref rA))
    (hpath : M.env (assign p.path) = some (.scalar pv))
    (hvalue : M.env (assign p.value) = some (.scalar v))
    (hindex : M.env (assign p.index) = some (.scalar i))
    (hchildVar : M.childVar = assign p.child)
    (hwrites : M.writes = [])
    (hex : M.heap.exclusive? childRef = true)
    (hrun : Ownership.Nested.runN body
      (callEnv (assign p.child) (.ref childRef) (assign p.path) (.scalar pv)
        (assign p.value) (.scalar v)) M.heap = .done Hout envb (.ref childRef) ws)
    (hpb : Ownership.PutBack.putBack Hout rA i childRef = some (rA, Hf)) :
    (execCounted assign body (countedSuffix p) M).1.heap = Hf ∧
      (execCounted assign body (countedSuffix p) M).2 =
        some (.done Hf
          (((M.env.set (assign p.childCheck) (.ref childRef)).set (assign p.recursive)
            (.ref childRef)).set (assign p.restored) (.ref rA)) (.ref rA) ws) ∧
      (execCounted assign body (countedSuffix p) M).1.env (assign p.restored) =
        some (.ref rA) ∧
      (execCounted assign body (countedSuffix p) M).1.writes = ws := by
  -- the layout's slots, so the interpreter's own binder expressions match
  have hchild4 : M.env 4 = some (.ref childRef) := by simpa [hl.child] using hchild
  have hparent3 : M.env 3 = some (.ref rA) := by simpa [hl.parent] using hparent
  have hpath5 : M.env 5 = some (.scalar pv) := by simpa [hl.path] using hpath
  have hvalue2 : M.env 2 = some (.scalar v) := by simpa [hl.value] using hvalue
  have hindex1 : M.env 1 = some (.scalar i) := by simpa [hl.index] using hindex
  have hchildVar4 : M.childVar = 4 := by simpa [hl.child] using hchildVar
  have hrun0 : Ownership.Nested.runN body
      (callEnv 4 (.ref childRef) 5 (.scalar pv) 2 (.scalar v)) M.heap =
      .done Hout envb (.ref childRef) ws := by
    simpa [hl.child, hl.path, hl.value] using hrun
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    simp [countedSuffix_fragment p, execCounted, hchild4, hparent3, hpath5, hvalue2, hindex1,
      hchildVar4, hwrites, hex, hrun0, hpb, Ownership.Env.set, hl.child, hl.parent, hl.index,
      hl.path, hl.value, hl.restored, hl.recursive, hl.childCheck]

/-- Execute the recognised fragment of an actual LCNF code value against the
counted heap. `projectNested` walks `code`, and the result is returned only when
the prefix it decoded is the expected `p` (by binder identity): this is the
counted counterpart of `execNestedAST`, and it is what makes the recognition
hypothesis of the whole-fragment theorem load-bearing. -/
def execCountedAST (declName takeOut : Lean.Name) (assign : Lean.FVarId → Ownership.Var)
    (body : Ownership.Nested.NCode) (p : NestedPrefix) (code : Code .impure)
    (s : NestedMachine) : Option (NestedMachine × Option Ownership.Res) :=
  match projectNested declName takeOut code with
  | none => none
  | some p' =>
      if p'.binderNames = p.binderNames then some (execCounted assign body p'.fragment s)
      else none

/-- The recognition hypothesis is consumed: for a code value the projection
decodes to `p`, `execCountedAST` executes that code's own trace. A code value the
recogniser rejects, or decodes to a different prefix, is not executed. -/
theorem execCountedAST_recognized (declName takeOut : Lean.Name)
    (assign : Lean.FVarId → Ownership.Var) (body : Ownership.Nested.NCode)
    (p : NestedPrefix) (code : Code .impure) (s : NestedMachine)
    (hproj : projectNested declName takeOut code = some p) :
    execCountedAST declName takeOut assign body p code s =
      some (execCounted assign body p.fragment s) := by
  simp [execCountedAST, hproj]

/-- The counted and model outcomes agree when their heaps are `HeapCompat` and the
result, the fault and the write trace are equal. The heap component is the
relation's only slack: the counted protocol's cursor stays one higher because of
the temporary pair's allocation, so an equality on heaps would be false. -/
structure NestedOutcome.Compat (a b : NestedOutcome) : Prop where
  /-- The reported result is the same value. -/
  result : a.result = b.result
  /-- The reported fault is the same fault. -/
  fault : a.fault = b.fault
  /-- The reported write trace is the same trace. -/
  writes : a.writes = b.writes
  /-- The heaps are related by `HeapCompat`. -/
  heap : Ownership.HeapCompat a.heap b.heap

/-- What a client can observe of a run at this boundary: the content of every
cell, the reported result, the fault and the write trace. The allocator cursor is
deliberately not part of it: addresses are not source-observable, and the cursor
is the one component `Compat` leaves free. -/
def Observed (a : NestedOutcome) :
    (Ownership.Ref → Option Ownership.Obj) × Option Ownership.Val ×
      Option Ownership.Fault × List Ownership.Write :=
  (a.heap.cells, a.result, a.fault, a.writes)

/-- The counted run and the model run are indistinguishable to every observation
of that boundary: `Compat` fixes each component the observation reads. -/
theorem NestedOutcome.Compat.observed_eq {a b : NestedOutcome}
    (h : NestedOutcome.Compat a b) :
    Observed a = Observed b := by
  unfold Observed
  rw [funext h.heap.cells, h.result, h.fault, h.writes]

/-- Consequently no predicate of cells, result, fault and trace can separate the
two runs: it holds of one exactly when it holds of the other. -/
theorem NestedOutcome.Compat.observed_iff {a b : NestedOutcome}
    (h : NestedOutcome.Compat a b)
    (p : (Ownership.Ref → Option Ownership.Obj) → Option Ownership.Val →
      Option Ownership.Fault → List Ownership.Write → Prop) :
    p a.heap.cells a.result a.fault a.writes ↔
      p b.heap.cells b.result b.fault b.writes := by
  rw [funext h.heap.cells, h.result, h.fault, h.writes]

/-- The counted fragment's whole trace, from the entry machine through the pair
protocol, the child call and the restoration. `p.fragment` splits at the pair's
release (`fragment_decomp`): `execCounted` runs the counted block to the boundary
state (`execCounted_boundary_env`), and then runs the post-release span from that
state (`execCounted_suffix`) with the caller's own `CountedChildCall` run, so the
call is consumed where the interpreter reaches it and the restoration's mutate
branch is derived at the call's output heap. The caller's accounting at the body's
return is derived from the boundary accounting and the call's edge effect, not
supplied.

The counted outcome is reported against the model's run of the same
extraction/call/restoration term (`Ownership.chain`) by `NestedOutcome.Compat`:
the heaps are `HeapCompat` — the same cell at every name, with the model cursor
no higher — and the result, fault and write trace are literally equal. The
statement is over `execCountedAST`, so the recogniser's verdict is spent by the
theorem.

The child call's boundary remains contractual (N10): the callee's body is not
captured, and the run the conclusion names is the admitted model body's. -/
theorem execCounted_full_fragment
    {code : Lean.Compiler.LCNF.Code Lean.Compiler.LCNF.Purity.impure}
    {p : NestedPrefix} {assign : Lean.FVarId → Ownership.Var}
    (declName takeOut : Lean.Name)
    (hproj : projectNested declName takeOut code = some p)
    (hl : NestedLayout assign p)
    (body : Ownership.Nested.NCode) (s : NestedMachine) (mEnv : Ownership.Env)
    (H : Ownership.Heap) (rA : Ownership.Ref) (o : Ownership.Obj) (i v pv : Nat)
    (childRef : Ownership.Ref) (path value : Ownership.Var) (l : Ownership.Path.Level)
    (hm : LevelMatch assign p l path value rA o i childRef)
    (hag : NestedAgrees assign p s mEnv H rA i v pv)
    (hcell : H.cells rA = some o) (hslot : o.fields[i]? = some (.ref childRef))
    (hidx : mEnv l.indexVar = some (.scalar i))
    {support : List Ownership.Var} {c : Ownership.Ctx} {ctx' : Ownership.Ctx}
    (hacc : Ownership.Accounted support H mEnv c)
    (hxu : c.us l.arrayVar = .owned) (hr : c.refOf l.arrayVar = some rA)
    (hmu : c.mult rA = 1) (he : c.mult childRef = 1)
    (hchk : Ownership.Nested.checkN c
      (Ownership.chain l.arrayVar l.indexVar l.parentVar l.childVar childRef path value
        l.resultVar l.restoredVar body) = some ctx')
    {Hout : Ownership.Heap}
    (hcall : Ownership.CountedChildCall
      (Ownership.CountedPair.protocol H rA childRef i).2 Hout
      ((mEnv.set l.parentVar (.ref rA)).set l.childVar (.ref childRef))
      ((c.move l.arrayVar l.parentVar).bindOwned l.childVar childRef)
      l.childVar path value body rA childRef
      (l.childVar :: Ownership.replaceVar support l.arrayVar l.parentVar)) :
    ∃ Hf envf ws Hm envm,
      execCountedAST declName takeOut assign body p code s =
          some ((execCounted assign body p.fragment s).1,
            some (.done Hf envf (.ref rA) (s.writes ++ ws))) ∧
      (execCounted assign body p.fragment s).1.heap = Hf ∧
      (execCounted assign body p.fragment s).1.env (assign p.restored) = some (.ref rA) ∧
      Ownership.Nested.runN
          (Ownership.chain l.arrayVar l.indexVar l.parentVar l.childVar childRef path value
            l.resultVar l.restoredVar body) mEnv H = .done Hm envm (.ref rA) ws ∧
      (∀ w ∈ ws, w.2 = true) ∧
      NestedOutcome.Compat
        (NestedOutcome.ofMachine assign p (execCounted assign body p.fragment s).1
          (Ownership.Res.done Hf envf (.ref rA) (s.writes ++ ws)))
        (NestedOutcome.ofModel (Ownership.Nested.runN
          (Ownership.chain l.arrayVar l.indexVar l.parentVar l.childVar childRef path value
            l.resultVar l.restoredVar body) mEnv H)) ∧
      Ownership.Accounted
        (l.childVar :: Ownership.replaceVar support l.arrayVar l.parentVar)
        (Ownership.CountedPair.protocol H rA childRef i).2
        ((mEnv.set l.parentVar (.ref rA)).set l.childVar (.ref childRef))
        ((c.move l.arrayVar l.parentVar).bindOwned l.childVar childRef) ∧
      Ownership.Accounted
        ((Ownership.replaceVar
            (Ownership.replaceVar
              (l.childVar :: Ownership.replaceVar support l.arrayVar l.parentVar)
              l.childVar l.resultVar) l.parentVar l.restoredVar).erase l.resultVar)
        Hf
        ((((mEnv.set l.parentVar (.ref rA)).set l.childVar (.ref childRef)).set
            l.resultVar (.ref childRef)).set l.restoredVar (.ref rA))
        (((((c.move l.arrayVar l.parentVar).bindOwned l.childVar childRef).move
            l.childVar l.resultVar).move l.parentVar l.restoredVar).setUs l.resultVar .dead) ∧
      Ownership.HeapCompat Hf Hm ∧
      (Ownership.CountedPair.protocol H rA childRef i).2.next = H.next + 1 ∧
      (Ownership.CountedPair.protocol H rA childRef i).2.cells H.next = none ∧
      (Ownership.CountedPair.protocol H rA childRef i).2.cells rA =
        some (Ownership.PutBack.parentAfter o i) ∧
      Ownership.Heap.Exclusive (Ownership.CountedPair.protocol H rA childRef i).2 rA ∧
      Ownership.Heap.Exclusive (Ownership.CountedPair.protocol H rA childRef i).2 childRef ∧
      Ownership.HeapCompat (Ownership.CountedPair.protocol H rA childRef i).2
        (H.set rA { o with fields := o.fields.setIfInBounds i (.scalar 0) }) ∧
      Ownership.PutBack.disposition? Hout rA i = some .mutate ∧
      Ownership.PutBack.putBack Hout rA i childRef = some (rA, Hf) ∧
      Hf = Ownership.PutBack.mutate Hout rA (Ownership.PutBack.parentAfter o i) i childRef ∧
      ((Ownership.PutBack.parentAfter o i).fields.setIfInBounds i (.ref childRef))[i]? =
        some (.ref childRef) ∧
      (∀ q, ¬ Ownership.Entry.MutableFootprint
          (Ownership.CountedPair.protocol H rA childRef i).2 childRef q →
        Hout.cells q = (Ownership.CountedPair.protocol H rA childRef i).2.cells q) ∧
      (∀ q, q ≠ rA → Hf.cells q = Hout.cells q) := by
  -- the entry's slot facts and the derived exclusivity of the array
  have harrS : s.env (assign p.array) = some (.ref rA) := hag.array_machine
  have hnodeS : s.nodes p.node = { index := .scalar i } := hag.nodes
  have hvalS : s.env (assign p.value) = some (.scalar v) := hag.value_machine
  have hexH : H.exclusive? rA = true :=
    Ownership.exclusive?_of_accounted hacc hxu hr hmu
  have hexS : s.heap.exclusive? rA = true := by rw [hag.heap]; exact hexH
  have hnextH : H.cells H.next = none := by
    cases hc : H.cells H.next with
    | none => rfl
    | some o' => exact absurd (hacc.domain H.next o' hc) (Nat.lt_irrefl H.next)
  -- the restoration boundary: the child's cell, the two targets' distinctness
  have hma : c.multOf l.arrayVar = 1 := by
    unfold Ownership.Ctx.multOf
    rw [hr]
    exact hmu
  obtain ⟨oc, hb⟩ :=
    Ownership.restorationBoundary_of_accounted hacc hxu hma hr he hcell hslot
  have hccNone : H.cells childRef ≠ none :=
    hacc.inv.rc_ne_zero (by rw [he]; exact Nat.le_refl 1)
  obtain ⟨oc', hcc⟩ : ∃ oc', H.cells childRef = some oc' := by
    cases hc : H.cells childRef with
    | none => exact absurd hc hccNone
    | some oc' => exact ⟨oc', rfl⟩
  have hne : rA ≠ childRef := hb.distinct
  -- the counted block, its boundary state and the boundary's own facts
  obtain ⟨M₁, hM₁run, hM₁parent, hM₁child, hM₁path, hM₁value, hM₁index, hM₁childVar,
    hM₁writes⟩ :=
    execCounted_boundary_env assign p body s rA childRef i v o hl harrS hnodeS
      (by rw [hag.heap]; exact hcell) hslot hvalS hexS
  have hbheap : M₁.heap = (Ownership.CountedPair.protocol H rA childRef i).2 := by
    have h := (execCounted_protocol_boundary assign p body s rA childRef i o oc' hl harrS hnodeS
      (by rw [hag.heap]; exact hcell) (by rw [hag.heap]; exact hcc) hslot hne
      (by rw [hag.heap]; exact hnextH) hexS).1
    simp only [hM₁run] at h
    simpa [hag.heap] using h
  have hbex : M₁.heap.exclusive? childRef = true := by
    rw [hbheap]
    exact (Ownership.Heap.exclusive?_eq_true).mpr
      ⟨oc, hb.child, hb.child_rc, hb.child_persistent⟩
  -- the chain: the model run, the restoration and the call's own run
  obtain ⟨Hf, Hm, envm, ws, haccB, hcompatB, hpairNone, hcursor, hexP, hexC, hdisp, hpb,
    hrestMut, haccF, hchainRun, ⟨envb, hbodyRun⟩, hcopyFree, hcompatF⟩ :=
    Ownership.counted_nested_chain (a := l.arrayVar) (i := l.indexVar) (fst := l.parentVar)
      (snd := l.childVar) (eR := childRef) (path := path) (x := value)
      (result := l.resultVar) (restored := l.restoredVar) (r := rA) (o := o)
      (idx := i) (Hout := Hout) (ctx' := ctx') (body := body) hacc hchk hr hcell hslot
      hidx hcall
  -- the counted call-entry state is the contract's own call environment
  have henvChild : ((mEnv.set l.parentVar (.ref rA)).set l.childVar (.ref childRef)) l.childVar =
      some (.ref childRef) := by simp [Ownership.Env.set]
  have henvPath : ((mEnv.set l.parentVar (.ref rA)).set l.childVar (.ref childRef)) path =
      some (.scalar pv) := by
    rw [hm.pathVar, hm.childVar, hm.parentVar]
    simpa [Ownership.Env.set, hl.path, hl.child, hl.parent] using hag.path_model
  have henvValue : ((mEnv.set l.parentVar (.ref rA)).set l.childVar (.ref childRef)) value =
      some (.scalar v) := by
    rw [hm.valueVar, hm.childVar, hm.parentVar]
    simpa [Ownership.Env.set, hl.value, hl.child, hl.parent] using hag.value_model
  have hiso : Ownership.Nested.isolateEnv
      ((mEnv.set l.parentVar (.ref rA)).set l.childVar (.ref childRef)) l.childVar path value =
      callEnv (assign p.child) (.ref childRef) (assign p.path) (.scalar pv)
        (assign p.value) (.scalar v) := by
    rw [isolateEnv_eq_callEnv (env := (mEnv.set l.parentVar (.ref rA)).set l.childVar (.ref childRef))
      henvChild henvPath henvValue]
    rw [← hm.childVar, ← hm.pathVar, ← hm.valueVar]
  have hbodyCall : Ownership.Nested.runN body
      (callEnv (assign p.child) (.ref childRef) (assign p.path) (.scalar pv)
        (assign p.value) (.scalar v)) M₁.heap = .done Hout envb (.ref childRef) ws := by
    rw [hbheap, ← hiso]
    exact hbodyRun
  -- the post-release span, from the boundary state
  obtain ⟨hsfxHeap, hsfxRes, hsfxRestored, hsfxWrites⟩ :=
    execCounted_suffix assign p body M₁ Hout Hf rA childRef i v pv envb ws hl hM₁child
      hM₁parent (by rw [hM₁path, hag.callPath]) hM₁value hM₁index
      (by rw [hM₁childVar]; exact hag.childVar) (by rw [hM₁writes]; exact hag.writes) hbex
      hbodyCall hpb
  -- the whole fragment is the block followed by the span
  have hfullRun : execCounted assign body p.fragment s =
      execCounted assign body (countedSuffix p) M₁ := by
    rw [fragment_decomp p]
    exact execCounted_append_of_done assign body (countedPrefix p.fragment) (countedSuffix p)
      s M₁ M₁.heap M₁.env .erased M₁.writes (countedPrefix_noRet p) hM₁run
  -- the counted entry point's whole-trace equation
  have hASTEq : execCountedAST declName takeOut assign body p code s =
      some ((execCounted assign body p.fragment s).1,
        some (.done Hf
          (((M₁.env.set (assign p.childCheck) (.ref childRef)).set (assign p.recursive)
            (.ref childRef)).set (assign p.restored) (.ref rA)) (.ref rA) (s.writes ++ ws))) := by
    rw [execCountedAST_recognized declName takeOut assign body p code s hproj, hfullRun]
    exact congrArg some (Prod.ext rfl (by rw [hsfxRes, hag.writes, List.nil_append]))
  refine ⟨Hf, _, ws, Hm, envm, hASTEq, ?_, ?_, hchainRun, hcopyFree, ?_, haccB, haccF, hcompatF,
    hcursor, hpairNone, hb.parent, hexP, hexC, hcompatB, hdisp, hpb, hrestMut, ?_, ?_, ?_⟩
  · rw [hfullRun]
    exact hsfxHeap
  · rw [hfullRun]
    exact hsfxRestored
  · rw [hchainRun]
    refine { result := ?_, fault := rfl, writes := ?_, heap := hcompatF }
    · rw [hfullRun]
      exact hsfxRestored
    · simp only [NestedOutcome.ofMachine, NestedOutcome.ofModel]
      simp [hag.writes]
  · simpa [Ownership.PutBack.parentAfter] using
      Array.getElem?_setIfInBounds_self_of_lt (xs := o.fields) (i := i) (a := Val.ref childRef)
        (by simpa [Ownership.PutBack.parentAfter] using hb.index)
  · exact hcall.call.confined
  · intro q hq
    rw [hrestMut]
    exact Ownership.Heap.set_other (H := Hout) (r := rA) (r' := q) _ hq

end OwnershipLcnf
