/-
The counted extraction/call/restoration chain.

`Ownership/CountedPair.lean` derives the counts at the protocol boundary and
`Ownership/PutBack.lean` derives the restoration's disposition; `Ownership/
CompleteAccounting.lean` states `Accounted` at the interpreter's own post-states
for the take-out and the put-back. This module joins them: it relates the
counted heap the protocol produces to the abstract heap the model language
writes, carries `Accounted` across that relation, and composes extraction, the
child call's boundary and restoration into one theorem.

## The relation to the abstract heap

The captured take-out allocates the temporary pair, so the counted heap's
fresh-name counter advances by one while the model's take-out is a single field
write. The relation is therefore not heap equality but `HeapCompat Hc Ha`: the
two heaps agree on every cell, and the counted cursor is no lower. Its only
slack is the cursor, and `HeapCompat.eq_of_cursor_eq` shows that slack is what
`HeapCompat` admits: with equal cursors the heaps are equal.

`Accounted` is a *boundary* relation for this protocol, not an
every-instruction one. While the pair is alive the two `.ref` fields it holds
are borrowed aliases: `CountedPair.takeOut` transfers the handles into the pair
without incrementing, so the pair's edges are counted twice — once by the
transferred handle and once by the pair's own field — and no support satisfies
the count equation there. `OwnershipTest/CountedNested.lean` kernel-checks that
refusal beside the boundary's positive accounting.

## What is derived and what is a premise

* the take-out's fresh-name side conditions (`r ≠ H.next`, `e ≠ H.next`) follow
  from the live-cell domain and the count equation, so `counted_takeOut` takes
  neither;
* the restoration boundary's `r ≠ e` follows from the count equation, the array
  slot and the checker's count-one condition, not from a caller premise;
* the child call's contract gains exactly one field: the call's edge effect
  `EdgePreserved Hin Hout`. The caller's `Accounted` at the body's return is
  *derived* from it (`accounted_of_edges`), together with the caller's invariant
  (`ChildCall.inv_caller`) and stored counts (`ChildCall.rc_eq`). Everything
  else — the suspended parent's cell, the child's exclusivity, the result
  binding — is derived from `PutBack.ChildCall` and from `Accounted`.

The chain is not edge-preserving step by step: its take-out lowers the extracted
child's incoming-edge count by one and the restoration raises it by one.
`counted_nested_chain_edges` proves the **net** statement — the chain's entry and
its restored counted heap have the same incoming-edge count at every name, the
cursor does not go backwards and no cell appears — and that is what an enclosing
call consumes as its `edges` field. `counted_nested_chain_two_levels_call`
constructs the outer `CountedChildCall` from the inner chain's net effect, with
the inner chain itself as the body, and `counted_nested_chain_two_levels` applies
the chain theorem at the outer level, so the two-level term's model run and final
accounting are derived from the same composition. The outer *model* boundary of
the compound body stays a hypothesis: `PutBack.ChildCall` is stated for the
admitted model body, and the finite-path induction derives it for a recursive
body, not yet for a `chain` term. `counted_nested_chain`'s `HeapCompat` is still
the final-state relation; the net statement is the entry-to-output one beside it.

Nothing here is a runtime, transport or address-identity claim: the heap is the
fragment's named-cell model, the child call is contractual and the emitted
recursive callee is not captured.
-/
import Ownership.CompleteAccounting
import Ownership.PutBack

namespace Ownership

/-! ## The heap relation -/

/-- Two heaps that agree on every cell, with the counted heap's fresh-name
counter no lower than the abstract one's. The cursor slack is exactly the pair
allocation the counted protocol performs and the model's take-out does not. -/
structure HeapCompat (Hc Ha : Heap) : Prop where
  /-- The two heaps hold the same cell at every name. -/
  cells : ∀ r, Hc.cells r = Ha.cells r
  /-- The abstract heap's cursor is no higher. -/
  cursor : Ha.next ≤ Hc.next

namespace HeapCompat

theorem refl (H : Heap) : HeapCompat H H := ⟨fun _ => rfl, Nat.le_refl _⟩

theorem trans {Hc Hm Ha : Heap} (h₁ : HeapCompat Hc Hm) (h₂ : HeapCompat Hm Ha) :
    HeapCompat Hc Ha :=
  ⟨fun r => (h₁.cells r).trans (h₂.cells r), Nat.le_trans h₂.cursor h₁.cursor⟩

/-- The agreed cells give the same count. -/
theorem rc {Hc Ha : Heap} (h : HeapCompat Hc Ha) (r : Ref) : Hc.rc r = Ha.rc r := by
  simp [Heap.rc, h.cells r]

/-- The agreed cells give the same persistence flag. -/
theorem isPersistent {Hc Ha : Heap} (h : HeapCompat Hc Ha) (r : Ref) :
    Hc.isPersistent r = Ha.isPersistent r := by
  simp [Heap.isPersistent, h.cells r]

/-- The executable exclusivity test reads only cells, so it agrees. -/
theorem exclusive? {Hc Ha : Heap} (h : HeapCompat Hc Ha) (r : Ref) :
    Hc.exclusive? r = Ha.exclusive? r := by
  simp [Heap.exclusive?, h.cells r]

/-- The put-back's branch test reads only cells, so it agrees. -/
theorem inPlace? {Hc Ha : Heap} (h : HeapCompat Hc Ha) (p : Ref) (i : Nat) :
    PutBack.inPlace? Hc p i = PutBack.inPlace? Ha p i := by
  simp [PutBack.inPlace?, h.cells p]

/-- The put-back's disposition reads only cells, so it agrees. -/
theorem disposition? {Hc Ha : Heap} (h : HeapCompat Hc Ha) (p : Ref) (i : Nat) :
    PutBack.disposition? Hc p i = PutBack.disposition? Ha p i := by
  simp [PutBack.disposition?, h.cells p, h.inPlace? p i]

/-- Setting the same cell in both heaps keeps the relation. -/
theorem set {Hc Ha : Heap} (h : HeapCompat Hc Ha) (r : Ref) (o : Obj) :
    HeapCompat (Hc.set r o) (Ha.set r o) := by
  refine ⟨fun q => ?_, by rw [Heap_set_next, Heap_set_next]; exact h.cursor⟩
  by_cases hq : q = r
  · subst hq
    rw [Heap.set_self, Heap.set_self]
  · rw [Heap.set_other _ _ _ _ hq, Heap.set_other _ _ _ _ hq]
    exact h.cells q

/-- The put-back's in-place branch keeps the relation: one cell is rewritten in
both heaps, so nothing is allocated. -/
theorem mutate {Hc Ha : Heap} (h : HeapCompat Hc Ha) (p : Ref) (o : Obj) (i : Nat)
    (c : Ref) : HeapCompat (PutBack.mutate Hc p o i c) (PutBack.mutate Ha p o i c) :=
  h.set p { o with fields := o.fields.setIfInBounds i (.ref c) }

/-- The two heaps are equal when the cursors coincide: the cursor is the
relation's only slack. -/
theorem eq_of_cursor_eq {Hc Ha : Heap} (h : HeapCompat Hc Ha) (hnext : Hc.next = Ha.next) :
    Hc = Ha := by
  cases Hc with
  | mk cc cn =>
    cases Ha with
    | mk ca can =>
      simp only at hnext
      subst hnext
      have hcells : cc = ca := funext h.cells
      rw [hcells]

/-! ### The incoming-edge count

The counted heap's cursor may be one past the abstract one's. Every name in that
extra range holds no cell: `Accounted.domain` bounds the abstract heap's live
cells by its cursor, and the cell agreement carries that to the counted side. An
empty cell contributes no edge, so the two edge counts agree. -/

/-- Dropping entries that are zero from the top of a range leaves the sum
unchanged. -/
theorem sum_range_zero_tail {f : Nat → Nat} {n m : Nat} (hnm : n ≤ m)
    (h : ∀ q, n ≤ q → q < m → f q = 0) :
    ((List.range m).map f).sum = ((List.range n).map f).sum := by
  induction m with
  | zero =>
      have : n = 0 := Nat.le_zero.mp hnm
      subst this
      rfl
  | succ k ih =>
      rcases Nat.lt_or_ge n (k + 1) with hlt | hge
      · have hnk : n ≤ k := Nat.lt_succ_iff.mp hlt
        have hfk : f k = 0 := h k hnk (Nat.lt_succ_self k)
        rw [List.range_succ, List.map_append, List.sum_append, List.map_singleton,
          List.sum_singleton, hfk, Nat.add_zero]
        exact ih hnk (fun q h1 h2 => h q h1 (Nat.lt_trans h2 (Nat.lt_succ_self k)))
      · have hkn : k + 1 = n := Nat.le_antisymm hge hnm
        rw [hkn]

/-- The incoming-edge count is a function of the cells and the cursor, provided
the abstract heap's live cells lie inside its own cursor range: the extra range
the counted cursor covers then holds no cell. The domain condition is exactly
`Accounted.domain`, but it is stated on its own so the chain can spend it at the
model take-out heap, whose accounting is not carried. -/
theorem IncomingCount_of_dom {Hc Ha : Heap} (h : HeapCompat Hc Ha)
    (hdom : ∀ q o, Ha.cells q = some o → q < Ha.next) (r : Ref) :
    IncomingCount Hc r = IncomingCount Ha r := by
  rw [IncomingCount_eq_edges, IncomingCount_eq_edges]
  have htail : ∀ q, Ha.next ≤ q → q < Hc.next → EdgeAt Hc q r = 0 := by
    intro q hq hq'
    have hnone : Ha.cells q = none := by
      cases hqcell : Ha.cells q with
      | none => rfl
      | some o => exact absurd (hdom q o hqcell) (Nat.not_lt.mpr hq)
    simp [EdgeAt, h.cells q, hnone]
  rw [sum_range_zero_tail h.cursor htail]
  exact sum_range_congr (fun q _ => by simp [EdgeAt, h.cells q])

/-- The incoming-edge count is a function of the cells and the cursor: the extra
range the counted cursor covers holds no cell. -/
theorem IncomingCount {support : List Var} {Hc Ha : Heap} {env : Env} {c : Ctx}
    (h : HeapCompat Hc Ha) (hacc : Accounted support Ha env c) (r : Ref) :
    IncomingCount Hc r = IncomingCount Ha r :=
  IncomingCount_of_dom h hacc.domain r

end HeapCompat

/-! ## The call's edge effect -/

/-- The effect a call must have on its caller's heap for the caller's accounting
to survive it: every reference keeps its incoming-edge count, the fresh-name
counter does not go backwards, and no cell appears where the entry had none.

Stored counts alone do not suffice. `PutBack.ChildCall` fixes every stored count
(`ChildCall.rc_eq`) and confines the body to the child's mutable footprint, yet a
body can store a scalar over a `.ref` slot of its own cell and erase an incoming
edge into a caller-owned cell whose stored count is two. The caller's count
equation then fails although every `ChildCall` field holds.
`OwnershipTest/CountedNested.lean` kernel-checks that refusal beside the harmless
rewrite of the same shape, where no edge is erased.

`incoming` is the missing semantic fact; `cursor` and `carrier` carry the
live-cell domain of `Accounted` across the call. With the three,
`accounted_of_edges` derives the caller's accounting at the body's return from
its accounting at the call's entry. -/
structure EdgePreserved (Hin Hout : Heap) : Prop where
  /-- Every reference has as many incoming heap edges after the call as before. -/
  incoming : ∀ r, IncomingCount Hout r = IncomingCount Hin r
  /-- The fresh-name counter advances (or stays): every name the entry used is
  still below the post-call cursor. -/
  cursor : Hin.next ≤ Hout.next
  /-- No cell appears where the call's entry had none. -/
  carrier : ∀ q o, Hout.cells q = some o → ∃ o', Hin.cells q = some o'

namespace EdgePreserved

theorem refl (H : Heap) : EdgePreserved H H :=
  ⟨fun _ => rfl, Nat.le_refl _, fun _ o h => ⟨o, h⟩⟩

theorem trans {H₁ H₂ H₃ : Heap} (h₁₂ : EdgePreserved H₁ H₂)
    (h₂₃ : EdgePreserved H₂ H₃) : EdgePreserved H₁ H₃ where
  incoming r := (h₂₃.incoming r).trans (h₁₂.incoming r)
  cursor := Nat.le_trans h₁₂.cursor h₂₃.cursor
  carrier q o h := by
    obtain ⟨o', h'⟩ := h₂₃.carrier q o h
    obtain ⟨o'', h''⟩ := h₁₂.carrier q o' h'
    exact ⟨o'', h''⟩

/-- The live-cell domain is carried when the entry's cells are inside its own
cursor range. -/
theorem domain_of {Hin Hout : Heap} (h : EdgePreserved Hin Hout)
    (hdom : ∀ q o, Hin.cells q = some o → q < Hin.next) :
    ∀ q o, Hout.cells q = some o → q < Hout.next := by
  intro q o hq
  obtain ⟨o', ho'⟩ := h.carrier q o hq
  exact Nat.lt_of_lt_of_le (hdom q o' ho') h.cursor

/-- A heap-compatible transport is an edge-preserving call effect in the
direction the cursor permits: the input is the heap with the lower cursor and the
output the compatible heap with the higher one. The domain premise is not
removable: `HeapCompat` only bounds the cursors, and a cell at a name the input's
cursor already passed contributes to the output's sum but not to the input's. -/
theorem of_compat {Hin Hout : Heap} (h : HeapCompat Hout Hin)
    (hdom : ∀ q o, Hin.cells q = some o → q < Hin.next) : EdgePreserved Hin Hout where
  incoming r := by
    rw [IncomingCount_eq_edges, IncomingCount_eq_edges]
    have htail : ∀ q, Hin.next ≤ q → q < Hout.next → EdgeAt Hout q r = 0 := by
      intro q hq hq'
      have hnone : Hin.cells q = none := by
        cases hqcell : Hin.cells q with
        | none => rfl
        | some o => exact absurd (hdom q o hqcell) (Nat.not_lt.mpr hq)
      simp [EdgeAt, h.cells q, hnone]
    rw [HeapCompat.sum_range_zero_tail h.cursor htail]
    exact sum_range_congr (fun q _ => by simp [EdgeAt, h.cells q])
  cursor := h.cursor
  carrier q o hq := ⟨o, (h.cells q).symm.trans hq⟩

/-- Rewriting one live cell with an object that holds the same number of `.ref q`
occurrences for every name leaves the incoming-edge count unchanged, so the
rewrite is an edge-preserving call effect. This is the shape of the child body's
in-place scalar store when the slot it overwrites held a scalar. -/
theorem set {H : Heap} {r : Ref} {o o' : Obj} (hcell : H.cells r = some o)
    (hrefs : ∀ q, RefCount o.fields q = RefCount o'.fields q) :
    EdgePreserved H (H.set r o') where
  incoming r' := by
    rw [IncomingCount_eq_edges, IncomingCount_eq_edges]
    exact sum_range_congr (fun q _ => by
      unfold EdgeAt
      by_cases hq : q = r
      · subst hq
        rw [Heap.set_self, hcell]
        exact (hrefs r').symm
      · rw [Heap.set_other H r q o' hq])
  cursor := by rw [PutBack.set_next]; exact Nat.le_refl _
  carrier q oq hq := by
    by_cases hqr : q = r
    · subst hqr
      exact ⟨o, hcell⟩
    · refine ⟨oq, ?_⟩
      rwa [Heap.set_other H r q o' hqr] at hq

end EdgePreserved

/-! ## Carrying the invariant and the accounting across the relation -/

/-- The checker invariant depends on the heap only through counts, liveness and
persistence, so the relation carries it. -/
theorem Inv.of_compat {Hc Ha : Heap} {env : Env} {c : Ctx}
    (hi : Inv Ha env c) (hh : HeapCompat Hc Ha) : Inv Hc env c where
  rc_eq r := by rw [hh.rc r, hi.rc_eq r]
  owned x r hx hr := hi.owned x r hx hr
  borrow x r hx hr := by
    obtain ⟨henv, hlive⟩ := hi.borrow x r hx hr
    exact ⟨henv, by rw [hh.cells r]; exact hlive⟩
  scalar x hx := hi.scalar x hx
  nonPersistent r o hc := hi.nonPersistent r o (by rw [← hh.cells r]; exact hc)

/-- The complete relation is carried too: the enumeration is a context fact, the
live-cell domain is bounded by the abstract cursor, and the count equation's
two sides agree by `HeapCompat.IncomingCount`. -/
theorem Accounted.of_compat {support : List Var} {Hc Ha : Heap} {env : Env} {c : Ctx}
    (h : Accounted support Ha env c) (hh : HeapCompat Hc Ha) :
    Accounted support Hc env c where
  inv := h.inv.of_compat hh
  support_nodup := h.support_nodup
  support_sound := h.support_sound
  support_complete := h.support_complete
  support_bound := h.support_bound
  domain r o hc :=
    Nat.lt_of_lt_of_le (h.domain r o (by rw [← hh.cells r]; exact hc)) hh.cursor
  count r := by
    rw [hh.rc r, h.count r, hh.IncomingCount h r]

/-! ## Derived exclusivity -/

/-- A count-one owned handle is exclusive at any accounted state. This is the
array assertion's and the child assertion's precondition, read off the count
equation rather than assumed: `Inv.rc_eq` turns the checker's count one into the
stored count, and `Inv.nonPersistent` supplies the flag. -/
theorem exclusive_of_accounted {support : List Var} {H : Heap} {env : Env} {c : Ctx}
    (h : Accounted support H env c) {x : Var} {r : Ref}
    (_hx : c.us x = .owned) (_hr : c.refOf x = some r) (hm : c.mult r = 1) :
    Heap.Exclusive H r :=
  h.inv.exclusive hm

/-- The executable form of `exclusive_of_accounted`, for the assertions the
fragment performs. -/
theorem exclusive?_of_accounted {support : List Var} {H : Heap} {env : Env} {c : Ctx}
    (h : Accounted support H env c) {x : Var} {r : Ref}
    (hx : c.us x = .owned) (hr : c.refOf x = some r) (hm : c.mult r = 1) :
    H.exclusive? r = true :=
  (Heap.exclusive?_eq_true).mpr (exclusive_of_accounted h hx hr hm)

/-! ## Carrying the accounting across a call -/

/-- The caller's accounting at the body's return, derived from its accounting at
the call and the call's edge effect.

Every field except `incoming` and the live-cell domain follows from
`PutBack.ChildCall`: the invariant is `ChildCall.inv_caller`, the stored counts
are `ChildCall.rc_eq`, and the enumeration is the context's. The domain follows
from the edge effect's `carrier` and `cursor`. The count equation is where the
edge premise is spent: without it a body that erases an incoming edge leaves the
caller's stored counts consistent but its count equation false. -/
theorem accounted_of_edges {support : List Var} {Hin Hout : Heap} {env : Env}
    {ctx : Ctx} {state path x : Var} {body : Nested.NCode} {p c : Ref}
    (hacc : Accounted support Hin env ctx)
    (hcall : PutBack.ChildCall Hin Hout env ctx state path x body p c)
    (hedges : EdgePreserved Hin Hout) : Accounted support Hout env ctx where
  inv := PutBack.ChildCall.inv_caller hcall hacc
  support_nodup := hacc.support_nodup
  support_sound := hacc.support_sound
  support_complete := hacc.support_complete
  support_bound := hacc.support_bound
  domain := hedges.domain_of hacc.domain
  count r := by
    calc Hout.rc r = Hin.rc r := PutBack.ChildCall.rc_eq hcall hacc r
      _ = IncomingCount Hin r + EnvOwnerCount ctx support r := hacc.count r
      _ = IncomingCount Hout r + EnvOwnerCount ctx support r := by
        rw [hedges.incoming r]

end Ownership

namespace Ownership

/-! ## The counted take-out

`CountedPair.protocol` runs the captured take-out, the two projection
increments and the pair's unique decrement. This section carries `Accounted`
from the entry to that boundary and records the heap facts the chain needs.

Two side conditions the checker cannot see are derived rather than assumed:
the parent is a live cell inside the cursor range (`Accounted.domain`), and the
extracted child's cell is live because its count is one (`Inv.rc_ne_zero`), so
neither endpoint can be the fresh name the pair occupies. -/

namespace HeapCompat

/-- Counting up keeps the relation: both heaps rewrite the same cell. -/
theorem inc {Hc Ha : Heap} (h : HeapCompat Hc Ha) (r : Ref) (n : Nat) :
    HeapCompat (Hc.inc r n) (Ha.inc r n) := by
  refine ⟨fun q => ?_, by rw [Heap_inc_next, Heap_inc_next]; exact h.cursor⟩
  unfold Heap.inc
  rw [h.cells r]
  cases hcell : Ha.cells r with
  | none => exact h.cells q
  | some o =>
      by_cases hq : q = r
      · subst hq; simp [Heap.set]
      · simp [Heap.set, hq, h.cells q]

/-- Counting down keeps the relation. -/
theorem dec {Hc Ha : Heap} (h : HeapCompat Hc Ha) (r : Ref) (n : Nat) :
    HeapCompat (Hc.dec r n) (Ha.dec r n) := by
  refine ⟨fun q => ?_, by rw [Heap_dec_next, Heap_dec_next]; exact h.cursor⟩
  unfold Heap.dec
  rw [h.cells r]
  cases hcell : Ha.cells r with
  | none => exact h.cells q
  | some o =>
      by_cases hq : q = r
      · subst hq; simp [Heap.set]
      · simp [Heap.set, hq, h.cells q]

end HeapCompat

/-- The take-out's placeholder write keeps the cursor. -/
theorem setPlaceholder_next (H : Heap) (p : Ref) (i : Nat) :
    (CountedPair.setPlaceholder H p i).next = H.next := by
  unfold CountedPair.setPlaceholder
  split
  · exact PutBack.set_next H _ _
  · rfl

/-- The pair allocation advances the cursor by one. -/
theorem allocPair_next (H : Heap) (p c : Ref) :
    (CountedPair.allocPair H p c).next = H.next + 1 :=
  PutBack.alloc_next H _

/-- The take-out advances the cursor by one: only the pair is allocated. -/
theorem takeOut_next (H : Heap) (p c : Ref) (i : Nat) :
    (CountedPair.takeOut H p c i).2.next = H.next + 1 := by
  show (CountedPair.setPlaceholder (CountedPair.allocPair H p c) p i).next = _
  rw [setPlaceholder_next, allocPair_next]

/-- The two projection increments keep the cursor. -/
theorem pairInc_next (H : Heap) (p c : Ref) :
    (CountedPair.pairInc H p c).next = H.next := by
  unfold CountedPair.pairInc
  rw [PutBack.inc_next, PutBack.inc_next]

/-- Releasing the pair's two edges keeps the cursor. -/
theorem pairFree_next (H : Heap) (p c pair : Ref) :
    (CountedPair.pairFree H p c pair).next = H.next := by
  show ((H.dec p 1).dec c 1).next = H.next
  rw [PutBack.dec_next, PutBack.dec_next]

/-- The protocol boundary's cursor is the entry's plus one, the pair's name. -/
theorem protocol_next {H : Heap} {p c : Ref} {i : Nat}
    (hpn : p ≠ H.next) (hcn : c ≠ H.next) :
    (CountedPair.protocol H p c i).2.next = H.next + 1 := by
  show (CountedPair.pairTraffic (CountedPair.takeOut H p c i).2 H.next).next = _
  rw [CountedPair.pairTraffic_takeOut hpn hcn, pairFree_next, pairInc_next, takeOut_next]

/-- The counted take-out, carried through `CountedPair.protocol`.

The abstract take-out heap is the model's own transition (the placeholder write),
and the counted heap is related to it by `HeapCompat`: the pair's allocation and
its release leave every cell where the model's write leaves it, with the cursor
one higher. The accounting holds at the boundary context the checker's take-out
rule produces. -/
theorem counted_takeOut {support : List Var} {H : Heap} {env : Env} {c : Ctx}
    (h : Accounted support H env c) {a fst snd e : Var} {r : Ref} {o : Obj} {idx : Nat}
    (ha : c.us a = .owned) (hma : c.multOf a = 1) (hr : c.refOf a = some r)
    (he : c.mult e = 1) (hfst : c.us fst ≠ .owned) (hsnd : c.us snd ≠ .owned)
    (hfs : fst ≠ snd) (her : e ≠ r) (hcell : H.cells r = some o)
    (hslot : o.fields[idx]? = some (.ref e)) :
    let B := CountedPair.protocol H r e idx
    Accounted (snd :: replaceVar support a fst) B.2
        ((env.set fst (.ref r)).set snd (.ref e)) ((c.move a fst).bindOwned snd e)
      ∧ HeapCompat B.2 (H.set r { o with fields := o.fields.setIfInBounds idx (.scalar 0) })
      ∧ B.2.cells H.next = none
      ∧ B.2.next = H.next + 1
      ∧ B.2.cells r = some { o with fields := o.fields.setIfInBounds idx (.scalar 0) } := by
  have hrn : r < H.next := h.domain r o hcell
  have hpn : r ≠ H.next := Nat.ne_of_lt hrn
  have hene : H.cells e ≠ none :=
    h.inv.rc_ne_zero (by rw [he]; exact Nat.le_refl 1)
  obtain ⟨oc, hCcell⟩ : ∃ oc, H.cells e = some oc := by
    cases hc : H.cells e with
    | none => exact absurd hc hene
    | some oc => exact ⟨oc, rfl⟩
  have hen : e < H.next := h.domain e oc hCcell
  have hcn : e ≠ H.next := Nat.ne_of_lt hen
  have hre : r ≠ e := fun hh => her hh.symm
  have hfresh : H.cells H.next = none := by
    cases hc : H.cells H.next with
    | none => rfl
    | some o' => exact absurd (h.domain H.next o' hc) (Nat.lt_irrefl _)
  have hb := CountedPair.protocol_boundary (H := H) (p := r) (c := e) (i := idx)
    (op := o) (oc := oc) hcell hCcell hre hpn hcn
  dsimp only at hb
  obtain ⟨-, hparent, hchild, hpair, -, -, -, -⟩ := hb
  have hpair' : (CountedPair.protocol H r e idx).2.cells H.next = none := hpair
  have htraffic : (CountedPair.protocol H r e idx).2 =
      CountedPair.pairFree (CountedPair.pairInc (CountedPair.takeOut H r e idx).2 r e)
        r e H.next := by
    show CountedPair.pairTraffic (CountedPair.takeOut H r e idx).2 H.next = _
    exact CountedPair.pairTraffic_takeOut hpn hcn
  have hcompat : HeapCompat (CountedPair.protocol H r e idx).2
      (H.set r { o with fields := o.fields.setIfInBounds idx (.scalar 0) }) := by
    refine ⟨fun q => ?_, ?_⟩
    · by_cases hqr : q = r
      · rw [hqr, hparent, Heap.set_self]
      · by_cases hqe : q = e
        · rw [hqe, hchild, Heap.set_other H r e _ (Ne.symm hre), hCcell]
        · by_cases hqn : q = H.next
          · rw [hqn, hpair', Heap.set_other H r H.next _ (Ne.symm hpn), hfresh]
          · rw [htraffic, CountedPair.pairFree_inc_cells_other hqr hqe hqn]
            show (CountedPair.setPlaceholder (CountedPair.allocPair H r e) r idx).cells q = _
            rw [CountedPair.setPlaceholder_cells_other hqr,
              CountedPair.allocPair_cells_other hqn, Heap.set_other H r q _ hqr]
    · rw [protocol_next hpn hcn, PutBack.set_next]
      exact Nat.le_succ H.next
  exact ⟨Accounted.of_compat (Accounted.takeOutOfSlot h ha hma hr he hfst hsnd hfs her
      hcell hslot) hcompat, hcompat, hpair, protocol_next hpn hcn, hparent⟩

/-! ## The restoration boundary, from accounting

`PutBack.restorationBoundary_of_entry` takes the entry's cells, counts,
persistence and slot. At an accounted state those are derivable: the parent's
count one is the checker's count-one handle read through `Inv.rc_eq`, the
persistence flag is `Inv.nonPersistent`, and the entry's two components are
different cells because the array's own slot holds the extracted element, which
the count equation cannot pay for twice. -/

theorem restorationBoundary_of_accounted {support : List Var} {H : Heap} {env : Env}
    {c : Ctx} (h : Accounted support H env c) {a e : Var} {r : Ref} {o : Obj} {idx : Nat}
    (ha : c.us a = .owned) (hma : c.multOf a = 1) (hr : c.refOf a = some r)
    (he : c.mult e = 1) (hcell : H.cells r = some o)
    (hslot : o.fields[idx]? = some (.ref e)) :
    ∃ oc, PutBack.Boundary (CountedPair.protocol H r e idx).2 r e idx o oc := by
  have hmr : c.mult r = 1 := by
    have h1 := hma
    unfold Ctx.multOf at h1
    rw [hr] at h1
    exact h1
  have hrc : o.rc = 1 := by
    have h1 : H.rc r = c.mult r := h.inv.rc_eq r
    rw [CountedPair.rc_of_cells hcell, hmr] at h1
    exact h1
  have hpers : o.persistent = false := h.inv.nonPersistent r o hcell
  have hlt : idx < o.fields.size := (Array.getElem?_eq_some_iff.mp hslot).1
  have hene : H.cells e ≠ none := h.inv.rc_ne_zero (by rw [he]; exact Nat.le_refl 1)
  obtain ⟨oc, hCcell⟩ : ∃ oc, H.cells e = some oc := by
    cases hc : H.cells e with
    | none => exact absurd hc hene
    | some oc => exact ⟨oc, rfl⟩
  have hcrc : oc.rc = 1 := by
    have h1 : H.rc e = c.mult e := h.inv.rc_eq e
    rw [CountedPair.rc_of_cells hCcell, he] at h1
    exact h1
  have hcpers : oc.persistent = false := h.inv.nonPersistent e oc hCcell
  have hpc : r ≠ e := by
    intro hre
    have hinc : IncomingCount H e = 1 := h.incoming_eq_one_of_slot he hcell hslot
    have hEpos : 1 ≤ EnvOwnerCount c support e := by
      have hamem : a ∈ support := h.support_complete a ha
      have hrefe : c.refOf a = some e := by rw [hr, hre]
      have hfil : a ∈ support.filter (fun z => c.us z = .owned ∧ c.refOf z = some e) := by
        rw [List.mem_filter]
        exact ⟨hamem, by simp [ha, hrefe]⟩
      exact List.length_pos_iff_exists_mem.mpr ⟨a, hfil⟩
    have hsum := h.mult_eq e
    rw [he, hinc] at hsum
    have hz : EnvOwnerCount c support e = 0 := by omega
    omega
  have hpn : r ≠ H.next := Nat.ne_of_lt (h.domain r o hcell)
  have hcn : e ≠ H.next := Nat.ne_of_lt (h.domain e oc hCcell)
  exact ⟨oc, PutBack.restorationBoundary_of_entry hcell hCcell hrc hcrc hpers hcpers hslot hpc hpn hcn⟩

/-! ## The child call's contract

`PutBack.ChildCall` states the call's boundary: admission, checking from the
isolated context, the caller's invariant, the annotations, the extraction
obligations, the parent's separation and the body's outcome. The counted
contract adds exactly one field — the call's edge effect on the caller's heap,
`EdgePreserved Hin Hout` — which is the semantic fact a counted body is
responsible for and which the boundary alone does not imply. Everything else
stays derived: the suspended parent's cell (`ChildCall.parent`), its count, the
child's exclusivity, the caller's invariant at the body's return
(`ChildCall.inv_caller`), the stored counts (`ChildCall.rc_eq`) and the result
binding are consequences.

The edge effect is not derived by the finite-path induction: the induction in
`OwnershipLcnf/PathRecursion.lean` derives ordinary `ChildContract` at every
level, while `edges` is an explicit premise of every theorem that consumes this
structure. The caller's accounting at the body's return is *not* a field: it is
`accounted_of`, derived from this structure, its `call`, and the caller's own
accounting at the call. For the emitted recursive callee the edge effect is not
available at all. -/
structure CountedChildCall (Hin Hout : Heap) (env : Env) (ctx : Ctx)
    (state path x : Var) (body : Nested.NCode) (p c : Ref)
    (support : List Var) : Prop where
  /-- The child call's boundary, unchanged from `Ownership.PutBack`. -/
  call : PutBack.ChildCall Hin Hout env ctx state path x body p c
  /-- The call's effect on the caller's incoming edges, cursor and cell carrier. -/
  edges : EdgePreserved Hin Hout

/-- The caller's complete accounting at the body's return, derived from its
accounting at the call and the call's edge effect. The structure does not carry
the caller's accounting, so it is an argument. -/
theorem CountedChildCall.accounted_of {Hin Hout : Heap} {env : Env} {ctx : Ctx}
    {state path x : Var} {body : Nested.NCode} {p c : Ref} {support : List Var}
    (h : CountedChildCall Hin Hout env ctx state path x body p c support)
    (hacc : Accounted support Hin env ctx) : Accounted support Hout env ctx :=
  accounted_of_edges hacc h.call h.edges

/-- The call's result binding, derived from the accounting: the checker's
`.callAt` rule moves the state's handle to the result variable, and the
enumeration follows the handle. The two context facts the rule supplies are
premises because the structure describes the body, not the caller's rule. -/
theorem CountedChildCall.move {Hin Hout : Heap} {env : Env} {ctx : Ctx}
    {state path x : Var} {body : Nested.NCode} {p c : Ref} {support : List Var}
    (h : CountedChildCall Hin Hout env ctx state path x body p c support)
    (hacc : Accounted support Hin env ctx) {result : Var}
    (howned : ctx.us state = .owned) (href : ctx.refOf state = some c)
    (hdead : ctx.us result ≠ .owned) :
    Accounted (replaceVar support state result) Hout (env.set result (.ref c))
      (ctx.move state result) :=
  (h.accounted_of hacc).move howned href hdead

/-! ## Restoration

The put-back takes the mutate branch on the heap the child call leaves: the
parent cell there is the take-out's placeholder-filled cell, at count one and
non-persistent, with the index in bounds. The branch selection and the functional
restoration are `PutBack`'s; the accounting is `Accounted.putBack` at the
counted heap, whose multiplicity facts come from the relation at the body's
return rather than from further premises. The copy branch is not special-cased:
a parent that is not exclusive selects it, and `OwnershipTest/PutBack.lean` and
`OwnershipTest/CountedNested.lean` exercise both. -/

theorem counted_restore {support : List Var} {Hc Hout : Heap} {envc env : Env}
    {ctxt ctx : Ctx} {fst result restored : Var} {r eR : Ref} {o oc : Obj} {idx : Nat}
    {state path x : Var} {body : Nested.NCode}
    (hb : PutBack.Boundary Hc r eR idx o oc)
    (hcall : PutBack.ChildCall Hc Hout envc ctxt state path x body r eR)
    (hacc : Accounted support Hout env ctx)
    (ha : ctx.us fst = .owned) (hr : ctx.refOf fst = some r)
    (he : ctx.us result = .owned) (hre : ctx.refOf result = some eR)
    (hres : ctx.us restored ≠ .owned)
    (hea : result ≠ fst) (hrer : result ≠ restored) :
    PutBack.disposition? Hout r idx = some .mutate
      ∧ PutBack.putBack Hout r idx eR =
          some (r, PutBack.mutate Hout r (PutBack.parentAfter o idx) idx eR)
      ∧ Accounted ((replaceVar support fst restored).erase result)
          (PutBack.mutate Hout r (PutBack.parentAfter o idx) idx eR)
          (env.set restored (.ref r))
          ((ctx.move fst restored).setUs result .dead) := by
  have hparent := hb.parent_after_call hcall
  have hlt : idx < o.fields.size := hb.index
  have hrc : (PutBack.parentAfter o idx).rc = 1 := by
    simpa [PutBack.parentAfter] using hb.parent_rc
  have hpers : (PutBack.parentAfter o idx).persistent = false := by
    simpa [PutBack.parentAfter] using hb.parent_persistent
  have hslot : (PutBack.parentAfter o idx).fields[idx]? = some (.scalar 0) :=
    Array.getElem?_setIfInBounds_self_of_lt hlt
  have hrmult : ctx.mult r = 1 := by
    have h1 : ctx.mult r = Hout.rc r := (hacc.inv.rc_eq r).symm
    rw [h1, CountedPair.rc_of_cells hparent, hrc]
  have hrmultE : ctx.mult eR = 1 := by
    have h1 : ctx.mult eR = Hout.rc eR := (hacc.inv.rc_eq eR).symm
    have h2 : Hout.rc eR = Hc.rc eR := hcall.child_rc
    have h3 : Hc.rc eR = oc.rc := CountedPair.rc_of_cells hb.child
    rw [h1, h2, h3, hb.child_rc]
  have hma : ctx.multOf fst = 1 := by
    unfold Ctx.multOf
    rw [hr]
    exact hrmult
  have hme : ctx.multOf result = 1 := by
    unfold Ctx.multOf
    rw [hre]
    exact hrmultE
  have hacc' := Accounted.putBack hacc ha hma hr he hme hre hres hea hrer hparent hslot
  refine ⟨PutBack.disposition_mutate_of_boundary hb hcall,
    PutBack.putBack_mutate_of_boundary hb hcall, ?_⟩
  simpa [Array.set!, PutBack.mutate] using hacc'

/-! ## Running the model on either heap

`run_compat` relates the model language's own run at the two heaps. Cell
agreement is not preserved by allocation: the `.setArr` copy branch allocates at
the heap's own cursor (`Ownership/Code.lean:142-152`), so two heaps whose cells
agree but whose cursors differ would put the fresh cell at different names. The
theorem therefore takes the run's copy-freedom — every recorded write flag is
`true`, i.e. every store took the in-place branch — and nothing allocates. The
premise is exactly what a child call's trace supplies (`ChildCall.writes_exclusive`),
and it is a premise on the *counted* side only; the write equalities in the
conclusion are derived by induction, not assumed on the abstract side. -/

/-- The relation on results: an identical environment, value (or fault) and
write trace, with the two heaps related by `HeapCompat`. -/
def ResCompat : Res → Res → Prop
  | .done Hc envc vc wsc, .done Ha enva va wsa =>
      envc = enva ∧ vc = va ∧ wsc = wsa ∧ HeapCompat Hc Ha
  | .fault Hc envc fc wsc, .fault Ha enva fa wsa =>
      envc = enva ∧ fc = fa ∧ wsc = wsa ∧ HeapCompat Hc Ha
  | _, _ => False

namespace ResCompat

/-- Appending one write record to related runs keeps them related. -/
theorem addWrite {r₁ r₂ : Res} (h : ResCompat r₁ r₂) (w : Write) :
    ResCompat (r₁.addWrite w) (r₂.addWrite w) := by
  rcases r₁ with ⟨H1, e1, v1, w1⟩ | ⟨H1, e1, f1, w1⟩ <;>
    rcases r₂ with ⟨H2, e2, v2, w2⟩ | ⟨H2, e2, f2, w2⟩ <;>
    simp_all [Res.addWrite, ResCompat]

/-- Prepending a body's write trace keeps related runs related. -/
theorem addWrites {r₁ r₂ : Res} (h : ResCompat r₁ r₂) (ws : List Write) :
    ResCompat (Nested.addWrites r₁ ws) (Nested.addWrites r₂ ws) := by
  rcases r₁ with ⟨H1, e1, v1, w1⟩ | ⟨H1, e1, f1, w1⟩ <;>
    rcases r₂ with ⟨H2, e2, v2, w2⟩ | ⟨H2, e2, f2, w2⟩ <;>
    simp_all [Nested.addWrites, ResCompat]

end ResCompat

/-- The write trace of a run extended by one write record. -/
theorem writes_addWrite (r : Res) (w : Write) :
    (r.addWrite w).writes = w :: r.writes := by
  cases r <;> rfl

/-- The write trace of a run preceded by a body's trace. -/
theorem writes_addWrites (r : Res) (ws : List Write) :
    (Nested.addWrites r ws).writes = ws ++ r.writes := by
  cases r <;> rfl

/-- A copy-free trace's suffix is copy-free. -/
theorem noCopy_tail {w : Write} {ws : List Write}
    (h : ∀ w' ∈ w :: ws, w'.2 = true) : ∀ w' ∈ ws, w'.2 = true :=
  fun w' hw => h w' (List.mem_cons_of_mem w hw)

/-- Both halves of a copy-free concatenated trace are copy-free. -/
theorem noCopy_append {ws ws' : List Write} (h : ∀ w ∈ ws ++ ws', w.2 = true) :
    (∀ w ∈ ws, w.2 = true) ∧ (∀ w ∈ ws', w.2 = true) :=
  ⟨fun w hw => h w (List.mem_append_left _ hw),
   fun w hw => h w (List.mem_append_right _ hw)⟩

/-- Related heaps give related faults at the same environment, fault and trace. -/
theorem ResCompat.fault {Hc Ha : Heap} {env : Env} {f : Fault} {ws : List Write}
    (hc : HeapCompat Hc Ha) : ResCompat (.fault Hc env f ws) (.fault Ha env f ws) :=
  ⟨rfl, rfl, rfl, hc⟩

/-- The fault case of `ResCompat`, as a rewrite rule for the discharge of the
branches that fault identically on both sides. -/
@[simp] theorem resCompat_fault_iff {Hc Ha : Heap} {env₁ env₂ : Env} {f₁ f₂ : Fault}
    {ws₁ ws₂ : List Write} :
    (ResCompat (.fault Hc env₁ f₁ ws₁) (.fault Ha env₂ f₂ ws₂)) ↔
      (env₁ = env₂ ∧ f₁ = f₂ ∧ ws₁ = ws₂ ∧ HeapCompat Hc Ha) := Iff.rfl

/-- A `Bool` that is not `true` is `false`. -/
theorem bool_eq_false_of_ne_true {b : Bool} (h : ¬ b = true) : b = false := by
  cases b with
  | false => rfl
  | true => exact absurd rfl h

/-- The model language's run agrees across the relation, for copy-free runs. -/
theorem run_compat {Hc Ha : Heap} {env : Env} {code : Code}
    (hc : HeapCompat Hc Ha)
    (hnoCopy : ∀ w ∈ (run code env Hc).writes, w.2 = true) :
    ResCompat (run code env Hc) (run code env Ha) := by
  induction code generalizing env Hc Ha with
  | «let» x v k ih =>
      cases v with
      | lit n =>
          simpa only [run] using
            ih (env := env.set x (.scalar n)) hc (by simpa [run] using hnoCopy)
      | size a =>
          simp only [run]
          cases ha : env a with
          | none => simpa [ha, resCompat_fault_iff] using hc
          | some va =>
              cases va with
              | ref r =>
                  cases hcell : Hc.cells r with
                  | none =>
                      have hcellA : Ha.cells r = none := by rw [← hc.cells r]; exact hcell
                      simpa [hcell, hcellA, resCompat_fault_iff] using hc
                  | some o =>
                      have hcellA : Ha.cells r = some o := by rw [← hc.cells r]; exact hcell
                      simp only [hcell, hcellA]
                      exact ih hc (by simpa [run, ha, hcell] using hnoCopy)
              | scalar n => simpa [ha, resCompat_fault_iff] using hc
              | erased => simpa [ha, resCompat_fault_iff] using hc
      | isShared y =>
          simp only [run]
          cases hy : env y with
          | none => simpa [hy, resCompat_fault_iff] using hc
          | some vy =>
              cases vy with
              | ref r =>
                  dsimp only
                  rw [hc.rc r]
                  exact ih hc (by simpa [run, hy, hc.rc r] using hnoCopy)
              | scalar n => simpa [hy, resCompat_fault_iff] using hc
              | erased => simpa [hy, resCompat_fault_iff] using hc
      | checkAlias y =>
          simp only [run]
          cases hy : env y with
          | none => simpa [hy, resCompat_fault_iff] using hc
          | some vy =>
              cases vy with
              | ref r =>
                  dsimp only
                  rw [hc.exclusive? r]
                  by_cases hex : Ha.exclusive? r = true
                  · simp only [hex]
                    exact ih hc (by simpa [run, hy, hc.exclusive? r, hex] using hnoCopy)
                  · simp only [bool_eq_false_of_ne_true hex]
                    exact ResCompat.fault hc
              | scalar n => simpa [hy, resCompat_fault_iff] using hc
              | erased => simpa [hy, resCompat_fault_iff] using hc
  | inc x n k ih =>
      simp only [run]
      cases hx : env x with
      | none => simpa [hx, resCompat_fault_iff] using hc
      | some vx =>
          cases vx with
          | ref r =>
              dsimp only
              exact ih (hc := hc.inc r n) (by simpa [run, hx] using hnoCopy)
          | scalar m => simpa [hx, resCompat_fault_iff] using hc
          | erased => simpa [hx, resCompat_fault_iff] using hc
  | dec x n k ih =>
      simp only [run]
      cases hx : env x with
      | none => simpa [hx, resCompat_fault_iff] using hc
      | some vx =>
          cases vx with
          | ref r =>
              dsimp only
              exact ih (hc := hc.dec r n) (by simpa [run, hx] using hnoCopy)
          | scalar m => simpa [hx, resCompat_fault_iff] using hc
          | erased => simpa [hx, resCompat_fault_iff] using hc
  | check x k ih =>
      simp only [run]
      cases hx : env x with
      | none => simpa [hx, resCompat_fault_iff] using hc
      | some vx =>
          cases vx with
          | ref r =>
              dsimp only
              rw [hc.exclusive? r]
              by_cases hex : Ha.exclusive? r = true
              · simp only [hex]
                exact ih hc (by simpa [run, hx, hc.exclusive? r, hex] using hnoCopy)
              · simp only [bool_eq_false_of_ne_true hex]
                exact ResCompat.fault hc
          | scalar m => simpa [hx, resCompat_fault_iff] using hc
          | erased => simpa [hx, resCompat_fault_iff] using hc
  | setArr x i v k ih =>
      simp only [run]
      cases hx : env x with
      | none => simpa [hx, resCompat_fault_iff] using hc
      | some vx =>
        cases vx with
        | scalar m => simpa [hx, resCompat_fault_iff] using hc
        | erased => simpa [hx, resCompat_fault_iff] using hc
        | ref r =>
          cases hi : env i with
          | none => simpa [hx, hi, resCompat_fault_iff] using hc
          | some vi =>
            cases vi with
            | ref r₂ => simpa [hx, hi, resCompat_fault_iff] using hc
            | erased => simpa [hx, hi, resCompat_fault_iff] using hc
            | scalar idx =>
              cases hv : env v with
              | none => simpa [hx, hi, hv, resCompat_fault_iff] using hc
              | some vv =>
                cases vv with
                | ref r₃ => simpa [hx, hi, hv, resCompat_fault_iff] using hc
                | erased => simpa [hx, hi, hv, resCompat_fault_iff] using hc
                | scalar val =>
                  cases hcell : Hc.cells r with
                  | none =>
                      have hcellA : Ha.cells r = none := by rw [← hc.cells r]; exact hcell
                      simpa [hx, hi, hv, hcell, hcellA, resCompat_fault_iff] using hc
                  | some o =>
                    have hcellA : Ha.cells r = some o := by rw [← hc.cells r]; exact hcell
                    simp only [hcell, hcellA]
                    rw [hc.exclusive? r]
                    by_cases hex : Ha.exclusive? r = true
                    · simp only [hex]
                      have hrun : (run (.setArr x i v k) env Hc).writes =
                          (r, true) :: (run k (env.set x (.ref r))
                            (Hc.set r { o with fields := o.fields.set! idx (.scalar val) })).writes := by
                        simp [run, hx, hi, hv, hcell, hc.exclusive? r, hex, writes_addWrite]
                      have hprem : ∀ w ∈ (run k (env.set x (.ref r))
                          (Hc.set r { o with fields := o.fields.set! idx (.scalar val) })).writes,
                          w.2 = true :=
                        fun w hw => hnoCopy w (by rw [hrun]; exact List.mem_cons_of_mem _ hw)
                      exact ResCompat.addWrite
                        (ih (hc := hc.set r { o with fields := o.fields.set! idx (.scalar val) })
                          hprem)
                        (r, true)
                    · exfalso
                      have hcopy : (run (.setArr x i v k) env Hc).writes =
                          (r, false) :: (run k
                            (env.set x (.ref (Hc.alloc (o.fields.set! idx (.scalar val))).1))
                            ((Hc.alloc (o.fields.set! idx (.scalar val))).2.dec r 1)).writes := by
                        simp [run, hx, hi, hv, hcell, hc.exclusive? r,
                          bool_eq_false_of_ne_true hex, writes_addWrite]
                      have hmem : (r, false) ∈ (run (.setArr x i v k) env Hc).writes := by
                        rw [hcopy]
                        exact List.mem_cons_self
                      exact absurd (hnoCopy (r, false) hmem) (by simp)
  | ret x => simp only [run]; exact ⟨rfl, rfl, rfl, hc⟩

/-- The nested interpreter's run agrees across the relation, for copy-free runs.
`NCode.base` delegates to `run_compat`; the take-out and the put-back are field
writes, so they preserve the relation; the recursive call runs the body on the
isolated environment and its continuation on whatever heap the body leaves, so
the induction is applied at those heaps. Every fault branch carries the same
fault on both sides. -/
theorem runN_compat {Hc Ha : Heap} {env : Env} {c : Nested.NCode}
    (hc : HeapCompat Hc Ha)
    (hnoCopy : ∀ w ∈ (Nested.runN c env Hc).writes, w.2 = true) :
    ResCompat (Nested.runN c env Hc) (Nested.runN c env Ha) := by
  induction c generalizing env Hc Ha with
  | base code =>
      exact run_compat hc (by simpa [Nested.runN] using hnoCopy)
  | takeOut a i fst snd e k ih =>
      simp only [Nested.runN]
      cases ha : env a with
      | none => simpa [ha, resCompat_fault_iff] using hc
      | some va =>
        cases va with
        | scalar n => simpa [ha, resCompat_fault_iff] using hc
        | erased => simpa [ha, resCompat_fault_iff] using hc
        | ref r =>
          cases hi : env i with
          | none => simpa [ha, hi, resCompat_fault_iff] using hc
          | some vi =>
            cases vi with
            | ref r₂ => simpa [ha, hi, resCompat_fault_iff] using hc
            | erased => simpa [ha, hi, resCompat_fault_iff] using hc
            | scalar idx =>
              cases hcell : Hc.cells r with
              | none =>
                  have hcellA : Ha.cells r = none := by rw [← hc.cells r]; exact hcell
                  simpa [hcell, hcellA, resCompat_fault_iff] using hc
              | some o =>
                have hcellA : Ha.cells r = some o := by rw [← hc.cells r]; exact hcell
                cases hslot : o.fields[idx]? with
                | none => simpa [hcell, hcellA, hslot, resCompat_fault_iff] using hc
                | some v =>
                  cases v with
                  | ref e' =>
                    by_cases heq : e' = e
                    · simp only [hcell, hcellA, hslot, heq]
                      exact ih (hc := hc.set r { o with fields := o.fields.setIfInBounds idx (.scalar 0) })
                        (by simpa [Nested.runN, ha, hi, hcell, hslot, heq] using hnoCopy)
                    · simp only [hcell, hcellA, hslot, heq]
                      exact ResCompat.fault hc
                  | scalar n => simpa [hcell, hcellA, hslot, resCompat_fault_iff] using hc
                  | erased => simpa [hcell, hcellA, hslot, resCompat_fault_iff] using hc
  | putBack a e i result k ih =>
      simp only [Nested.runN]
      cases ha : env a with
      | none => simpa [ha, resCompat_fault_iff] using hc
      | some va =>
        cases va with
        | scalar n => simpa [ha, resCompat_fault_iff] using hc
        | erased => simpa [ha, resCompat_fault_iff] using hc
        | ref r =>
          cases he' : env e with
          | none => simpa [ha, he', resCompat_fault_iff] using hc
          | some ve =>
            cases ve with
            | scalar n => simpa [ha, he', resCompat_fault_iff] using hc
            | erased => simpa [ha, he', resCompat_fault_iff] using hc
            | ref eR =>
              cases hi : env i with
              | none => simpa [ha, he', hi, resCompat_fault_iff] using hc
              | some vi =>
                cases vi with
                | ref r₂ => simpa [ha, he', hi, resCompat_fault_iff] using hc
                | erased => simpa [ha, he', hi, resCompat_fault_iff] using hc
                | scalar idx =>
                  cases hcell : Hc.cells r with
                  | none =>
                      have hcellA : Ha.cells r = none := by rw [← hc.cells r]; exact hcell
                      simpa [hcell, hcellA, resCompat_fault_iff] using hc
                  | some o =>
                    have hcellA : Ha.cells r = some o := by rw [← hc.cells r]; exact hcell
                    simp only [hcell, hcellA]
                    exact ih (hc := hc.set r { o with fields := o.fields.set! idx (.ref eR) })
                      (by simpa [Nested.runN, ha, he', hi, hcell] using hnoCopy)
  | callAt state path x result body k ihbody ihk =>
      simp only [Nested.runN]
      cases hs : env state with
      | none => simpa [hs, resCompat_fault_iff] using hc
      | some vs =>
        cases vs with
        | scalar n => simpa [hs, resCompat_fault_iff] using hc
        | erased => simpa [hs, resCompat_fault_iff] using hc
        | ref r =>
          cases hp : env path with
          | none => simpa [hs, hp, resCompat_fault_iff] using hc
          | some vp =>
            cases vp with
            | ref r₂ => simpa [hs, hp, resCompat_fault_iff] using hc
            | erased => simpa [hs, hp, resCompat_fault_iff] using hc
            | scalar pv =>
              cases hx : env x with
              | none => simpa [hs, hp, hx, resCompat_fault_iff] using hc
              | some vx =>
                cases vx with
                | ref r₃ => simpa [hs, hp, hx, resCompat_fault_iff] using hc
                | erased => simpa [hs, hp, hx, resCompat_fault_iff] using hc
                | scalar xv =>
                  dsimp only
                  rw [hc.exclusive? r]
                  by_cases hex : Ha.exclusive? r = true
                  · simp only [hex]
                    have hbodyPre : ∀ w ∈ (Nested.runN body
                        (Nested.isolateEnv env state path x) Hc).writes, w.2 = true := by
                      intro w hw
                      refine hnoCopy w ?_
                      cases hb : Nested.runN body (Nested.isolateEnv env state path x) Hc with
                      | done H' envb vb wsb =>
                          rw [hb] at hw
                          have hmem : w ∈ wsb ++ (Nested.runN k
                              (env.set result (.ref r)) H').writes :=
                            List.mem_append.mpr (Or.inl hw)
                          simpa [Nested.runN, hs, hp, hx, hc.exclusive? r, hex, hb,
                            writes_addWrites] using hmem
                      | fault H' envb f wsb =>
                          rw [hb] at hw
                          simpa [Nested.runN, hs, hp, hx, hc.exclusive? r, hex, hb] using hw
                    cases hb : Nested.runN body (Nested.isolateEnv env state path x) Hc with
                    | done H' envb vb wsb =>
                        have hcomp :=
                          ihbody (env := Nested.isolateEnv env state path x) hc hbodyPre
                        rw [hb] at hcomp
                        cases ha' : Nested.runN body (Nested.isolateEnv env state path x) Ha with
                        | done H'a envb' vb' wsb' =>
                            rw [ha'] at hcomp
                            obtain ⟨he, hv, hw, hch⟩ := hcomp
                            subst he
                            subst hv
                            subst hw
                            have hkPre : ∀ w ∈ (Nested.runN k
                                (env.set result (.ref r)) H').writes, w.2 = true := by
                              intro w hw'
                              refine hnoCopy w ?_
                              have hmem : w ∈ wsb ++ (Nested.runN k
                                  (env.set result (.ref r)) H').writes :=
                                List.mem_append.mpr (Or.inr hw')
                              simpa [Nested.runN, hs, hp, hx, hc.exclusive? r, hex, hb,
                                writes_addWrites] using hmem
                            dsimp only
                            exact ResCompat.addWrites
                              (ihk (env := env.set result (.ref r)) hch hkPre) wsb
                        | fault H'a envb' f' wsb' =>
                            rw [ha'] at hcomp
                            exact absurd hcomp (by simp [ResCompat])
                    | fault H' envb f wsb =>
                        have hcomp :=
                          ihbody (env := Nested.isolateEnv env state path x) hc hbodyPre
                        rw [hb] at hcomp
                        cases ha' : Nested.runN body (Nested.isolateEnv env state path x) Ha with
                        | done H'a envb' vb' wsb' =>
                            rw [ha'] at hcomp
                            exact absurd hcomp (by simp [ResCompat])
                        | fault H'a envb' f' wsb' =>
                            rw [ha'] at hcomp
                            exact hcomp
                  · simp only [bool_eq_false_of_ne_true hex]
                    exact ResCompat.fault hc
  | ret x => simp only [Nested.runN]; exact ⟨rfl, rfl, rfl, hc⟩

/-! ## The counted extraction/call/restoration chain

The program the recogniser's trace denotes: take the parent and child out into two
fresh handles, call the body on the extracted child, put the result back into the
parent at the selected index, and return the restored parent. -/
def chain (a i fst snd e path x result restored : Var) (body : Nested.NCode) : Nested.NCode :=
  .takeOut a i fst snd e
    (.callAt snd path x result body (.putBack fst result i restored (.ret restored)))

/-- The put-back's disposition reads only the parent cell, so the child call
leaves it where the boundary had it (`ChildCall.parent`). -/
theorem disposition?_parent_after_call {Hin Hout : Heap} {env : Env} {ctx : Ctx}
    {state path x : Var} {body : Nested.NCode} {p c : Ref} {idx : Nat}
    (hcall : PutBack.ChildCall Hin Hout env ctx state path x body p c) :
    PutBack.disposition? Hout p idx = PutBack.disposition? Hin p idx := by
  have hcells : Hout.cells p = Hin.cells p := hcall.parent
  have hin : PutBack.inPlace? Hout p idx = PutBack.inPlace? Hin p idx := by
    simp [PutBack.inPlace?, hcells]
  simp [PutBack.disposition?, hcells, hin]

/-- The counted extraction, child call and restoration, composed.

The extraction is `counted_takeOut` at the entry; the child call's return is the
caller's accounted boundary state, whose result binding is derived
(`CountedChildCall.move`); the restoration is `counted_restore`, which derives the
mutate branch and carries the accounting. The model's own `runN` of the chain
term is related to the counted heap by `HeapCompat` throughout, so the conclusion
names both the extracted store's disposition and the restored one, and relates
the counted post-state to the abstract run's own final heap. The call's own run at
the boundary heap is named as well, at the same write trace the model's run
carries: that trace is what a counted reading of the fragment records, and naming
it here is what lets the two traces be related rather than each derived on its own.

The caller's heap and index facts (`hcell`, `hslot`, `hidx`) are premises the
checker cannot see, and they replace `Nested.TakeOutsOK`/`Nested.Agrees` here
because those predicates' take-out case existentially quantifies the index, which
cannot pin the conclusion's `idx`, while the body's share of both predicates is
`PutBack.ChildCall.extraction`/`annotations`. The restoration boundary, the
bounds fact and the entry's two distinct components are derived from the
accounting (`restorationBoundary_of_accounted`). -/
theorem counted_nested_chain {support : List Var} {H : Heap} {env : Env} {c : Ctx}
    (hacc : Accounted support H env c)
    {a i fst snd path x result restored : Var} {r eR : Ref} {o : Obj} {idx : Nat}
    {body : Nested.NCode} {Hout : Heap} {ctx' : Ctx}
    (hchk : Nested.checkN c (chain a i fst snd eR path x result restored body) = some ctx')
    (hr : c.refOf a = some r)
    (hcell : H.cells r = some o) (hslot : o.fields[idx]? = some (.ref eR))
    (hidx : env i = some (.scalar idx))
    (hcall : CountedChildCall (CountedPair.protocol H r eR idx).2 Hout
      ((env.set fst (.ref r)).set snd (.ref eR)) ((c.move a fst).bindOwned snd eR)
      snd path x body r eR (snd :: replaceVar support a fst)) :
    ∃ Hf Hm envm ws,
      Accounted (snd :: replaceVar support a fst) (CountedPair.protocol H r eR idx).2
        ((env.set fst (.ref r)).set snd (.ref eR)) ((c.move a fst).bindOwned snd eR)
      ∧ HeapCompat (CountedPair.protocol H r eR idx).2
          (H.set r { o with fields := o.fields.setIfInBounds idx (.scalar 0) })
      ∧ (CountedPair.protocol H r eR idx).2.cells H.next = none
      ∧ (CountedPair.protocol H r eR idx).2.next = H.next + 1
      ∧ Heap.Exclusive (CountedPair.protocol H r eR idx).2 r
      ∧ Heap.Exclusive (CountedPair.protocol H r eR idx).2 eR
      ∧ PutBack.disposition? Hout r idx = some .mutate
      ∧ PutBack.putBack Hout r idx eR = some (r, Hf)
      ∧ Hf = PutBack.mutate Hout r (PutBack.parentAfter o idx) idx eR
      ∧ Accounted
          ((replaceVar (replaceVar (snd :: replaceVar support a fst) snd result)
            fst restored).erase result)
          Hf
          ((((env.set fst (.ref r)).set snd (.ref eR)).set result (.ref eR)).set restored (.ref r))
          (((((c.move a fst).bindOwned snd eR).move snd result).move fst restored).setUs
            result .dead)
      ∧ Nested.runN (chain a i fst snd eR path x result restored body) env H =
          .done Hm envm (.ref r) ws
      ∧ (∃ envb,
          Nested.runN body (Nested.isolateEnv ((env.set fst (.ref r)).set snd (.ref eR)) snd path x)
            (CountedPair.protocol H r eR idx).2 = .done Hout envb (.ref eR) ws)
      ∧ (∀ w ∈ ws, w.2 = true)
      ∧ HeapCompat Hf Hm := by
  -- the checker's take-out conditions at the entry
  obtain ⟨ha, hma, hiU, he, hfstDead, hsndDead, hfs, rchk, hrchk, her, hopen, hrest⟩ :=
    Nested.checkNF_takeOut_some (ctx' := ctx')
      (show Nested.checkNF c [] (Nested.NCode.takeOut a i fst snd eR
        (.callAt snd path x result body (.putBack fst result i restored (.ret restored)))) =
        some ctx' from hchk)
  have hrr : rchk = r := Option.some.inj (hrchk.symm.trans hr)
  subst rchk
  have hfst : c.us fst ≠ .owned := by rw [hfstDead]; decide
  have hsnd : c.us snd ≠ .owned := by rw [hsndDead]; decide
  -- the call's conditions at the take-out context
  obtain ⟨hcs, hcmof, hcp, hcx, hcr, -, rc, cb, y, hcref, hcopen, hbody, hretv, hyOwned,
    hyRef, hput⟩ := Nested.checkNF_callAt_facts (ctx' := ctx') hrest
  have hrc : rc = eR := by
    rw [Ctx.bindOwned_refOf_self] at hcref
    exact (Option.some.inj hcref).symm
  subst rc
  -- the put-back's conditions at the post-call context
  obtain ⟨p1, p2, p3, p4, p5, p6, p7, p8, rp, rep, f2, rest2, hrp, hrep, hfs2, hfa, hfi,
    hfe, hrest3⟩ := Nested.checkNF_putBack_some (ctx' := ctx') hput
  obtain ⟨hf2, hrest2⟩ : f2 = { arr := r, idx := i, elem := eR } ∧ rest2 = [] := by
    simpa using hfs2.symm
  have hrp' : rp = r := by
    rw [hf2] at hfa
    exact hfa.symm
  have hrep' : rep = eR := by
    rw [hf2] at hfe
    exact hfe.symm
  -- the extraction
  obtain ⟨oc, hb⟩ := restorationBoundary_of_accounted hacc ha hma hr he hcell hslot
  have her' : eR ≠ r := hb.distinct.symm
  obtain ⟨haccB, hcompatB, hpairNone, hnext, hcellB⟩ :=
    counted_takeOut hacc ha hma hr he hfst hsnd hfs her' hcell hslot
  -- the boundary's exclusivity
  have hexclP : Heap.Exclusive (CountedPair.protocol H r eR idx).2 r :=
    ⟨_, hcellB, hb.parent_rc, hb.parent_persistent⟩
  have hexclC : Heap.Exclusive (CountedPair.protocol H r eR idx).2 eR :=
    ⟨oc, hb.child, hb.child_rc, hb.child_persistent⟩
  have hexclC? : (CountedPair.protocol H r eR idx).2.exclusive? eR = true :=
    (Heap.exclusive?_eq_true).mpr hexclC
  -- the call's result binding, derived from the accounting
  have hacc2 := hcall.move haccB (result := result) hcs hcref (by rw [hcr]; decide)
  -- the restoration
  obtain ⟨hdisp, hpb, haccF⟩ :=
    counted_restore (Hc := (CountedPair.protocol H r eR idx).2) hb hcall.call hacc2
      p1 (by rw [hrp'] at hrp; exact hrp) p3 (by rw [hrep'] at hrep; exact hrep)
      (by rw [p6]; decide) p7 p8
  have henvA : env a = some (.ref r) := (hacc.inv.owned a r ha hr).1
  -- the child call's run and its abstract counterpart
  obtain ⟨envb, ws, hrunBodyC⟩ := hcall.call.outcome
  have hnoCopy : ∀ w ∈ ws, w.2 = true := hcall.call.writes_exclusive hrunBodyC
  have hcompBody := runN_compat (Hc := (CountedPair.protocol H r eR idx).2) hcompatB
    (by rw [hrunBodyC]; exact hnoCopy)
  rw [hrunBodyC] at hcompBody
  cases haB : Nested.runN body
      (Nested.isolateEnv ((env.set fst (.ref r)).set snd (.ref eR)) snd path x)
      (H.set r { o with fields := o.fields.setIfInBounds idx (.scalar 0) }) with
  | fault Hb envb' f' ws' =>
      rw [haB] at hcompBody
      exact absurd hcompBody (by simp [ResCompat])
  | done Hb envb' vb' ws' =>
      rw [haB] at hcompBody
      obtain ⟨hEb, hVb, hWb, hcompHb⟩ := hcompBody
      subst hEb
      subst hVb
      subst hWb
      -- the environment and heap facts the model's own run reads
      obtain ⟨pv, hpv⟩ := haccB.inv.scalar path hcp
      obtain ⟨xv, hxv⟩ := haccB.inv.scalar x hcx
      have henv₁path : ((env.set fst (.ref r)).set snd (.ref eR)) path = some (.scalar pv) := hpv
      have henv₁x : ((env.set fst (.ref r)).set snd (.ref eR)) x = some (.scalar xv) := hxv
      have henv₁snd : ((env.set fst (.ref r)).set snd (.ref eR)) snd = some (.ref eR) :=
        Env.set_self _ _ _
      have henv₁fst : ((env.set fst (.ref r)).set snd (.ref eR)) fst = some (.ref r) := by
        rw [Env.set_other (x := snd) (y := fst) (v := .ref eR) (h := hfs)]
        exact Env.set_self _ _ _
      have hi_ne_fst : i ≠ fst := by
        intro hh
        rw [hh] at hiU
        rw [hfstDead] at hiU
        exact absurd hiU (by decide)
      have hi_ne_snd : i ≠ snd := by
        intro hh
        rw [hh] at hiU
        rw [hsndDead] at hiU
        exact absurd hiU (by decide)
      have hi_ne_result : i ≠ result := by
        intro hh
        rw [hh] at p5
        rw [p3] at p5
        exact absurd p5 (by decide)
      have henv₂fst :
          ((((env.set fst (.ref r)).set snd (.ref eR)).set result (.ref eR)) fst) =
            some (.ref r) := by
        rw [Env.set_other (x := result) (y := fst) (v := .ref eR) (h := Ne.symm p7)]
        exact henv₁fst
      have henv₂result :
          ((((env.set fst (.ref r)).set snd (.ref eR)).set result (.ref eR)) result) =
            some (.ref eR) := Env.set_self _ _ _
      have henv₂i :
          ((((env.set fst (.ref r)).set snd (.ref eR)).set result (.ref eR)) i) =
            some (.scalar idx) := by
        rw [Env.set_other (x := result) (y := i) (v := .ref eR) (h := hi_ne_result),
          Env.set_other (x := snd) (y := i) (v := .ref eR) (h := hi_ne_snd),
          Env.set_other (x := fst) (y := i) (v := .ref r) (h := hi_ne_fst)]
        exact hidx
      have hH1excl :
          (H.set r { o with fields := o.fields.setIfInBounds idx (.scalar 0) }).exclusive? eR =
            true := by
        rw [← hcompatB.exclusive? eR]
        exact hexclC?
      have hHbcell : Hb.cells r = some (PutBack.parentAfter o idx) := by
        rw [← hcompHb.cells r, hcall.call.parent, hcellB]
        rfl
      have hcont : Nested.runN (.putBack fst result i restored (.ret restored))
          ((((env.set fst (.ref r)).set snd (.ref eR)).set result (.ref eR))) Hb =
          .done (PutBack.mutate Hb r (PutBack.parentAfter o idx) idx eR)
            (((((env.set fst (.ref r)).set snd (.ref eR)).set result (.ref eR)).set restored
              (.ref r))) (.ref r) [] :=
        PutBack.mutate_eq_model (H := Hb) (p := r) (c := eR) (i := idx)
          (o := PutBack.parentAfter o idx) (a := fst) (e := result) (iv := i)
          (result := restored) hHbcell henv₂fst henv₂result henv₂i
      refine ⟨PutBack.mutate Hout r (PutBack.parentAfter o idx) idx eR,
        PutBack.mutate Hb r (PutBack.parentAfter o idx) idx eR,
        ((((env.set fst (.ref r)).set snd (.ref eR)).set result (.ref eR)).set restored
          (.ref r)), ws, haccB, hcompatB, hpairNone, hnext, hexclP, hexclC,
        hdisp, hpb, rfl, haccF, ?_, ⟨envb, hrunBodyC⟩, hnoCopy,
        hcompHb.mutate r (PutBack.parentAfter o idx) idx eR⟩
      have htake : Nested.runN (chain a i fst snd eR path x result restored body) env H =
          Nested.runN
            (.callAt snd path x result body (.putBack fst result i restored (.ret restored)))
            ((env.set fst (.ref r)).set snd (.ref eR))
            (H.set r { o with fields := o.fields.setIfInBounds idx (.scalar 0) }) := by
        simp [chain, Nested.runN, henvA, hidx, hcell, hslot]
      have hcallStep : Nested.runN
            (.callAt snd path x result body (.putBack fst result i restored (.ret restored)))
            ((env.set fst (.ref r)).set snd (.ref eR))
            (H.set r { o with fields := o.fields.setIfInBounds idx (.scalar 0) }) =
          Nested.addWrites
            (Nested.runN (.putBack fst result i restored (.ret restored))
              (((env.set fst (.ref r)).set snd (.ref eR)).set result (.ref eR)) Hb) ws := by
        simp [Nested.runN, henv₁path, henv₁x, hH1excl, haB]
      have hdone : Nested.addWrites
            (Nested.runN (.putBack fst result i restored (.ret restored))
              (((env.set fst (.ref r)).set snd (.ref eR)).set result (.ref eR)) Hb) ws =
          .done (PutBack.mutate Hb r (PutBack.parentAfter o idx) idx eR)
            ((((env.set fst (.ref r)).set snd (.ref eR)).set result (.ref eR)).set restored (.ref r))
            (.ref r) ws := by
        rw [hcont]
        simp [Nested.addWrites, List.append_nil]
      exact htake.trans (hcallStep.trans hdone)

/-! ## The chain's net edge effect

The chain is not edge-preserving step by step: the take-out lowers the extracted
child's incoming-edge count by one and the restoration raises it by one. The
*net* run is edge-preserving, and that is what an enclosing call needs for its
`edges` field. The decomposition is entry → boundary (`counted_takeOut`, whose
model take-out heap differs from the entry at exactly the selected slot), boundary
→ call output (the child call's own `edges`), and call output → final (the
restoration's slot fill).

The cursor and carrier fields are direct: the sole allocation is the temporary
pair, which the release erases and whose absence the boundary records
(`B.2.cells H.next = none`, `B.2.next = H.next + 1`); the child call's `edges`
supplies its own `carrier` and `cursor`; and the restoration rewrites a cell the
call's output already holds, so it adds none. -/

/-- The chain's net effect on the counted heap: the entry and the restored
counted heap have the same incoming-edge count at every name, the cursor does not
go backwards, and no cell appears that the entry lacked. The restored heap is the
one `counted_nested_chain` names, so this is exactly the edge effect an enclosing
call's `edges` field needs when the chain is its body.

The entry's index binding `env i = some (.scalar idx)` is carried for uniformity
with `counted_nested_chain`, whose premises this matches; the net effect reads
neither it nor the environment. -/
theorem counted_nested_chain_edges {support : List Var} {H : Heap} {env : Env} {c : Ctx}
    (hacc : Accounted support H env c)
    {a i fst snd path x result restored : Var} {r eR : Ref} {o : Obj} {idx : Nat}
    {body : Nested.NCode} {Hout : Heap} {ctx' : Ctx}
    (hchk : Nested.checkN c (chain a i fst snd eR path x result restored body) = some ctx')
    (hr : c.refOf a = some r)
    (hcell : H.cells r = some o) (hslot : o.fields[idx]? = some (.ref eR))
    (_hidx : env i = some (.scalar idx))
    (hcall : CountedChildCall (CountedPair.protocol H r eR idx).2 Hout
      ((env.set fst (.ref r)).set snd (.ref eR)) ((c.move a fst).bindOwned snd eR)
      snd path x body r eR (snd :: replaceVar support a fst)) :
    EdgePreserved H (PutBack.mutate Hout r (PutBack.parentAfter o idx) idx eR) := by
  -- the checker's take-out conditions at the entry
  obtain ⟨ha, hma, -, he, hfstDead, hsndDead, hfs, rchk, hrchk, -, -, -⟩ :=
    Nested.checkNF_takeOut_some (ctx' := ctx')
      (show Nested.checkNF c [] (Nested.NCode.takeOut a i fst snd eR
        (.callAt snd path x result body (.putBack fst result i restored (.ret restored)))) =
        some ctx' from hchk)
  have hrr : rchk = r := Option.some.inj (hrchk.symm.trans hr)
  subst rchk
  have hfst : c.us fst ≠ .owned := by rw [hfstDead]; decide
  have hsnd : c.us snd ≠ .owned := by rw [hsndDead]; decide
  -- the entry's parent cell is inside the cursor range
  have hrn : r < H.next := hacc.domain r o hcell
  -- the restoration boundary, which supplies the entry's distinctness
  obtain ⟨oc, hb⟩ := restorationBoundary_of_accounted hacc ha hma hr he hcell hslot
  -- the boundary's cells and the relation to the model's take-out heap
  obtain ⟨-, hcompatB, -, hnext, -⟩ :=
    counted_takeOut hacc ha hma hr he hfst hsnd hfs hb.distinct.symm hcell hslot
  -- the model take-out heap and its live-cell domain
  have hdomH' : ∀ q oq, (H.set r { o with fields := o.fields.setIfInBounds idx (.scalar 0) }).cells q
      = some oq → q < (H.set r { o with fields := o.fields.setIfInBounds idx (.scalar 0) }).next := by
    intro q oq hq
    by_cases hqr : q = r
    · rw [hqr]
      exact hacc.domain r o hcell
    · have hq' : H.cells q = some oq := by
        rw [Heap.set_other _ _ _ _ hqr] at hq
        exact hq
      exact hacc.domain q oq hq'
  -- entry → boundary: only the selected slot's edge moves, and it is `eR`'s
  have hboundaryE :
      IncomingCount (CountedPair.protocol H r eR idx).2 eR + 1 = IncomingCount H eR := by
    have hset := IncomingCount_set_of_ref (H := H) (r := r) (e := eR) (o := o)
      (idx := idx) (w := 0) hcell hrn hslot
    rw [← HeapCompat.IncomingCount_of_dom hcompatB hdomH' eR] at hset
    exact hset.symm
  have hboundaryNe : ∀ q, q ≠ eR →
      IncomingCount (CountedPair.protocol H r eR idx).2 q = IncomingCount H q := by
    intro q hq
    rw [HeapCompat.IncomingCount_of_dom hcompatB hdomH' q]
    exact IncomingCount_set_of_ref_ne hcell hrn hslot hq
  -- the call's output holds the parent cell the take-out left, inside its cursor
  have houtCell : Hout.cells r = some (PutBack.parentAfter o idx) := by
    rw [hcall.call.parent, hcompatB.cells r]
    simp [PutBack.parentAfter, Heap.set_self]
  have hrHout : r < Hout.next := by
    have h1 : r < (CountedPair.protocol H r eR idx).2.next := by
      rw [hnext]; exact Nat.lt_succ_of_lt hrn
    exact Nat.lt_of_lt_of_le h1 hcall.edges.cursor
  have hparentSlot : (PutBack.parentAfter o idx).fields[idx]? = some (.scalar 0) := by
    simpa [PutBack.parentAfter] using
      (Array.getElem?_setIfInBounds_self_of_lt (xs := o.fields) (i := idx)
        (a := Val.scalar 0) (Array.getElem?_eq_some_iff.mp hslot).1)
  -- call output → final: the restoration fills the selected slot with `eR`
  have hfinalE :
      IncomingCount (PutBack.mutate Hout r (PutBack.parentAfter o idx) idx eR) eR
        = IncomingCount Hout eR + 1 := by
    have h := IncomingCount_set_fill (H := Hout) (r := r) (re := eR)
      (o := PutBack.parentAfter o idx) (idx := idx) (old := 0) houtCell hrHout hparentSlot
    simpa [PutBack.mutate, Array.set!_eq_setIfInBounds] using h
  have hfinalNe : ∀ q, q ≠ eR →
      IncomingCount (PutBack.mutate Hout r (PutBack.parentAfter o idx) idx eR) q
        = IncomingCount Hout q := by
    intro q hq
    have h := IncomingCount_set_fill_ne (H := Hout) (r := r) (re := eR)
      (o := PutBack.parentAfter o idx) (idx := idx) (old := 0) houtCell hrHout hparentSlot hq
    simpa [PutBack.mutate, Array.set!_eq_setIfInBounds] using h
  refine ⟨?_, ?_, ?_⟩
  · intro q
    by_cases hq : q = eR
    · rw [hq, hfinalE, hcall.edges.incoming eR, hboundaryE]
    · rw [hfinalNe q hq, hcall.edges.incoming q, hboundaryNe q hq]
  · have h1 : H.next ≤ (CountedPair.protocol H r eR idx).2.next := by
      rw [hnext]; exact Nat.le_succ H.next
    exact Nat.le_trans h1 hcall.edges.cursor
  · intro q oq hq
    by_cases hqr : q = r
    · rw [hqr]
      exact ⟨o, hcell⟩
    · have hq' : Hout.cells q = some oq := by
        simpa [PutBack.mutate, Heap.set_other Hout r q _ hqr] using hq
      obtain ⟨oq', hoq'⟩ := hcall.edges.carrier q oq hq'
      refine ⟨oq', ?_⟩
      rw [hcompatB.cells q] at hoq'
      rw [Heap.set_other _ _ _ _ hqr] at hoq'
      exact hoq'

/-! ## The two-level chain

The enclosing call's `edges` field is exactly the net effect above: when the
outer level's body is the inner chain, the outer `CountedChildCall` is
`⟨the outer boundary, the inner chain's net effect⟩`. The outer chain theorem
then applies unchanged, so the two-level chain's model run, trace, `HeapCompat`
and final accounting follow from the same composition, and its own net effect is
`counted_nested_chain_edges` again one level up.

The inner level's entry is the outer boundary's *isolated* state: the outer call
hands its extracted child (`snd`) as the inner parent, so `rIn` is the outer
`eR`, and the outer `ChildCall`'s body is the inner chain term itself. The model
boundary of the outer call stays a hypothesis — it is the admitted-body contract
`PutBack.ChildCall`, which the finite-path induction derives for a recursive body
but which is stated here for the *compound* body `chain …`; what the theorem adds
is the previously missing half, that the compound body's edge effect is derived
rather than assumed. -/

/-- The outer counted child call at a two-level chain: the body is the inner
chain term and the `edges` field is the inner chain's net effect
(`counted_nested_chain_edges`), so the structure is constructed rather than
assumed at this level. -/
theorem counted_nested_chain_two_levels_call {support : List Var} {H : Heap} {env : Env}
    {c : Ctx}
    {a fst snd path x : Var} {r eR : Ref} {idx : Nat}
    {aIn iIn fstIn sndIn pathIn xIn resultIn restoredIn : Var}
    {rIn eRIn : Ref} {oIn : Obj} {idxIn : Nat} {body : Nested.NCode}
    {suppIn : List Var} {HoutIn : Heap} {ctxIn' : Ctx}
    (haccIn : Accounted suppIn (CountedPair.protocol H r eR idx).2
      (Nested.isolateEnv ((env.set fst (.ref r)).set snd (.ref eR)) snd path x)
      (Nested.isolatedCtx ((c.move a fst).bindOwned snd eR) snd path x eR))
    (hchkIn : Nested.checkN
      (Nested.isolatedCtx ((c.move a fst).bindOwned snd eR) snd path x eR)
      (chain aIn iIn fstIn sndIn eRIn pathIn xIn resultIn restoredIn body) = some ctxIn')
    (hrIn : (Nested.isolatedCtx ((c.move a fst).bindOwned snd eR) snd path x eR).refOf aIn
      = some rIn)
    (hcellIn : (CountedPair.protocol H r eR idx).2.cells rIn = some oIn)
    (hslotIn : oIn.fields[idxIn]? = some (.ref eRIn))
    (hidxIn : Nested.isolateEnv ((env.set fst (.ref r)).set snd (.ref eR)) snd path x iIn
      = some (.scalar idxIn))
    (hcallIn : CountedChildCall
      (CountedPair.protocol (CountedPair.protocol H r eR idx).2 rIn eRIn idxIn).2 HoutIn
      (((Nested.isolateEnv ((env.set fst (.ref r)).set snd (.ref eR)) snd path x).set fstIn
        (.ref rIn)).set sndIn (.ref eRIn))
      (((Nested.isolatedCtx ((c.move a fst).bindOwned snd eR) snd path x eR).move aIn
        fstIn).bindOwned sndIn eRIn)
      sndIn pathIn xIn body rIn eRIn (sndIn :: replaceVar suppIn aIn fstIn))
    (hcallOut : PutBack.ChildCall (CountedPair.protocol H r eR idx).2
      (PutBack.mutate HoutIn rIn (PutBack.parentAfter oIn idxIn) idxIn eRIn)
      ((env.set fst (.ref r)).set snd (.ref eR)) ((c.move a fst).bindOwned snd eR)
      snd path x (chain aIn iIn fstIn sndIn eRIn pathIn xIn resultIn restoredIn body) r eR) :
    CountedChildCall (CountedPair.protocol H r eR idx).2
      (PutBack.mutate HoutIn rIn (PutBack.parentAfter oIn idxIn) idxIn eRIn)
      ((env.set fst (.ref r)).set snd (.ref eR)) ((c.move a fst).bindOwned snd eR)
      snd path x (chain aIn iIn fstIn sndIn eRIn pathIn xIn resultIn restoredIn body)
      r eR (snd :: replaceVar support a fst) :=
  ⟨hcallOut, counted_nested_chain_edges haccIn hchkIn hrIn hcellIn hslotIn hidxIn hcallIn⟩

/-- The two-level chain: the outer level's child body is the inner chain, whose
net edge effect is the outer call's `edges`. The chain theorem applies at the
outer level with the constructed counted call, so the two-level term's model run,
its all-exclusive trace and `HeapCompat` to the final counted heap are derived;
the inner chain's net effect and the whole two-level run's net effect are the two
`EdgePreserved` conjuncts. -/
theorem counted_nested_chain_two_levels {support : List Var} {H : Heap} {env : Env} {c : Ctx}
    {a i fst snd path x result restored : Var} {r eR : Ref} {o : Obj} {idx : Nat}
    {ctx' : Ctx}
    {aIn iIn fstIn sndIn pathIn xIn resultIn restoredIn : Var}
    {rIn eRIn : Ref} {oIn : Obj} {idxIn : Nat} {body : Nested.NCode}
    {suppIn : List Var} {HoutIn : Heap} {ctxIn' : Ctx}
    (hacc : Accounted support H env c)
    (hchk : Nested.checkN c (chain a i fst snd eR path x result restored
      (chain aIn iIn fstIn sndIn eRIn pathIn xIn resultIn restoredIn body)) = some ctx')
    (hr : c.refOf a = some r)
    (hcell : H.cells r = some o) (hslot : o.fields[idx]? = some (.ref eR))
    (hidx : env i = some (.scalar idx))
    (haccIn : Accounted suppIn (CountedPair.protocol H r eR idx).2
      (Nested.isolateEnv ((env.set fst (.ref r)).set snd (.ref eR)) snd path x)
      (Nested.isolatedCtx ((c.move a fst).bindOwned snd eR) snd path x eR))
    (hchkIn : Nested.checkN
      (Nested.isolatedCtx ((c.move a fst).bindOwned snd eR) snd path x eR)
      (chain aIn iIn fstIn sndIn eRIn pathIn xIn resultIn restoredIn body) = some ctxIn')
    (hrIn : (Nested.isolatedCtx ((c.move a fst).bindOwned snd eR) snd path x eR).refOf aIn
      = some rIn)
    (hcellIn : (CountedPair.protocol H r eR idx).2.cells rIn = some oIn)
    (hslotIn : oIn.fields[idxIn]? = some (.ref eRIn))
    (hidxIn : Nested.isolateEnv ((env.set fst (.ref r)).set snd (.ref eR)) snd path x iIn
      = some (.scalar idxIn))
    (hcallIn : CountedChildCall
      (CountedPair.protocol (CountedPair.protocol H r eR idx).2 rIn eRIn idxIn).2 HoutIn
      (((Nested.isolateEnv ((env.set fst (.ref r)).set snd (.ref eR)) snd path x).set fstIn
        (.ref rIn)).set sndIn (.ref eRIn))
      (((Nested.isolatedCtx ((c.move a fst).bindOwned snd eR) snd path x eR).move aIn
        fstIn).bindOwned sndIn eRIn)
      sndIn pathIn xIn body rIn eRIn (sndIn :: replaceVar suppIn aIn fstIn))
    (hcallOut : PutBack.ChildCall (CountedPair.protocol H r eR idx).2
      (PutBack.mutate HoutIn rIn (PutBack.parentAfter oIn idxIn) idxIn eRIn)
      ((env.set fst (.ref r)).set snd (.ref eR)) ((c.move a fst).bindOwned snd eR)
      snd path x (chain aIn iIn fstIn sndIn eRIn pathIn xIn resultIn restoredIn body) r eR) :
    EdgePreserved H
        (PutBack.mutate
          (PutBack.mutate HoutIn rIn (PutBack.parentAfter oIn idxIn) idxIn eRIn)
          r (PutBack.parentAfter o idx) idx eR)
      ∧ Accounted
          (List.erase
            (replaceVar (replaceVar (snd :: replaceVar support a fst) snd result) fst restored)
            result)
          (PutBack.mutate
            (PutBack.mutate HoutIn rIn (PutBack.parentAfter oIn idxIn) idxIn eRIn)
            r (PutBack.parentAfter o idx) idx eR)
          ((((env.set fst (.ref r)).set snd (.ref eR)).set result (.ref eR)).set restored
            (.ref r))
          (((((c.move a fst).bindOwned snd eR).move snd result).move fst restored).setUs
            result .dead)
      ∧ (∃ Hm envm ws,
          Nested.runN (chain a i fst snd eR path x result restored
            (chain aIn iIn fstIn sndIn eRIn pathIn xIn resultIn restoredIn body)) env H
              = .done Hm envm (.ref r) ws
            ∧ (∀ w ∈ ws, w.2 = true)
            ∧ HeapCompat
                (PutBack.mutate
                  (PutBack.mutate HoutIn rIn (PutBack.parentAfter oIn idxIn) idxIn eRIn)
                  r (PutBack.parentAfter o idx) idx eR) Hm) := by
  have hcall := counted_nested_chain_two_levels_call (support := support)
    haccIn hchkIn hrIn hcellIn hslotIn hidxIn hcallIn hcallOut
  have hedges := counted_nested_chain_edges (support := support)
    (body := chain aIn iIn fstIn sndIn eRIn pathIn xIn resultIn restoredIn body)
    hacc hchk hr hcell hslot hidx hcall
  obtain ⟨Hf, Hm, envm, ws, -, -, -, -, -, -, -, -, hHf, haccF, hrun, -, hws, hcompF⟩ :=
    counted_nested_chain hacc hchk hr hcell hslot hidx hcall
  rw [hHf] at haccF hcompF
  exact ⟨hedges, haccF, Hm, envm, ws, hrun, hws, hcompF⟩

/-! ## The chain's two store dispositions, named -/

/-- The extraction's placeholder store lands on an exclusive cell: the pair
release leaves the parent at its entry count, so the extracted store's target is
`Heap.Exclusive`. -/
theorem counted_nested_chain_extraction {support : List Var} {H : Heap} {env : Env} {c : Ctx}
    (hacc : Accounted support H env c)
    {a i fst snd path x result restored : Var} {r eR : Ref} {o : Obj} {idx : Nat}
    {body : Nested.NCode} {Hout : Heap} {ctx' : Ctx}
    (hchk : Nested.checkN c (chain a i fst snd eR path x result restored body) = some ctx')
    (hr : c.refOf a = some r)
    (hcell : H.cells r = some o) (hslot : o.fields[idx]? = some (.ref eR))
    (hidx : env i = some (.scalar idx))
    (hcall : CountedChildCall (CountedPair.protocol H r eR idx).2 Hout
      ((env.set fst (.ref r)).set snd (.ref eR)) ((c.move a fst).bindOwned snd eR)
      snd path x body r eR (snd :: replaceVar support a fst)) :
    Heap.Exclusive (CountedPair.protocol H r eR idx).2 r := by
  obtain ⟨-, -, -, -, -, -, -, -, hexclP, -, -, -, -, -, -, -, -⟩ :=
    counted_nested_chain hacc hchk hr hcell hslot hidx hcall
  exact hexclP

/-- The restoration takes the mutate branch and writes the returned child handle
into the parent's selected slot. -/
theorem counted_nested_chain_restoration {support : List Var} {H : Heap} {env : Env} {c : Ctx}
    (hacc : Accounted support H env c)
    {a i fst snd path x result restored : Var} {r eR : Ref} {o : Obj} {idx : Nat}
    {body : Nested.NCode} {Hout : Heap} {ctx' : Ctx}
    (hchk : Nested.checkN c (chain a i fst snd eR path x result restored body) = some ctx')
    (hr : c.refOf a = some r)
    (hcell : H.cells r = some o) (hslot : o.fields[idx]? = some (.ref eR))
    (hidx : env i = some (.scalar idx))
    (hcall : CountedChildCall (CountedPair.protocol H r eR idx).2 Hout
      ((env.set fst (.ref r)).set snd (.ref eR)) ((c.move a fst).bindOwned snd eR)
      snd path x body r eR (snd :: replaceVar support a fst)) :
    PutBack.disposition? Hout r idx = some .mutate ∧
      ((PutBack.parentAfter o idx).fields.setIfInBounds idx (.ref eR))[idx]? =
        some (.ref eR) := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, hdisp, -, -, -, -, -, -⟩ :=
    counted_nested_chain hacc hchk hr hcell hslot hidx hcall
  refine ⟨hdisp, ?_⟩
  have hlt : idx < (PutBack.parentAfter o idx).fields.size := by
    simpa [PutBack.parentAfter] using (Array.getElem?_eq_some_iff.mp hslot).1
  exact Array.getElem?_setIfInBounds_self_of_lt hlt
