/-
The one-pair struct model: an object with exactly two reference fields, a
selected component and a retained sibling, and the two branches the structured
write takes at runtime.

This is a model, not the emitted `setAt` LCNF. The false/unique branch reuses
the pair cell in place: the selected field is overwritten with the child's
result, the retained field keeps its exact reference, and the address is
unchanged. The true/shared branch cannot write in place: it increments the
retained sibling for the new pair's reference, allocates a fresh pair whose
selected field holds the replacement child and whose retained field is the
same sibling, then decrements the old pair for the caller's consumed handle.
The old pair keeps its fields and persistence; only its count drops from `k` to
`k - 1`.

The branch entry is the state after the selected component's child write. In
the exclusive arm that child is a nested run the M4a checker accepts; in the
shared arm it is an explicitly contracted replacement, so both arms start from
the branch-entry heap/context this module's lemmas name. The emitted shared
dispatch also increments both pair-field references before it consumes the
caller's old handle and runs the child inside the reset join; that
child/argument accounting is part of the premised branch entry here, and the
copy relation itself adds the retained sibling's reference, allocates the fresh
pair and consumes the old pair handle. Nothing here claims a
contract for every callback, a whole-heap separation invariant, or that these
relations hold of the compiler's AST.

`PCode` is the pair fragment of the checker: a designated exclusive pair write
is admitted only when the pair variable is owned once and the result variable is
dead. The same code copies at runtime when the pair is shared, but the shared
path is not labelled a designated exclusive write, so `checkP` refuses it and
`runP` records a non-exclusive write there.
-/
import Ownership.Nested

namespace Ownership

/-! ## Heap support lemmas -/

namespace Heap

@[simp] theorem set_next (H : Heap) (r : Ref) (o : Obj) : (H.set r o).next = H.next := rfl

@[simp] theorem inc_next (H : Heap) (r : Ref) (n : Nat) : (H.inc r n).next = H.next := by
  unfold inc
  split <;> rfl

@[simp] theorem dec_next (H : Heap) (r : Ref) (n : Nat) : (H.dec r n).next = H.next := by
  unfold dec
  split <;> rfl

@[simp] theorem alloc_next (H : Heap) (fields : Array Val) :
    (H.alloc fields).2.next = H.next + 1 := rfl

theorem inc_cells_other {H : Heap} {r r' : Ref} {n : Nat} (h : r' ≠ r) :
    (H.inc r n).cells r' = H.cells r' := by
  unfold inc
  split
  · rfl
  · exact set_other _ _ _ _ h

theorem inc_cells_self {H : Heap} {r : Ref} {n : Nat} {o : Obj}
    (h : H.cells r = some o) :
    (H.inc r n).cells r = some { o with rc := o.rc + n } := by
  unfold inc
  rw [h]
  simp [set]

theorem dec_cells_self {H : Heap} {r : Ref} {n : Nat} {o : Obj}
    (h : H.cells r = some o) :
    (H.dec r n).cells r = some { o with rc := o.rc - n } := by
  unfold dec
  rw [h]
  simp [set]

end Heap

namespace Pair

/-! ## Sides and pair fields -/

inductive Side where
  | left
  | right
  deriving DecidableEq, Repr

namespace Side

def idx : Side → Nat
  | .left => 0
  | .right => 1

def other : Side → Nat
  | .left => 1
  | .right => 0

@[simp] theorem idx_left : idx .left = 0 := rfl

@[simp] theorem idx_right : idx .right = 1 := rfl

@[simp] theorem other_left : other .left = 1 := rfl

@[simp] theorem other_right : other .right = 0 := rfl

@[simp] theorem idx_lt_two (s : Side) : idx s < 2 := by cases s <;> simp

@[simp] theorem other_lt_two (s : Side) : other s < 2 := by cases s <;> simp

theorem idx_ne_other (s : Side) : idx s ≠ other s := by cases s <;> decide

end Side

/-- The two reference fields of a pair, in left/right order. -/
structure Fields where
  left : Ref
  right : Ref
  deriving Repr

namespace Fields

/-- The selected field. -/
def get (f : Fields) : Side → Ref
  | .left => f.left
  | .right => f.right

/-- The field the branch retains unchanged. -/
def retained (f : Fields) : Side → Ref
  | .left => f.right
  | .right => f.left

/-- The pair as an object's field array. -/
def toArray (f : Fields) : Array Val := #[.ref f.left, .ref f.right]

@[simp] theorem toArray_size (f : Fields) : f.toArray.size = 2 := rfl

@[simp] theorem toArray_zero (f : Fields) : f.toArray[0]? = some (.ref f.left) := rfl

@[simp] theorem toArray_one (f : Fields) : f.toArray[1]? = some (.ref f.right) := rfl

end Fields

/-- The field at an index, if present. -/
def field? (o : Obj) (i : Nat) : Option Val := o.fields[i]?

/-- An object is a pair when it has exactly two fields and both are references. -/
def pairOf? (o : Obj) : Option Fields :=
  if o.fields.size = 2 then
    match field? o 0 with
    | some (.ref l) =>
      match field? o 1 with
      | some (.ref r) => some ⟨l, r⟩
      | _ => none
    | _ => none
  else none

theorem pairOf?_size {o : Obj} {pf : Fields} (h : pairOf? o = some pf) :
    o.fields.size = 2 := by
  unfold pairOf? at h
  split at h
  · assumption
  · simp at h

theorem pairOf?_left {o : Obj} {pf : Fields} (h : pairOf? o = some pf) :
    field? o 0 = some (.ref pf.left) := by
  have hsize := pairOf?_size h
  unfold pairOf? at h
  rw [if_pos hsize] at h
  split at h
  · rename_i l hl
    split at h
    · rename_i r hr
      simp only [Option.some.injEq] at h
      subst h
      exact hl
    · simp at h
  · simp at h

theorem pairOf?_right {o : Obj} {pf : Fields} (h : pairOf? o = some pf) :
    field? o 1 = some (.ref pf.right) := by
  have hsize := pairOf?_size h
  unfold pairOf? at h
  rw [if_pos hsize] at h
  split at h
  · rename_i l hl
    split at h
    · rename_i r hr
      simp only [Option.some.injEq] at h
      subst h
      exact hr
    · simp at h
  · simp at h

@[simp] theorem pairOf?_toArray (l r : Ref) :
    pairOf? ⟨#[.ref l, .ref r], 1, false⟩ = some ⟨l, r⟩ := by
  simp [pairOf?, field?]

/-- Overwriting one field of a pair with a reference keeps it a pair. -/
theorem pairOf?_set_ref {o : Obj} {pf : Fields} (h : pairOf? o = some pf)
    {idx : Nat} (hidx : idx < 2) (rep : Ref) :
    ∃ pf', pairOf? { o with fields := o.fields.set! idx (.ref rep) } = some pf' := by
  have hsize := pairOf?_size h
  have hleft := pairOf?_left h
  have hright := pairOf?_right h
  have hcases : idx = 0 ∨ idx = 1 := by omega
  rcases hcases with rfl | rfl
  · refine ⟨{ pf with left := rep }, ?_⟩
    have hsz : (o.fields.set! 0 (.ref rep)).size = 2 := by
      simp [Array.size_set!, hsize]
    have hright' : o.fields[1] = .ref pf.right := by
      have hh := hright
      simp only [field?] at hh
      exact (Array.getElem?_eq_some_iff.mp hh).choose_spec
    unfold pairOf?
    rw [if_pos hsz]
    simp only [field?]
    simp [Array.set!, Array.getElem?_setIfInBounds, hsize]
    rw [hright']
  · refine ⟨{ pf with right := rep }, ?_⟩
    have hsz : (o.fields.set! 1 (.ref rep)).size = 2 := by
      simp [Array.size_set!, hsize]
    have hleft' : o.fields[0] = .ref pf.left := by
      have hh := hleft
      simp only [field?] at hh
      exact (Array.getElem?_eq_some_iff.mp hh).choose_spec
    unfold pairOf?
    rw [if_pos hsz]
    simp only [field?]
    simp [Array.set!, Array.getElem?_setIfInBounds, hsize]
    rw [hleft']

/-! ## The two pair-branch heap transitions -/

/-- In-place pair update, the exclusive branch: the selected field becomes the
replacement child and the pair cell keeps its address, count and persistence. -/
def reuse (H : Heap) (r : Ref) (o : Obj) (sel : Side) (rep : Ref) : Heap :=
  H.set r { o with fields := o.fields.set! sel.idx (.ref rep) }

/-- Copy update, the shared branch: increment the retained sibling for the new
pair's reference, allocate the fresh pair with the selected field replaced, then
decrement the old pair for the caller's consumed handle. -/
def copy (H : Heap) (r : Ref) (o : Obj) (sel : Side) (s rep : Ref) : Heap :=
  (((H.inc s 1).alloc (o.fields.set! sel.idx (.ref rep))).2).dec r 1

/-- The fresh pair's address: the copy's allocation point. -/
def copyRef (H : Heap) : Ref := H.next

@[simp] theorem reuse_cells_self (H : Heap) (r : Ref) (o : Obj) (sel : Side) (rep : Ref) :
    (reuse H r o sel rep).cells r =
      some { o with fields := o.fields.set! sel.idx (.ref rep) } := by
  simp [reuse]

theorem reuse_cells_other {H : Heap} {r r' : Ref} {o : Obj} {sel : Side} {rep : Ref}
    (h : r' ≠ r) : (reuse H r o sel rep).cells r' = H.cells r' := by
  exact Heap.set_other _ _ _ _ h

theorem reuse_rc_self (H : Heap) (r : Ref) (o : Obj) (sel : Side) (rep : Ref) :
    (reuse H r o sel rep).rc r = o.rc := by
  simp [reuse, Heap.rc]

theorem reuse_persistent_self (H : Heap) (r : Ref) (o : Obj) (sel : Side) (rep : Ref) :
    (reuse H r o sel rep).isPersistent r = o.persistent := by
  simp [reuse, Heap.isPersistent]

theorem reuse_exclusive {H : Heap} {r : Ref} {o : Obj} {sel : Side} {rep : Ref}
    (hcell : H.cells r = some o) (hex : H.exclusive? r = true) :
    (reuse H r o sel rep).exclusive? r = true := by
  simp [reuse, Heap.exclusive?, hcell] at hex ⊢
  exact hex

theorem copy_cells_old {H : Heap} {r : Ref} {o : Obj} {sel : Side} {s rep : Ref}
    (hcell : H.cells r = some o) (hsr : s ≠ r) (hnr : H.next ≠ r) :
    (copy H r o sel s rep).cells r = some { o with rc := o.rc - 1 } := by
  unfold copy
  have h2 : ((H.inc s 1).alloc (o.fields.set! sel.idx (.ref rep))).2.cells r = some o := by
    rw [Heap.alloc_cells_other (by rw [Heap.inc_next]; exact Ne.symm hnr)]
    rw [Heap.inc_cells_other (H := H) (r := s) (r' := r) (Ne.symm hsr)]
    exact hcell
  rw [Heap.dec_cells_self h2]

theorem copy_cells_retained {H : Heap} {r : Ref} {o : Obj} {sel : Side} {s rep : Ref}
    {os : Obj} (hslive : H.cells s = some os) (hsr : s ≠ r) (hsn : s ≠ H.next) :
    (copy H r o sel s rep).cells s = some { os with rc := os.rc + 1 } := by
  unfold copy
  have h2 : ((H.inc s 1).alloc (o.fields.set! sel.idx (.ref rep))).2.cells s =
      some { os with rc := os.rc + 1 } := by
    rw [Heap.alloc_cells_other (by rw [Heap.inc_next]; exact hsn)]
    exact Heap.inc_cells_self hslive
  rw [Heap.dec_other hsr]
  exact h2

theorem copy_cells_other {H : Heap} {q r : Ref} {o : Obj} {sel : Side} {s rep : Ref}
    (hqr : q ≠ r) (hqn : q ≠ H.next) (hqs : q ≠ s) :
    (copy H r o sel s rep).cells q = H.cells q := by
  unfold copy
  rw [Heap.dec_other hqr]
  rw [Heap.alloc_cells_other (by rw [Heap.inc_next]; exact hqn)]
  rw [Heap.inc_cells_other hqs]

theorem copy_cells_new (H : Heap) (r : Ref) (o : Obj) (sel : Side) (s rep : Ref)
    (h : copyRef H ≠ r) :
    (copy H r o sel s rep).cells (copyRef H) =
      some ⟨o.fields.set! sel.idx (.ref rep), 1, false⟩ := by
  unfold copy copyRef
  have h' : H.next ≠ r := h
  rw [Heap.dec_other h']
  have h2 := Heap.alloc_cells_self (H.inc s 1) (o.fields.set! sel.idx (.ref rep))
  rw [Heap.inc_next] at h2
  exact h2

theorem copy_rc_old {H : Heap} {r : Ref} {o : Obj} {sel : Side} {s rep : Ref}
    (hcell : H.cells r = some o) (hsr : s ≠ r) (hnr : H.next ≠ r) :
    (copy H r o sel s rep).rc r = o.rc - 1 := by
  rw [Heap.rc, copy_cells_old hcell hsr hnr]
  simp [Heap.rc, hcell]

theorem copy_rc_retained {H : Heap} {r : Ref} {o : Obj} {sel : Side} {s rep : Ref}
    {os : Obj} (hslive : H.cells s = some os) (hsr : s ≠ r) (hsn : s ≠ H.next) :
    (copy H r o sel s rep).rc s = H.rc s + 1 := by
  rw [Heap.rc, copy_cells_retained hslive hsr hsn]
  simp [Heap.rc, hslive]

theorem copy_rc_new (H : Heap) (r : Ref) (o : Obj) (sel : Side) (s rep : Ref)
    (h : copyRef H ≠ r) :
    (copy H r o sel s rep).rc (copyRef H) = 1 := by
  rw [Heap.rc, copy_cells_new H r o sel s rep h]
  rfl

@[simp] theorem copy_next (H : Heap) (r : Ref) (o : Obj) (sel : Side) (s rep : Ref) :
    (copy H r o sel s rep).next = H.next + 1 := by
  unfold copy
  simp

theorem copy_old_fields {H : Heap} {r : Ref} {o : Obj} {sel : Side} {s rep : Ref}
    (hcell : H.cells r = some o) (hsr : s ≠ r) (hnr : H.next ≠ r) :
    ((copy H r o sel s rep).cells r).map (·.fields) = some o.fields := by
  rw [copy_cells_old hcell hsr hnr]
  rfl

theorem copy_old_persistent {H : Heap} {r : Ref} {o : Obj} {sel : Side} {s rep : Ref}
    (hcell : H.cells r = some o) (hsr : s ≠ r) (hnr : H.next ≠ r) :
    ((copy H r o sel s rep).cells r).map (·.persistent) = some o.persistent := by
  rw [copy_cells_old hcell hsr hnr]
  rfl

end Pair

/-! ## Context transitions -/

namespace Ctx

/-- Bind a variable to the fresh pair as its single owned handle. -/
def bindFresh (c : Ctx) (x : Var) (r : Ref) : Ctx :=
  { c with
      us := fun z => if z = x then .owned else c.us z
      refOf := fun z => if z = x then some r else c.refOf z
      mult := fun q => if q = r then 1 else c.mult q }

@[simp] theorem bindFresh_us_self (c : Ctx) (x : Var) (r : Ref) :
    (c.bindFresh x r).us x = .owned := by simp [bindFresh]

@[simp] theorem bindFresh_us_other (c : Ctx) (x z : Var) (r : Ref) (h : z ≠ x) :
    (c.bindFresh x r).us z = c.us z := by simp [bindFresh, h]

@[simp] theorem bindFresh_refOf_self (c : Ctx) (x : Var) (r : Ref) :
    (c.bindFresh x r).refOf x = some r := by simp [bindFresh]

@[simp] theorem bindFresh_refOf_other (c : Ctx) (x z : Var) (r : Ref) (h : z ≠ x) :
    (c.bindFresh x r).refOf z = c.refOf z := by simp [bindFresh, h]

@[simp] theorem bindFresh_mult_self (c : Ctx) (x : Var) (r : Ref) :
    (c.bindFresh x r).mult r = 1 := by simp [bindFresh]

@[simp] theorem bindFresh_mult_other (c : Ctx) (x : Var) (r q : Ref) (h : q ≠ r) :
    (c.bindFresh x r).mult q = c.mult q := by simp [bindFresh, h]

/-- The unique branch's context: the pair handle moves to the result variable,
which denotes the same pair. -/
def pairReuse (c : Ctx) (pairVar result : Var) : Ctx := c.move pairVar result

/-- The shared branch's context: the retained sibling gains the new pair's
reference, the consumed old handle lowers the old pair's count, and the result
variable owns the fresh pair once. The pair variable becomes dead. -/
def pairCopy (c : Ctx) (pairVar result : Var) (r s r' : Ref) : Ctx :=
  (((c.inc s 1).bindFresh result r').dec r 1).setUs pairVar .dead

@[simp] theorem pairReuse_us_result (c : Ctx) (pairVar result : Var) :
    (c.pairReuse pairVar result).us result = c.us pairVar := by
  simp [pairReuse, Ctx.move]

@[simp] theorem pairReuse_refOf_result (c : Ctx) (pairVar result : Var) :
    (c.pairReuse pairVar result).refOf result = c.refOf pairVar := by
  simp [pairReuse, Ctx.move]

@[simp] theorem pairReuse_mult (c : Ctx) (pairVar result : Var) :
    (c.pairReuse pairVar result).mult = c.mult := by
  simp [pairReuse, Ctx.move]

@[simp] theorem pairCopy_us_result {c : Ctx} {pairVar result : Var} {r s r' : Ref}
    (h : pairVar ≠ result) : (c.pairCopy pairVar result r s r').us result = .owned := by
  have h' : result ≠ pairVar := Ne.symm h
  simp [pairCopy, h']

@[simp] theorem pairCopy_us_pair {c : Ctx} {pairVar result : Var} {r s r' : Ref} :
    (c.pairCopy pairVar result r s r').us pairVar = .dead := by
  simp [pairCopy]

@[simp] theorem pairCopy_refOf_result (c : Ctx) (pairVar result : Var) (r s r' : Ref) :
    (c.pairCopy pairVar result r s r').refOf result = some r' := by
  simp [pairCopy]

@[simp] theorem pairCopy_mult_r {c : Ctx} {pairVar result : Var} {r s r' : Ref}
    (hrs : r ≠ s) (hrr : r ≠ r') :
    (c.pairCopy pairVar result r s r').mult r = c.mult r - 1 := by
  simp [pairCopy, hrs, hrr]

@[simp] theorem pairCopy_mult_s {c : Ctx} {pairVar result : Var} {r s r' : Ref}
    (hsr : s ≠ r) (hsr' : s ≠ r') :
    (c.pairCopy pairVar result r s r').mult s = c.mult s + 1 := by
  simp [pairCopy, hsr, hsr']

@[simp] theorem pairCopy_mult_r' {c : Ctx} {pairVar result : Var} {r s r' : Ref}
    (hrr : r' ≠ r) :
    (c.pairCopy pairVar result r s r').mult r' = 1 := by
  simp [pairCopy, hrr]

end Ctx

/-! ## Invariant preservation for the two branches -/

namespace Inv

/-- Duplicating a handle preserves the invariant; unlike `Inv.inc` this takes
the cell rather than an owned variable as the existence witness, because the
retained sibling is a field reference and not necessarily a named handle. -/
theorem incCell {H : Heap} {env : Env} {c : Ctx} {r : Ref} {n : Nat} {o : Obj}
    (hi : Inv H env c) (hcell : H.cells r = some o) :
    Inv (H.inc r n) env (c.inc r n) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro r'
    by_cases h : r' = r
    · cases h
      rw [Heap.rc_inc_self hcell, Ctx.inc_self, hi.rc_eq r]
    · rw [Heap.rc_inc_other h, Ctx.inc_other (c := c) (r := r) (r' := r') (n := n) h]
      exact hi.rc_eq r'
  · intro y r' hy href
    have h := hi.owned y r' hy href
    refine ⟨h.1, ?_⟩
    by_cases hrr : r' = r
    · cases hrr
      rw [Ctx.inc_self]
      omega
    · rw [Ctx.inc_other (c := c) (r := r) (r' := r') (n := n) hrr]
      exact h.2
  · intro y r' hy href
    have h := hi.borrow y r' hy href
    refine ⟨h.1, ?_⟩
    by_cases hrr : r' = r
    · cases hrr
      rw [Heap.inc_cells_self hcell]
      exact Option.some_ne_none _
    · rw [Heap.inc_cells_other hrr]
      exact h.2
  · exact hi.scalar
  · exact nonPersistent_inc hi

/-- Allocating a fresh pair and binding it to a dead variable preserves the
invariant when the allocation point is fresh. -/
theorem allocBind {H : Heap} {env : Env} {c : Ctx} {fields : Array Val} {x : Var}
    (hi : Inv H env c) (hx : c.us x = .dead) (hfresh : H.cells H.next = none) :
    Inv (H.alloc fields).2 (env.set x (.ref H.next)) (c.bindFresh x H.next) := by
  have hrc0 : H.rc H.next = 0 := by simp [Heap.rc, hfresh]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro q
    by_cases hq : q = H.next
    · cases hq
      rw [Heap.rc, Heap.alloc_cells_self]
      simp
    · rw [Heap.rc, Heap.alloc_cells_other hq]
      rw [Ctx.bindFresh_mult_other (c := c) (x := x) (r := H.next) (q := q) hq]
      exact hi.rc_eq q
  · intro y q hy href
    by_cases hyx : y = x
    · subst hyx
      have hqr : H.next = q := by simpa using href
      subst hqr
      exact ⟨by simp [Env.set], by simp⟩
    · have hy' : c.us y = .owned := by simpa [Ctx.bindFresh, hyx] using hy
      have href' : c.refOf y = some q := by simpa [Ctx.bindFresh, hyx] using href
      have h := hi.owned y q hy' href'
      refine ⟨by simpa [Env.set, hyx] using h.1, ?_⟩
      by_cases hq : q = H.next
      · subst hq
        have hrc := hi.rc_eq H.next
        rw [hrc0] at hrc
        omega
      · rw [Ctx.bindFresh_mult_other (c := c) (x := x) (r := H.next) (q := q) hq]
        exact h.2
  · intro y q hy href
    by_cases hyx : y = x
    · subst hyx
      simp [Ctx.bindFresh] at hy
    · have hy' : c.us y = .borrow := by simpa [Ctx.bindFresh, hyx] using hy
      have href' : c.refOf y = some q := by simpa [Ctx.bindFresh, hyx] using href
      have h := hi.borrow y q hy' href'
      refine ⟨by simpa [Env.set, hyx] using h.1, ?_⟩
      by_cases hq : q = H.next
      · subst hq
        rw [Heap.alloc_cells_self]
        exact Option.some_ne_none _
      · rw [Heap.alloc_cells_other hq]
        exact h.2
  · intro y hy
    by_cases hyx : y = x
    · subst hyx
      simp [Ctx.bindFresh] at hy
    · have hy' : c.us y = .scalar := by simpa [Ctx.bindFresh, hyx] using hy
      obtain ⟨n, hn⟩ := hi.scalar y hy'
      exact ⟨n, by simpa [Env.set, hyx] using hn⟩
  · intro q o hcell
    by_cases hq : q = H.next
    · subst hq
      rw [Heap.alloc_cells_self] at hcell
      injection hcell with hcell
      subst hcell
      rfl
    · rw [Heap.alloc_cells_other hq] at hcell
      exact hi.nonPersistent q o hcell

end Inv

namespace Pair

/-! ## The pair fragment and its checker -/

inductive PCode where
  | pairWrite (sel : Side) (pairVar : Var) (rep : Ref) (result : Var) (k : PCode)
  | ret (x : Var)

/-- One pair write's runtime branch. The branch is selected by the pair's count
and persistence, exactly as the emitted `isShared` test is. -/
structure Step where
  ref : Ref
  heap : Heap
  write : Write

def step (sel : Side) (H : Heap) (r : Ref) (o : Obj) (pf : Fields) (rep : Ref) : Step :=
  if H.exclusive? r then
    { ref := r, heap := reuse H r o sel rep, write := (r, true) }
  else
    { ref := copyRef H, heap := copy H r o sel (pf.retained sel) rep, write := (r, false) }

theorem step_reuse {sel : Side} {H : Heap} {r : Ref} {o : Obj} {pf : Fields} {rep : Ref}
    (hex : H.exclusive? r = true) :
    step sel H r o pf rep =
      { ref := r, heap := reuse H r o sel rep, write := (r, true) } := by
  simp [step, hex]

theorem step_copy {sel : Side} {H : Heap} {r : Ref} {o : Obj} {pf : Fields} {rep : Ref}
    (hex : H.exclusive? r = false) :
    step sel H r o pf rep =
      { ref := copyRef H, heap := copy H r o sel (pf.retained sel) rep, write := (r, false) } := by
  simp [step, hex]

def runP : PCode → Env → Heap → Res
  | .pairWrite sel pairVar rep result k, env, H =>
      match env pairVar with
      | some (.ref r) =>
          match H.cells r with
          | some o =>
              match pairOf? o with
              | some pf =>
                  let st := step sel H r o pf rep
                  (runP k (env.set result (.ref st.ref)) st.heap).addWrite st.write
              | none => .fault H env (.badVar pairVar) []
          | none => .fault H env (.noCell r) []
      | _ => .fault H env (.badVar pairVar) []
  | .ret x, env, H => .done H env (env x |>.getD .erased) []

theorem runP_reuse {sel : Side} {H : Heap} {env : Env} {pairVar result : Var}
    {rep : Ref} {r : Ref} {o : Obj} {pf : Fields} {k : PCode}
    (henv : env pairVar = some (.ref r)) (hcell : H.cells r = some o)
    (hpf : pairOf? o = some pf) (hex : H.exclusive? r = true) :
    runP (.pairWrite sel pairVar rep result k) env H =
      (runP k (env.set result (.ref r)) (reuse H r o sel rep)).addWrite (r, true) := by
  simp [runP, henv, hcell, hpf, step_reuse hex]

theorem runP_copy {sel : Side} {H : Heap} {env : Env} {pairVar result : Var}
    {rep : Ref} {r : Ref} {o : Obj} {pf : Fields} {k : PCode}
    (henv : env pairVar = some (.ref r)) (hcell : H.cells r = some o)
    (hpf : pairOf? o = some pf) (hex : H.exclusive? r = false) :
    runP (.pairWrite sel pairVar rep result k) env H =
      (runP k (env.set result (.ref (copyRef H))) (copy H r o sel (pf.retained sel) rep)).addWrite
        (r, false) := by
  simp [runP, henv, hcell, hpf, step_copy hex]

/-- The checker for the pair fragment. A pair write is a designated exclusive
write only when the pair variable is owned once; a shared pair is refused and
must go through the copy relation, not through this checker. -/
def checkP (c : Ctx) : PCode → Option Ctx
  | .pairWrite _ pairVar _ result k =>
      if c.us pairVar = .owned ∧ c.multOf pairVar = 1 ∧ c.us result = .dead ∧ pairVar ≠ result then
        match c.refOf pairVar with
        | some _ => checkP (c.pairReuse pairVar result) k
        | none => none
      else none
  | .ret x =>
      if c.us x = .owned ∨ c.us x = .scalar then some c else none

theorem checkP_pairWrite {c : Ctx} {sel : Side} {pairVar result : Var} {rep : Ref}
    {r : Ref} {k : PCode} {ctx' : Ctx}
    (hown : c.us pairVar = .owned) (hm : c.multOf pairVar = 1)
    (hres : c.us result = .dead) (hne : pairVar ≠ result)
    (hr : c.refOf pairVar = some r)
    (hk : checkP (c.pairReuse pairVar result) k = some ctx') :
    checkP c (.pairWrite sel pairVar rep result k) = some ctx' := by
  simp [checkP, hown, hm, hres, hne, hr, hk]

theorem checkP_refuses_shared {c : Ctx} {sel : Side} {pairVar result : Var} {rep : Ref}
    {k : PCode} (hm : c.multOf pairVar = 2) :
    checkP c (.pairWrite sel pairVar rep result k) = none := by
  simp [checkP, hm]

theorem checkP_refuses_incShared {c : Ctx} {sel : Side} {pairVar result : Var} {rep : Ref}
    {k : PCode} (hm : 1 < c.multOf pairVar) :
    checkP c (.pairWrite sel pairVar rep result k) = none := by
  simp [checkP]
  omega

theorem checkP_sound {c : PCode} {ctx ctx' : Ctx} {H : Heap} {env : Env}
    (hc : checkP ctx c = some ctx') (hi : Inv H env ctx)
    (hshape : ∀ x r, ctx.us x = .owned → ctx.refOf x = some r →
      ∃ o pf, H.cells r = some o ∧ pairOf? o = some pf) :
    ∃ H' env' v ws, runP c env H = .done H' env' v ws ∧
      (∀ w ∈ ws, w.2 = true) ∧ Inv H' env' ctx' := by
  induction c generalizing ctx ctx' H env with
  | pairWrite sel pairVar rep result k ih =>
      by_cases hx : ctx.us pairVar = .owned ∧ ctx.multOf pairVar = 1 ∧
          ctx.us result = .dead ∧ pairVar ≠ result
      · obtain ⟨hown, hm, hres, hne⟩ := hx
        simp [checkP, hown, hm, hres, hne] at hc
        cases hr : ctx.refOf pairVar with
        | none => simp [hr] at hc
        | some r =>
            have hc' : checkP (ctx.pairReuse pairVar result) k = some ctx' := by
              simpa [hr] using hc
            obtain ⟨o, pf, hcell, hpf⟩ := hshape pairVar r hown hr
            have hmul : ctx.mult r = 1 := by
              have h := hm
              unfold Ctx.multOf at h
              rw [hr] at h
              exact h
            have henv : env pairVar = some (.ref r) := (hi.owned pairVar r hown hr).1
            have hex : H.exclusive? r = true :=
              (Heap.exclusive?_eq_true).mpr (hi.exclusive hmul)
            have hrun := runP_reuse (sel := sel) (H := H) (env := env)
              (pairVar := pairVar) (result := result) (rep := rep) (r := r) (o := o)
              (pf := pf) (k := k) henv hcell hpf hex
            have hshape' : ∀ x q, (ctx.pairReuse pairVar result).us x = .owned →
                (ctx.pairReuse pairVar result).refOf x = some q →
                ∃ o' pf', (reuse H r o sel rep).cells q = some o' ∧
                  pairOf? o' = some pf' := by
              intro x q hx' hrx
              by_cases hxr : x = result
              · subst hxr
                have hq : ctx.refOf pairVar = some q := by
                  simpa [Ctx.pairReuse, Ctx.move] using hrx
                rw [hr] at hq
                have hqr : q = r := (Option.some.inj hq).symm
                subst hqr
                obtain ⟨pf', hpf'⟩ := pairOf?_set_ref hpf (Side.idx_lt_two sel) rep
                exact ⟨_, pf', by rw [reuse_cells_self], hpf'⟩
              · have hxpair : x ≠ pairVar := by
                  intro h; subst h
                  simp [Ctx.pairReuse, Ctx.move, hne] at hx'
                have hus : ctx.us x = .owned := by
                  simpa [Ctx.pairReuse, Ctx.move, hxr, hxpair] using hx'
                have href : ctx.refOf x = some q := by
                  simpa [Ctx.pairReuse, Ctx.move, hxr] using hrx
                obtain ⟨o', pf', hqc, hpf'⟩ := hshape x q hus href
                by_cases hqr : q = r
                · subst hqr
                  have ho' : o' = o := by
                    rw [hcell] at hqc
                    exact (Option.some.inj hqc).symm
                  subst o'
                  obtain ⟨pf'', hpf''⟩ := pairOf?_set_ref hpf' (Side.idx_lt_two sel) rep
                  exact ⟨_, pf'', by rw [reuse_cells_self], hpf''⟩
                · exact ⟨o', pf', by rw [reuse_cells_other hqr]; exact hqc, hpf'⟩
            have hiFields : Inv (reuse H r o sel rep) env ctx := hi.setFields hcell
            have hiMoved : Inv (reuse H r o sel rep) (env.set result (.ref r))
                (ctx.pairReuse pairVar result) :=
              Inv.move hiFields hown hr
            obtain ⟨H', env', v, ws, hrun', hws, hinv⟩ :=
              ih (ctx := ctx.pairReuse pairVar result) (ctx' := ctx')
                 (H := reuse H r o sel rep) (env := env.set result (.ref r))
                 hc' hiMoved hshape'
            refine ⟨H', env', v, (r, true) :: ws, ?_, ?_, hinv⟩
            · rw [hrun, hrun']
              rfl
            · intro w hw
              simp only [List.mem_cons] at hw
              rcases hw with rfl | hw
              · rfl
              · exact hws w hw
      · simp [checkP, hx] at hc
  | ret x =>
      by_cases hx : ctx.us x = .owned ∨ ctx.us x = .scalar
      · simp only [checkP, hx, if_true] at hc
        have hctx : ctx' = ctx := by simpa using hc.symm
        subst hctx
        exact ⟨H, env, env x |>.getD .erased, [], rfl, by simp, hi⟩
      · simp [checkP, hx] at hc

/-! ## The shared copy's exact poststate -/

/-- The shared branch's reconstruction, stated in the form the certificate uses:
the old pair keeps its fields and persistence and loses exactly one count; the
fresh pair holds the replacement selected field and the retained sibling at one
count; the retained sibling gains one; the pair-owning result variable denotes
the fresh pair. -/
theorem copy_poststate {H : Heap} {r : Ref} {o : Obj} {sel : Side} {s rep : Ref}
    {os : Obj} (hcell : H.cells r = some o) (hslive : H.cells s = some os)
    (hsr : s ≠ r) (hnr : H.next ≠ r) (hsn : s ≠ H.next) :
    (copy H r o sel s rep).cells r = some { o with rc := o.rc - 1 } ∧
      ((copy H r o sel s rep).cells r).map (·.fields) = some o.fields ∧
      ((copy H r o sel s rep).cells r).map (·.persistent) = some o.persistent ∧
      (copy H r o sel s rep).cells (copyRef H) =
        some ⟨o.fields.set! sel.idx (.ref rep), 1, false⟩ ∧
      (copy H r o sel s rep).rc s = H.rc s + 1 ∧
      (copy H r o sel s rep).rc (copyRef H) = 1 ∧
      (copy H r o sel s rep).next = H.next + 1 := by
  refine ⟨copy_cells_old hcell hsr hnr, copy_old_fields hcell hsr hnr,
    copy_old_persistent hcell hsr hnr, copy_cells_new H r o sel s rep hnr,
    copy_rc_retained hslive hsr hsn, copy_rc_new H r o sel s rep hnr, by simp⟩

/-- The shared branch preserves the invariant, under the branch-entry premises:
the pair enters with `k ≥ 2`, its selected component's child effect has already
been accounted for in `H` and `ctx`, and the allocation point is fresh. -/
theorem copy_inv {H : Heap} {env : Env} {c : Ctx} {pairVar result : Var} {r s rep : Ref}
    {o os : Obj} {sel : Side} {k : Nat}
    (hi : Inv H env c) (hown : c.us pairVar = .owned) (href : c.refOf pairVar = some r)
    (hres : c.us result = .dead) (hne : pairVar ≠ result)
    (hcell : H.cells r = some o) (hk : c.mult r = k) (hk2 : 2 ≤ k)
    (hslive : H.cells s = some os) (hsr : s ≠ r)
    (hfresh : H.cells H.next = none) (hnextr : H.next ≠ r) (hnexts : H.next ≠ s) :
    Inv (copy H r o sel s rep) ((env.set result (.ref (copyRef H))).erase pairVar)
      (c.pairCopy pairVar result r s (copyRef H)) := by
  have hinc : Inv (H.inc s 1) env (c.inc s 1) := hi.incCell hslive
  have hfresh' : (H.inc s 1).cells (H.inc s 1).next = none := by
    rw [Heap.inc_next]
    rw [Heap.inc_cells_other hnexts]
    exact hfresh
  have halloc : Inv (((H.inc s 1).alloc (o.fields.set! sel.idx (.ref rep))).2)
      (env.set result (.ref (H.inc s 1).next))
      ((c.inc s 1).bindFresh result (H.inc s 1).next) :=
    hinc.allocBind hres hfresh'
  have hnextr' : (H.inc s 1).next ≠ r := by simpa using hnextr
  have hmut : ((c.inc s 1).bindFresh result (H.inc s 1).next).mult r = k := by
    rw [Ctx.bindFresh_mult_other (c := c.inc s 1) (x := result)
      (r := (H.inc s 1).next) (q := r) (Ne.symm hnextr')]
    rw [Ctx.inc_other (c := c) (r := s) (r' := r) (n := 1) (Ne.symm hsr)]
    exact hk
  have hdec := halloc.dec (x := pairVar) (n := 1) (r := r)
    (by simpa [Ctx.inc_us, Ctx.bindFresh_us_other (h := hne)] using hown)
    (by simpa [Ctx.inc_refOf, Ctx.bindFresh_refOf_other (h := hne)] using href)
    (by rw [hmut]; omega)
  simpa [copy, copyRef, Ctx.pairCopy, Heap.inc_next] using hdec

end Pair
end Ownership
