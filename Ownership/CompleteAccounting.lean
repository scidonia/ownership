/-
Complete ownership and reference-count accounting for the supported fragment.

`Inv` relates the heap count to the checker's `Ctx.mult`; `OwnersAccounted`
supplies the environment-side count-one fact for one designated handle. Neither
counts the heap's incoming edges against the environment's owners, so a
configuration with one count and two owners survives both. This module states
and proves the complete relation.

`Accounted support H env c` relates four things: the checker invariant, a finite
enumeration `support` of the owning variables (duplicate-free, sound, complete,
and bound to a reference), the live-cell domain `r < H.next` that the edge count
enumerates, and the count equation
`H.rc r = IncomingCount H r + EnvOwnerCount c support r`.

What the relation covers. The operations of the straight-line fragment
(`Ownership.Code`) and the nested protocol's two atomic steps: the scalar
`.let`, the alias bind, `.check`, `.setArr`, `.ret`, and — on the heap side —
an in-place scalar store, a take-out edge removal and a put-back edge fill. Each
step preserves the relation at the interpreter's own post-state, with its side
conditions as premises.

What it excludes. `.inc` entirely: it raises `H.rc` and `c.mult` together and
introduces neither a destination variable nor a heap edge, so no accounting
state exists immediately after it (`inc_rejected`). `.dec x n` with `n ≠ 1`: one
owning variable leaves and one count is released, so a multi-handle decrement
releases counts no obligation carried (`decTwo_rejected`); modelled ownership
credits are the alternative and are not part of this relation. There is no
`.borrow` producer in `Code`, so the fragment's uses are `owned`, `scalar` and
`dead` only.

What remains a client obligation. The count equation is not derivable from
`Inv` (`alias_rejected`), and the checker does not require the alias target or
the scalar-`.let` target to be fresh, nor the store's selected slot to hold a
scalar: `Supported` carries the first two as certificates and `StoreSlots` the
last. The take-out's extracted element is *not* one of them: its no-second-edge
premise follows from the relation, the array's slot and the checker's count-one
condition (`Accounted.incoming_eq_one_of_slot`), so `Accounted.takeOutOfSlot`
states that step without a client-supplied edge count.

What it covers of execution. Each `Supported` constructor carries the checker's
own rule at that constructor, with the certificates above beside it — `bindLit`
has no checker premise at all, so its freshness premise is certificate alone.
Apart from those certificates, the fragment's only departure from the checker's
rules is `n = 1` at `.dec`.
So the fragment is check acceptance restricted to the counted constructors, and
`Ownership.Preservation` proves that reading: `Ownership.supported_check` gives
the checker's acceptance, and `supported_run` follows the resulting fault-free
run with `Accounted` at every state it reaches.

This is not a statement about physical memory. The heap here is the fragment's
named-cell model; nothing in this module says a compiled program mutates memory,
that a reference count is a C object's count, or that the model's count one is
an address-level uniqueness fact.
-/
import Ownership.Accounting

namespace Ownership

/-! ## Counting helpers -/

/-- Occurrences of `.ref q` in one object's field array. -/
def RefCount (fields : Array Val) (q : Ref) : Nat :=
  (fields.toList.filter (fun v => v = .ref q)).length

/-- The edges into `r` contributed by the cell at `q`. -/
def EdgeAt (H : Heap) (q r : Ref) : Nat :=
  match H.cells q with
  | some o => RefCount o.fields r
  | none => 0

/-- `IncomingCount` is the sum of the per-cell edge counts over the cursor
range. -/
theorem IncomingCount_eq_edges (H : Heap) (r : Ref) :
    IncomingCount H r = ((List.range H.next).map (fun q => EdgeAt H q r)).sum := rfl

theorem sum_range_congr {f g : Nat → Nat} {n : Nat} (h : ∀ q, q < n → f q = g q) :
    ((List.range n).map f).sum = ((List.range n).map g).sum := by
  induction n with
  | zero => simp
  | succ m ih =>
    rw [List.range_succ, List.map_append, List.map_append, List.sum_append, List.sum_append]
    have h₁ := ih (fun q hq => h q (Nat.lt_trans hq (Nat.lt_succ_self m)))
    have h₂ := h m (Nat.lt_succ_self m)
    simp [h₁, h₂]

/-- Raising one entry of a finite range by one raises the sum by one. -/
theorem sum_range_update {f g : Nat → Nat} {n r : Nat}
    (hr : r < n) (h : f r = g r + 1) (hother : ∀ q, q ≠ r → f q = g q) :
    ((List.range n).map f).sum = ((List.range n).map g).sum + 1 := by
  induction n with
  | zero => exact absurd hr (Nat.not_lt_zero r)
  | succ m ih =>
    rw [List.range_succ, List.map_append, List.map_append, List.sum_append, List.sum_append]
    by_cases hrm : r = m
    · have hm : f m = g m + 1 := by rw [← hrm]; exact h
      have hc : ((List.range m).map f).sum = ((List.range m).map g).sum :=
        sum_range_congr (fun q hq => hother q (by omega))
      simp only [List.map_singleton, List.sum_singleton]
      omega
    · have hr' : r < m := by omega
      have hi := ih hr'
      have hm : f m = g m := hother m (fun h => hrm h.symm)
      simp only [List.map_singleton, List.sum_singleton]
      omega

/-- Two sums over the same finite range differ by the difference of their `r`
entries when the two functions agree everywhere else. -/
theorem sum_range_split {f g : Nat → Nat} {n r : Nat} (hr : r < n)
    (h : ∀ q, q ≠ r → q < n → f q = g q) :
    ((List.range n).map f).sum + g r = ((List.range n).map g).sum + f r := by
  induction n with
  | zero => exact absurd hr (Nat.not_lt_zero r)
  | succ m ih =>
    rw [List.range_succ, List.map_append, List.map_append, List.sum_append, List.sum_append]
    by_cases hrm : r = m
    · rw [hrm]
      have hc : ((List.range m).map f).sum = ((List.range m).map g).sum :=
        sum_range_congr (fun q hq => h q (by omega) (by omega))
      simp only [List.map_singleton, List.sum_singleton]
      omega
    · have hr' : r < m := by omega
      have hi := ih hr' (fun q hq hq' => h q hq (by omega))
      have hm : f m = g m := h m (fun h => hrm h.symm) (by omega)
      simp only [List.map_singleton, List.sum_singleton]
      omega

/-! ### Replacing one field-array entry -/

theorem filter_set_length_eq {l : List Val} {i : Nat} {old new : Val}
    {p : Val → Bool} (h : l[i]? = some old) (hp : p old = p new) :
    ((l.set i new).filter p).length = (l.filter p).length := by
  induction l generalizing i with
  | nil => simp at h
  | cons a t ih =>
    cases i with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at h
      subst h
      rw [List.set_cons_zero, List.filter_cons, List.filter_cons]
      by_cases hpn : p new = true <;> simp [hpn, hp]
    | succ k =>
      rw [List.set_cons_succ, List.filter_cons, List.filter_cons]
      by_cases hpa : p a = true
      · simp [hpa, ih (i := k) (by simpa using h)]
      · simp [hpa, ih (i := k) (by simpa using h)]

theorem filter_set_length_remove {l : List Val} {i : Nat} {old new : Val}
    {p : Val → Bool} (h : l[i]? = some old) (hold : p old = true) (hnew : p new = false) :
    ((l.set i new).filter p).length + 1 = (l.filter p).length := by
  induction l generalizing i with
  | nil => simp at h
  | cons a t ih =>
    cases i with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at h
      subst h
      rw [List.set_cons_zero, List.filter_cons, List.filter_cons]
      simp [hold, hnew]
    | succ k =>
      rw [List.set_cons_succ, List.filter_cons, List.filter_cons]
      by_cases hpa : p a = true
      · simp [hpa, ih (i := k) (by simpa using h)]
      · simp [hpa, ih (i := k) (by simpa using h)]

theorem filter_set_length_add {l : List Val} {i : Nat} {old new : Val}
    {p : Val → Bool} (h : l[i]? = some old) (hold : p old = false) (hnew : p new = true) :
    ((l.set i new).filter p).length = (l.filter p).length + 1 := by
  induction l generalizing i with
  | nil => simp at h
  | cons a t ih =>
    cases i with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at h
      subst h
      rw [List.set_cons_zero, List.filter_cons, List.filter_cons]
      simp [hold, hnew]
    | succ k =>
      rw [List.set_cons_succ, List.filter_cons, List.filter_cons]
      by_cases hpa : p a = true
      · simp [hpa, ih (i := k) (by simpa using h)]
      · simp [hpa, ih (i := k) (by simpa using h)]

/-- A `.scalar` slot rewritten with another `.scalar` leaves every reference's
occurrence count unchanged. -/
theorem RefCount_set_scalar_scalar {fields : Array Val} {i old w : Nat}
    (h : fields[i]? = some (.scalar old)) (q : Ref) :
    RefCount (fields.set! i (.scalar w)) q = RefCount fields q := by
  unfold RefCount
  rw [Array.toList_set!]
  rw [← Array.getElem?_toList] at h
  exact filter_set_length_eq (p := fun v => v = .ref q) (old := .scalar old)
    (new := .scalar w) h (by simp)

/-- Emptying a slot that held `.ref e` lowers `e`'s occurrence count by one. -/
theorem RefCount_set_ref_scalar_of_eq {fields : Array Val} {i w : Nat} {e : Ref}
    (h : fields[i]? = some (.ref e)) :
    RefCount (fields.set! i (.scalar w)) e + 1 = RefCount fields e := by
  unfold RefCount
  rw [Array.toList_set!]
  rw [← Array.getElem?_toList] at h
  exact filter_set_length_remove (p := fun v => v = .ref e) (old := .ref e)
    (new := .scalar w) h (by simp) (by simp)

/-- Emptying a slot that held `.ref e` leaves every other reference's occurrence
count unchanged. -/
theorem RefCount_set_ref_scalar_of_ne {fields : Array Val} {i w : Nat} {e q : Ref}
    (h : fields[i]? = some (.ref e)) (hq : q ≠ e) :
    RefCount (fields.set! i (.scalar w)) q = RefCount fields q := by
  unfold RefCount
  rw [Array.toList_set!]
  rw [← Array.getElem?_toList] at h
  have hqe : e ≠ q := fun hh => hq hh.symm
  exact filter_set_length_eq (p := fun v => v = .ref q) (old := .ref e)
    (new := .scalar w) h (by simp [hqe])

/-- Filling a `.scalar` slot with `.ref e` raises `e`'s occurrence count by
one. -/
theorem RefCount_set_scalar_ref_of_eq {fields : Array Val} {i old : Nat} {e : Ref}
    (h : fields[i]? = some (.scalar old)) :
    RefCount (fields.set! i (.ref e)) e = RefCount fields e + 1 := by
  unfold RefCount
  rw [Array.toList_set!]
  rw [← Array.getElem?_toList] at h
  exact filter_set_length_add (p := fun v => v = .ref e) (old := .scalar old)
    (new := .ref e) h (by simp) (by simp)

/-- Filling a `.scalar` slot with `.ref e` leaves every other reference's
occurrence count unchanged. -/
theorem RefCount_set_scalar_ref_of_ne {fields : Array Val} {i old : Nat} {e q : Ref}
    (h : fields[i]? = some (.scalar old)) (hq : q ≠ e) :
    RefCount (fields.set! i (.ref e)) q = RefCount fields q := by
  unfold RefCount
  rw [Array.toList_set!]
  rw [← Array.getElem?_toList] at h
  have hqe : e ≠ q := fun hh => hq hh.symm
  exact filter_set_length_eq (p := fun v => v = .ref q) (old := .scalar old)
    (new := .ref e) h (by simp [hqe])

/-- An empty-slot rewrite of the same kind as the take-out's. -/
theorem RefCount_setIfInBounds_ref_scalar_of_eq {fields : Array Val} {i w : Nat} {e : Ref}
    (h : fields[i]? = some (.ref e)) :
    RefCount (fields.setIfInBounds i (.scalar w)) e + 1 = RefCount fields e := by
  unfold RefCount
  rw [Array.toList_setIfInBounds]
  rw [← Array.getElem?_toList] at h
  exact filter_set_length_remove (p := fun v => v = .ref e) (old := .ref e)
    (new := .scalar w) h (by simp) (by simp)

/-- The same rewrite leaves every other reference's occurrence count unchanged. -/
theorem RefCount_setIfInBounds_ref_scalar_of_ne {fields : Array Val} {i w : Nat} {e q : Ref}
    (h : fields[i]? = some (.ref e)) (hq : q ≠ e) :
    RefCount (fields.setIfInBounds i (.scalar w)) q = RefCount fields q := by
  unfold RefCount
  rw [Array.toList_setIfInBounds]
  rw [← Array.getElem?_toList] at h
  have hqe : e ≠ q := fun hh => hq hh.symm
  exact filter_set_length_eq (p := fun v => v = .ref q) (old := .ref e)
    (new := .scalar w) h (by simp [hqe])

/-! ### The edge count under one cell replacement -/

/-- Replacing the cell at `r` changes the incoming-edge count of `q` only by the
difference between the old and the new field array's `.ref q` occurrences. -/
theorem IncomingCount_set {H : Heap} {r q : Ref} {o o' : Obj}
    (hcell : H.cells r = some o) (hnext : r < H.next) :
    IncomingCount (H.set r o') q + RefCount o.fields q
      = IncomingCount H q + RefCount o'.fields q := by
  have hsplit := sum_range_split (f := fun p => EdgeAt (H.set r o') p q)
    (g := fun p => EdgeAt H p q) hnext (fun p hp _ => by
      simp [EdgeAt, Heap.set_other H r p o' hp])
  have hfr : EdgeAt (H.set r o') r q = RefCount o'.fields q := by
    simp [EdgeAt, Heap.set]
  have hgr : EdgeAt H r q = RefCount o.fields q := by
    simp [EdgeAt, hcell]
  rw [hfr, hgr] at hsplit
  have h1 : IncomingCount (H.set r o') q
      = ((List.range H.next).map (fun p => EdgeAt (H.set r o') p q)).sum := rfl
  have h2 : IncomingCount H q
      = ((List.range H.next).map (fun p => EdgeAt H p q)).sum := rfl
  rw [h1, h2]
  exact hsplit


/-- The incoming-edge count is unchanged when only a cell's count field changes
(`Heap.inc`, `Heap.dec`). -/
theorem IncomingCount_inc {H : Heap} {r : Ref} {n : Nat} (q : Ref) :
    IncomingCount (H.inc r n) q = IncomingCount H q := by
  cases h : H.cells r with
  | none => simp [IncomingCount_eq_edges, Heap.inc, h]
  | some o =>
    have hnext : (H.inc r n).next = H.next := by
      simp only [Heap.inc, h]
      rfl
    rw [IncomingCount_eq_edges, IncomingCount_eq_edges, hnext]
    apply sum_range_congr
    intro p _
    by_cases hpr : p = r
    · subst hpr
      simp [EdgeAt, Heap.inc, h, Heap.set]
    · simp [EdgeAt, Heap.inc, h, Heap.set_other _ _ _ _ hpr]

theorem IncomingCount_dec {H : Heap} {r : Ref} {n : Nat} (q : Ref) :
    IncomingCount (H.dec r n) q = IncomingCount H q := by
  cases h : H.cells r with
  | none => simp [IncomingCount_eq_edges, Heap.dec, h]
  | some o =>
    have hnext : (H.dec r n).next = H.next := by
      simp only [Heap.dec, h]
      rfl
    rw [IncomingCount_eq_edges, IncomingCount_eq_edges, hnext]
    apply sum_range_congr
    intro p _
    by_cases hpr : p = r
    · subst hpr
      simp [EdgeAt, Heap.dec, h, Heap.set]
    · simp [EdgeAt, Heap.dec, h, Heap.set_other _ _ _ _ hpr]

/-- The in-place scalar store leaves every incoming-edge count unchanged. -/
theorem IncomingCount_set_scalar_of_scalar {H : Heap} {r : Ref} {o : Obj}
    {idx old w : Nat} (hcell : H.cells r = some o) (hnext : r < H.next)
    (hslot : o.fields[idx]? = some (.scalar old)) (q : Ref) :
    IncomingCount (H.set r { o with fields := o.fields.set! idx (.scalar w) }) q
      = IncomingCount H q := by
  have h := IncomingCount_set (H := H) (r := r) (q := q) (o := o)
    (o' := { o with fields := o.fields.set! idx (.scalar w) }) hcell hnext
  have hrc : RefCount ({ o with fields := o.fields.set! idx (.scalar w) } : Obj).fields q
      = RefCount o.fields q :=
    RefCount_set_scalar_scalar hslot q
  rw [hrc] at h
  exact Nat.add_right_cancel h

/-- The take-out's edge removal raises the emptied reference's incoming count by
exactly one: the count after the store is one lower. -/
theorem IncomingCount_set_of_ref {H : Heap} {r e : Ref} {o : Obj} {idx w : Nat}
    (hcell : H.cells r = some o) (hnext : r < H.next)
    (hslot : o.fields[idx]? = some (.ref e)) :
    IncomingCount H e
      = IncomingCount
          (H.set r { o with fields := o.fields.setIfInBounds idx (.scalar w) }) e + 1 := by
  have h := IncomingCount_set (H := H) (r := r) (q := e) (o := o)
    (o' := { o with fields := o.fields.setIfInBounds idx (.scalar w) }) hcell hnext
  have hrc :
      RefCount ({ o with fields := o.fields.setIfInBounds idx (.scalar w) } : Obj).fields e + 1
        = RefCount o.fields e :=
    RefCount_setIfInBounds_ref_scalar_of_eq hslot
  rw [← hrc] at h
  omega

/-- The take-out's edge removal leaves every other reference's incoming count
unchanged. -/
theorem IncomingCount_set_of_ref_ne {H : Heap} {r e : Ref} {o : Obj} {idx w : Nat}
    (hcell : H.cells r = some o) (hnext : r < H.next)
    (hslot : o.fields[idx]? = some (.ref e)) {q : Ref} (hq : q ≠ e) :
    IncomingCount
        (H.set r { o with fields := o.fields.setIfInBounds idx (.scalar w) }) q
      = IncomingCount H q := by
  have h := IncomingCount_set (H := H) (r := r) (q := q) (o := o)
    (o' := { o with fields := o.fields.setIfInBounds idx (.scalar w) }) hcell hnext
  have hrc :
      RefCount ({ o with fields := o.fields.setIfInBounds idx (.scalar w) } : Obj).fields q
        = RefCount o.fields q :=
    RefCount_setIfInBounds_ref_scalar_of_ne hslot hq
  rw [hrc] at h
  exact Nat.add_right_cancel h

/-- The put-back's edge fill raises the returned reference's incoming count by
exactly one. -/
theorem IncomingCount_set_fill {H : Heap} {r re : Ref} {o : Obj} {idx old : Nat}
    (hcell : H.cells r = some o) (hnext : r < H.next)
    (hslot : o.fields[idx]? = some (.scalar old)) :
    IncomingCount (H.set r { o with fields := o.fields.set! idx (.ref re) }) re
      = IncomingCount H re + 1 := by
  have h := IncomingCount_set (H := H) (r := r) (q := re) (o := o)
    (o' := { o with fields := o.fields.set! idx (.ref re) }) hcell hnext
  have hrc : RefCount ({ o with fields := o.fields.set! idx (.ref re) } : Obj).fields re
      = RefCount o.fields re + 1 :=
    RefCount_set_scalar_ref_of_eq hslot
  rw [hrc] at h
  omega

/-- The put-back's edge fill leaves every other reference's incoming count
unchanged. -/
theorem IncomingCount_set_fill_ne {H : Heap} {r re : Ref} {o : Obj} {idx old : Nat}
    (hcell : H.cells r = some o) (hnext : r < H.next)
    (hslot : o.fields[idx]? = some (.scalar old)) {q : Ref} (hq : q ≠ re) :
    IncomingCount (H.set r { o with fields := o.fields.set! idx (.ref re) }) q
      = IncomingCount H q := by
  have h := IncomingCount_set (H := H) (r := r) (q := q) (o := o)
    (o' := { o with fields := o.fields.set! idx (.ref re) }) hcell hnext
  have hrc : RefCount ({ o with fields := o.fields.set! idx (.ref re) } : Obj).fields q
      = RefCount o.fields q :=
    RefCount_set_scalar_ref_of_ne hslot hq
  rw [hrc] at h
  exact Nat.add_right_cancel h

/-- The cell replacement leaves the heap's cell domain where it was, so the
`domain` field of the relation is preserved by every field effect. -/
theorem Heap_set_next (H : Heap) (r : Ref) (o : Obj) :
    (H.set r o).next = H.next := rfl

theorem Heap_inc_next (H : Heap) (r : Ref) (n : Nat) :
    (H.inc r n).next = H.next := by
  cases h : H.cells r with
  | none => simp [Heap.inc, h]
  | some o =>
    simp only [Heap.inc, h]
    rfl

theorem Heap_dec_next (H : Heap) (r : Ref) (n : Nat) :
    (H.dec r n).next = H.next := by
  cases h : H.cells r with
  | none => simp [Heap.dec, h]
  | some o =>
    simp only [Heap.dec, h]
    rfl

/-! ### Supports and the environment-owner count -/

/-- Replace one variable by another in a support enumeration. The ownership move
transfers a handle from the first to the second; the enumeration follows it. -/
def replaceVar (l : List Var) (x y : Var) : List Var :=
  l.map (fun z => if z = x then y else z)

theorem replaceVar_length (l : List Var) (x y : Var) :
    (replaceVar l x y).length = l.length := by
  simp [replaceVar]

/-- Membership in a rewritten support: the entries are the old entries other than
`x`, together with `y` when `x` was present. -/
theorem replaceVar_mem {l : List Var} {x y z : Var} :
    z ∈ replaceVar l x y ↔ (z = y ∧ x ∈ l) ∨ (z ∈ l ∧ z ≠ x) := by
  unfold replaceVar
  rw [List.mem_map]
  constructor
  · rintro ⟨w, hw, hwz⟩
    by_cases hwx : w = x
    · subst hwx
      have hzy : z = y := by simpa using hwz.symm
      exact Or.inl ⟨hzy, hw⟩
    · have hzw : z = w := by simpa [hwx] using hwz.symm
      subst hzw
      exact Or.inr ⟨hw, hwx⟩
  · rintro (⟨rfl, hx⟩ | ⟨hz, hzx⟩)
    · exact ⟨x, hx, by simp⟩
    · exact ⟨z, hz, by simp [hzx]⟩

theorem replaceVar_cons (a : Var) (t : List Var) (x y : Var) :
    replaceVar (a :: t) x y = (if a = x then y else a) :: replaceVar t x y := by
  simp [replaceVar]

theorem replaceVar_nodup {l : List Var} {x y : Var} (h : l.Nodup) (hy : y ∉ l) :
    (replaceVar l x y).Nodup := by
  induction l with
  | nil => simp [replaceVar]
  | cons a t ih =>
    rw [List.nodup_cons] at h
    have hy' : y ∉ t := fun hh => hy (List.mem_cons_of_mem a hh)
    have ih' := ih h.2 hy'
    by_cases hax : a = x
    · subst hax
      have hmap : replaceVar t a y = t := by
        unfold replaceVar
        rw [List.map_congr_left (g := id) (fun z hz => by
          have hza : z ≠ a := fun hh => h.1 (hh ▸ hz)
          simp [hza])]
        simp
      rw [replaceVar_cons, hmap]
      simp [hy', h.2]
    · have hfa : (if a = x then y else a) = a := by simp [hax]
      rw [replaceVar_cons, hfa]
      rw [List.nodup_cons]
      refine ⟨?_, ih'⟩
      intro hmem
      rw [replaceVar_mem] at hmem
      rcases hmem with ⟨hay, hx⟩ | ⟨ht, _⟩
      · have : y ∈ a :: t := by
          rw [← hay]
          exact List.mem_cons_self
        exact hy this
      · exact h.1 ht


/-- Removing an entry the predicate rejects leaves a filtered length alone. -/
theorem filter_erase_length_eq {α : Type} [BEq α] [LawfulBEq α]
    {l : List α} {P : α → Bool} {x : α} (hP : P x = false) :
    ((l.erase x).filter P).length = (l.filter P).length := by
  induction l with
  | nil => simp
  | cons a t ih =>
    by_cases hax : a = x
    · subst hax
      rw [List.erase_cons_head, List.filter_cons, hP]
      simp
    · have hbeq : (a == x) = false := by
        by_cases h : (a == x) = true
        · exact absurd (beq_iff_eq.mp h) hax
        · simpa using h
      rw [List.erase_cons_tail (by rw [hbeq]; simp), List.filter_cons, List.filter_cons]
      by_cases hpa : P a = true <;> simp [hpa, ih]

/-- Removing a counted entry lowers a filtered length by one. -/
theorem filter_erase_length_add {α : Type} [BEq α] [LawfulBEq α]
    {l : List α} {P : α → Bool} {x : α} (hx : x ∈ l) (hP : P x = true) :
    ((l.erase x).filter P).length + 1 = (l.filter P).length := by
  induction l with
  | nil => simp at hx
  | cons a t ih =>
    by_cases hax : a = x
    · subst hax
      rw [List.erase_cons_head, List.filter_cons_of_pos hP]
      simp
    · have hbeq : (a == x) = false := by
        by_cases h : (a == x) = true
        · exact absurd (beq_iff_eq.mp h) hax
        · simpa using h
      rw [List.erase_cons_tail (by rw [hbeq]; simp), List.filter_cons, List.filter_cons]
      have hx' : x ∈ t := by
        rcases List.mem_cons.mp hx with h | h
        · exact absurd h.symm hax
        · exact h
      by_cases hpa : P a = true <;> simp [hpa, ih hx']

/-! ### Environment-owner counts under context effects -/

/-- A context rewrite away from the support leaves the owner count alone. -/
theorem EnvOwnerCount_setUs {c : Ctx} {x : Var} {u : U} {vs : List Var} {r : Ref}
    (hx : x ∉ vs) :
    EnvOwnerCount (c.setUs x u) vs r = EnvOwnerCount c vs r := by
  unfold EnvOwnerCount
  congr 1
  apply List.filter_congr
  intro z hz
  have hzx : z ≠ x := fun h => hx (h ▸ hz)
  simp [Ctx.setUs, hzx]

/-- The move transfers the enumeration's `x` entry to `y`, which the support
does not already contain. -/
theorem EnvOwnerCount_move {c : Ctx} {x y : Var} {vs : List Var} {r : Ref}
    (hy : y ∉ vs) :
    EnvOwnerCount (c.move x y) (replaceVar vs x y) r = EnvOwnerCount c vs r := by
  unfold EnvOwnerCount replaceVar
  rw [List.filter_map, List.length_map]
  congr 1
  apply List.filter_congr
  intro z hz
  by_cases hzx : z = x
  · subst hzx
    simp [Ctx.move_us_y, Ctx.move_refOf_y]
  · have hzy : z ≠ y := fun h => hy (h ▸ hz)
    have hfz : (if z = x then y else z) = z := by simp [hzx]
    simp only [Function.comp_apply]
    rw [hfz]
    simp [Ctx.move_us_other (c := c) (x := x) (y := y) (z := z) hzy hzx,
      Ctx.move_refOf_other (c := c) (x := x) (y := y) (z := z) hzy]

/-- A counted support entry is one owner; removing it lowers the count by one. -/
theorem EnvOwnerCount_erase {c : Ctx} {vs : List Var} {x : Var} {r : Ref}
    (hx : x ∈ vs) (hP : c.us x = .owned ∧ c.refOf x = some r) :
    EnvOwnerCount c (vs.erase x) r + 1 = EnvOwnerCount c vs r := by
  unfold EnvOwnerCount
  exact filter_erase_length_add
    (P := fun z => c.us z = .owned ∧ c.refOf z = some r) hx (by simp [hP])

/-- The take-out's fresh owner is the only new contribution. -/
theorem EnvOwnerCount_bindOwned {c : Ctx} {x : Var} {e : Ref} {vs : List Var} {r : Ref}
    (hx : x ∉ vs) :
    EnvOwnerCount (c.bindOwned x e) (x :: vs) r
      = EnvOwnerCount c vs r + (if e = r then 1 else 0) := by
  unfold EnvOwnerCount
  rw [List.filter_cons]
  have htail :
      List.filter (fun z => (c.bindOwned x e).us z = .owned ∧
        (c.bindOwned x e).refOf z = some r) vs
        = List.filter (fun z => c.us z = .owned ∧ c.refOf z = some r) vs := by
    apply List.filter_congr
    intro z hz
    have hzx : z ≠ x := fun h => hx (h ▸ hz)
    simp [Ctx.bindOwned, hzx]
  rw [htail]
  by_cases her : e = r
  · subst her
    simp [Ctx.bindOwned]
  · simp [Ctx.bindOwned, her]

/-- A decrement changes only the count, so the owner count is untouched. -/
theorem EnvOwnerCount_dec (c : Ctx) (r : Ref) (n : Nat) (vs : List Var) (q : Ref) :
    EnvOwnerCount (c.dec r n) vs q = EnvOwnerCount c vs q := rfl

/-- A filtered list of a duplicate-free list is duplicate-free. -/
theorem nodup_filter {l : List Var} {P : Var → Bool} (h : l.Nodup) :
    (l.filter P).Nodup := by
  induction l with
  | nil => simp
  | cons a t ih =>
    rw [List.nodup_cons] at h
    have ih' := ih h.2
    rw [List.filter_cons]
    by_cases hpa : P a = true
    · simp [hpa, ih', h.1]
    · simp [hpa, ih']

/-- Two distinct members make a list at least two long. -/
theorem two_le_length_of_nodup_mem {l : List Var} {x y : Var}
    (_h : l.Nodup) (hx : x ∈ l) (hy : y ∈ l) (hxy : x ≠ y) : 2 ≤ l.length := by
  have h1 : x ∈ l.erase y := (List.mem_erase_of_ne hxy).mpr hx
  have hpos : 0 < (l.erase y).length := List.length_pos_iff_exists_mem.mpr ⟨x, h1⟩
  have hlen : (l.erase y).length = l.length - 1 := List.length_erase_of_mem hy
  omega

/-- Two duplicate-free enumerations of the same set have the same length. -/
theorem length_eq_of_nodup_mem_iff {l₁ : List Var} :
    ∀ {l₂ : List Var}, l₁.Nodup → l₂.Nodup →
      (∀ z, z ∈ l₁ ↔ z ∈ l₂) → l₁.length = l₂.length := by
  induction l₁ with
  | nil =>
    intro l₂ _ h₂ h
    have hempty : l₂ = [] := by
      cases l₂ with
      | nil => rfl
      | cons b t =>
        have hb : b ∈ ([] : List Var) := (h b).mpr List.mem_cons_self
        simp at hb
    subst hempty
    rfl
  | cons a t ih =>
    intro l₂ h₁ h₂ h
    rw [List.nodup_cons] at h₁
    have ha : a ∈ l₂ := (h a).mp List.mem_cons_self
    have hsub : ∀ z, z ∈ t ↔ z ∈ l₂.erase a := by
      intro z
      constructor
      · intro hz
        have hza : z ≠ a := by
          intro hh
          subst hh
          exact h₁.1 hz
        have hz₂ : z ∈ l₂ := (h z).mp (List.mem_cons_of_mem a hz)
        exact (List.mem_erase_of_ne hza).mpr hz₂
      · intro hz
        have hz₂ : z ∈ l₂ := List.mem_of_mem_erase hz
        have hz' : z ∈ a :: t := (h z).mpr hz₂
        rcases List.mem_cons.mp hz' with hza | hzt
        · subst hza
          exact absurd hz h₂.not_mem_erase
        · exact hzt
    have ih' := ih h₁.2 (h₂.erase a) hsub
    have hpos : 0 < l₂.length := List.length_pos_iff_exists_mem.mpr ⟨a, ha⟩
    rw [List.length_cons, ih', List.length_erase_of_mem ha]
    omega

/-- A sum of naturals is at least any of its entries. -/
theorem le_sum_of_mem {l : List Nat} {a : Nat} (h : a ∈ l) : a ≤ l.sum := by
  induction l with
  | nil => simp at h
  | cons b t ih =>
    rw [List.sum_cons]
    rcases List.mem_cons.mp h with rfl | ht
    · omega
    · have := ih ht
      omega

/-- A field array holding `.ref e` at one index contributes at least one edge. -/
theorem RefCount_pos_of_slot {fields : Array Val} {i : Nat} {e : Ref}
    (h : fields[i]? = some (.ref e)) : 1 ≤ RefCount fields e := by
  unfold RefCount
  rw [← Array.getElem?_toList] at h
  have hmem : Val.ref e ∈ fields.toList := List.mem_of_getElem? h
  have hf : Val.ref e ∈ fields.toList.filter (fun v => v = Val.ref e) := by
    rw [List.mem_filter]
    exact ⟨hmem, by simp⟩
  exact List.length_pos_iff_exists_mem.mpr ⟨_, hf⟩

/-! ## The complete relation -/

/-- The complete accounting relation: the checker invariant, a duplicate-free,
sound, complete and bound enumeration of the owning variables, the live-cell
domain the edge count enumerates, and the count equation. -/
structure Accounted (support : List Var) (H : Heap) (env : Env) (c : Ctx) : Prop where
  /-- The checker invariant: the stored count is `mult`, owned variables denote
  their reference, and every live cell is non-persistent. -/
  inv : Inv H env c
  /-- The enumeration is duplicate-free. A repeated entry would inflate
  `EnvOwnerCount` (`dupSupport_witness`). -/
  support_nodup : support.Nodup
  /-- Every enumeration entry is an owning variable. -/
  support_sound : ∀ x, x ∈ support → c.us x = .owned
  /-- Every owning variable is enumerated. An omitted owner breaks the count
  equation (`omittedOwner_witness`). -/
  support_complete : ∀ x, c.us x = .owned → x ∈ support
  /-- Every enumeration entry names a reference. Without this a root could own
  nothing (`unboundRoot_witness`). -/
  support_bound : ∀ x, x ∈ support → ∃ r, c.refOf x = some r
  /-- Every live cell is inside the range the edge count enumerates. Without
  this an out-of-range cell hides its edges (`outOfRange_rejected`). -/
  domain : ∀ r o, H.cells r = some o → r < H.next
  /-- The count equation, over two independently computed quantities. -/
  count : ∀ r, H.rc r = IncomingCount H r + EnvOwnerCount c support r

namespace Accounted

/-- The checker-facing form of the count equation. -/
theorem mult_eq {support : List Var} {H : Heap} {env : Env} {c : Ctx}
    (h : Accounted support H env c) (r : Ref) :
    c.mult r = IncomingCount H r + EnvOwnerCount c support r := by
  rw [← h.inv.rc_eq r, h.count r]

/-- A count-one object is carried by exactly one counted obligation. -/
theorem count_one_dichotomy {support : List Var} {H : Heap} {env : Env} {c : Ctx}
    (h : Accounted support H env c) {r : Ref} (hm : c.mult r = 1) :
    (EnvOwnerCount c support r = 1 ∧ IncomingCount H r = 0) ∨
      (EnvOwnerCount c support r = 0 ∧ IncomingCount H r = 1) := by
  have hsum := h.mult_eq r
  rw [hm] at hsum
  by_cases hE : EnvOwnerCount c support r = 0
  · exact Or.inr ⟨hE, by omega⟩
  · have hE1 : EnvOwnerCount c support r = 1 := by omega
    exact Or.inl ⟨hE1, by omega⟩

/-- At count one, two owning variables naming the reference are the same
variable. -/
theorem at_most_one_owner {support : List Var} {H : Heap} {env : Env} {c : Ctx}
    (h : Accounted support H env c) {r : Ref} (hm : c.mult r = 1)
    {x y : Var} (hx : c.us x = .owned) (hy : c.us y = .owned)
    (hrx : c.refOf x = some r) (hry : c.refOf y = some r) : x = y := by
  by_cases hxy : x = y
  · exact hxy
  · exfalso
    have hxmem : x ∈ support := h.support_complete x hx
    have hymem : y ∈ support := h.support_complete y hy
    have hfx : x ∈ support.filter (fun z => c.us z = .owned ∧ c.refOf z = some r) := by
      rw [List.mem_filter]
      exact ⟨hxmem, by simp [hx, hrx]⟩
    have hfy : y ∈ support.filter (fun z => c.us z = .owned ∧ c.refOf z = some r) := by
      rw [List.mem_filter]
      exact ⟨hymem, by simp [hy, hry]⟩
    have htwo : 2 ≤ EnvOwnerCount c support r := by
      unfold EnvOwnerCount
      exact two_le_length_of_nodup_mem (nodup_filter h.support_nodup) hfx hfy hxy
    have hsum := h.mult_eq r
    rw [hm] at hsum
    omega

/-- At count one the heap contributes at most one incoming edge. -/
theorem incoming_le_one {support : List Var} {H : Heap} {env : Env} {c : Ctx}
    (h : Accounted support H env c) {r : Ref} (hm : c.mult r = 1) :
    IncomingCount H r ≤ 1 := by
  have hsum := h.mult_eq r
  rw [hm] at hsum
  omega

/-- The retained environment-side predicate is a consequence of the relation. -/
theorem ownersAccounted {support : List Var} {H : Heap} {env : Env} {c : Ctx}
    (h : Accounted support H env c) : OwnersAccounted c := by
  constructor
  · intro r x hm hx hr
    have hxmem : x ∈ support := h.support_complete x hx
    have hfy : x ∈ support.filter (fun z => c.us z = .owned ∧ c.refOf z = some r) := by
      rw [List.mem_filter]
      exact ⟨hxmem, by simp [hx, hr]⟩
    have hpos : 0 < EnvOwnerCount c support r := by
      unfold EnvOwnerCount
      exact List.length_pos_iff_exists_mem.mpr ⟨x, hfy⟩
    have hsum := h.mult_eq r
    rw [hm] at hsum
    omega
  · intro r hm x y hx hy hrx hry
    exact at_most_one_owner h hm hx hy hrx hry

/-- The count equation in the retained contract's shape. -/
theorem countFidelity {support : List Var} {H : Heap} {env : Env} {c : Ctx}
    (h : Accounted support H env c) : CountFidelity H c support :=
  fun r => h.count r

/-- From the relation plus one incoming edge, the extracted element has no
owning variable. The edge count is **not** supplied by the checker footprint:
`UniqueTree` gives `H.rc e = 1`, a count rather than the absence of a second
edge, so a no-second-edge premise belongs to the caller. -/
theorem noOwnerOfSingleEdge {support : List Var} {H : Heap} {env : Env} {c : Ctx}
    (h : Accounted support H env c) {e : Ref} (hm : c.mult e = 1)
    (hedge : IncomingCount H e = 1) :
    ∀ y, c.us y = .owned → c.refOf y = some e → False := by
  intro y hy hry
  have hsum := h.mult_eq e
  rw [hm, hedge] at hsum
  have hE0 : EnvOwnerCount c support e = 0 := by omega
  have hymem : y ∈ support := h.support_complete y hy
  have hfy : y ∈ support.filter (fun z => c.us z = .owned ∧ c.refOf z = some e) := by
    rw [List.mem_filter]
    exact ⟨hymem, by simp [hy, hry]⟩
  have hpos : 0 < EnvOwnerCount c support e := by
    unfold EnvOwnerCount
    exact List.length_pos_iff_exists_mem.mpr ⟨y, hfy⟩
  omega

/-- A live cell whose slot holds `.ref e` gives at least one incoming edge to
`e`. The live-cell domain is what makes the enumeration see the slot: this is
the fact `outOfRange_rejected` shows is not free. -/
theorem IncomingCount_pos_of_slot {support : List Var} {H : Heap} {env : Env} {c : Ctx}
    (h : Accounted support H env c) {r : Ref} {o : Obj} {idx : Nat} {e : Ref}
    (hcell : H.cells r = some o) (hslot : o.fields[idx]? = some (.ref e)) :
    1 ≤ IncomingCount H e := by
  have hnext : r < H.next := h.domain r o hcell
  rw [IncomingCount_eq_edges]
  have hmem : EdgeAt H r e ∈ (List.range H.next).map (fun q => EdgeAt H q e) :=
    List.mem_map.mpr ⟨r, List.mem_range.mpr hnext, rfl⟩
  have hpos : 1 ≤ EdgeAt H r e := by
    rw [show EdgeAt H r e = RefCount o.fields e from by simp [EdgeAt, hcell]]
    exact RefCount_pos_of_slot hslot
  exact Nat.le_trans hpos (le_sum_of_mem hmem)

/-- At count one the slot's edge is the child's only one: the relation bounds
the incoming count by one, and the slot supplies one. This is the supplier of
the take-out's no-second-edge premise that the checker does not see. -/
theorem incoming_eq_one_of_slot {support : List Var} {H : Heap} {env : Env}
    {c : Ctx} (h : Accounted support H env c) {r : Ref} {o : Obj} {idx : Nat} {e : Ref}
    (he : c.mult e = 1) (hcell : H.cells r = some o)
    (hslot : o.fields[idx]? = some (.ref e)) : IncomingCount H e = 1 :=
  Nat.le_antisymm (h.incoming_le_one he) (IncomingCount_pos_of_slot h hcell hslot)

/-! ## The initializer -/

/-- The initializer's field array holds no reference. -/
theorem RefCount_initFields (n : Nat) (q : Ref) :
    RefCount (Array.replicate n (.scalar 0)) q = 0 := by
  unfold RefCount
  rw [Array.toList_replicate]
  simp

theorem IncomingCount_initHeap (n : Nat) (q : Ref) :
    IncomingCount (Runner.initHeap n).2 q = 0 := by
  rw [IncomingCount_eq_edges]
  have hnext : (Runner.initHeap n).2.next = 1 := rfl
  rw [hnext]
  simp only [List.range_one, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
  have hcells : (Runner.initHeap n).2.cells 0
      = some ⟨Array.replicate n (.scalar 0), 1, false⟩ := by
    simp [Runner.initHeap]
  simp [EdgeAt, hcells, RefCount_initFields]

theorem EnvOwnerCount_initCtx (r q : Ref) :
    EnvOwnerCount (Runner.initCtx r) [0] q = if q = r then 1 else 0 := by
  unfold EnvOwnerCount
  by_cases hqr : q = r
  · subst hqr
    simp [Runner.initCtx]
  · have hne : ¬ (r = q) := fun h => hqr h.symm
    simp [Runner.initCtx, hqr, hne]

/-- The initializer establishes the relation: one owning variable, one live
cell, and no heap edges, because every initial field is a scalar. -/
theorem initCtx (n : Nat) :
    Accounted [0] (Runner.initHeap n).2 (Runner.initEnv (Runner.initHeap n).1)
      (Runner.initCtx (Runner.initHeap n).1) := by
  refine
    { inv := Runner.initInv n
      support_nodup := List.nodup_cons.mpr ⟨by simp, List.nodup_nil⟩
      support_sound := ?_
      support_complete := ?_
      support_bound := ?_
      domain := ?_
      count := ?_ }
  · intro x hx
    simp only [List.mem_singleton] at hx
    subst hx
    exact Runner.initCtx_us_zero _
  · intro x hx
    have hx0 : x = 0 := (initCtx_us_eq _ x).mp hx
    simp [hx0]
  · intro x hx
    simp only [List.mem_singleton] at hx
    subst hx
    exact ⟨_, Runner.initCtx_refOf_zero _⟩
  · intro q o hc
    by_cases hq : q = 0
    · subst hq
      simp [Runner.initHeap]
    · have hnone : (Runner.initHeap n).2.cells q = none := by
        simp [Runner.initHeap, hq]
      rw [hnone] at hc
      exact absurd hc (by simp)
  · intro q
    rw [IncomingCount_initHeap, EnvOwnerCount_initCtx]
    by_cases hq : q = (Runner.initHeap n).1
    · subst hq
      simp [Runner.initHeap, Heap.rc]
    · have hq0 : ¬ q = 0 := fun hh => hq (by simpa [Runner.initHeap] using hh)
      simp [Heap.rc, Runner.initHeap, hq0]

/-! ## Context operations -/

/-- Setting a non-owning variable dead preserves the relation. The premise is
required: deadening an *owning* variable would drop a counted obligation while
releasing no count, so that case is preserved only together with a heap effect
(`decOne`, or the put-back's fill). -/
theorem setDead {support : List Var} {H : Heap} {env : Env} {c : Ctx}
    (h : Accounted support H env c) {x : Var} (hx : c.us x ≠ .owned) :
    Accounted support H env (c.setUs x .dead) := by
  have hx' : x ∉ support := fun hmem => hx (h.support_sound x hmem)
  refine
    { inv := h.inv.setDead
      support_nodup := h.support_nodup
      support_sound := ?_
      support_complete := ?_
      support_bound := ?_
      domain := h.domain
      count := ?_ }
  · intro z hz
    by_cases hzx : z = x
    · subst hzx
      exact absurd hz hx'
    · simpa [Ctx.setUs, hzx] using h.support_sound z hz
  · intro z hz
    by_cases hzx : z = x
    · subst hzx
      simp [Ctx.setUs] at hz
    · exact h.support_complete z (by simpa [Ctx.setUs, hzx] using hz)
  · intro z hz
    simpa [Ctx.setUs] using h.support_bound z hz
  · intro r
    rw [h.count r, EnvOwnerCount_setUs hx']

/-- Binding a scalar leaves the relation alone; the environment-side count does
not depend on the environment. The premise keeps the count: re-marking an
owning variable as a scalar releases no count, and the checker does not supply
the condition (`scalarOverwrite_rejected`). -/
theorem setScalar {support : List Var} {H : Heap} {env : Env} {c : Ctx}
    (h : Accounted support H env c) {x : Var} (n : Nat) (hx : c.us x ≠ .owned) :
    Accounted support H (env.set x (.scalar n)) (c.setUs x .scalar) := by
  have hx' : x ∉ support := fun hmem => hx (h.support_sound x hmem)
  refine
    { inv := h.inv.setScalar (n := n)
      support_nodup := h.support_nodup
      support_sound := ?_
      support_complete := ?_
      support_bound := ?_
      domain := h.domain
      count := ?_ }
  · intro z hz
    by_cases hzx : z = x
    · subst hzx
      exact absurd hz hx'
    · simpa [Ctx.setUs, hzx] using h.support_sound z hz
  · intro z hz
    by_cases hzx : z = x
    · subst hzx
      simp [Ctx.setUs] at hz
    · exact h.support_complete z (by simpa [Ctx.setUs, hzx] using hz)
  · intro z hz
    simpa [Ctx.setUs] using h.support_bound z hz
  · intro r
    rw [h.count r, EnvOwnerCount_setUs hx']

/-- Moving a handle from `x` to a non-owning `y` preserves the relation; the
enumeration follows the handle. The `y` premise is required: moving onto an
already-owned `y` destroys that owner's obligation without changing a count. -/
theorem move {support : List Var} {H : Heap} {env : Env} {c : Ctx}
    (h : Accounted support H env c) {x y : Var} {r : Ref}
    (hx : c.us x = .owned) (hr : c.refOf x = some r) (hy : c.us y ≠ .owned) :
    Accounted (replaceVar support x y) H (env.set y (.ref r)) (c.move x y) := by
  have hy' : y ∉ support := fun hmem => hy (h.support_sound y hmem)
  refine
    { inv := h.inv.move hx hr
      support_nodup := replaceVar_nodup h.support_nodup hy'
      support_sound := ?_
      support_complete := ?_
      support_bound := ?_
      domain := h.domain
      count := ?_ }
  · intro z hz
    rw [replaceVar_mem] at hz
    rcases hz with ⟨rfl, _⟩ | ⟨hz, hzx⟩
    · rw [Ctx.move_us_y]
      exact hx
    · have hzy : z ≠ y := fun h => hy' (h ▸ hz)
      rw [Ctx.move_us_other (c := c) (x := x) (y := y) (z := z) hzy hzx]
      exact h.support_sound z hz
  · intro z hz
    by_cases hzy : z = y
    · rw [hzy] at hz
      rw [Ctx.move_us_y] at hz
      have hxmem : x ∈ support := h.support_complete x hz
      rw [replaceVar_mem]
      exact Or.inl ⟨hzy, hxmem⟩
    · by_cases hzx : z = x
      · exfalso
        have hxy : x ≠ y := fun hh => hzy (hzx.trans hh)
        have hdead : (c.move x y).us x = .dead := by simp [Ctx.move, hxy]
        rw [hzx] at hz
        rw [hdead] at hz
        exact absurd hz (by simp)
      · have hmv : (c.move x y).us z = c.us z :=
          Ctx.move_us_other (c := c) (x := x) (y := y) (z := z) hzy hzx
        rw [hmv] at hz
        have hmem : z ∈ support := h.support_complete z hz
        rw [replaceVar_mem]
        exact Or.inr ⟨hmem, hzx⟩
  · intro z hz
    rw [replaceVar_mem] at hz
    rcases hz with ⟨hz_eq, _⟩ | ⟨hz, hzx⟩
    · exact ⟨r, by rw [hz_eq, Ctx.move_refOf_y (c := c)]; exact hr⟩
    · have hzy : z ≠ y := fun h => hy' (h ▸ hz)
      obtain ⟨q, hq⟩ := h.support_bound z hz
      exact ⟨q, by
        rw [Ctx.move_refOf_other (c := c) (x := x) (y := y) (z := z) hzy]
        exact hq⟩
  · intro q
    rw [h.count q, EnvOwnerCount_move hy']

/-- One owner leaves and one count is released; the edge count and every other
obligation are untouched. `n = 1` is forced by the equation: a multi-handle
decrement releases counts no obligation carried (`decTwo_rejected`). -/
theorem decOne {support : List Var} {H : Heap} {env : Env} {c : Ctx}
    (h : Accounted support H env c) {x : Var} {r : Ref}
    (hx : c.us x = .owned) (hr : c.refOf x = some r) (hlt : 1 < c.mult r) :
    Accounted (support.erase x) (H.dec r 1) (env.erase x)
      ((c.dec r 1).setUs x .dead) := by
  have hxmem : x ∈ support := h.support_complete x hx
  have hxnmem : x ∉ support.erase x := List.Nodup.not_mem_erase h.support_nodup
  refine
    { inv := h.inv.dec hx hr hlt
      support_nodup := h.support_nodup.erase x
      support_sound := ?_
      support_complete := ?_
      support_bound := ?_
      domain := ?_
      count := ?_ }
  · intro z hz
    have hz' : z ∈ support := List.mem_of_mem_erase hz
    have hzx : z ≠ x := fun h => hxnmem (h ▸ hz)
    simpa [Ctx.setUs, hzx] using h.support_sound z hz'
  · intro z hz
    have hzx : z ≠ x := by
      intro h
      rw [h] at hz
      rw [Ctx.setUs_self] at hz
      exact absurd hz (by simp)
    have hz' : (c.dec r 1).us z = .owned := by simpa [Ctx.setUs, hzx] using hz
    have hmem : z ∈ support := h.support_complete z (by simpa using hz')
    exact (List.mem_erase_of_ne hzx).mpr hmem
  · intro z hz
    obtain ⟨q, hq⟩ := h.support_bound z (List.mem_of_mem_erase hz)
    exact ⟨q, by simpa [Ctx.setUs] using hq⟩
  · intro q o hc
    rw [Heap_dec_next]
    cases hr0 : H.cells r with
    | none =>
      exact h.domain q o (by simpa [Heap.dec, hr0] using hc)
    | some ob =>
      simp only [Heap.dec, hr0] at hc
      by_cases hqr : q = r
      · rw [hqr]
        exact h.domain r ob hr0
      · rw [Heap.set_other _ _ _ _ hqr] at hc
        exact h.domain q o hc
  · intro q
    have hinc : IncomingCount (H.dec r 1) q = IncomingCount H q := IncomingCount_dec q
    have hEcount :
        EnvOwnerCount ((c.dec r 1).setUs x .dead) (support.erase x) q
          = EnvOwnerCount c (support.erase x) q :=
      (EnvOwnerCount_setUs (c := c.dec r 1) (u := .dead) hxnmem).trans
        (EnvOwnerCount_dec c r 1 (support.erase x) q)
    have hrc : Heap.rc (H.dec r 1) q = Heap.rc H q - (if q = r then 1 else 0) := by
      by_cases hqr : q = r
      · rw [hqr, Heap.rc_dec_self]
        simp
      · rw [Heap.rc_dec_other hqr]
        simp [hqr]
    rw [hrc, hinc, hEcount, h.count q]
    by_cases hqr : q = r
    · rw [hqr]
      have hE : EnvOwnerCount c (support.erase x) r + 1 = EnvOwnerCount c support r :=
        EnvOwnerCount_erase hxmem ⟨hx, hr⟩
      have hif : (if r = r then 1 else 0) = 1 := by simp
      rw [hif]
      omega
    · have hxr : ¬ (c.refOf x = some q) := by
        intro hh
        exact hqr (Option.some.inj (by rw [hh] at hr; exact hr))
      have hPx : decide (c.us x = .owned ∧ c.refOf x = some q) = false := by
        by_cases h : c.us x = .owned ∧ c.refOf x = some q
        · exact absurd h.2 hxr
        · simp [h]
      have hE : EnvOwnerCount c (support.erase x) q = EnvOwnerCount c support q := by
        unfold EnvOwnerCount
        exact filter_erase_length_eq hPx
      rw [hE]
      simp [hqr]


/-! ### The heap effects -/

/-- The in-place scalar store: a `.scalar` slot rewritten with another
`.scalar` changes only the heap, so every support field and the count equation
hold at the same context. -/
theorem setFieldsScalar {support : List Var} {H : Heap} {env : Env} {c : Ctx}
    (h : Accounted support H env c) {r : Ref} {o : Obj} {idx old w : Nat}
    (hcell : H.cells r = some o) (hslot : o.fields[idx]? = some (.scalar old)) :
    Accounted support (H.set r { o with fields := o.fields.set! idx (.scalar w) }) env c := by
  have hnext : r < H.next := h.domain r o hcell
  refine
    { inv := h.inv.setFields hcell
      support_nodup := h.support_nodup
      support_sound := h.support_sound
      support_complete := h.support_complete
      support_bound := h.support_bound
      domain := ?_
      count := ?_ }
  · intro q o' hc
    rw [Heap_set_next]
    by_cases hqr : q = r
    · rw [hqr]
      exact h.domain r o hcell
    · rw [Heap.set_other _ _ _ _ hqr] at hc
      exact h.domain q o' hc
  · intro q
    have hrc : Heap.rc (H.set r { o with fields := o.fields.set! idx (.scalar w) }) q
        = Heap.rc H q := by
      by_cases hqr : q = r
      · rw [hqr, Heap.rc_set_self]
        simp [Heap.rc, hcell]
      · rw [Heap.rc_set_other hqr]
    rw [hrc, h.count q, IncomingCount_set_scalar_of_scalar hcell hnext hslot q]

/-- The designated store's own post-state: the in-place scalar write at the
checker's returned context. -/
theorem setArrInPlace {support : List Var} {H : Heap} {env : Env} {c : Ctx}
    (h : Accounted support H env c) {x : Var} {r : Ref} {o : Obj}
    {idx old val : Nat} (hx : c.us x = .owned) (hr : c.refOf x = some r)
    (hcell : H.cells r = some o) (hslot : o.fields[idx]? = some (.scalar old)) :
    Accounted support (H.set r { o with fields := o.fields.set! idx (.scalar val) })
      (env.set x (.ref r)) c := by
  have hnext : r < H.next := h.domain r o hcell
  refine
    { inv := h.inv.setArr hx hr hcell
      support_nodup := h.support_nodup
      support_sound := h.support_sound
      support_complete := h.support_complete
      support_bound := h.support_bound
      domain := ?_
      count := ?_ }
  · intro q o' hc
    rw [Heap_set_next]
    by_cases hqr : q = r
    · rw [hqr]
      exact h.domain r o hcell
    · rw [Heap.set_other _ _ _ _ hqr] at hc
      exact h.domain q o' hc
  · intro q
    have hrc : Heap.rc (H.set r { o with fields := o.fields.set! idx (.scalar val) }) q
        = Heap.rc H q := by
      by_cases hqr : q = r
      · rw [hqr, Heap.rc_set_self]
        simp [Heap.rc, hcell]
      · rw [Heap.rc_set_other hqr]
    rw [hrc, h.count q, IncomingCount_set_scalar_of_scalar hcell hnext hslot q]


/-- The take-out's atomic step: the array's handle moves to `fst`, the extracted
element's edge is removed from the array's slot and one fresh owner for it is
bound. The edge drop is exactly the new owner's contribution, so the count
equation holds at the interpreter's post-state. `hedge` is the no-second-edge
premise the checker does not supply (`noOwnerOfSingleEdge` consumes it); `hr` is
the `refOf` side of the checker's `c.multOf a = 1` condition. -/
theorem takeOut {support : List Var} {H : Heap} {env : Env} {c : Ctx}
    (h : Accounted support H env c) {a fst snd e : Var} {r : Ref} {o : Obj} {idx : Nat}
    (ha : c.us a = .owned) (_hma : c.multOf a = 1) (hr : c.refOf a = some r)
    (he : c.mult e = 1) (hfst : c.us fst ≠ .owned) (hsnd : c.us snd ≠ .owned)
    (hfs : fst ≠ snd) (_her : e ≠ r) (hcell : H.cells r = some o)
    (hslot : o.fields[idx]? = some (.ref e)) (hedge : IncomingCount H e = 1) :
    Accounted (snd :: replaceVar support a fst)
      (H.set r { o with fields := o.fields.setIfInBounds idx (.scalar 0) })
      ((env.set fst (.ref r)).set snd (.ref e)) ((c.move a fst).bindOwned snd e) := by
  have hfst' : fst ∉ support := fun hmem => hfst (h.support_sound fst hmem)
  have hsnd' : snd ∉ support := fun hmem => hsnd (h.support_sound snd hmem)
  have hnext : r < H.next := h.domain r o hcell
  have h₁ := h.move ha hr hfst
  have hsn : snd ∉ replaceVar support a fst := by
    rw [replaceVar_mem]
    rintro (⟨h1, _⟩ | ⟨h2, _⟩)
    · exact hfs h1.symm
    · exact hsnd' h2
  refine
    { inv := (h₁.inv.bindOwned he).setFields hcell
      support_nodup := List.nodup_cons.mpr ⟨hsn, h₁.support_nodup⟩
      support_sound := ?_
      support_complete := ?_
      support_bound := ?_
      domain := ?_
      count := ?_ }
  · intro z hz
    rcases List.mem_cons.mp hz with hz | hz
    · rw [hz]
      exact Ctx.bindOwned_us_self (c := c.move a fst) (x := snd) (r := e)
    · have hzs : z ≠ snd := fun hh => hsn (hh ▸ hz)
      rw [Ctx.bindOwned_us_other (c := c.move a fst) (x := snd) (z := z) (r := e) hzs]
      exact h₁.support_sound z hz
  · intro z hz
    by_cases hzs : z = snd
    · rw [hzs]
      exact List.mem_cons_self
    · have hz' : (c.move a fst).us z = .owned := by
        simpa [Ctx.bindOwned, hzs] using hz
      exact List.mem_cons_of_mem snd (h₁.support_complete z hz')
  · intro z hz
    rcases List.mem_cons.mp hz with hz | hz
    · rw [hz]
      exact ⟨e, Ctx.bindOwned_refOf_self (c := c.move a fst) (x := snd) (r := e)⟩
    · have hzs : z ≠ snd := fun hh => hsn (hh ▸ hz)
      obtain ⟨q, hq⟩ := h₁.support_bound z hz
      exact ⟨q, by simpa [Ctx.bindOwned, hzs] using hq⟩
  · intro q o' hc
    rw [Heap_set_next]
    by_cases hqr : q = r
    · rw [hqr]
      exact h.domain r o hcell
    · rw [Heap.set_other _ _ _ _ hqr] at hc
      exact h.domain q o' hc
  · intro q
    have hrc : Heap.rc
        (H.set r { o with fields := o.fields.setIfInBounds idx (.scalar 0) }) q
        = Heap.rc H q := by
      by_cases hqr : q = r
      · rw [hqr, Heap.rc_set_self]
        simp [Heap.rc, hcell]
      · rw [Heap.rc_set_other hqr]
    have hEcount :
        EnvOwnerCount ((c.move a fst).bindOwned snd e)
            (snd :: replaceVar support a fst) q
          = EnvOwnerCount c support q + (if e = q then 1 else 0) := by
      rw [EnvOwnerCount_bindOwned (c := c.move a fst) (x := snd) (r := q) hsn,
        EnvOwnerCount_move (c := c) (x := a) (y := fst) (r := q) hfst']
    rw [hrc, hEcount, h.count q]
    by_cases hqe : q = e
    · have hEe : EnvOwnerCount c support e = 0 := by
        have hsum := h.mult_eq e
        rw [he, hedge] at hsum
        omega
      rw [hqe]
      have hI := IncomingCount_set_of_ref (H := H) (r := r) (e := e) (o := o)
        (idx := idx) (w := 0) hcell hnext hslot
      have hif : (if e = e then 1 else 0) = 1 := by simp
      rw [hif, hI]
      omega
    · have hI := IncomingCount_set_of_ref_ne (H := H) (r := r) (e := e) (o := o)
        (idx := idx) (w := 0) hcell hnext hslot (q := q) hqe
      have hif : (if e = q then 1 else 0) = 0 := by
        have hq : ¬ (e = q) := fun hh => hqe hh.symm
        simp [hq]
      rw [hI, hif]
      omega

/-- The take-out with no client-supplied edge count: at a count-one child whose
slot is filled, `IncomingCount H e = 1` follows from the relation, the slot and
the checker's count-one condition (`Accounted.incoming_eq_one_of_slot`). What
remains is the checker's own take-out rule — fresh target variables, a distinct
extracted element, the count-one array handle — rather than a client-supplied
edge count. -/
theorem takeOutOfSlot {support : List Var} {H : Heap} {env : Env} {c : Ctx}
    (h : Accounted support H env c) {a fst snd e : Var} {r : Ref} {o : Obj} {idx : Nat}
    (ha : c.us a = .owned) (hma : c.multOf a = 1) (hr : c.refOf a = some r)
    (he : c.mult e = 1) (hfst : c.us fst ≠ .owned) (hsnd : c.us snd ≠ .owned)
    (hfs : fst ≠ snd) (her : e ≠ r) (hcell : H.cells r = some o)
    (hslot : o.fields[idx]? = some (.ref e)) :
    Accounted (snd :: replaceVar support a fst)
      (H.set r { o with fields := o.fields.setIfInBounds idx (.scalar 0) })
      ((env.set fst (.ref r)).set snd (.ref e)) ((c.move a fst).bindOwned snd e) :=
  takeOut h ha hma hr he hfst hsnd hfs her hcell hslot
    (incoming_eq_one_of_slot h he hcell hslot)

/-- The put-back's atomic step: the array's handle moves to `result`, the
returned element's handle is deadened, and its edge is filled into the slot the
take-out emptied. One owner leaves (`e`) and one edge arrives, so the count
equation holds at the interpreter's post-state. The environment is set only at
`result`: the dead variable keeps its stale binding, which the relation excludes
by counting `us`. -/
theorem putBack {support : List Var} {H : Heap} {env : Env} {c : Ctx}
    (h : Accounted support H env c) {a e result : Var} {r re : Ref} {o : Obj}
    {idx old : Nat}
    (ha : c.us a = .owned) (_hma : c.multOf a = 1) (hr : c.refOf a = some r)
    (he : c.us e = .owned) (_hme : c.multOf e = 1) (hre : c.refOf e = some re)
    (hres : c.us result ≠ .owned) (hea : e ≠ a) (hrer : e ≠ result)
    (hcell : H.cells r = some o) (hslot : o.fields[idx]? = some (.scalar old)) :
    Accounted ((replaceVar support a result).erase e)
      (H.set r { o with fields := o.fields.set! idx (.ref re) })
      (env.set result (.ref r)) ((c.move a result).setUs e .dead) := by
  have hres' : result ∉ support := fun hmem => hres (h.support_sound result hmem)
  have hnext : r < H.next := h.domain r o hcell
  have h₁ := h.move ha hr hres
  have henodup : (replaceVar support a result).Nodup := h₁.support_nodup
  have henmem : e ∉ (replaceVar support a result).erase e :=
    List.Nodup.not_mem_erase henodup
  have hemem : e ∈ replaceVar support a result := by
    rw [replaceVar_mem]
    exact Or.inr ⟨h.support_complete e he, hea⟩
  have heus : (c.move a result).us e = .owned := by
    rw [Ctx.move_us_other (c := c) (x := a) (y := result) (z := e) hrer hea]
    exact he
  have heref : (c.move a result).refOf e = some re := by
    rw [Ctx.move_refOf_other (c := c) (x := a) (y := result) (z := e) hrer]
    exact hre
  refine
    { inv := (h₁.inv.setDead).setFields hcell
      support_nodup := henodup.erase e
      support_sound := ?_
      support_complete := ?_
      support_bound := ?_
      domain := ?_
      count := ?_ }
  · intro z hz
    have hz' : z ∈ replaceVar support a result := List.mem_of_mem_erase hz
    have hze : z ≠ e := fun hh => henmem (hh ▸ hz)
    rw [Ctx.setUs_other (c := c.move a result) (x := e) (y := z) (u := .dead) hze]
    exact h₁.support_sound z hz'
  · intro z hz
    have hze : z ≠ e := by
      intro hh
      rw [hh] at hz
      rw [Ctx.setUs_self] at hz
      exact absurd hz (by simp)
    have hz' : (c.move a result).us z = .owned := by
      simpa [Ctx.setUs, hze] using hz
    have hmem := h₁.support_complete z hz'
    exact (List.mem_erase_of_ne hze).mpr hmem
  · intro z hz
    obtain ⟨q, hq⟩ := h₁.support_bound z (List.mem_of_mem_erase hz)
    exact ⟨q, by simpa [Ctx.setUs] using hq⟩
  · intro q o' hc
    rw [Heap_set_next]
    by_cases hqr : q = r
    · rw [hqr]
      exact h.domain r o hcell
    · rw [Heap.set_other _ _ _ _ hqr] at hc
      exact h.domain q o' hc
  · intro q
    have hrc : Heap.rc (H.set r { o with fields := o.fields.set! idx (.ref re) }) q
        = Heap.rc H q := by
      by_cases hqr : q = r
      · rw [hqr, Heap.rc_set_self]
        simp [Heap.rc, hcell]
      · rw [Heap.rc_set_other hqr]
    have hEset :
        EnvOwnerCount ((c.move a result).setUs e .dead)
            ((replaceVar support a result).erase e) q
          = EnvOwnerCount (c.move a result) ((replaceVar support a result).erase e) q :=
      EnvOwnerCount_setUs (c := c.move a result) (x := e) (u := .dead) henmem
    rw [hrc, hEset, h.count q]
    by_cases hq : q = re
    · have hEerase :
          EnvOwnerCount (c.move a result) ((replaceVar support a result).erase e) re + 1
            = EnvOwnerCount (c.move a result) (replaceVar support a result) re :=
        EnvOwnerCount_erase (c := c.move a result) (vs := replaceVar support a result)
          (x := e) (r := re) hemem ⟨heus, heref⟩
      have hmoveE :
          EnvOwnerCount (c.move a result) (replaceVar support a result) re
            = EnvOwnerCount c support re :=
        EnvOwnerCount_move (c := c) (x := a) (y := result) (r := re) hres'
      rw [hq]
      have hI := IncomingCount_set_fill (H := H) (r := r) (re := re) (o := o)
        (idx := idx) (old := old) hcell hnext hslot
      rw [hI]
      omega
    · have hPx : decide ((c.move a result).us e = .owned ∧
          (c.move a result).refOf e = some q) = false := by
        have hqre : ¬ (re = q) := fun hh => hq hh.symm
        have : ¬ (some re = some q) := fun hh => hqre (Option.some.inj hh)
        by_cases hh : (c.move a result).us e = .owned ∧ (c.move a result).refOf e = some q
        · exfalso
          exact this (hh.2.symm.trans heref).symm
        · simp [hh]
      have hEerase :
          EnvOwnerCount (c.move a result) ((replaceVar support a result).erase e) q
            = EnvOwnerCount (c.move a result) (replaceVar support a result) q := by
        unfold EnvOwnerCount
        exact filter_erase_length_eq hPx
      have hmoveE :
          EnvOwnerCount (c.move a result) (replaceVar support a result) q
            = EnvOwnerCount c support q :=
        EnvOwnerCount_move (c := c) (x := a) (y := result) (r := q) hres'
      have hI := IncomingCount_set_fill_ne (H := H) (r := r) (re := re) (o := o)
        (idx := idx) (old := old) hcell hnext hslot (q := q) hq
      rw [hI]
      omega


end Accounted

/-- Any two duplicate-free, sound and complete enumerations give the same owner
count at every reference, so the equation's right-hand side does not depend on
which valid index is supplied. -/
theorem EnvOwnerCount_eq_of_sound_complete {c : Ctx} {r : Ref} {l₁ l₂ : List Var}
    (h₁ : l₁.Nodup) (hs₁ : ∀ z, z ∈ l₁ → c.us z = .owned)
    (hc₁ : ∀ z, c.us z = .owned → z ∈ l₁)
    (h₂ : l₂.Nodup) (hs₂ : ∀ z, z ∈ l₂ → c.us z = .owned)
    (hc₂ : ∀ z, c.us z = .owned → z ∈ l₂) :
    EnvOwnerCount c l₁ r = EnvOwnerCount c l₂ r := by
  unfold EnvOwnerCount
  have hmem : ∀ z, z ∈ l₁.filter (fun z => c.us z = .owned ∧ c.refOf z = some r)
      ↔ z ∈ l₂.filter (fun z => c.us z = .owned ∧ c.refOf z = some r) := by
    intro z
    rw [List.mem_filter, List.mem_filter]
    constructor
    · rintro ⟨hz, hp⟩
      exact ⟨hc₂ z (hs₁ z hz), hp⟩
    · rintro ⟨hz, hp⟩
      exact ⟨hc₁ z (hs₂ z hz), hp⟩
  have hlen := length_eq_of_nodup_mem_iff (nodup_filter h₁) (nodup_filter h₂) hmem
  exact hlen

/-! ## Countermodels and field necessity -/

/-- A list all of whose members equal one value is at most one long when it is
duplicate-free. -/
theorem nodup_length_le_one {l : List Var} (h : l.Nodup) {a : Var}
    (hall : ∀ z, z ∈ l → z = a) : l.length ≤ 1 := by
  cases l with
  | nil => simp
  | cons x t =>
    cases t with
    | nil => simp
    | cons y u =>
      exfalso
      rw [List.nodup_cons] at h
      have hx : x = a := hall x List.mem_cons_self
      have hy : y = a := hall y (List.mem_cons_of_mem x List.mem_cons_self)
      have hxy : x = y := hx.trans hy.symm
      exact h.1 (by rw [hxy]; exact List.mem_cons_self)

/-- The initializer's heap under the alias configuration. -/
def aliasHeap (n : Nat) : Heap := (Runner.initHeap n).2

/-- The alias configuration's environment: variable 1 is bound to the array. -/
def aliasEnv (n : Nat) : Env :=
  (Runner.initEnv (Runner.initHeap n).1).set 1 (.ref (Runner.initHeap n).1)

/-- The alias configuration's context: `bindOwned` marks the duplicate as a
second owner. -/
def aliasCtx (n : Nat) : Ctx :=
  (Runner.initCtx (Runner.initHeap n).1).bindOwned 1 (Runner.initHeap n).1

/-- The alias configuration is not accounted: `Inv` preserves it, but one count
carries two owners. -/
theorem alias_rejected (n : Nat) :
    Inv (aliasHeap n) (aliasEnv n) (aliasCtx n) ∧
      ∀ support, ¬ Accounted support (aliasHeap n) (aliasEnv n) (aliasCtx n) := by
  have hmult : (Runner.initCtx (Runner.initHeap n).1).mult (Runner.initHeap n).1 = 1 := by
    simp [Runner.initCtx]
  constructor
  · exact Inv.bindOwned (Runner.initInv n) hmult
  · intro support h
    have hI : IncomingCount (aliasHeap n) (Runner.initHeap n).1 = 0 :=
      Accounted.IncomingCount_initHeap n _
    have hrc : Heap.rc (aliasHeap n) (Runner.initHeap n).1 = 1 := by
      simp [aliasHeap, Heap.rc, Runner.initHeap]
    have hE : EnvOwnerCount (aliasCtx n) support (Runner.initHeap n).1 = 1 := by
      have hcount := h.count (Runner.initHeap n).1
      rw [hI, hrc] at hcount
      omega
    have h0 : (aliasCtx n).us 0 = .owned := by
      simp [aliasCtx, Ctx.bindOwned, Runner.initCtx]
    have h1 : (aliasCtx n).us 1 = .owned := by
      simp [aliasCtx, Ctx.bindOwned]
    have hr0 : (aliasCtx n).refOf 0 = some (Runner.initHeap n).1 := by
      simp [aliasCtx, Ctx.bindOwned, Runner.initCtx]
    have hr1 : (aliasCtx n).refOf 1 = some (Runner.initHeap n).1 := by
      simp [aliasCtx, Ctx.bindOwned]
    have hm0 : 0 ∈ support := h.support_complete 0 h0
    have hm1 : 1 ∈ support := h.support_complete 1 h1
    have hf0 : 0 ∈ support.filter (fun z => (aliasCtx n).us z = .owned ∧
        (aliasCtx n).refOf z = some (Runner.initHeap n).1) := by
      rw [List.mem_filter]; exact ⟨hm0, by simp [h0, hr0]⟩
    have hf1 : 1 ∈ support.filter (fun z => (aliasCtx n).us z = .owned ∧
        (aliasCtx n).refOf z = some (Runner.initHeap n).1) := by
      rw [List.mem_filter]; exact ⟨hm1, by simp [h1, hr1]⟩
    have htwo : 2 ≤ EnvOwnerCount (aliasCtx n) support (Runner.initHeap n).1 := by
      unfold EnvOwnerCount
      exact two_le_length_of_nodup_mem (nodup_filter h.support_nodup) hf0 hf1 (by decide)
    omega

/-- The incremented initializer: duplicating the count on the heap and in the
context leaves both obligations unchanged, so no accounting state exists. -/
theorem inc_rejected (n : Nat) :
    Inv ((aliasHeap n).inc (Runner.initHeap n).1 1) (Runner.initEnv (Runner.initHeap n).1)
        ((Runner.initCtx (Runner.initHeap n).1).inc (Runner.initHeap n).1 1) ∧
      ∀ support, ¬ Accounted support ((aliasHeap n).inc (Runner.initHeap n).1 1)
        (Runner.initEnv (Runner.initHeap n).1)
        ((Runner.initCtx (Runner.initHeap n).1).inc (Runner.initHeap n).1 1) := by
  have hx : (Runner.initCtx (Runner.initHeap n).1).us 0 = .owned :=
    Runner.initCtx_us_zero _
  have hr : (Runner.initCtx (Runner.initHeap n).1).refOf 0 = some (Runner.initHeap n).1 :=
    Runner.initCtx_refOf_zero _
  constructor
  · exact Inv.inc (Runner.initInv n) hx hr
  · intro support h
    have hI : IncomingCount (aliasHeap n) (Runner.initHeap n).1 = 0 :=
      Accounted.IncomingCount_initHeap n _
    have hI' : IncomingCount ((aliasHeap n).inc (Runner.initHeap n).1 1)
        (Runner.initHeap n).1 = 0 := by
      rw [IncomingCount_inc]; exact hI
    have hrc : Heap.rc ((aliasHeap n).inc (Runner.initHeap n).1 1)
        (Runner.initHeap n).1 = 2 := by
      simp [aliasHeap, Heap.inc, Heap.rc, Runner.initHeap]
    have hE : EnvOwnerCount ((Runner.initCtx (Runner.initHeap n).1).inc
        (Runner.initHeap n).1 1) support (Runner.initHeap n).1 = 1 := by
      have hsound : ∀ z, z ∈ support → ((Runner.initCtx (Runner.initHeap n).1).inc
          (Runner.initHeap n).1 1).us z = .owned := h.support_sound
      have hcomplete : ∀ z, ((Runner.initCtx (Runner.initHeap n).1).inc
          (Runner.initHeap n).1 1).us z = .owned → z ∈ support := h.support_complete
      have hbase : EnvOwnerCount ((Runner.initCtx (Runner.initHeap n).1).inc
          (Runner.initHeap n).1 1) [0] (Runner.initHeap n).1 = 1 := by
        simp [EnvOwnerCount, Ctx.inc, Runner.initCtx, Runner.initHeap]
      rw [← hbase]
      exact EnvOwnerCount_eq_of_sound_complete h.support_nodup hsound hcomplete
        (List.nodup_cons.mpr ⟨by simp, List.nodup_nil⟩)
        (by intro z hz; simp only [List.mem_singleton] at hz; subst hz; simp [Runner.initCtx])
        (by
          intro z hz
          have hz0 : z = 0 := (initCtx_us_eq _ z).mp (by simpa [Ctx.inc] using hz)
          simp [hz0])
    have hcount := h.count (Runner.initHeap n).1
    rw [hI', hrc, hE] at hcount
    omega

/-- A decrement of an admitted `n ≠ 1` releases counts no obligation carried: at
an accounted pre-state with `2 < c.mult r` the post-state admits no support.
At `c.mult r = 1` the same operation is not a countermodel (truncated
subtraction), which is why the pre-state condition is part of the statement. -/
theorem decTwo_rejected {support : List Var} {H : Heap} {env : Env} {c : Ctx}
    (h : Accounted support H env c) {x : Var} {r : Ref} {n : Nat}
    (hx : c.us x = .owned) (hr : c.refOf x = some r) (_hlt : 2 < c.mult r)
    (hn : n ≠ 1) (hnr : n < c.mult r) :
    ¬ Accounted (support.erase x) (H.dec r n) (env.erase x)
        ((c.dec r n).setUs x .dead) := by
  intro h'
  have hxnmem : x ∉ support.erase x := List.Nodup.not_mem_erase h.support_nodup
  have hE' : EnvOwnerCount ((c.dec r n).setUs x .dead) (support.erase x) r + 1
      = EnvOwnerCount c support r := by
    have h1 : EnvOwnerCount ((c.dec r n).setUs x .dead) (support.erase x) r
        = EnvOwnerCount c (support.erase x) r :=
      (EnvOwnerCount_setUs (c := c.dec r n) (x := x) (u := .dead) hxnmem).trans
        (EnvOwnerCount_dec c r n (support.erase x) r)
    rw [h1]
    exact EnvOwnerCount_erase (h.support_complete x hx) ⟨hx, hr⟩
  have hinc : IncomingCount (H.dec r n) r = IncomingCount H r := IncomingCount_dec r
  have hrc : Heap.rc (H.dec r n) r = Heap.rc H r - n := Heap.rc_dec_self H r n
  have hcount := h'.count r
  rw [hinc, hrc] at hcount
  have hmul := h.mult_eq r
  have hrcE := h.inv.rc_eq r
  omega

/-! ### The out-of-range pair -/

/-- The out-of-range witness heap: two live cells, the cursor at `1`, so the cell
at `1` hides its edge into `0`. -/
def outOfRangeHeap : Heap :=
  { cells := fun r' => if r' = 0 then some ⟨#[.scalar 0], 2, false⟩
      else if r' = 1 then some ⟨#[.ref 0], 1, false⟩ else none
    next := 1 }

/-- The same heap with the cursor past both cells. -/
def inRangeHeap : Heap :=
  { cells := fun r' => if r' = 0 then some ⟨#[.scalar 0], 2, false⟩
      else if r' = 1 then some ⟨#[.ref 0], 1, false⟩ else none
    next := 2 }

/-- The witness environment: variables 0 and 1 name the two cells. -/
def witnessEnv : Env :=
  fun x => if x = 0 then some (.ref 0) else if x = 1 then some (.ref 1) else none

/-- The witness context: both owning variables, counts 2 and 1. -/
def witnessCtx : Ctx :=
  { us := fun x => if x = 0 then .owned else if x = 1 then .owned else .dead
    refOf := fun x => if x = 0 then some 0 else if x = 1 then some 1 else none
    mult := fun r' => if r' = 0 then 2 else if r' = 1 then 1 else 0 }

/-- Both witness heaps have the same cells; the invariant does not mention the
cursor, so one proof serves the refused and the accepted cursor. -/
theorem inv_witness (next : Ref) :
    Inv
      { cells := fun r' => if r' = 0 then some ⟨#[.scalar 0], 2, false⟩
          else if r' = 1 then some ⟨#[.ref 0], 1, false⟩ else none
        next := next }
      witnessEnv witnessCtx := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro r
    by_cases h0 : r = 0
    · rw [h0]
      rfl
    · by_cases h1 : r = 1
      · rw [h1]
        rfl
      · have hr : Heap.rc
          { cells := fun r' => if r' = 0 then some ⟨#[.scalar 0], 2, false⟩
              else if r' = 1 then some ⟨#[.ref 0], 1, false⟩ else none
            next := next } r = 0 := by
          simp [Heap.rc, h0, h1]
        have hm : witnessCtx.mult r = 0 := by simp [witnessCtx, h0, h1]
        rw [hr, hm]
  · intro x r hx hr
    by_cases hx0 : x = 0
    · subst hx0
      have hs : some (0 : Ref) = some r := by simpa [witnessCtx] using hr
      have hr0 : r = 0 := (Option.some.inj hs).symm
      subst hr0
      exact ⟨rfl, by decide⟩
    · by_cases hx1 : x = 1
      · subst hx1
        have hs : some (1 : Ref) = some r := by simpa [witnessCtx] using hr
        have hr1 : r = 1 := (Option.some.inj hs).symm
        subst hr1
        exact ⟨rfl, by decide⟩
      · have hdead : witnessCtx.us x = U.dead := by simp [witnessCtx, hx0, hx1]
        rw [hdead] at hx
        exact absurd hx (by decide)
  · intro x r hx hr
    by_cases hx0 : x = 0
    · rw [hx0] at hx; simp [witnessCtx] at hx
    · by_cases hx1 : x = 1
      · rw [hx1] at hx; simp [witnessCtx] at hx
      · rw [show witnessCtx.us x = U.dead from by simp [witnessCtx, hx0, hx1]] at hx
        exact absurd hx (by decide)
  · intro x hx
    by_cases hx0 : x = 0
    · rw [hx0] at hx; simp [witnessCtx] at hx
    · by_cases hx1 : x = 1
      · rw [hx1] at hx; simp [witnessCtx] at hx
      · rw [show witnessCtx.us x = U.dead from by simp [witnessCtx, hx0, hx1]] at hx
        exact absurd hx (by decide)
  · intro r o hc
    by_cases h0 : r = 0
    · rw [h0] at hc
      simp [h0] at hc
      subst hc
      rfl
    · by_cases h1 : r = 1
      · rw [h1] at hc
        simp [h0] at hc
        subst hc
        rfl
      · simp [h0, h1] at hc

theorem inv_outOfRange : Inv outOfRangeHeap witnessEnv witnessCtx := inv_witness 1

/-- The out-of-range configuration is refused: a live cell at or beyond the
cursor hides its edges, so the count equation fails. -/
theorem outOfRange_rejected :
    Inv outOfRangeHeap witnessEnv witnessCtx ∧
      ∀ support, ¬ Accounted support outOfRangeHeap witnessEnv witnessCtx := by
  constructor
  · exact inv_outOfRange
  · intro support h
    have hI : IncomingCount outOfRangeHeap 0 = 0 := by decide
    have hrc : Heap.rc outOfRangeHeap 0 = 2 := by decide
    have hcount := h.count 0
    rw [hI, hrc] at hcount
    have hnodup := nodup_filter (P := fun z => witnessCtx.us z = .owned ∧
      witnessCtx.refOf z = some 0) h.support_nodup
    have hall : ∀ z ∈ support.filter (fun z => witnessCtx.us z = .owned ∧
        witnessCtx.refOf z = some 0), z = 0 := by
      intro z hz
      rw [List.mem_filter] at hz
      have hp := of_decide_eq_true hz.2
      rcases hp with ⟨hu, hr⟩
      by_cases h0 : z = 0
      · exact h0
      · by_cases h1 : z = 1
        · subst h1
          simp [witnessCtx] at hr
        · rw [show witnessCtx.us z = U.dead from by simp [witnessCtx, h0, h1]] at hu
          exact absurd hu (by decide)
    have hle : (support.filter (fun z => witnessCtx.us z = .owned ∧
        witnessCtx.refOf z = some 0)).length ≤ 1 := nodup_length_le_one hnodup hall
    unfold EnvOwnerCount at hcount
    omega

/-- The same state with the cursor past both cells is accounted: the relation is
not refusing everything. -/
theorem outOfRange_accepted : Accounted [0, 1] inRangeHeap witnessEnv witnessCtx := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact inv_witness 2
  · exact List.nodup_cons.mpr ⟨by simp,
      List.nodup_cons.mpr ⟨by simp, List.nodup_nil⟩⟩
  · intro x hx
    simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl <;> simp [witnessCtx]
  · intro x hx
    by_cases h0 : x = 0
    · rw [h0]
      simp [witnessCtx]
    · by_cases h1 : x = 1
      · rw [h1]
        simp [witnessCtx]
      · rw [show witnessCtx.us x = U.dead from by simp [witnessCtx, h0, h1]] at hx
        exact absurd hx (by decide)
  · intro x hx
    simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl
    · exact ⟨0, by simp [witnessCtx]⟩
    · exact ⟨1, by simp [witnessCtx]⟩
  · intro r o hc
    by_cases h0 : r = 0
    · rw [h0]
      decide
    · by_cases h1 : r = 1
      · rw [h1]
        decide
      · have hnone : inRangeHeap.cells r = none := by
          simp [inRangeHeap, outOfRangeHeap, h0, h1]
        rw [hnone] at hc
        exact absurd hc (by simp)
  · intro r
    by_cases h0 : r = 0
    · rw [h0]
      decide
    · by_cases h1 : r = 1
      · rw [h1]
        decide
      · have hrc : Heap.rc inRangeHeap r = 0 := by
          simp [Heap.rc, inRangeHeap, outOfRangeHeap, h0, h1]
        have h0' : (0 : Ref) ≠ r := fun hh => h0 hh.symm
        have h1' : (1 : Ref) ≠ r := fun hh => h1 hh.symm
        have hI : IncomingCount inRangeHeap r = 0 := by
          rw [IncomingCount_eq_edges]
          simp [List.range_succ, EdgeAt, inRangeHeap, RefCount, h0, h1, h0']
        have hE : EnvOwnerCount witnessCtx [0, 1] r = 0 := by
          simp [EnvOwnerCount, witnessCtx, h0, h1, h0', h1']
        rw [hrc, hI, hE]

/-! ### The field-necessity witnesses -/

/-- A repeated enumeration inflates the count: `[0,0]` counts two owners where
`[0]` counts one, so `support_nodup` is load-bearing. -/
theorem dupSupport_witness (n : Nat) :
    EnvOwnerCount (Runner.initCtx (Runner.initHeap n).1) [0, 0] (Runner.initHeap n).1 = 2 ∧
      EnvOwnerCount (Runner.initCtx (Runner.initHeap n).1) [0] (Runner.initHeap n).1 = 1 := by
  constructor
  · simp [EnvOwnerCount, Runner.initCtx, Runner.initHeap]
  · simp [EnvOwnerCount, Runner.initCtx, Runner.initHeap]

/-- A sound, bound but incomplete enumeration satisfies the count equation and
still omits an owner, so `support_complete` is load-bearing. -/
theorem omittedOwner_witness (n : Nat) :
    (aliasCtx n).us 0 = .owned ∧ (aliasCtx n).us 1 = .owned ∧
      (aliasCtx n).refOf 0 = some (Runner.initHeap n).1 ∧
      (aliasCtx n).refOf 1 = some (Runner.initHeap n).1 ∧
      EnvOwnerCount (aliasCtx n) [1] (Runner.initHeap n).1 = 1 ∧
      EnvOwnerCount (aliasCtx n) [0] (Runner.initHeap n).1 = 1 ∧
      Heap.rc (aliasHeap n) (Runner.initHeap n).1
        = IncomingCount (aliasHeap n) (Runner.initHeap n).1
          + EnvOwnerCount (aliasCtx n) [1] (Runner.initHeap n).1 := by
  refine ⟨by simp [aliasCtx, Ctx.bindOwned, Runner.initCtx],
    by simp [aliasCtx, Ctx.bindOwned],
    by simp [aliasCtx, Ctx.bindOwned, Runner.initCtx],
    by simp [aliasCtx, Ctx.bindOwned], ?_, ?_, ?_⟩
  · simp [EnvOwnerCount, aliasCtx, Ctx.bindOwned, Runner.initCtx, Runner.initHeap]
  · simp [EnvOwnerCount, aliasCtx, Ctx.bindOwned, Runner.initCtx, Runner.initHeap]
  · have hI : IncomingCount (aliasHeap n) (Runner.initHeap n).1 = 0 :=
      Accounted.IncomingCount_initHeap n _
    have hrc : Heap.rc (aliasHeap n) (Runner.initHeap n).1 = 1 := by
      simp [aliasHeap, Heap.rc, Runner.initHeap]
    have hE : EnvOwnerCount (aliasCtx n) [1] (Runner.initHeap n).1 = 1 := by
      simp [EnvOwnerCount, aliasCtx, Ctx.bindOwned, Runner.initHeap]
    rw [hI, hrc, hE]

/-- An owned variable with no reference contributes nothing and names nothing,
so `support_bound` is load-bearing. -/
theorem unboundRoot_witness {c : Ctx} {r : Ref} (hx : c.us 7 = .owned)
    (hr : c.refOf 7 = none) : EnvOwnerCount c [7] r = 0 := by
  unfold EnvOwnerCount
  have hnot : ¬ (c.us 7 = .owned ∧ c.refOf 7 = some r) := by
    rw [hr]
    intro hh
    exact absurd hh.2 (by simp)
  simp [hnot]

/-- The binding-only twin of `inc_rejected`: a fresh owner without the take-out's
edge removal leaves one owner and one edge against a count of one. -/
def bindAloneHeap : Heap :=
  { cells := fun r' => if r' = 0 then some ⟨#[.ref 1], 1, false⟩
      else if r' = 1 then some ⟨#[.scalar 0], 1, false⟩ else none
    next := 2 }

def bindAloneEnv : Env := fun x => if x = 0 then some (.ref 0) else none

def bindAloneCtx : Ctx :=
  { us := fun x => if x = 0 then .owned else .dead
    refOf := fun x => if x = 0 then some 0 else none
    mult := fun r' => if r' = 0 then 1 else if r' = 1 then 1 else 0 }

theorem bindAlone_rejected :
    Inv bindAloneHeap (bindAloneEnv.set 1 (.ref 1)) (bindAloneCtx.bindOwned 1 1) ∧
      ∀ support, ¬ Accounted support bindAloneHeap (bindAloneEnv.set 1 (.ref 1))
        (bindAloneCtx.bindOwned 1 1) := by
  have hi : Inv bindAloneHeap bindAloneEnv bindAloneCtx := by
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · intro r
      by_cases h0 : r = 0
      · subst h0; decide
      · by_cases h1 : r = 1
        · subst h1; decide
        · have hr : Heap.rc bindAloneHeap r = 0 := by
            simp [Heap.rc, bindAloneHeap, h0, h1]
          have hm : bindAloneCtx.mult r = 0 := by simp [bindAloneCtx, h0, h1]
          rw [hr, hm]
    · intro x r hx hr
      by_cases hx0 : x = 0
      · subst hx0
        have hs : some (0 : Ref) = some r := by simpa [bindAloneCtx] using hr
        have hr0 : r = 0 := (Option.some.inj hs).symm
        subst hr0
        exact ⟨by decide, by decide⟩
      · rw [show bindAloneCtx.us x = U.dead from by simp [bindAloneCtx, hx0]] at hx
        exact absurd hx (by decide)
    · intro x r hx hr
      by_cases hx0 : x = 0
      · rw [hx0] at hx; simp [bindAloneCtx] at hx
      · rw [show bindAloneCtx.us x = U.dead from by simp [bindAloneCtx, hx0]] at hx
        exact absurd hx (by decide)
    · intro x hx
      by_cases hx0 : x = 0
      · rw [hx0] at hx; simp [bindAloneCtx] at hx
      · rw [show bindAloneCtx.us x = U.dead from by simp [bindAloneCtx, hx0]] at hx
        exact absurd hx (by decide)
    · intro r o hc
      by_cases h0 : r = 0
      · rw [h0] at hc
        simp [bindAloneHeap] at hc
        subst hc
        rfl
      · by_cases h1 : r = 1
        · rw [h1] at hc
          simp [bindAloneHeap, h0] at hc
          subst hc
          rfl
        · simp [bindAloneHeap, h0, h1] at hc
  constructor
  · exact Inv.bindOwned hi (by decide)
  · intro support h
    have hI : IncomingCount bindAloneHeap 1 = 1 := by decide
    have hrc : Heap.rc bindAloneHeap 1 = 1 := by decide
    have hcount := h.count 1
    rw [hI, hrc] at hcount
    have hone : (bindAloneCtx.bindOwned 1 1).us 1 = .owned :=
      Ctx.bindOwned_us_self ..
    have href : (bindAloneCtx.bindOwned 1 1).refOf 1 = some 1 :=
      Ctx.bindOwned_refOf_self ..
    have hmem : 1 ∈ support := h.support_complete 1 hone
    have hf : 1 ∈ support.filter (fun z => (bindAloneCtx.bindOwned 1 1).us z = .owned ∧
        (bindAloneCtx.bindOwned 1 1).refOf z = some 1) := by
      rw [List.mem_filter]; exact ⟨hmem, by simp [hone, href]⟩
    have hpos : 0 < EnvOwnerCount (bindAloneCtx.bindOwned 1 1) support 1 := by
      unfold EnvOwnerCount
      exact List.length_pos_iff_exists_mem.mpr ⟨1, hf⟩
    omega

/-- The scalar overwrite the checker admits: rebinding an owning variable as a
scalar leaves the count with no obligation, so `Supported`'s scalar constructors
need the freshness premise. -/
theorem scalarOverwrite_rejected (n : Nat) :
    Inv (Runner.initHeap n).2
        ((Runner.initEnv (Runner.initHeap n).1).set 0 (.scalar 0))
        ((Runner.initCtx (Runner.initHeap n).1).setUs 0 .scalar) ∧
      ∀ support, ¬ Accounted support (Runner.initHeap n).2
        ((Runner.initEnv (Runner.initHeap n).1).set 0 (.scalar 0))
        ((Runner.initCtx (Runner.initHeap n).1).setUs 0 .scalar) := by
  constructor
  · exact Inv.setScalar (Runner.initInv n) (n := 0)
  · intro support h
    have hI : IncomingCount (Runner.initHeap n).2 (Runner.initHeap n).1 = 0 :=
      Accounted.IncomingCount_initHeap n _
    have hrc : Heap.rc (Runner.initHeap n).2 (Runner.initHeap n).1 = 1 := by
      simp [Heap.rc, Runner.initHeap]
    have hE : EnvOwnerCount ((Runner.initCtx (Runner.initHeap n).1).setUs 0 .scalar)
        support (Runner.initHeap n).1 = 0 := by
      have hnone : ∀ z, ((Runner.initCtx (Runner.initHeap n).1).setUs 0 .scalar).us z
          = .owned → False := by
        intro z hz
        by_cases h0 : z = 0
        · subst h0
          rw [Ctx.setUs_self] at hz
          exact absurd hz (by decide)
        · rw [Ctx.setUs_other (c := Runner.initCtx (Runner.initHeap n).1) (x := 0)
            (y := z) (u := .scalar) h0] at hz
          have : z = 0 := (initCtx_us_eq _ z).mp hz
          exact h0 this
      have hEq := EnvOwnerCount_eq_of_sound_complete (c := (Runner.initCtx
        (Runner.initHeap n).1).setUs 0 .scalar) (r := (Runner.initHeap n).1)
        (l₁ := support) (l₂ := []) h.support_nodup h.support_sound h.support_complete
        List.nodup_nil (by intro z hz; simp at hz) (by intro z hz; exact absurd hz (hnone z))
      rw [hEq]
      simp [EnvOwnerCount]
    have hcount := h.count (Runner.initHeap n).1
    rw [hI, hrc, hE] at hcount
    omega

/-! ## The supported fragment -/

/-- The counted supported fragment of the model, indexed by the context each
continuation is checked at. Every constructor's continuation is indexed at the
context the checker's matching rule threads, each constructor carries the
checker's own rule at that constructor, and the accounting certificates the
checker cannot see are further premises: a fresh alias target and a fresh
scalar-`.let` target. Apart from those certificates, the only departure from the
checker's rules is `n = 1` at `.dec`, where `decOne`'s `1 < c.mult r` is exactly
the checker's `n < c.mult r` at `n = 1`. `.inc` and any `.dec x n` with `n ≠ 1` are excluded: no accounting
state exists after an increment (`inc_rejected`) and a multi-handle decrement
releases counts no obligation carried (`decTwo_rejected`).

So the fragment is check acceptance restricted to the counted constructors: from
`Supported c s` the checker accepts the program
(`Ownership.supported_check`), which is what lets a preservation
theorem follow the fault-free run. The store's slot fact is deliberately absent:
no context records which value a cell's selected slot holds, so it is the
`StoreSlots` premise of `Ownership.supported_run` rather than a constructor
premise. -/
inductive Supported : Ctx → Code → Prop where
  | ret (c : Ctx) (x : Var) :
      (c.us x = .owned ∨ c.us x = .scalar) → Supported c (.ret x)
  | bindLit (c : Ctx) (x : Var) (n : Nat) (k : Code) (hx : c.us x ≠ .owned) :
      Supported (c.setUs x .scalar) k → Supported c (.let x (.lit n) k)
  | bindSize (c : Ctx) (x a : Var) (r : Ref) (k : Code) (hx : c.us x ≠ .owned)
      (ha : c.us a = .owned ∨ c.us a = .borrow) (hr : c.refOf a = some r) :
      Supported (c.setUs x .scalar) k → Supported c (.let x (.size a) k)
  | bindShared (c : Ctx) (x y : Var) (r : Ref) (k : Code) (hx : c.us x ≠ .owned)
      (hy : c.us y = .owned ∨ c.us y = .borrow) (hr : c.refOf y = some r) :
      Supported (c.setUs x .scalar) k → Supported c (.let x (.isShared y) k)
  | bindAlias (c : Ctx) (x y : Var) (k : Code) (hx : c.us x = .owned)
      (hm : c.multOf x = 1) (hy : c.us y ≠ .owned) :
      Supported (c.move x y) k → Supported c (.let y (.checkAlias x) k)
  | check (c : Ctx) (x : Var) (k : Code) (hx : c.us x = .owned)
      (hm : c.multOf x = 1) :
      Supported c k → Supported c (.check x k)
  | setArr (c : Ctx) (x i v : Var) (k : Code) (hx : c.us x = .owned)
      (hm : c.multOf x = 1) (hi : c.us i = .scalar) (hv : c.us v = .scalar) :
      Supported c k → Supported c (.setArr x i v k)
  | decOne (c : Ctx) (x : Var) (r : Ref) (k : Code) (hx : c.us x = .owned)
      (hr : c.refOf x = some r) (hlt : 1 < c.mult r) :
      Supported ((c.dec r 1).setUs x .dead) k → Supported c (.dec x 1 k)


end Ownership
