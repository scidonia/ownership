/-
A finite multi-allocation relation between `LeanLLVM`'s byte memory and the
integrated ownership state.

`LlvmBridge/Ownership.lean` relates one `Cap.Integrated` allocation's buffer to
the emitted kernel's byte memory at one caller-supplied window.  This file
extends that relation to a finite map: `Cap.AddressMap.Map` assigns every live
allocation a window, and `MemRepMap m map s` says the flat memory holds each
live allocation's buffer at that allocation's window.

What is proved:

* `MemRepMap.write` — an accepted integrated write at an in-window offset
  (`off < w.len`) preserves the relation at the kernel's post-memory
  (`writeByte m (w.addr off) v`), and frames every other allocation's component.
  The frame is `Window.Disjoint`, taken from the map's `WellFormed`, which
  supplies the avoidance hypothesis of `MemRep.frame_write`.
* `MemRepMap.write_len` — an accepted write at a mapped allocation is in-window.
  The window bound of `MemRepMap.write` is therefore a consequence of acceptance
  together with the relation, not an extra assumption.
* `sealed_store8_write_comp_map` — the composition at the sealed boundary: the
  emitted body completes, the post-memory satisfies the updated relation, and an
  unrelated allocation's component and bytes are unchanged.  The map itself is
  unchanged, so every unrelated window is too.
* `memRepMap_twoAlloc` — the concrete two-allocation model: the map's
  `twoAllocMap`/`twoAllocState` fixture represented in a concrete memory that
  holds both windows' bytes.
* `example_write_model` — a concrete accepted write in that model preserves the
  relation and leaves the second allocation's component and bytes alone.
* `example_third_frame` — the flat-memory frame: the write in the first window
  does not change a byte of the second.
* The refusal controls: `MemRepMap.exec_write_eq_none_of_len_le` (an
  out-of-window write is refused) with its fixture instance
  `example_out_of_window_refused`, and `overlapping_window_refused` with
  `overlapping_window_shares_addr` (the window the map refuses really would share
  a flat address).  `example_window_addr_none` is the map's own refusal to
  produce an address outside a window, and `twoAlloc_write0_accepted` /
  `twoAlloc_write0_exists` are the affirmative control that the same model does
  accept an in-window write, so the refusals are not vacuous.

What is assumed, and stays stated rather than discharged:

* the map's well-formedness and coverage (`Cap.AddressMap.Rel`) — the map is
  caller-supplied; nothing here proves that a loader assigns the windows;
* the initial representation `MemRepMap m map s` — the flat memory already holds
  every window;
* the pointer-width fact `off < 2 ^ 63` that the emitted `getelementptr` needs;
* the projection from clang's emission, and the executable edge (ABI, native
  execution, a live handle, the physical allocation), unchanged from
  `LlvmBridge/Ownership.lean`.

No `sorry`, no new axiom, and no `Cap` definition is re-proved: the one-window
memory facts are `MemRep.set`, `MemRep.frame_write`, `postMem` and
`runFuel_store8_at_mem`; the ownership side is `exec_write_parts`,
`heap_write_lookup` and `Cap.AddressMap.Rel.write`.
-/
import Cap.AddressMap
import LlvmBridge.Ownership

namespace LlvmBridge

open LeanLLVM
open Cap.AddressMap

/-! ### Window addresses -/

/-- The kernel's post-memory at a mapped window is the memory with the byte
written at that window's flat address. -/
theorem postMem_window (m : Mem) (w : Cap.AddressMap.Window) (off : Nat)
    (bv : BitVec 8) :
    postMem m w.base off bv = writeByte m (w.addr off) (byteOf bv) := rfl

/-- Two disjoint windows never share a flat address.  This is the separation
between one window's offsets and another's that a frame needs. -/
theorem disjoint_addr_ne {w₁ w₂ : Cap.AddressMap.Window}
    (hd : w₁.Disjoint w₂) {i j : Nat} (hi : i < w₁.len) (hj : j < w₂.len) :
    w₁.base + i ≠ w₂.base + j := by
  unfold Cap.AddressMap.Window.Disjoint Cap.AddressMap.Window.stop at hd
  rcases hd with hd | hd <;> omega

/-! ### The relation over a finite map -/

/-- The flat memory holds every allocation the map places: the map relates to
the state, and every mapped allocation's component buffer is represented at its
window's base and has the window's recorded length. -/
def MemRepMap (m : Mem) (map : Cap.AddressMap.Map) (s : Cap.Integrated.State) : Prop :=
  Cap.AddressMap.Rel map s ∧
    ∀ (a : Cap.AllocId) (w : Cap.AddressMap.Window),
      map.lookup? a = some w →
        ∃ (st : Cap.Reconstruction.State) (buf : List UInt8),
          s.find? a = some st ∧ st.heap.lookup? a = some buf ∧
            buf.length = w.len ∧ MemRep m buf w.base

/-- The map relation is part of the memory relation. -/
theorem MemRepMap.rel {m : Mem} {map : Cap.AddressMap.Map}
    {s : Cap.Integrated.State} (h : MemRepMap m map s) :
    Cap.AddressMap.Rel map s := h.1

/-- A mapped allocation has a represented component buffer. -/
theorem MemRepMap.buffer {m : Mem} {map : Cap.AddressMap.Map}
    {s : Cap.Integrated.State} (h : MemRepMap m map s) {a : Cap.AllocId}
    {w : Cap.AddressMap.Window} (hw : map.lookup? a = some w) :
    ∃ (st : Cap.Reconstruction.State) (buf : List UInt8),
      s.find? a = some st ∧ st.heap.lookup? a = some buf ∧
        buf.length = w.len ∧ MemRep m buf w.base := h.2 a w hw

/-- An accepted write at a mapped allocation is inside that allocation's window.
The write guard's in-range offset is the buffer's length, which the relation
identifies with the window's length; no separate bound is assumed. -/
theorem MemRepMap.write_len {m : Mem} {map : Cap.AddressMap.Map}
    {s s' : Cap.Integrated.State} {a : Cap.AllocId} {id : Cap.CapId}
    {off : Nat} {v : UInt8} {w : Cap.AddressMap.Window}
    (hmap : MemRepMap m map s) (hw : map.lookup? a = some w)
    (hwrite : s.exec (.write a id off v) = some s') : off < w.len := by
  obtain ⟨hrel, hbuf⟩ := hmap
  obtain ⟨st, st', c, h', hfind, hwf, hfind', hleaf, hstate, hq, hceil, halloc, hlo,
    hhi, hhw, hst'⟩ := exec_write_parts hwrite
  obtain ⟨st_a, buf, hfind_a, hbuf_a, hlen_a, hrep_a⟩ := hbuf a w hw
  have hst_eq : st_a = st := Option.some.inj (hfind_a.symm.trans hfind)
  have hbuf_a' : st.heap.lookup? a = some buf := hst_eq ▸ hbuf_a
  have hst_alloc : st.alloc = a := Cap.Integrated.State.find?_alloc hfind
  rw [hst_alloc] at hhw
  obtain ⟨hpost, hlt⟩ := heap_write_lookup (buf := buf) hbuf_a' hhw
  rw [← hlen_a]
  exact hlt

/-- **An accepted write preserves the multi-allocation relation.**

`hmap` relates the memory to the map and the state, `hw` places `a` at window
`w`, `hoff` puts the write inside that window, and `hwrite` is the accepted
integrated command.  The post-memory is the kernel's one byte at `w.addr off`.
Every other allocation's window is disjoint from `w` by the map's `WellFormed`,
so `MemRep.frame_write` keeps its buffer represented; the component frame is the
ownership model's own `exec_frames_other`.  The map is unchanged. -/
theorem MemRepMap.write {m : Mem} {map : Cap.AddressMap.Map}
    {s s' : Cap.Integrated.State} {a : Cap.AllocId} {id : Cap.CapId}
    {off : Nat} {v : UInt8} {w : Cap.AddressMap.Window}
    (hmap : MemRepMap m map s) (hw : map.lookup? a = some w)
    (hoff : off < w.len) (hwrite : s.exec (.write a id off v) = some s') :
    MemRepMap (writeByte m (w.addr off) v) map s' ∧
      (∀ b : Cap.AllocId, b ≠ a → s'.find? b = s.find? b) := by
  obtain ⟨hrel, hbuf⟩ := hmap
  obtain ⟨st, st', c, h', hfind, hwf, hfind', hleaf, hstate, hq, hceil, halloc, hlo,
    hhi, hhw, hst'⟩ := exec_write_parts hwrite
  obtain ⟨st_a, buf, hfind_a, hbuf_a, hlen_a, hrep_a⟩ := hbuf a w hw
  have hst_eq : st_a = st := Option.some.inj (hfind_a.symm.trans hfind)
  have hbuf_a' : st.heap.lookup? a = some buf := hst_eq ▸ hbuf_a
  have hst_alloc : st.alloc = a := Cap.Integrated.State.find?_alloc hfind
  rw [hst_alloc] at hhw
  obtain ⟨hpost, hlt⟩ := heap_write_lookup (buf := buf) hbuf_a' hhw
  subst hst'
  obtain ⟨hrel', hframes⟩ := Cap.AddressMap.Rel.write hrel hwrite
  refine ⟨⟨hrel', ?_⟩, fun b hb => (hframes b hb).1⟩
  intro b wb hwb
  by_cases hba : b = a
  · subst hba
    have hwb_eq : wb = w := Option.some.inj (hwb.symm.trans hw)
    subst hwb_eq
    exact ⟨_, buf.set off v, hfind', hpost, by rw [List.length_set]; exact hlen_a,
      MemRep.set hrep_a hlt⟩
  · obtain ⟨st_b, buf_b, hfind_b, hbuf_b, hlen_b, hrep_b⟩ := hbuf b wb hwb
    have hfind_b' : s'.find? b = some st_b := by
      rw [Cap.Integrated.State.exec_frames_other hwrite
        (by simpa [Cap.Integrated.Cmd.allocId] using hba)]
      exact hfind_b
    have hdisj : wb.Disjoint w := hrel.1.2.1 b wb a w hwb hw hba
    have hrep_b' : MemRep (writeByte m (w.addr off) v) buf_b wb.base := by
      apply MemRep.frame_write (base := w.base) (off := off) (v := v) hrep_b
      intro j bv hj
      have hjlen : j < wb.len := by
        rw [← hlen_b]
        exact (List.getElem?_eq_some_iff.mp hj).1
      exact disjoint_addr_ne hdisj hjlen hoff
    exact ⟨st_b, buf_b, hfind_b', hbuf_b, hlen_b, hrep_b'⟩

/-- A write whose offset is at or past the mapped window's end is refused:
acceptance would put the offset below the buffer's length, which the relation
identifies with the window's length. -/
theorem MemRepMap.exec_write_eq_none_of_len_le {m : Mem} {map : Cap.AddressMap.Map}
    {s : Cap.Integrated.State} {a : Cap.AllocId} {id : Cap.CapId}
    {off : Nat} {v : UInt8} {w : Cap.AddressMap.Window}
    (hmap : MemRepMap m map s) (hw : map.lookup? a = some w) (hoff : w.len ≤ off) :
    s.exec (.write a id off v) = none := by
  cases h : s.exec (.write a id off v) with
  | none => rfl
  | some s' =>
      have hlt := MemRepMap.write_len hmap hw h
      omega

/-! ### The sealed boundary -/

/-- **The composed statement over a finite map, at the sealed boundary.**

`hmap` relates the sealed state's memory to the map, `hw` places `a` at window
`w`, `hacc` is an accepted `Cap.Sealed.write` (the check the sealed boundary
performs), and `hoff` is the pointer-width fact the emitted `getelementptr`
needs.  The offset's in-window bound is derived from the accepted write
(`MemRepMap.write_len`).  The conclusion: the emitted body completes at every
positive budget with the post-memory, that memory satisfies the updated
relation, and an unrelated allocation's component and bytes are unchanged.  The
map is the same term, so every unrelated window is unchanged too. -/
theorem sealed_store8_write_comp_map
    {s s' : Cap.Sealed} {a : Cap.AllocId} {id : Cap.CapId}
    {off : Nat} {bv : BitVec 8} {m : Mem}
    {map : Cap.AddressMap.Map} {w : Cap.AddressMap.Window}
    (hmap : MemRepMap m map (Cap.Integrated.Sealed.state s))
    (hw : map.lookup? a = some w)
    (hacc : Cap.Sealed.write s a id off (byteOf bv) = .ok s')
    (hoff : off < 2 ^ 63) :
    (∀ n : Nat, runFuel noCalls (n + 1) store8IR (store8State m w.base off bv) =
        some (.ret none (postMem m w.base off bv))) ∧
      MemRepMap (postMem m w.base off bv) map (Cap.Integrated.Sealed.state s') ∧
      (∀ b : Cap.AllocId, b ≠ a →
        (Cap.Integrated.Sealed.state s').find? b =
          (Cap.Integrated.Sealed.state s).find? b) ∧
      (∀ b : Cap.AllocId, b ≠ a →
        (Cap.Integrated.Sealed.state s').snapshot b =
          (Cap.Integrated.Sealed.state s).snapshot b) := by
  have hexec : (Cap.Integrated.Sealed.state s).exec
      (.write a id off (byteOf bv)) = some (Cap.Integrated.Sealed.state s') :=
    (Cap.Integrated.Sealed.write_ok_iff s a id off (byteOf bv) s').mp hacc
  have hlen := MemRepMap.write_len hmap hw hexec
  obtain ⟨hmap', hframes⟩ := MemRepMap.write hmap hw hlen hexec
  refine ⟨runFuel_store8_at_mem m w.base off bv hoff, ?_, hframes, ?_⟩
  · rw [postMem_window]
    exact hmap'
  · intro b hb
    rw [Cap.Integrated.State.snapshot, Cap.Integrated.State.snapshot, hframes b hb]

/-! ### A concrete two-allocation model

The memory is `len` cells per window, and the buffers are the fixture heaps'
zero buffers.  Reads and frames below are ordinary `readByte` facts, so the
model is a witness that the relation is inhabited at two allocations rather than
a restatement of it. -/

/-- `n` cells for a window starting at `base`: offset `i` holds `b` at
`base + i`. -/
def byteCells (base : Nat) : Nat → UInt8 → Mem
  | 0, _ => []
  | n + 1, b => (base + n, b) :: byteCells base n b

/-- An in-window cell reads back its byte. -/
theorem readByte_byteCells_self (base n : Nat) (b : UInt8) {i : Nat}
    (hi : i < n) : readByte (byteCells base n b) (base + i) = some b := by
  induction n with
  | zero => omega
  | succ k ih =>
      show readByte ((base + k, b) :: byteCells base k b) (base + i) = some b
      by_cases hik : i = k
      · subst hik
        simp [readByte]
      · have hlt : i < k := by omega
        have hne : base + k ≠ base + i := by omega
        simp only [readByte]
        rw [ite_eq_right hne]
        exact ih hlt

/-- A window's cells produce no byte outside it. -/
theorem readByte_byteCells_none (base n : Nat) (b : UInt8) (a : Nat)
    (h : ∀ i, i < n → base + i ≠ a) : readByte (byteCells base n b) a = none := by
  induction n with
  | zero => rfl
  | succ k ih =>
      show readByte ((base + k, b) :: byteCells base k b) a = none
      simp only [readByte]
      rw [ite_eq_right (h k (by omega))]
      exact ih (fun i hi => h i (by omega))

/-- A read one cell list already answers survives appending a second. -/
theorem readByte_append_of_some {l₁ l₂ : Mem} {a : Nat} {v : UInt8}
    (h : readByte l₁ a = some v) : readByte (l₁ ++ l₂) a = some v := by
  induction l₁ with
  | nil => simp [readByte] at h
  | cons c rest ih =>
      obtain ⟨x, y⟩ := c
      show readByte ((x, y) :: (rest ++ l₂)) a = some v
      simp only [readByte] at h ⊢
      by_cases hx : x = a
      · rw [ite_eq_left hx] at h ⊢
        exact h
      · rw [ite_eq_right hx] at h ⊢
        exact ih h

/-- A cell list that answers nothing leaves the appended list to answer. -/
theorem readByte_append_of_none {l₁ l₂ : Mem} {a : Nat}
    (h : readByte l₁ a = none) : readByte (l₁ ++ l₂) a = readByte l₂ a := by
  induction l₁ with
  | nil => rfl
  | cons c rest ih =>
      obtain ⟨x, y⟩ := c
      show readByte ((x, y) :: (rest ++ l₂)) a = readByte l₂ a
      simp only [readByte] at h ⊢
      by_cases hx : x = a
      · rw [ite_eq_left hx] at h
        simp at h
      · rw [ite_eq_right hx] at h ⊢
        exact ih h

/-- A buffer of `n` copies of `0` is represented by `n` cells holding `0`. -/
theorem memRep_replicate_zero {m : Mem} {base n : Nat}
    (h : ∀ i, i < n → readByte m (base + i) = some 0) :
    MemRep m (List.replicate n 0) base := by
  intro off x hx
  have hoff : off < n := by
    simpa using (List.getElem?_eq_some_iff.mp hx).1
  have hx' : x = 0 := by
    have h' := hx
    rw [List.getElem?_replicate] at h'
    rw [ite_eq_left hoff] at h'
    exact (Option.some.inj h').symm
  subst hx'
  exact h off hoff

/-- A concrete flat memory holding both fixture windows: 64 zero bytes at 4096
and 32 zero bytes at 8192, which are the fixture heaps' buffers. -/
def mem0 : Mem :=
  byteCells window0.base window0.len 0 ++ byteCells window3.base window3.len 0

theorem readByte_mem0_left {i : Nat} (hi : i < window0.len) :
    readByte mem0 (window0.base + i) = some 0 :=
  readByte_append_of_some (readByte_byteCells_self window0.base window0.len 0 hi)

theorem readByte_mem0_right {j : Nat} (hj : j < window3.len) :
    readByte mem0 (window3.base + j) = some 0 := by
  have hnone : readByte (byteCells window0.base window0.len (0 : UInt8))
      (window3.base + j) = none := by
    apply readByte_byteCells_none
    intro i hi
    simp only [window0, window3] at hi ⊢
    omega
  rw [mem0, readByte_append_of_none hnone]
  exact readByte_byteCells_self window3.base window3.len 0 hj

theorem memRep_mem0_left :
    MemRep mem0 (List.replicate window0.len 0) window0.base :=
  memRep_replicate_zero (fun _ hi => readByte_mem0_left hi)

theorem memRep_mem0_right :
    MemRep mem0 (List.replicate window3.len 0) window3.base :=
  memRep_replicate_zero (fun _ hj => readByte_mem0_right hj)

/-- The first fixture component is the zero buffer of its window's length. -/
theorem twoAlloc_find0 :
    twoAllocState.find? ⟨0⟩ =
      some (Cap.Reconstruction.State.initial ⟨0⟩ 64 64 (by decide) ⟨1⟩ ⟨2⟩) := by
  simp [twoAllocState, Cap.Integrated.State.find?, Cap.Integrated.findState?,
    Cap.Reconstruction.State.initial, show (⟨3⟩ : Cap.AllocId) ≠ ⟨0⟩ by decide]

theorem twoAlloc_heap0 :
    (Cap.Reconstruction.State.initial ⟨0⟩ 64 64 (by decide) ⟨1⟩ ⟨2⟩).heap.lookup? ⟨0⟩ =
      some (List.replicate 64 0) := by
  simp [Cap.Reconstruction.State.initial, Cap.Heap.alloc, Cap.Heap.empty,
    Cap.Heap.lookup?, Cap.Heap.lookupList?, Cap.Heap.updateList]

theorem twoAlloc_heap3 :
    (Cap.Reconstruction.State.initial ⟨3⟩ 32 32 (by decide) ⟨4⟩ ⟨5⟩).heap.lookup? ⟨3⟩ =
      some (List.replicate 32 0) := by
  simp [Cap.Reconstruction.State.initial, Cap.Heap.alloc, Cap.Heap.empty,
    Cap.Heap.lookup?, Cap.Heap.lookupList?, Cap.Heap.updateList]

/-- **The two-allocation model.**  The map's two live allocations are both
represented in `mem0` at their own windows. -/
theorem memRepMap_twoAlloc : MemRepMap mem0 twoAllocMap twoAllocState := by
  refine ⟨Cap.AddressMap.twoAlloc_rel, ?_⟩
  intro a w hw
  by_cases h0 : a = ⟨0⟩
  · subst h0
    rw [Cap.AddressMap.twoAllocMap_lookup0] at hw
    have hw0 : w = window0 := (Option.some.inj hw).symm
    subst hw0
    refine ⟨Cap.Reconstruction.State.initial ⟨0⟩ 64 64 (by decide) ⟨1⟩ ⟨2⟩,
      List.replicate 64 0, twoAlloc_find0, twoAlloc_heap0, ?_, ?_⟩
    · simp [window0]
    · simpa [window0] using memRep_mem0_left
  · by_cases h3 : a = ⟨3⟩
    · subst h3
      rw [Cap.AddressMap.twoAllocMap_lookup3] at hw
      have hw3 : w = window3 := (Option.some.inj hw).symm
      subst hw3
      refine ⟨Cap.Reconstruction.State.initial ⟨3⟩ 32 32 (by decide) ⟨4⟩ ⟨5⟩,
        List.replicate 32 0, Cap.AddressMap.twoAlloc_find3, twoAlloc_heap3, ?_, ?_⟩
      · simp [window3]
      · simpa [window3] using memRep_mem0_right
    · rw [Cap.AddressMap.twoAllocMap_lookup_other h0 h3] at hw
      simp at hw

/-- **The affirmative control.**  The concrete write through allocation `⟨0⟩`'s
root fragment is accepted; without this, the refusal controls below would be
compatible with a model whose writes are all refused. -/
theorem twoAlloc_write0_accepted :
    (twoAllocState.exec (.write ⟨0⟩ ⟨1⟩ 5 9)).isSome = true := by
  decide

theorem twoAlloc_write0_exists :
    ∃ s', twoAllocState.exec (.write ⟨0⟩ ⟨1⟩ 5 9) = some s' := by
  have h := twoAlloc_write0_accepted
  cases hex : twoAllocState.exec (.write ⟨0⟩ ⟨1⟩ 5 9) with
  | none => simp [hex] at h
  | some s' => exact ⟨s', rfl⟩

/-- **The concrete write control.**  In the two-allocation model, the accepted
write at offset 5 of `⟨0⟩` leaves the relation holding at the kernel's
post-memory, and the second allocation's component and bytes are unchanged. -/
theorem example_write_model :
    ∃ s', twoAllocState.exec (.write ⟨0⟩ ⟨1⟩ 5 9) = some s' ∧
      MemRepMap (writeByte mem0 (window0.addr 5) 9) twoAllocMap s' ∧
      s'.find? ⟨3⟩ = twoAllocState.find? ⟨3⟩ ∧
      s'.snapshot ⟨3⟩ = twoAllocState.snapshot ⟨3⟩ := by
  obtain ⟨s', hex⟩ := twoAlloc_write0_exists
  have hlen : 5 < window0.len := by simp [window0]
  obtain ⟨hmap', hframes⟩ :=
    MemRepMap.write memRepMap_twoAlloc Cap.AddressMap.twoAllocMap_lookup0 hlen hex
  refine ⟨s', hex, hmap', hframes ⟨3⟩ (by decide), ?_⟩
  rw [Cap.Integrated.State.snapshot, Cap.Integrated.State.snapshot,
    hframes ⟨3⟩ (by decide)]

/-- **The flat-memory frame.**  A write in the first window leaves every byte of
the second reading exactly as it did, which is the disjointness the write
theorem uses discharged at the concrete addresses. -/
theorem example_third_frame {j : Nat} (hj : j < window3.len) :
    readByte (writeByte mem0 (window0.addr 5) 9) (window3.addr j) =
      readByte mem0 (window3.addr j) := by
  have hrep : MemRep (writeByte mem0 (window0.addr 5) 9)
      (List.replicate window3.len 0) window3.base := by
    apply MemRep.frame_write (base := window0.base) (off := 5) (v := 9) memRep_mem0_right
    intro k b hb
    have hk : k < window3.len := by
      simpa using (List.getElem?_eq_some_iff.mp hb).1
    simp only [allocAddr, window0, window3] at hk ⊢
    omega
  have h1 := hrep j 0 (List.getElem?_replicate_of_lt hj)
  have h2 := memRep_mem0_right j 0 (List.getElem?_replicate_of_lt hj)
  simpa [Cap.AddressMap.Window.addr, allocAddr] using h1.trans h2.symm

/-! ### Refused controls -/

/-- **Out-of-window write refused.**  At the end of `⟨0⟩`'s window the accepted
write relation has no room: the model refuses the command. -/
theorem example_out_of_window_refused :
    twoAllocState.exec (.write ⟨0⟩ ⟨1⟩ 64 9) = none :=
  MemRepMap.exec_write_eq_none_of_len_le memRepMap_twoAlloc
    Cap.AddressMap.twoAllocMap_lookup0 (by simp [window0])

/-- The map produces no address past the window's end, so there is no kernel
call site there either. -/
theorem example_window_addr_none : twoAllocMap.addr? ⟨0⟩ 64 = none :=
  Cap.AddressMap.out_of_window_addr_none

/-- An overlapping window is refused by the map. -/
theorem overlapping_window_refused :
    (twoAllocMap.alloc ⟨9⟩ { base := 4128, len := 16 }).isNone = true :=
  Cap.AddressMap.overlapping_alloc_refused

/-- The refused window really would overlap: its first address is offset 32 of
`⟨0⟩`'s window, an in-window offset. -/
theorem overlapping_window_shares_addr :
    ∃ i j, i < window0.len ∧ j < 16 ∧ window0.base + i = (4128 : Nat) + j :=
  ⟨32, 0, by simp [window0], by simp, by simp [window0]⟩

/-! ### Axiom footprint

The same floor the one-window composition pays, pinned here so a change fails
the build rather than the audit. -/

/--
info: 'LlvmBridge.MemRepMap.write' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms LlvmBridge.MemRepMap.write

/--
info: 'LlvmBridge.MemRepMap.write_len' depends on axioms: [propext]
-/
#guard_msgs in
#print axioms LlvmBridge.MemRepMap.write_len

/--
info: 'LlvmBridge.sealed_store8_write_comp_map' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms LlvmBridge.sealed_store8_write_comp_map

/--
info: 'LlvmBridge.memRepMap_twoAlloc' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms LlvmBridge.memRepMap_twoAlloc

/--
info: 'LlvmBridge.example_write_model' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms LlvmBridge.example_write_model

end LlvmBridge
