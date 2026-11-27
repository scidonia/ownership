/-
The composed kernel theorem: one authorized integrated byte write.

`LlvmBridge/Store8.lean` proves that the clang-emitted body writes the argument
byte at `p + i` in `LeanLLVM`'s byte memory, from any starting memory, in one
control step, with no `ub` and no divergence.  This file adds the half the review
asks for: a relation between one `Cap.Integrated` allocation's heap bytes and
that memory at an explicit address map, the whole-share read--write fragment an
accepted write consumes, and the composition of the two.

The address map is the simplest map one allocation admits: offset `off` is the
flat address `base + off` (`allocAddr`), which is injective on the window
(`allocAddr_injective`).  `MemRep m buf base` says the flat memory holds the
allocation's buffer at that map.  Multi-allocation safety is not assumed away:
`MemRep.frame_write` states the disjointness hypothesis a second allocation
needs before the frame can be read for it.

What is proved, for one accepted integrated write:

* `write_authority` — the write consumed a current, active, whole-share
  (`c.q = st.D`) read--write (`c.ceiling = .readWrite`) fragment covering the
  written offset.  The command's own guard supplies this; it is not assumed.
* `component_write_parts` and `heap_write_lookup` — the component write behind
  it is a `Cap.Heap.write?` at that offset, so the post-heap is `List.set` and
  the offset was in range.
* `store8_exec_write_comp` — the composed statement.  The emitted body completes
  at every positive budget with the reference store's post-memory
  (`writeByte` at `base + off`); that memory represents the post-state's buffer;
  the frame holds outside the written address; the written byte reads back on
  both sides; the post-state's component holds the updated buffer; every other
  allocation's state is unchanged; the integrated invariant survives.
* `exec_write_read_frame` — every other offset of the same allocation reads as
  it did.
* `sealed_store8_write_comp` — the same at the sealed boundary.  `Cap.Sealed`
  re-exports `Cap.Integrated.Sealed`; an accepted `Cap.Sealed.write` is exactly
  the underlying state's accepted write command (`Cap.Integrated.Sealed.write_ok_iff`),
  so the composed statement is available without opening the sealed value's
  private constructor.

What is assumed, and stays stated rather than discharged:

* `MemRep m buf base` — the flat memory already holds the allocation's window.
  `LeanLLVM` has no allocation bounds, so the C-level in-bounds guarantee is the
  Cap-side guard plus `off < buf.length`, which `component_write_parts` and
  `heap_write_lookup` derive from the accepted write; it is not a theorem about
  C.  `off < 2 ^ 63` is the `getelementptr` adding case the emitted body's
  semantics needs — the pointer-width/arithmetic assumption.
* the projection from clang's raw emission to the parser's surface, unchanged
  from `LlvmBridge/Store8.lean` (`scripts/project-ir.sed` and the bridge's
  `README.md`); this file adds no projection step and does not re-justify one.
* one allocation and one address map.  The theorem writes one byte in one
  window; two live allocations need the disjointness hypothesis of
  `MemRep.frame_write`, and nothing here proves that a loader assigns it.
* the executable edge.  ABI, native execution, a live handle and the physical
  allocation are outside this model, as `Cap.Sealed`'s `boundaryClaims` and the
  bridge's `README.md` record.

No `sorry`, no new axiom, and no `Cap` or `LeanLLVM` definition is re-proved: the
kernel step is `runFuel_store8IR_succ`, the byte is `store8Model_read_at`, the
frame is `store8Model_frame`, and the ownership side is `State.exec_inv`,
`State.find?_alloc`, `State.exec_frames_other` and `Heap.write_ne`.
-/
import Cap.Sealed
import LlvmBridge.Store8

namespace LlvmBridge

open LeanLLVM

/-! ### The address map and the memory representation -/

/-- The flat address of offset `off` in an allocation whose window starts at
`base`. -/
def allocAddr (base off : Nat) : Nat := base + off

/-- Offsets inside one allocation's window map to distinct addresses. -/
theorem allocAddr_injective {base : Nat} : Function.Injective (allocAddr base) :=
  fun _ _ h => Nat.add_left_cancel h

/-- The flat memory `m` holds `buf` at `base`: every offset the buffer has reads
back the buffer's byte at `base + off`. -/
def MemRep (m : Mem) (buf : List UInt8) (base : Nat) : Prop :=
  ∀ (off : Nat) (b : UInt8), buf[off]? = some b → readByte m (allocAddr base off) = some b

/-- A write inside the window updates the represented buffer. -/
theorem MemRep.set {m : Mem} {buf : List UInt8} {base off : Nat} {v : UInt8}
    (hrep : MemRep m buf base) (hlt : off < buf.length) :
    MemRep (writeByte m (allocAddr base off) v) (buf.set off v) base := by
  intro j b hb
  by_cases hjo : off = j
  · subst hjo
    rw [readByte_writeByte_same]
    rw [List.getElem?_set_self hlt] at hb
    exact hb
  · have haddr : allocAddr base off ≠ allocAddr base j := fun h =>
      hjo (allocAddr_injective h)
    rw [readByte_writeByte_other m v haddr]
    rw [List.getElem?_set_ne hjo] at hb
    exact hrep j b hb

/-- Agreement outside a footprint preserves a representation whose whole window
avoids the footprint. -/
theorem MemRep.of_agrees {m m' : Mem} {buf : List UInt8} {base : Nat}
    {frame : Nat → Prop} (hagree : AgreesOutsideMem m' m frame)
    (hrep : MemRep m buf base)
    (havoid : ∀ (j : Nat) (b : UInt8), buf[j]? = some b → ¬ frame (allocAddr base j)) :
    MemRep m' buf base := by
  intro j b hb
  rw [hagree (allocAddr base j) (havoid j b hb)]
  exact hrep j b hb

/-- A write at one address leaves a second allocation's representation intact
whenever that allocation's window avoids the written address.  This is the
disjointness an address map for two live allocations owes, stated where it is
used rather than assumed globally.  The written byte is arbitrary, so the frame
serves the kernel's `byteOf bv` and the ownership model's own writes alike. -/
theorem MemRep.frame_write {m : Mem} {buf₂ : List UInt8} {base base₂ : Nat}
    {off : Nat} {v : UInt8} (hrep₂ : MemRep m buf₂ base₂)
    (havoid : ∀ (j : Nat) (b : UInt8), buf₂[j]? = some b →
      allocAddr base₂ j ≠ allocAddr base off) :
    MemRep (writeByte m (allocAddr base off) v) buf₂ base₂ :=
  MemRep.of_agrees
    (fun _ hc => readByte_writeByte_other m v (fun h => hc h.symm))
    hrep₂ havoid

/-! ### The emitted body at an explicit memory

`LlvmBridge/Store8.lean` states its call-site theorem at `initState`, whose
memory is empty.  The one control step it proves (`runFuel_store8IR_succ`) is
already parametric in the state, so the memory can be fixed before the run; this
section does exactly that and nothing else. -/

/-- The reference store's post-memory for the kernel called at this window. -/
def postMem (m : Mem) (base off : Nat) (bv : BitVec 8) : Mem :=
  writeByte m (allocAddr base off) (byteOf bv)

/-- The emitted body's initial state at flat memory `m`, called with the
allocation's base address, the offset and the byte. -/
def store8State (m : Mem) (base off : Nat) (bv : BitVec 8) : State :=
  { initState store8IR (store8Args base (BitVec.ofNat 64 off) bv) with mem := m }

/-- At every positive budget the emitted body's run from this memory is the
reference store's single outcome: the byte written at `base + off`, `void`
returned.  The proof is `runFuel_store8IR_succ`, the kernel step the bridge
already proves, instantiated at this state. -/
theorem runFuel_store8_at_mem (m : Mem) (base off : Nat) (bv : BitVec 8)
    (hoff : off < 2 ^ 63) (n : Nat) :
    runFuel noCalls (n + 1) store8IR (store8State m base off bv) =
      some (.ret none (postMem m base off bv)) := by
  have hoff64 : off < 2 ^ 64 :=
    Nat.lt_of_lt_of_le hoff (by decide)
  have hx : (BitVec.ofNat 64 off).toNat = off := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hoff64]
  have hpos : (BitVec.ofNat 64 off).toNat < 2 ^ 63 := by omega
  have hpc : (store8State m base off bv).pc = "entry" := rfl
  have h0 : lookupName (store8State m base off bv).env "%0" = some (.ptr base) := by
    simp [store8State, initState, store8IR, store8Args]
  have h1 : lookupName (store8State m base off bv).env "%1" =
      some (.int 64 (BitVec.ofNat 64 off)) := by
    simp [store8State, initState, store8IR, store8Args, lookupName]
  have h2 : lookupName (store8State m base off bv).env "%2" = some (.int 8 bv) := by
    simp [store8State, initState, store8IR, store8Args, lookupName]
  simpa [store8State, postMem, allocAddr, store8Addr, hx] using
    runFuel_store8IR_succ (store8State m base off bv) base (BitVec.ofNat 64 off) bv
      hpc h0 h1 h2 hpos n

/-- Every outcome the emitted body reaches from this memory is the reference
store's outcome, so the run-level statement carries the refinement, not only
completion.  The empty budget is not an outcome (`runFuel` returns `none`). -/
theorem store8IR_refines_model_at_mem (m : Mem) (base off : Nat) (bv : BitVec 8)
    (hoff : off < 2 ^ 63) {out : Outcome}
    (h : ∃ n, runFuel noCalls n store8IR (store8State m base off bv) = some out) :
    out = .ret none (postMem m base off bv) := by
  obtain ⟨n, hn⟩ := h
  rcases n with _ | k
  · simp [runFuel] at hn
  · rw [runFuel_store8_at_mem m base off bv hoff k] at hn
    simpa using hn.symm

/-- The reference store's outcome is a behaviour of the emitted body at this
memory, so the behaviour set is not empty. -/
theorem store8IR_completes_at_mem (m : Mem) (base off : Nat) (bv : BitVec 8)
    (hoff : off < 2 ^ 63) :
    ∃ n, runFuel noCalls n store8IR (store8State m base off bv) =
      some (.ret none (postMem m base off bv)) :=
  ⟨1, runFuel_store8_at_mem m base off bv hoff 0⟩

/-! ### The ownership side: the component write behind an accepted command -/

/-- A successful heap write is `List.set` at the written offset, and the offset
was inside the buffer. -/
theorem heap_write_lookup {h h' : Cap.Heap} {a : Cap.AllocId} {off : Nat}
    {v : UInt8} {buf : List UInt8} (hl : h.lookup? a = some buf)
    (hw : h.write? a off v = some h') :
    h'.lookup? a = some (buf.set off v) ∧ off < buf.length := by
  cases hl' : h.lookup? a with
  | none => simp [Cap.Heap.write?, hl'] at hw
  | some xs =>
      have hxs : xs = buf := Option.some.inj (hl'.symm.trans hl)
      rw [hxs] at hl'
      by_cases hlt : off < buf.length
      · simp only [Cap.Heap.write?, hl', ite_eq_left hlt, Option.some.injEq] at hw
        subst hw
        exact ⟨Cap.Heap.lookupList?_updateList h.bufs (xs := buf) hl, hlt⟩
      · simp [Cap.Heap.write?, hl', hlt] at hw

/-- A heap read at an offset the buffer holds returns that byte. -/
theorem heap_read_of_lookup {h : Cap.Heap} {a : Cap.AllocId} {buf : List UInt8}
    {off : Nat} {b : UInt8} (hl : h.lookup? a = some buf) (hb : buf[off]? = some b) :
    h.read? a off = some b := by
  unfold Cap.Heap.read?
  rw [hl]
  simpa using hb

/-- An accepted component write is a heap write at the written offset, under a
current active whole-share read--write fragment that covers it. -/
theorem component_write_parts {st st' : Cap.Reconstruction.State} {id : Cap.CapId}
    {off : Nat} {v : UInt8} (h : st.write id off v = some st') :
    ∃ (c : Cap.Leaf) (h' : Cap.Heap),
      st.forest.findLeaf? id = some c ∧ c.state = .active ∧ c.q = st.D ∧
      c.ceiling = .readWrite ∧ c.lo ≤ off ∧ off < c.hi ∧
      st.heap.write? st.alloc off v = some h' ∧ st' = { st with heap := h' } := by
  cases hf : st.forest.findLeaf? id with
  | none => simp [Cap.Reconstruction.State.write, hf] at h
  | some c =>
      by_cases hg : c.state = .active ∧ c.q = st.D ∧ c.ceiling = .readWrite ∧
          c.lo ≤ off ∧ off < c.hi
      · simp only [Cap.Reconstruction.State.write, hf, dite_eq_left hg] at h
        cases hw : st.heap.write? st.alloc off v with
        | none => simp [hw] at h
        | some h' =>
            simp only [hw, Option.some.injEq] at h
            subst h
            exact ⟨c, h', rfl, hg.1, hg.2.1, hg.2.2.1, hg.2.2.2.1, hg.2.2.2.2,
              rfl, rfl⟩
      · simp only [Cap.Reconstruction.State.write, hf, dite_eq_right hg] at h
        simp at h

/-- A successful component update of a present allocation updates exactly that
allocation's component. -/
theorem updateState_find {l l' : List Cap.Reconstruction.State} {a : Cap.AllocId}
    {f : Cap.Reconstruction.State → Option Cap.Reconstruction.State}
    (h : Cap.Integrated.updateState l a f = some l') :
    ∃ st st', Cap.Integrated.findState? l a = some st ∧ f st = some st' ∧
      Cap.Integrated.findState? l' a = some st' := by
  induction l generalizing l' with
  | nil => simp [Cap.Integrated.updateState] at h
  | cons head tail ih =>
      simp only [Cap.Integrated.updateState] at h
      by_cases hk : head.alloc = a
      · rw [ite_eq_left hk] at h
        cases hf : f head with
        | none => simp [hf] at h
        | some next =>
            simp only [hf] at h
            by_cases hk' : next.alloc = a
            · rw [ite_eq_left hk'] at h
              simp only [Option.some.injEq] at h
              subst h
              exact ⟨head, next, by simp [Cap.Integrated.findState?, hk], hf,
                by simp [Cap.Integrated.findState?, hk']⟩
            · rw [ite_eq_right hk'] at h
              simp at h
      · rw [ite_eq_right hk] at h
        cases hrec : Cap.Integrated.updateState tail a f with
        | none => simp [hrec] at h
        | some tail' =>
            simp only [hrec, Option.some.injEq] at h
            subst h
            obtain ⟨st, st', hfind, hf, hfind'⟩ := ih hrec
            refine ⟨st, st', ?_, hf, ?_⟩
            · simpa [Cap.Integrated.findState?, hk] using hfind
            · simpa [Cap.Integrated.findState?, hk] using hfind'

/-- A successful integrated update of a present allocation updates exactly that
allocation's component. -/
theorem update_find {s s' : Cap.Integrated.State} {a : Cap.AllocId}
    {f : Cap.Reconstruction.State → Option Cap.Reconstruction.State}
    (h : s.update a f = some s') :
    ∃ st st', s.find? a = some st ∧ f st = some st' ∧ s'.find? a = some st' := by
  unfold Cap.Integrated.State.update at h
  cases hupd : Cap.Integrated.updateState s.allocs a f with
  | none => simp [hupd] at h
  | some l' =>
      simp only [hupd, Option.map_some, Option.some.injEq] at h
      subst h
      obtain ⟨st, st', hfind, hf, hfind'⟩ := updateState_find hupd
      refine ⟨st, st', hfind, hf, ?_⟩
      simpa [Cap.Integrated.State.find?] using hfind'

/-- An accepted integrated write exposes its authorized fragment and the
component write that produced the post-state. -/
theorem exec_write_parts {s s' : Cap.Integrated.State} {a : Cap.AllocId}
    {id : Cap.CapId} {off : Nat} {v : UInt8}
    (h : s.exec (.write a id off v) = some s') :
    ∃ (st st' : Cap.Reconstruction.State) (c : Cap.Leaf) (h' : Cap.Heap),
      s.find? a = some st ∧ st.write id off v = some st' ∧ s'.find? a = some st' ∧
      st.forest.findLeaf? id = some c ∧ c.state = .active ∧ c.q = st.D ∧
      c.ceiling = .readWrite ∧ c.lo ≤ off ∧ off < c.hi ∧
      st.heap.write? st.alloc off v = some h' ∧ st' = { st with heap := h' } := by
  have hupd : s.update a (fun st => st.write id off v) = some s' := h
  obtain ⟨st, st', hfind, hwf, hfind'⟩ := update_find hupd
  obtain ⟨c, h', hleaf, hstate, hq, hceil, hlo, hhi, hhw, hst'⟩ :=
    component_write_parts hwf
  exact ⟨st, st', c, h', hfind, hwf, hfind', hleaf, hstate, hq, hceil, hlo, hhi,
    hhw, hst'⟩

/-- The capability an accepted integrated write consumed: a current, active,
whole-share, read--write fragment covering the written offset.  Derived from the
command's guard, not assumed. -/
theorem write_authority {s s' : Cap.Integrated.State} {a : Cap.AllocId}
    {id : Cap.CapId} {off : Nat} {v : UInt8}
    (h : s.exec (.write a id off v) = some s') :
    ∃ (st : Cap.Reconstruction.State) (c : Cap.Leaf),
      s.find? a = some st ∧ st.forest.findLeaf? id = some c ∧
      c.state = .active ∧ c.q = st.D ∧ c.ceiling = .readWrite ∧
      c.lo ≤ off ∧ off < c.hi := by
  obtain ⟨st, st', c, h', hfind, hwf, hfind', hleaf, hstate, hq, hceil, hlo, hhi,
    hhw, hst'⟩ := exec_write_parts h
  exact ⟨st, c, hfind, hleaf, hstate, hq, hceil, hlo, hhi⟩

/-! ### The composition -/

/-- **One authorized integrated byte write, executed by the emitted body.**

`hinv` is the integrated invariant, `hfind`/`hb` name the allocation's component
and its buffer, `hrep` is the representation of that buffer in the flat memory at
`base`, `hwrite` is the accepted integrated write (the check `Cap.Sealed.write`
performs), and `hoff` is the pointer-width assumption the emitted
`getelementptr` needs.  The conclusion is the review's schema for this one
write: the kernel completes with the reference store's post-memory, that memory
represents the post-state's buffer, the frame holds outside the written address,
the written byte reads back on both sides, the post-state's component holds the
updated buffer, other allocations are unchanged, and the integrated invariant
survives. -/
theorem store8_exec_write_comp
    {s s' : Cap.Integrated.State} {a : Cap.AllocId} {id : Cap.CapId}
    {off : Nat} {bv : BitVec 8} {m : Mem} {base : Nat}
    {st : Cap.Reconstruction.State} {buf : List UInt8}
    (hinv : s.Inv) (hfind : s.find? a = some st)
    (hb : st.heap.lookup? a = some buf) (hrep : MemRep m buf base)
    (hwrite : s.exec (.write a id off (byteOf bv)) = some s')
    (hoff : off < 2 ^ 63) :
    (∀ n : Nat, runFuel noCalls (n + 1) store8IR (store8State m base off bv) =
        some (.ret none (postMem m base off bv))) ∧
      MemRep (postMem m base off bv) (buf.set off (byteOf bv)) base ∧
      AgreesOutsideMem (postMem m base off bv) m
        (fun addr => addr = allocAddr base off) ∧
      s'.Inv ∧
      (∃ st' : Cap.Reconstruction.State, s'.find? a = some st' ∧
        st'.heap.lookup? a = some (buf.set off (byteOf bv))) ∧
      readByte (postMem m base off bv) (allocAddr base off) = some (byteOf bv) ∧
      s'.read? a off = some (byteOf bv) ∧
      (∀ b : Cap.AllocId, b ≠ a → s'.find? b = s.find? b) := by
  obtain ⟨st₁, st', c, h', hfind₁, hwf, hfind', hleaf, hstate, hq, hceil, hlo, hhi,
    hhw, hst'⟩ := exec_write_parts hwrite
  have hst₁ : st = st₁ := Option.some.inj (hfind.symm.trans hfind₁)
  have hb₁ : st₁.heap.lookup? a = some buf := hst₁ ▸ hb
  have hst_alloc : st₁.alloc = a := Cap.Integrated.State.find?_alloc hfind₁
  rw [hst_alloc] at hhw
  obtain ⟨hpost, hlt⟩ : h'.lookup? a = some (buf.set off (byteOf bv)) ∧
      off < buf.length := heap_write_lookup (buf := buf) hb₁ hhw
  subst hst'
  refine ⟨runFuel_store8_at_mem m base off bv hoff, ?_,
    by simpa [postMem, store8Model, allocAddr] using
      store8Model_frame m base off (byteOf bv),
    Cap.Integrated.State.exec_inv hwrite hinv, ?_,
    by simpa [postMem, store8Model, allocAddr] using
      store8Model_read_at m base off (byteOf bv), ?_, ?_⟩
  · exact MemRep.set hrep hlt
  · exact ⟨_, hfind', hpost⟩
  · have hread : h'.read? a off = some (byteOf bv) :=
      heap_read_of_lookup hpost (List.getElem?_set_self hlt)
    simpa [Cap.Integrated.State.read?, hfind', hst_alloc] using hread
  · intro b hb
    exact Cap.Integrated.State.exec_frames_other hwrite
      (by simpa [Cap.Integrated.Cmd.allocId] using hb)

/-- A write at one offset leaves every other offset of the same allocation
reading as it did. -/
theorem exec_write_read_frame {s s' : Cap.Integrated.State} {a : Cap.AllocId}
    {id : Cap.CapId} {off : Nat} {v : UInt8} {j : Nat}
    (h : s.exec (.write a id off v) = some s') (hj : off ≠ j) :
    s'.read? a j = s.read? a j := by
  obtain ⟨st, st', c, h', hfind, hwf, hfind', hleaf, hstate, hq, hceil, hlo, hhi,
    hhw, hst'⟩ := exec_write_parts h
  have hst_alloc : st.alloc = a := Cap.Integrated.State.find?_alloc hfind
  rw [hst_alloc] at hhw
  subst hst'
  have hne : h'.read? a j = st.heap.read? a j := Cap.Heap.write_ne hhw hj
  simp only [Cap.Integrated.State.read?, hfind, hfind']
  simpa [hst_alloc] using hne

/-- The composed statement at the sealed boundary.  `s` and `s'` are sealed
values; `hacc` is an accepted `Cap.Sealed.write`, which
`Cap.Integrated.Sealed.write_ok_iff` identifies with the underlying state's
accepted write command, and the conclusion is the composed kernel statement about
the states the sealed values carry. -/
theorem sealed_store8_write_comp
    {s s' : Cap.Sealed} {a : Cap.AllocId} {id : Cap.CapId}
    {off : Nat} {bv : BitVec 8} {m : Mem} {base : Nat}
    {st : Cap.Reconstruction.State} {buf : List UInt8}
    (hfind : (Cap.Integrated.Sealed.state s).find? a = some st)
    (hb : st.heap.lookup? a = some buf) (hrep : MemRep m buf base)
    (hacc : Cap.Sealed.write s a id off (byteOf bv) = .ok s')
    (hoff : off < 2 ^ 63) :
    (∀ n : Nat, runFuel noCalls (n + 1) store8IR (store8State m base off bv) =
        some (.ret none (postMem m base off bv))) ∧
      MemRep (postMem m base off bv) (buf.set off (byteOf bv)) base ∧
      AgreesOutsideMem (postMem m base off bv) m
        (fun addr => addr = allocAddr base off) ∧
      (Cap.Integrated.Sealed.state s').Inv ∧
      (∃ st' : Cap.Reconstruction.State,
        (Cap.Integrated.Sealed.state s').find? a = some st' ∧
        st'.heap.lookup? a = some (buf.set off (byteOf bv))) := by
  have hexec : (Cap.Integrated.Sealed.state s).exec
      (.write a id off (byteOf bv)) = some (Cap.Integrated.Sealed.state s') :=
    (Cap.Integrated.Sealed.write_ok_iff s a id off (byteOf bv) s').mp hacc
  obtain ⟨hcomplete, hrep', hframe, hinv', hpost, hbyte, hread, hframeAlloc⟩ :=
    store8_exec_write_comp (Cap.Integrated.Sealed.state_inv s) hfind hb hrep hexec hoff
  exact ⟨hcomplete, hrep', hframe, hinv', hpost⟩

/-! ### Axiom footprint

The standard floor the bridge already pays: `propext`, `Classical.choice` and
`Quot.sound` are what `Cap`'s list and `Option` vocabulary arrives with, and the
composed statements add no axiom of their own. -/

/--
info: 'LlvmBridge.store8_exec_write_comp' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms LlvmBridge.store8_exec_write_comp

/--
info: 'LlvmBridge.sealed_store8_write_comp' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms LlvmBridge.sealed_store8_write_comp

/--
info: 'LlvmBridge.write_authority' depends on axioms: [propext]
-/
#guard_msgs in
#print axioms LlvmBridge.write_authority

end LlvmBridge
