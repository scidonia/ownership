/-
Union-find under the repaired access discipline.

The functional union-find (`Cap/UFCompress`, `Cap/UFRun`) reads parent entries
without access evidence, because a runtime index cannot discharge a static
`Ctx.CanRead` premise. This module supplies the missing link: the representation
predicate `UFRep` describes a whole-share read-write parent array of length `n`
whose stored bytes are all valid node indices. From it, *any* runtime index
`i < n` yields the static access evidence (`Ctx.CanRead`, `Ctx.CanWrite`), and a
parent read is proved to return a value below `n` — which is exactly what the
recursive chase needs for its next index. The chase and one-step compression are
then typed by that evidence; the compression's write is a checked write whose
guard comes from the invariant rather than from the program text.

This is the checked *read* route over the pure backend model. It is not an
interpreter, an FFI path, a compiler guarantee or an in-place claim.
-/
import Cap.Access
import Cap.Typed
import Cap.UFCompress
import Cap.IProg

namespace Cap

/-- A whole-share read-write parent array of length `n` under capability `id`,
whose stored bytes are all valid node indices. This is the representation
predicate the checked chase runs under: its data invariant is what turns a
runtime index into an in-range access and what bounds each parent read. -/
def UFRep (w : World) (a : AllocId) (id : CapId) (n : Nat) : Prop :=
  ∃ o c b, w.ctx.findOwner? a = some o ∧ o.root.find? id = some c ∧
    c.state = .active ∧ c.q = w.ctx.D ∧ c.ceiling = .readWrite ∧
    c.lo = 0 ∧ c.hi = n ∧ w.heaps a = some b ∧ b.buf.length = n ∧
    ∀ i, i < n → ∃ v, b.buf[i]? = some v ∧ v.toNat < n

/-- A runtime index below the array length is readable under the representation
predicate. -/
theorem UFRep.canRead {w : World} {a : AllocId} {id : CapId} {n : Nat}
    (h : UFRep w a id n) {i : Nat} (hi : i < n) : Ctx.CanRead w.ctx a id i := by
  obtain ⟨o, c, b, hfind, hc, hact, hq, hceil, hlo, hhi, -, -, -⟩ := h
  refine ⟨o, hfind, c, hc, hact, ?_, ?_, ?_⟩
  · simpa [hq] using c.pos
  · omega
  · omega

/-- A runtime index below the array length is writable under the representation
predicate. -/
theorem UFRep.canWrite {w : World} {a : AllocId} {id : CapId} {n : Nat}
    (h : UFRep w a id n) {i : Nat} (hi : i < n) : Ctx.CanWrite w.ctx a id i := by
  obtain ⟨o, c, b, hfind, hc, hact, hq, hceil, hlo, hhi, -, -, -⟩ := h
  refine ⟨o, hfind, ?_⟩
  unfold Owner.writableB
  rw [hc]
  exact decide_eq_true ⟨hact, hq, hceil, by omega, by omega⟩

/-- One parent read at an index, carrying the access evidence it was admitted
under. -/
def readParent? (w : World) (a : AllocId) (id : CapId) (i : Nat)
    (_h : Ctx.CanRead w.ctx a id i) : Option Nat :=
  ((w.heaps a).bind (·.read i)).map (·.toNat)

/-- A represented parent read succeeds. -/
theorem UFRep.readParent?_some {w : World} {a : AllocId} {id : CapId} {n : Nat}
    (h : UFRep w a id n) {i : Nat} (hi : i < n) :
    ∃ v, readParent? w a id i (h.canRead hi) = some v := by
  obtain ⟨-, -, b, -, -, -, -, -, -, -, hb, -, hdata⟩ := h
  obtain ⟨v, hv, -⟩ := hdata i hi
  refine ⟨v.toNat, ?_⟩
  unfold readParent?
  rw [hb]
  simp only [Option.bind_some, Backend.read, hv, Option.map_some]

/-- A represented parent read returns a valid node index: the runtime fact the
chase's next iteration needs. -/
theorem UFRep.readParent?_lt {w : World} {a : AllocId} {id : CapId} {n : Nat}
    (h : UFRep w a id n) {i : Nat} (hi : i < n) {r : Nat}
    (hread : readParent? w a id i (h.canRead hi) = some r) : r < n := by
  have hrep := h
  obtain ⟨-, -, b, -, -, -, -, -, -, -, hb, -, hdata⟩ := hrep
  obtain ⟨v, hv, hvlt⟩ := hdata i hi
  have hsome : readParent? w a id i (h.canRead hi) = some v.toNat := by
    unfold readParent?
    rw [hb]
    simp only [Option.bind_some, Backend.read, hv, Option.map_some]
  rw [hsome] at hread
  exact Option.some.inj hread ▸ hvlt

/-- A represented parent read is a byte value, so it is below 256. -/
theorem UFRep.readParent?_byte_lt {w : World} {a : AllocId} {id : CapId} {n : Nat}
    (h : UFRep w a id n) {i : Nat} (hi : i < n) {r : Nat}
    (hread : readParent? w a id i (h.canRead hi) = some r) : r < 256 := by
  have hrep := h
  obtain ⟨-, -, b, -, -, -, -, -, -, -, hb, -, hdata⟩ := hrep
  obtain ⟨v, hv, -⟩ := hdata i hi
  have hsome : readParent? w a id i (h.canRead hi) = some v.toNat := by
    unfold readParent?
    rw [hb]
    simp only [Option.bind_some, Backend.read, hv, Option.map_some]
  rw [hsome] at hread
  exact Option.some.inj hread ▸ v.toNat_lt

/-- The checked chase: follow parent links from the (in-range) node `x`, stopping
at a fixed point. The index evidence at every step is derived from `UFRep`; the
next index is in range by `readParent?_lt`. Fuel bounds the walk. -/
def findRootC (w : World) (a : AllocId) (id : CapId) (n : Nat) (h : UFRep w a id n) :
    Nat → (x : Nat) → x < n → Option Nat
  | 0, _, _ => none
  | fuel + 1, x, hx =>
    match hr : readParent? w a id x (h.canRead hx) with
    | none => none
    | some r =>
      if r = x then some x
      else findRootC w a id n h fuel r (h.readParent?_lt hx hr)

/-! ### Semantic reading of the chase

The checked chase reads the byte backend. This section reads that backend as the
functional model's parent array, so the chase inherits the functional search's
root and reachability facts. -/

/-- The functional parent array a backend represents. -/
def UFArr (b : Backend) : UF.Arr := b.buf.map UInt8.toNat

/-- An in-range entry of the represented array is the stored byte read as a
node index. -/
theorem UFArr_getD {b : Backend} {i : Nat} (hi : i < b.buf.length) :
    (UFArr b).getD i i = (b.buf[i]).toNat := by
  unfold UFArr
  rw [List.getD_eq_getElem?_getD, List.getElem?_map]
  rw [List.getElem?_eq_getElem hi]
  rfl

/-- A parent read is the represented array's step. -/
theorem UFRep.readParent?_step {w : World} {a : AllocId} {id : CapId} {n : Nat}
    (h : UFRep w a id n) {b : Backend} (hb : w.heaps a = some b)
    {i : Nat} (hi : i < n) :
    readParent? w a id i (h.canRead hi) = some (UF.step (UFArr b) i) := by
  have hlen : b.buf.length = n := by
    obtain ⟨-, -, b', -, -, -, -, -, -, -, hb', hlen, -⟩ := h
    rw [hb'] at hb
    exact (Option.some.inj hb) ▸ hlen
  have hbi : i < b.buf.length := by omega
  unfold readParent? UF.step UF.parentOf
  rw [hb]
  simp only [Option.bind_some, Backend.read]
  rw [List.getElem?_eq_getElem hbi, UFArr_getD hbi]
  rfl

/-- Under the representation predicate and enough fuel to stop, the checked
chase returns the functional search's result. -/
theorem findRootC_eq_of_stops {w : World} {a : AllocId} {id : CapId} {n : Nat}
    (h : UFRep w a id n) {b : Backend} (hb : w.heaps a = some b) :
    ∀ {fuel x : Nat} (hx : x < n), UF.StopsAt (UFArr b) fuel x →
      findRootC w a id n h fuel x hx = some (UF.findRootF (UFArr b) fuel x) := by
  intro fuel
  induction fuel with
  | zero =>
    intro x hx hstop
    exact (UF.stopsAt_zero (UFArr b) x hstop).elim
  | succ fuel ih =>
    intro x hx hstop
    unfold findRootC
    split
    · rename_i hread
      have hstep := UFRep.readParent?_step h hb hx
      rw [hstep] at hread
      cases hread
    · rename_i r hread
      have hrstep : r = UF.step (UFArr b) x := by
        rw [UFRep.readParent?_step h hb hx] at hread
        exact (Option.some.inj hread).symm
      cases hrstep
      rcases (UF.stopsAt_succ (UFArr b) fuel x).mp hstop with hroot | ⟨hnot, htail⟩
      · have hroot' : UF.step (UFArr b) x = x := hroot
        rw [if_pos hroot']
        rw [UF.findRootF_succ, if_pos hroot']
      · have hnot' : ¬ UF.step (UFArr b) x = x := hnot
        rw [if_neg hnot']
        rw [UF.findRootF_succ, if_neg hnot']
        exact ih (h.readParent?_lt hx hread) htail

/-- A completed checked chase stops at a root of the represented parent array. -/
theorem findRootC_root {w : World} {a : AllocId} {id : CapId} {n : Nat}
    (h : UFRep w a id n) {b : Backend} (hb : w.heaps a = some b)
    {fuel x : Nat} (hx : x < n) (hstop : UF.StopsAt (UFArr b) fuel x) {r : Nat}
    (hr : findRootC w a id n h fuel x hx = some r) :
    UF.IsRoot (UFArr b) r := by
  rw [findRootC_eq_of_stops h hb hx hstop] at hr
  have heq : UF.findRootF (UFArr b) fuel x = r := Option.some.inj hr
  rw [← heq]
  exact UF.findRootF_root hstop

/-- One-step compression through the checked write: `parent[x] := r`, with the
write guard derived from the representation predicate at the runtime index. -/
def compressC (w : World) (a : AllocId) (id : CapId) (n : Nat)
    (_h : UFRep w a id n) (x : Nat) (_hx : x < n) (u : UInt8) : Except String World :=
  w.writeChecked a id x u

/-- Writing a byte and reading the array commute: the functional array of the
written backend is the written functional array. -/
theorem map_toNat_set {l : List UInt8} {x : Nat} {u : UInt8} :
    (l.set x u).map UInt8.toNat = (l.map UInt8.toNat).set x u.toNat := by
  induction l generalizing x with
  | nil => simp
  | cons y ys ih =>
    cases x with
    | zero => simp
    | succ x => simp [ih]

/-- An accepted checked compression writes one byte and leaves the rest alone. -/
theorem compressC_backend {w : World} {a : AllocId} {id : CapId} {n : Nat}
    {h : UFRep w a id n} {x : Nat} {hx : x < n} {u : UInt8} {w' : World}
    (hw : compressC w a id n h x hx u = .ok w') :
    ∃ b b', w.heaps a = some b ∧ w'.heaps a = some b' ∧ b'.buf = b.buf.set x u := by
  unfold compressC at hw
  obtain ⟨o, b, b', hfind, hwrit, hb, hwrite, hctx, hheaps⟩ := World.writeChecked_sound hw
  refine ⟨b, b', hb, ?_, Backend.write_buf hwrite⟩
  rw [hheaps]
  simp [hb]

/-- The checked compression writes exactly the functional model's `compress`. -/
theorem compressC_UFArr {w : World} {a : AllocId} {id : CapId} {n : Nat}
    {h : UFRep w a id n} {x : Nat} {hx : x < n} {u : UInt8} {w' : World}
    (hw : compressC w a id n h x hx u = .ok w')
    {b b' : Backend} (hb : w.heaps a = some b) (hb' : w'.heaps a = some b') :
    UFArr b' = UF.compress (UFArr b) x u.toNat := by
  obtain ⟨b0, b0', hb0, hb0', hbuf0⟩ := compressC_backend hw
  have hbb : b = b0 := Option.some.inj (hb.symm.trans hb0)
  have hb'b : b' = b0' := Option.some.inj (hb'.symm.trans hb0')
  subst hbb hb'b
  unfold UFArr UF.compress
  rw [hbuf0, map_toNat_set]

/-- A compression to a reachable node creates no new partition pair: every pair
`Same` after the checked write was already `Same` in the represented array. -/
theorem compressC_same_sound {w : World} {a : AllocId} {id : CapId} {n : Nat}
    {h : UFRep w a id n} {x : Nat} {hx : x < n} {u : UInt8} {w' : World}
    (hw : compressC w a id n h x hx u = .ok w')
    {b b' : Backend} (hb : w.heaps a = some b) (hb' : w'.heaps a = some b')
    (hxlen : x < (UFArr b).length) (hreach : UF.Reach (UFArr b) x u.toNat) :
    ∀ {p q : Nat}, UF.Same (UFArr b') p q → UF.Same (UFArr b) p q := by
  have heq : UFArr b' = UF.compress (UFArr b) x u.toNat :=
    compressC_UFArr hw hb hb'
  intro p q hpq
  rw [heq] at hpq
  exact UF.compress_same_sound hxlen hreach hpq

/-- A completed checked chase reaches its result in the represented array. -/
theorem findRootC_reachable {w : World} {a : AllocId} {id : CapId} {n : Nat}
    (h : UFRep w a id n) {b : Backend} (hb : w.heaps a = some b)
    {fuel x : Nat} (hx : x < n) (hstop : UF.StopsAt (UFArr b) fuel x) {r : Nat}
    (hr : findRootC w a id n h fuel x hx = some r) :
    UF.Reach (UFArr b) x r := by
  rw [findRootC_eq_of_stops h hb hx hstop] at hr
  have heq : UF.findRootF (UFArr b) fuel x = r := Option.some.inj hr
  rw [← heq]
  exact UF.findRootF_reachable (UFArr b) fuel x

/-- A represented compression write is never refused: the guard is the
representation's own and the world invariant supplies the backend bounds. -/
theorem compressC_ok {w : World} {a : AllocId} {id : CapId} {n : Nat}
    (h : UFRep w a id n) (hwf : w.WellFormed) {x : Nat} (hx : x < n) (u : UInt8) :
    ∃ w', compressC w a id n h x hx u = .ok w' := by
  simpa [compressC] using World.write_succeeds (h.canWrite hx) rfl hwf

/-- A represented compression preserves the world invariant. -/
theorem compressC_wf {w w' : World} {a : AllocId} {id : CapId} {n : Nat}
    {h : UFRep w a id n} {x : Nat} {hx : x < n} {u : UInt8}
    (hw : compressC w a id n h x hx u = .ok w') (hwf : w.WellFormed) :
    w'.WellFormed := by
  simpa [compressC] using World.writeChecked_wf hw hwf

end Cap
