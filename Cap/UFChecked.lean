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

/-- One-step compression through the checked write: `parent[x] := r`, with the
write guard derived from the representation predicate at the runtime index. -/
def compressC (w : World) (a : AllocId) (id : CapId) (n : Nat)
    (_h : UFRep w a id n) (x : Nat) (_hx : x < n) (u : UInt8) : Except String World :=
  w.writeChecked a id x u

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
