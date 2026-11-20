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

/-! ### The no-split direction for compression to a root

The one-step soundness theorem says compression creates no new `Same` pair. The
converse needs the orbit to be linear: if a node reaches two nodes, one of them
reaches the other. Compression to a root preserves every `Same` pair, because
each node of the component still reaches that root. -/

/-- Orbits are linear: two nodes reached from one node are comparable by
reachability. -/
theorem reach_or_reach_of_common {p : UF.Arr} {a b c : Nat}
    (hab : UF.Reach p a b) (hac : UF.Reach p a c) :
    UF.Reach p b c ∨ UF.Reach p c b := by
  obtain ⟨m, hm⟩ := UF.reach_iff_iterate.mp hab
  obtain ⟨n, hn⟩ := UF.reach_iff_iterate.mp hac
  rcases Nat.le_total m n with hle | hle
  · left
    refine UF.reach_iff_iterate.mpr ⟨n - m, ?_⟩
    calc UF.iter p (n - m) b
        = UF.iter p (n - m) (UF.iter p m a) := by rw [hm]
      _ = UF.iter p (n - m + m) a := by rw [UF.iter_add]
      _ = UF.iter p n a := by rw [Nat.sub_add_cancel hle]
      _ = c := hn
  · right
    refine UF.reach_iff_iterate.mpr ⟨m - n, ?_⟩
    calc UF.iter p (m - n) c
        = UF.iter p (m - n) (UF.iter p n a) := by rw [hn]
      _ = UF.iter p (m - n + n) a := by rw [UF.iter_add]
      _ = UF.iter p m a := by rw [Nat.sub_add_cancel hle]
      _ = b := hm

/-- A root reaches only itself. -/
theorem root_reach_eq {p : UF.Arr} {r c : Nat} (hr : UF.IsRoot p r)
    (h : UF.Reach p r c) : c = r := by
  rcases h with rfl | hreach
  · rfl
  · obtain ⟨k, _, hk⟩ := UF.reachable_iff_iterate.mp hreach
    have hiter : ∀ k, UF.iter p k r = r := by
      intro k
      induction k with
      | zero => rfl
      | succ k ih =>
        show UF.step p (UF.iter p k r) = r
        rw [ih]
        exact hr
    rw [← hk, hiter k]

/-- Iterating from a node through a compression to `r` either follows the
original orbit or has already reached `r`. -/
theorem iter_compress_root {p : UF.Arr} {x r : Nat} (hx : x < p.length)
    (hr : UF.IsRoot p r) :
    ∀ k a, UF.iter (UF.compress p x r) k a = UF.iter p k a ∨
      UF.iter (UF.compress p x r) k a = r := by
  intro k
  induction k with
  | zero =>
    intro a
    exact Or.inl rfl
  | succ k ih =>
    intro a
    rcases ih a with hstep | hstep
    · -- the compressed iterate is the original one; take one more step
      by_cases hxk : UF.iter p k a = x
      · right
        show UF.step (UF.compress p x r) (UF.iter (UF.compress p x r) k a) = r
        rw [hstep, hxk]
        exact UF.compress_step_self hx
      · left
        show UF.step (UF.compress p x r) (UF.iter (UF.compress p x r) k a) = UF.step p (UF.iter p k a)
        rw [hstep]
        exact UF.compress_step_of_ne hxk
    · right
      change UF.step (UF.compress p x r) (UF.iter (UF.compress p x r) k a) = r
      rw [hstep]
      by_cases hrx : r = x
      · subst hrx
        exact UF.compress_step_self hx
      · rw [UF.compress_step_of_ne hrx]
        exact hr

/-- Compression to a root preserves reachability of that root. -/
theorem reach_root_compress {p : UF.Arr} {x r a : Nat} (hx : x < p.length)
    (hr : UF.IsRoot p r) (ha : UF.Reach p a r) :
    UF.Reach (UF.compress p x r) a r := by
  obtain ⟨k, hk⟩ := UF.reach_iff_iterate.mp ha
  refine UF.reach_iff_iterate.mpr ⟨k, ?_⟩
  rcases iter_compress_root hx hr k a with h | h
  · rw [h, hk]
  · exact h

/-- Compression to a root preserves `Same` in both directions. -/
theorem compress_same_iff_of_root {p : UF.Arr} {x r : Nat} (hx : x < p.length)
    (hr : UF.IsRoot p r) (hxr : UF.Reach p x r) {a b : Nat} :
    UF.Same (UF.compress p x r) a b ↔ UF.Same p a b := by
  constructor
  · exact UF.compress_same_sound hx hxr
  · rintro ⟨c, hac, hbc⟩
    by_cases hbar : UF.Reach p a x
    · have har : UF.Reach p a r := UF.reach_trans hbar hxr
      have hcr : UF.Reach p c r := by
        rcases reach_or_reach_of_common hac har with h | h
        · exact h
        · have : c = r := root_reach_eq hr h
          rw [this]
          exact Or.inl rfl
      have hbr : UF.Reach p b r := UF.reach_trans hbc hcr
      exact ⟨r, reach_root_compress hx hr har, reach_root_compress hx hr hbr⟩
    · by_cases hbbr : UF.Reach p b x
      · have hbr : UF.Reach p b r := UF.reach_trans hbbr hxr
        have hcr : UF.Reach p c r := by
          rcases reach_or_reach_of_common hbc hbr with h | h
          · exact h
          · have : c = r := root_reach_eq hr h
            rw [this]
            exact Or.inl rfl
        have har : UF.Reach p a r := UF.reach_trans hac hcr
        exact ⟨r, reach_root_compress hx hr har, reach_root_compress hx hr hbr⟩
      · exact UF.compress_preserves_same ⟨c, hac, hbc⟩ hbar hbbr

/-- Compress every listed node to `r`, in the given order. -/
def UF.compressAll (p : UF.Arr) (r : Nat) : List Nat → UF.Arr
  | [] => p
  | x :: xs => UF.compressAll (UF.compress p x r) r xs

/-- Compression to a root leaves that root a root. -/
theorem isRoot_compress {p : UF.Arr} {x r : Nat} (hx : x < p.length)
    (hr : UF.IsRoot p r) : UF.IsRoot (UF.compress p x r) r := by
  by_cases hrx : r = x
  · subst hrx
    exact UF.compress_step_self hx
  · show UF.step (UF.compress p x r) r = r
    rw [UF.compress_step_of_ne hrx]
    exact hr

/-- Full path compression preserves the partition: compressing a list of
in-range nodes, each of which reaches the root `r`, preserves `Same` in both
directions. -/
theorem compressAll_same_iff {p : UF.Arr} {r : Nat} (hr : UF.IsRoot p r)
    {ys : List Nat} {a b : Nat}
    (hys : ∀ y ∈ ys, y < p.length ∧ UF.Reach p y r) :
    UF.Same (UF.compressAll p r ys) a b ↔ UF.Same p a b := by
  induction ys generalizing p with
  | nil => exact Iff.rfl
  | cons x xs ih =>
    obtain ⟨hxlen, hxreach⟩ := hys x (List.mem_cons_self ..)
    have htail : ∀ y ∈ xs, y < (UF.compress p x r).length ∧
        UF.Reach (UF.compress p x r) y r := by
      intro y hy
      obtain ⟨hylen, hyreach⟩ := hys y (List.mem_cons_of_mem x hy)
      exact ⟨by rwa [UF.compress, List.length_set], reach_root_compress hxlen hr hyreach⟩
    have hroot : UF.IsRoot (UF.compress p x r) r := isRoot_compress hxlen hr
    have hstep : UF.Same (UF.compress p x r) a b ↔ UF.Same p a b :=
      compress_same_iff_of_root hxlen hr hxreach
    exact (ih hroot htail).trans hstep

/-- Full compression of the concrete path 3 → 2 → 1 to the root 0 lands on the
constant array. -/
example : UF.compressAll UF.uf3 0 [3, 2, 1] = [0, 0, 0, 0] := by decide

/-! ### Completion under a ranked forest

A represented parent map may contain cycles, so fuel alone bounds the chase.
A rank that strictly decreases at every non-root step is the forest invariant
under which the chase stops at a root within `rank x + 1` steps. -/

/-- The ranked-forest invariant: every in-range step stays in range, and every
non-root node steps to a strictly smaller rank. -/
def Ranked (p : UF.Arr) (n : Nat) (rank : Nat → Nat) : Prop :=
  (∀ i, i < n → UF.step p i < n) ∧
    ∀ i, i < n → UF.IsRoot p i ∨ rank (UF.step p i) < rank i

/-- More fuel cannot lose a stop. -/
theorem stopsAt_mono {p : UF.Arr} : ∀ {fuel x : Nat}, UF.StopsAt p fuel x →
    ∀ k, UF.StopsAt p (fuel + k) x
  | 0, x, h => by cases h
  | fuel + 1, x, h => by
    intro k
    rcases (UF.stopsAt_succ (p := p) (fuel := fuel) (x := x)).mp h with root | ⟨nr, tail⟩
    · have heq : fuel + 1 + k = fuel + k + 1 := by omega
      rw [heq, UF.stopsAt_succ]
      exact Or.inl root
    · have heq : fuel + 1 + k = fuel + k + 1 := by omega
      rw [heq, UF.stopsAt_succ]
      exact Or.inr ⟨nr, stopsAt_mono tail k⟩

/-- A ranked forest's chase stops within the rank: every node reaches a fixed
point in at most `rank x` parent steps. -/
theorem stopsAt_of_ranked {p : UF.Arr} {n : Nat} {rank : Nat → Nat}
    (hr : Ranked p n rank) :
    ∀ m i, i < n → rank i < m → UF.StopsAt p (rank i + 1) i := by
  intro m
  induction m with
  | zero => intro i hi hlt; omega
  | succ m ih =>
    intro i hi hlt
    rw [UF.stopsAt_succ]
    by_cases hroot : UF.IsRoot p i
    · exact Or.inl hroot
    · refine Or.inr ⟨hroot, ?_⟩
      have hdec : rank (UF.step p i) < rank i :=
        (hr.2 i hi).resolve_left hroot
      have hstepn : UF.step p i < n := hr.1 i hi
      have htail := ih (UF.step p i) hstepn (by omega)
      have harith : rank (UF.step p i) + 1 +
          (rank i - (rank (UF.step p i) + 1)) = rank i := by omega
      have := stopsAt_mono htail (rank i - (rank (UF.step p i) + 1))
      rwa [harith] at this

/-- A represented, ranked parent map's chase completes: with `rank x + 1` fuel it
returns a root of the represented forest. -/
theorem findRootC_ranked_root {w : World} {a : AllocId} {id : CapId} {n : Nat}
    (h : UFRep w a id n) {b : Backend} (hb : w.heaps a = some b)
    {rank : Nat → Nat} (hrank : Ranked (UFArr b) n rank)
    {x : Nat} (hx : x < n) :
    ∃ r, findRootC w a id n h (rank x + 1) x hx = some r ∧ UF.IsRoot (UFArr b) r := by
  have hstop := stopsAt_of_ranked hrank (rank x + 1) x hx (by omega)
  refine ⟨UF.findRootF (UFArr b) (rank x + 1) x,
    findRootC_eq_of_stops h hb hx hstop, UF.findRootF_root hstop⟩

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

/-- A compression write at a represented index, with a value in range, preserves
the representation predicate. -/
theorem UFRep.compress_preserves {w w' : World} {a : AllocId} {id : CapId} {n : Nat}
    (h : UFRep w a id n) {x : Nat} (hx : x < n) {u : UInt8} (hu : u.toNat < n)
    (hw : compressC w a id n h x hx u = .ok w') :
    UFRep w' a id n := by
  obtain ⟨o, c, b, hfind, hc, hact, hq, hceil, hlo, hhi, hb, hlen, hdata⟩ := h
  unfold compressC at hw
  obtain ⟨o', b0, b', hfind', hwrit, hb0, hwrite, hctx, hheaps⟩ :=
    World.writeChecked_sound hw
  have hb0b : b = b0 := Option.some.inj (hb.symm.trans hb0)
  rw [← hb0b] at hwrite
  have hb' : b'.buf = b.buf.set x u := Backend.write_buf hwrite
  refine ⟨o, c, b', ?_, hc, hact, ?_, hceil, hlo, hhi, ?_, ?_, ?_⟩
  · rw [hctx]
    exact hfind
  · rw [hctx]
    exact hq
  · rw [hheaps]
    simp [hb]
  · rw [hb', List.length_set, hlen]
  · intro i hi
    rw [hb', List.getElem?_set]
    by_cases hix : x = i
    · rw [if_pos hix]
      rw [if_pos (by omega)]
      exact ⟨u, rfl, hu⟩
    · rw [if_neg hix]
      exact hdata i hi

/-- The checked one-step compression to a root preserves `Same` in both
directions. -/
theorem compressC_same_iff {w w' : World} {a : AllocId} {id : CapId} {n : Nat}
    {h : UFRep w a id n} {x : Nat} {hx : x < n} {u : UInt8} {w' : World}
    (hw : compressC w a id n h x hx u = .ok w')
    {b b' : Backend} (hb : w.heaps a = some b) (hb' : w'.heaps a = some b')
    (hxlen : x < (UFArr b).length) (hreach : UF.Reach (UFArr b) x u.toNat)
    (hroot : UF.IsRoot (UFArr b) u.toNat) :
    ∀ {p q : Nat}, UF.Same (UFArr b') p q ↔ UF.Same (UFArr b) p q := by
  have heq : UFArr b' = UF.compress (UFArr b) x u.toNat :=
    compressC_UFArr hw hb hb'
  intro p q
  rw [heq]
  exact compress_same_iff_of_root hxlen hroot hreach

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
