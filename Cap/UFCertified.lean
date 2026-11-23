/-
A certified algorithm-facing interface for union-find.

`Cert pre α post` is a total computation that, from any world satisfying `pre`,
returns a value and a world satisfying `post`. It is the permission-bearing core
the review asks for, specialised here to the operations union-find needs:

* `readParentCert` reads a parent through the representation predicate and
  returns the value together with its range proof and its identity in the
  functional model;
* `compressCert` writes a parent through the checked write and preserves the
  representation predicate and the world invariant;
* `findCompressCert` runs the chase and compresses the queried node to the root it
  reached, returning the root, preserving the representation, and creating no new
  partition pair.

The byte backend bounds the node domain: `findCompressCert` requires `n ≤ 256`
(the review's domain obligation). `Cert.pure` and `Cert.bind` give sequential
composition when the continuation's precondition is implied by the first
computation's postcondition; a continuation whose *construction* needs a runtime
fact (for example a compression whose proof argument is the value just read)
needs a dependently indexed computation type, which this layer does not yet
provide. Deriving the compression path from the chase and executing the
algorithm inside the sealed lifecycle remain outside this module.
-/
import Cap.FullInv
import Cap.UFChecked
import Cap.UFForest

namespace Cap

/-- A total computation with a permission precondition and a result relation on
the starting world, the value and the final world. -/
abbrev Cert (pre : World → Prop) (α : Type) (post : World → α → World → Prop) :
    Type :=
  ∀ w, pre w → { p : α × World // post w p.1 p.2 }

/-- Read one parent entry through the representation predicate. -/
def readParentCert (a : AllocId) (id : CapId) (n x : Nat) (hx : x < n) :
    Cert (fun w => UFRep w a id n ∧ w.WellFormed) Nat
      (fun w0 v w' => w' = w0 ∧ v < n ∧ v < 256 ∧ UFRep w0 a id n ∧
        w0.WellFormed ∧ ∃ b, w0.heaps a = some b ∧ v = UF.step (UFArr b) x) :=
  fun w h => by
    let hrep := h.1
    have hsome := hrep.readParent?_some hx
    match hv : readParent? w a id x (hrep.canRead hx) with
    | none =>
      exact False.elim (by
        obtain ⟨v, hv'⟩ := hsome
        rw [hv] at hv'
        nomatch hv')
    | some v =>
      have hlt : v < n := hrep.readParent?_lt hx hv
      have hbyte : v < 256 := hrep.readParent?_byte_lt hx hv
      have hex : ∃ b, w.heaps a = some b ∧ v = UF.step (UFArr b) x := by
        have hrep' := hrep
        obtain ⟨-, -, b, -, -, -, -, -, -, -, hb, -, -⟩ := hrep'
        refine ⟨b, hb, ?_⟩
        rw [UFRep.readParent?_step hrep hb hx] at hv
        exact (Option.some.inj hv).symm
      exact ⟨(v, w), rfl, hlt, hbyte, hrep, h.2, hex⟩

/-- The identity computation. -/
def Cert.pure (a : α) : Cert (fun _ => True) α
    (fun w a' w' => a' = a ∧ w' = w) :=
  fun w _ => ⟨(a, w), rfl, rfl⟩

/-- Sequential composition: run `p`, then continue with `k` on its value,
provided the continuation's precondition is implied by `p`'s postcondition. -/
def Cert.bind {pre : World → Prop} {α : Type} {mid : World → α → World → Prop}
    {pre2 : α → World → Prop} {β : Type} {post : World → β → World → Prop}
    (p : Cert pre α mid) (k : ∀ a, Cert (pre2 a) β post)
    (h : ∀ w a w', mid w a w' → pre2 a w') :
    Cert pre β (fun w b w' => ∃ a w1, mid w a w1 ∧ post w1 b w') :=
  fun w hw => by
    let r1 := p w hw
    let w1 := r1.1.2
    let r2 := k r1.1.1 w1 (h w r1.1.1 w1 r1.property)
    refine ⟨(r2.1.1, r2.1.2), ?_⟩
    exact ⟨r1.1.1, w1, r1.property, r2.property⟩

/-- Compress a represented node to a represented target byte, preserving the
representation predicate and the world invariant. -/
def compressCert (a : AllocId) (id : CapId) (n x r : Nat)
    (hx : x < n) (hr : r < n) (hr256 : r < 256) :
    Cert (fun w => UFRep w a id n ∧ w.WellFormed) Unit
      (fun w0 _ w' => UFRep w' a id n ∧ w'.WellFormed ∧
        ∃ b b', w0.heaps a = some b ∧ w'.heaps a = some b' ∧
          b'.buf = b.buf.set x r.toUInt8) :=
  fun w h => by
    let u : UInt8 := r.toUInt8
    have huEq : u.toNat = r := by
      show r.toUInt8.toNat = r
      have hmod : r.toUInt8.toNat = r % 256 := by simp
      omega
    have hu : u.toNat < n := by omega
    match hw : compressC w a id n h.1 x hx u with
    | .error e =>
      exact False.elim (by
        obtain ⟨w', hok⟩ := compressC_ok h.1 h.2 hx u
        rw [hw] at hok
        nomatch hok)
    | .ok w' =>
      have hpost : UFRep w' a id n ∧ w'.WellFormed ∧
          ∃ b b', w.heaps a = some b ∧ w'.heaps a = some b' ∧
            b'.buf = b.buf.set x r.toUInt8 := by
        obtain ⟨b0, b', hb0, hb', hbuf⟩ := compressC_backend hw
        exact ⟨UFRep.compress_preserves h.1 hx hu hw, compressC_wf hw h.2,
          b0, b', hb0, hb', hbuf⟩
      exact ⟨((), w'), hpost⟩

/-- The identity computation meets its specification on any world. -/
example : Cert (fun _ => True) Nat (fun w a w' => a = 5 ∧ w' = w) :=
  Cert.pure 5

/-- Weaken a computation's precondition. -/
def Cert.weaken {pre pre' : World → Prop} {α : Type}
    {post : World → α → World → Prop} (p : Cert pre α post)
    (h : ∀ w, pre' w → pre w) : Cert pre' α post :=
  fun w hw => p w (h w hw)

/-- Parallel composition? No: a dependent bind. The continuation is built with
the first computation's value *and its postcondition*, and runs at the
intermediate world (`pre = (· = w1)`). This is what a continuation that needs a
runtime fact at construction (compressing to the value just read) requires. -/
def Cert.bindDep {pre : World → Prop} {α : Type} {mid : World → α → World → Prop}
    {β : Type} (post : α → World → β → World → Prop)
    (p : Cert pre α mid)
    (k : (a : α) → (w0 w1 : World) → mid w0 a w1 →
      Cert (fun w => w = w1) β (post a)) :
    Cert pre β (fun w b w' => ∃ a w1, mid w a w1 ∧ post a w1 b w') :=
  fun w hw => by
    let r := p w hw
    let r2 := k r.1.1 w r.1.2 r.property r.1.2 rfl
    refine ⟨(r2.1.1, r2.1.2), ?_⟩
    exact ⟨r.1.1, r.1.2, r.property, r2.property⟩

/-- The compression half of read-then-compress, indexed by the value read; the
program returns that value. -/
def readThenCompressInner (a : AllocId) (id : CapId) (n x : Nat)
    (v : Nat) (w1 : World) (b : Nat) (w' : World) : Prop :=
  ∃ w2, (UFRep w2 a id n ∧ w2.WellFormed ∧
      ∃ b0 b1, w1.heaps a = some b0 ∧ w2.heaps a = some b1 ∧
        b1.buf = b0.buf.set x v.toUInt8) ∧ b = v ∧ w' = w2

/-- The whole postcondition of read-then-compress. -/
def readThenCompressPost (a : AllocId) (id : CapId) (n x : Nat)
    (w0 : World) (b : Nat) (w' : World) : Prop :=
  ∃ v w1, (w1 = w0 ∧ v < n ∧ v < 256 ∧ UFRep w0 a id n ∧ w0.WellFormed ∧
      ∃ bb, w0.heaps a = some bb ∧ v = UF.step (UFArr bb) x) ∧
    readThenCompressInner a id n x v w1 b w'

/-- Read a parent and compress the same node to the value read, returning the
value: the dependent composition the plain bind could not express. -/
def readThenCompressCert (a : AllocId) (id : CapId) (n x : Nat)
    (hx : x < n) (hn : n ≤ 256) :
    Cert (fun w => UFRep w a id n ∧ w.WellFormed) Nat
      (readThenCompressPost a id n x) :=
  Cert.bindDep (post := readThenCompressInner a id n x)
    (readParentCert a id n x hx)
    (fun v w0 w1 hmid => by
      obtain ⟨hw1, hvlt, hv256, hrep, hwf, -⟩ := hmid
      have hrep' : UFRep w1 a id n := by rwa [hw1]
      have hwf' : w1.WellFormed := by rwa [hw1]
      refine fun w hw => ?_
      subst hw
      let r := (compressCert a id n x v hx hvlt hv256) w ⟨hrep', hwf'⟩
      refine ⟨(v, r.1.2), ?_⟩
      exact ⟨r.1.2, r.property, rfl, rfl⟩)

/-- Reachability from an in-range node stays in range under the ranked forest
invariant. -/
theorem Ranked.reach_lt {p : UF.Arr} {n : Nat} {rank : Nat → Nat}
    (hr : Ranked p n rank) {x r : Nat} (hx : x < n) (hreach : UF.Reach p x r) :
    r < n := by
  rcases hreach with rfl | h
  · exact hx
  · obtain ⟨k, hk⟩ := UF.reachable_iff_iterate.mp h
    obtain ⟨-, hk⟩ := hk
    have key : ∀ k y, y < n → UF.iter p k y < n := by
      intro k
      induction k with
      | zero =>
        intro y hy
        change y < n
        exact hy
      | succ k ih =>
        intro y hy
        show UF.step p (UF.iter p k y) < n
        exact hr.1 _ (ih y hy)
    rw [← hk]
    exact key k x hx

/-- The certified algorithm: find the root of `x` and compress `x` to it. The
world must represent a ranked forest over a byte-sized domain (`n ≤ 256`). -/
def findCompressCert (a : AllocId) (id : CapId) (n : Nat) (rank : Nat → Nat)
    (x : Nat) (hx : x < n) (hn : n ≤ 256) :
    Cert (fun w => UFRep w a id n ∧ w.WellFormed ∧
        ∃ b, w.heaps a = some b ∧ Ranked (UFArr b) n rank) Nat
      (fun w0 v w' => ∃ b b', w0.heaps a = some b ∧ w'.heaps a = some b' ∧
        UFRep w' a id n ∧ w'.WellFormed ∧ v < n ∧ UF.IsRoot (UFArr b) v ∧
        b'.buf = b.buf.set x v.toUInt8 ∧
        (∀ p q, UF.Same (UFArr b') p q ↔ UF.Same (UFArr b) p q)) :=
  fun w hpre => by
    let hrep := hpre.1
    let hwf := hpre.2.1
    match hb : w.heaps a with
    | none =>
      exact False.elim (by
        obtain ⟨b, hb', _⟩ := hpre.2.2
        rw [hb] at hb'
        nomatch hb')
    | some b =>
      have hrank : Ranked (UFArr b) n rank := by
        obtain ⟨b', hb', hr⟩ := hpre.2.2
        rw [hb] at hb'
        cases hb'
        exact hr
      have hstop : UF.StopsAt (UFArr b) (rank x + 1) x :=
        stopsAt_of_ranked hrank (rank x + 1) x hx (by omega)
      match hr : findRootC w a id n hrep (rank x + 1) x hx with
      | none =>
        exact False.elim (by
          obtain ⟨r, hr', _⟩ := findRootC_ranked_root hrep hb hrank hx
          rw [hr] at hr'
          nomatch hr')
      | some r =>
        have hrootp : UF.IsRoot (UFArr b) r :=
          findRootC_root hrep hb hx hstop hr
        have hrlt : r < n :=
          Ranked.reach_lt hrank hx (findRootC_reachable hrep hb hx hstop hr)
        have hr256 : r < 256 := by omega
        let u : UInt8 := r.toUInt8
        have huEq : u.toNat = r := by
          show r.toUInt8.toNat = r
          have hmod : r.toUInt8.toNat = r % 256 := by simp
          omega
        have hu : u.toNat < n := by omega
        match hw : compressC w a id n hrep x hx u with
        | .error e =>
          exact False.elim (by
            obtain ⟨w', hok⟩ := compressC_ok hrep hwf hx u
            rw [hw] at hok
            nomatch hok)
        | .ok w' =>
          have hpost : ∃ b b', w.heaps a = some b ∧ w'.heaps a = some b' ∧
              UFRep w' a id n ∧ w'.WellFormed ∧ r < n ∧ UF.IsRoot (UFArr b) r ∧
              b'.buf = b.buf.set x r.toUInt8 ∧
              (∀ p q, UF.Same (UFArr b') p q ↔ UF.Same (UFArr b) p q) := by
            obtain ⟨b0, b', hb0, hb', hbuf⟩ := compressC_backend hw
            have hb0b : b = b0 := Option.some.inj (hb.symm.trans hb0)
            rw [← hb0b] at hbuf
            have hreach : UF.Reach (UFArr b) x r :=
              findRootC_reachable hrep hb hx hstop hr
            have hxlen : x < (UFArr b).length := by
              unfold UFArr
              rw [List.length_map]
              obtain ⟨-, -, b0', -, -, -, -, -, -, -, hb0', hlen, -⟩ := hrep
              have hbb : b = b0' := by
                have h1 := hb
                rw [hb0'] at h1
                exact (Option.some.inj h1).symm
              rw [hbb, hlen]
              exact hx
            have hiff : ∀ p q, UF.Same (UFArr b') p q ↔ UF.Same (UFArr b) p q := by
              have hroot' : UF.IsRoot (UFArr b) u.toNat := by simpa [huEq] using hrootp
              have hreach' : UF.Reach (UFArr b) x u.toNat := by simpa [huEq] using hreach
              intro p q
              exact compressC_same_iff (w' := w') (p := p) (q := q) hw hb hb' hxlen hreach' hroot'
            exact ⟨b, b', hb, hb', UFRep.compress_preserves hrep hx hu hw,
              compressC_wf hw hwf, hrlt, hrootp, hbuf, hiff⟩
          exact ⟨(r, w'), hpost⟩

/-! ### The path from the chase

The path compressed by full path compression is read off the orbit: `rootPath`
collects the non-root nodes visited from `x` until the search stops. Every node
on it is in range and reaches the search's result, so `compressAll` over it
preserves the partition. -/

/-- The nodes visited before the search stops: `x`, its parent, and so on while
the node is not a root and fuel remains. -/
def rootPath (p : UF.Arr) : Nat → Nat → List Nat
  | 0, _ => []
  | fuel + 1, x => if UF.step p x = x then [] else x :: rootPath p fuel (UF.step p x)

/-- Every node on the path is reachable from the start. -/
theorem rootPath_mem_reach_from {p : UF.Arr} :
    ∀ {fuel x y : Nat}, y ∈ rootPath p fuel x → UF.Reach p x y
  | 0, x, y, h => by simp [rootPath] at h
  | fuel + 1, x, y, h => by
    rw [rootPath] at h
    by_cases hroot : UF.step p x = x
    · simp [hroot] at h
    · rw [if_neg hroot] at h
      rcases List.mem_cons.mp h with heq | htail
      · rw [heq]
        exact Or.inl rfl
      · exact UF.reach_trans (Or.inr (UF.Reachable.one rfl))
          (rootPath_mem_reach_from htail)

/-- Every node on the path reaches the search's result. -/
theorem rootPath_mem_reach_result {p : UF.Arr} :
    ∀ {fuel x y : Nat}, y ∈ rootPath p fuel x →
      UF.Reach p y (UF.findRootF p fuel x)
  | 0, x, y, h => by simp [rootPath] at h
  | fuel + 1, x, y, h => by
    rw [rootPath] at h
    by_cases hroot : UF.step p x = x
    · simp [hroot] at h
    · rw [if_neg hroot] at h
      rw [UF.findRootF_succ, if_neg hroot]
      rcases List.mem_cons.mp h with heq | htail
      · rw [heq]
        exact UF.reach_trans (Or.inr (UF.Reachable.one rfl))
          (UF.findRootF_reachable p fuel (UF.step p x))
      · exact rootPath_mem_reach_result htail

/-- Full path compression along the chase's own path preserves the partition:
the path is in range and every node on it reaches the root the search stopped
at. -/
theorem rootPath_compress_same_iff {w : World} {a : AllocId} {id : CapId} {n : Nat}
    (hrep : UFRep w a id n) {b : Backend} (hb : w.heaps a = some b)
    {rank : Nat → Nat} (hrank : Ranked (UFArr b) n rank)
    {x : Nat} (hx : x < n)
    (hstop : UF.StopsAt (UFArr b) (rank x + 1) x) {p q : Nat} :
    UF.Same (UF.compressAll (UFArr b) (UF.findRootF (UFArr b) (rank x + 1) x)
        (rootPath (UFArr b) (rank x + 1) x)) p q ↔
      UF.Same (UFArr b) p q := by
  have hroot : UF.IsRoot (UFArr b) (UF.findRootF (UFArr b) (rank x + 1) x) :=
    UF.findRootF_root hstop
  have hlen : (UFArr b).length = n := by
    obtain ⟨-, -, b0, -, -, -, -, -, -, -, hb0, hlen, -⟩ := hrep
    have hbb : b = b0 := Option.some.inj (hb.symm.trans hb0)
    subst hbb
    unfold UFArr
    rw [List.length_map, hlen]
  apply compressAll_same_iff hroot
  intro y hy
  have hxy : UF.Reach (UFArr b) x y := rootPath_mem_reach_from hy
  refine ⟨?_, rootPath_mem_reach_result hy⟩
  have hylt : y < n := Ranked.reach_lt hrank hx hxy
  rwa [hlen]

/-- The buffer after compressing a list of nodes to `r`. -/
def compressBuf (r : Nat) : List UInt8 → List Nat → List UInt8
  | buf, [] => buf
  | buf, x :: xs => compressBuf r (buf.set x r.toUInt8) xs

theorem map_compressBuf {r : Nat} (hr256 : r < 256) :
    ∀ (l : List UInt8) (path : List Nat),
      (compressBuf r l path).map UInt8.toNat =
        UF.compressAll (l.map UInt8.toNat) r path
  | l, [] => rfl
  | l, x :: xs => by
    rw [compressBuf, map_compressBuf hr256 (l.set x r.toUInt8) xs]
    have hu : r.toUInt8.toNat = r := by
      show r % 256 = r
      omega
    rw [map_toNat_set, hu]
    rfl

/-- Compress every node of a path to `r` through the certified write. -/
def compressPathCert (a : AllocId) (id : CapId) (n r : Nat)
    (path : List Nat) (hr : r < n) (hr256 : r < 256)
    (hpath : ∀ x ∈ path, x < n) :
    Cert (fun w => UFRep w a id n ∧ w.WellFormed) Unit
      (fun w0 _ w' => UFRep w' a id n ∧ w'.WellFormed ∧
        ∃ b0 b', w0.heaps a = some b0 ∧ w'.heaps a = some b' ∧
          b'.buf = compressBuf r b0.buf path) :=
  match path with
  | [] => fun w hw => by
    have hpost : UFRep w a id n ∧ w.WellFormed ∧
        ∃ b0 b', w.heaps a = some b0 ∧ w.heaps a = some b' ∧
          b'.buf = compressBuf r b0.buf [] := by
      obtain ⟨-, -, b, -, -, -, -, -, -, -, hb, -, -⟩ := hw.1
      exact ⟨hw.1, hw.2, b, b, hb, hb, rfl⟩
    exact ⟨((), w), hpost⟩
  | x :: xs => fun w hw => by
    let r1 := compressCert a id n x r (hpath x (by simp)) hr hr256 w hw
    have hpre1 : UFRep r1.1.2 a id n ∧ r1.1.2.WellFormed :=
      ⟨r1.property.1, r1.property.2.1⟩
    let r2 := compressPathCert a id n r xs hr hr256
      (fun y hy => hpath y (by simp [hy])) r1.1.2 hpre1
    have hpost : UFRep r2.1.2 a id n ∧ r2.1.2.WellFormed ∧
        ∃ b0 b', w.heaps a = some b0 ∧ r2.1.2.heaps a = some b' ∧
          b'.buf = compressBuf r b0.buf (x :: xs) := by
      obtain ⟨hrep1, hwf1, b0, b1, hb0, hb1, hbuf1⟩ := r1.property
      obtain ⟨hrep2, hwf2, b1', b2, hb1', hb2, hbuf2⟩ := r2.property
      have hb1eq : b1' = b1 := Option.some.inj (hb1'.symm.trans hb1)
      rw [hb1eq] at hbuf2
      refine ⟨hrep2, hwf2, b0, b2, hb0, hb2, ?_⟩
      rw [hbuf2, hbuf1]
      rfl
    exact ⟨((), r2.1.2), hpost⟩

theorem compressPathCert_compressAll {w : World} {a : AllocId} {id : CapId}
    {n r : Nat} {path : List Nat} (hr : r < n) (hr256 : r < 256)
    (hpath : ∀ x ∈ path, x < n) (hw : UFRep w a id n ∧ w.WellFormed) :
    ∃ w', (compressPathCert a id n r path hr hr256 hpath w hw).1.2 = w' ∧
      ∃ b0 b', w.heaps a = some b0 ∧ w'.heaps a = some b' ∧
        UFArr b' = UF.compressAll (UFArr b0) r path := by
  obtain ⟨hwrep, hwwf, b0, b', hb0, hb', hbuf⟩ :=
    (compressPathCert a id n r path hr hr256 hpath w hw).property
  refine ⟨_, rfl, b0, b', hb0, hb', ?_⟩
  show (b'.buf.map UInt8.toNat) = UF.compressAll (b0.buf.map UInt8.toNat) r path
  rw [hbuf]
  exact map_compressBuf hr256 b0.buf path


/-- Execute the full path read off the chase through the certified write:
compressing every node of `rootPath` to the chase's result. -/
def compressRootPathCert (a : AllocId) (id : CapId) (n : Nat)
    (rank : Nat → Nat) (b : Backend) (hrank : Ranked (UFArr b) n rank)
    (x : Nat) (hx : x < n) (hn : n ≤ 256) :
    Cert (fun w => UFRep w a id n ∧ w.WellFormed ∧ w.heaps a = some b) Unit
      (fun w0 _ w' => UFRep w' a id n ∧ w'.WellFormed ∧
        ∃ b0 b', w0.heaps a = some b0 ∧ w'.heaps a = some b' ∧
          b'.buf = compressBuf (UF.findRootF (UFArr b) (rank x + 1) x) b0.buf
            (rootPath (UFArr b) (rank x + 1) x)) := by
  intro w hw
  have hr : UF.findRootF (UFArr b) (rank x + 1) x < n :=
    findRootF_lt hrank.1 hx
  have hr256 : UF.findRootF (UFArr b) (rank x + 1) x < 256 := by omega
  have hpath : ∀ y ∈ rootPath (UFArr b) (rank x + 1) x, y < n := by
    intro y hy
    exact Ranked.reach_lt hrank hx (rootPath_mem_reach_from hy)
  exact compressPathCert a id n (UF.findRootF (UFArr b) (rank x + 1) x)
    (rootPath (UFArr b) (rank x + 1) x) hr hr256 hpath w ⟨hw.1, hw.2.1⟩

/-- The full-path certificate's final array is `compressAll` of its initial
array, so the pure partition theorem applies to the executed writes. -/
theorem compressRootPathCert_compressAll {w : World} {a : AllocId} {id : CapId}
    {n : Nat} {rank : Nat → Nat} {b : Backend} {hrank : Ranked (UFArr b) n rank}
    {x : Nat} (hx : x < n) (hn : n ≤ 256)
    (hw : UFRep w a id n ∧ w.WellFormed ∧ w.heaps a = some b) :
    ∃ w', (compressRootPathCert a id n rank b hrank x hx hn w hw).1.2 = w' ∧
      ∃ b0 b', w.heaps a = some b0 ∧ w'.heaps a = some b' ∧
        UFArr b' = UF.compressAll (UFArr b0)
          (UF.findRootF (UFArr b) (rank x + 1) x)
          (rootPath (UFArr b) (rank x + 1) x) := by
  obtain ⟨hwrep, hwwf, b0, b', hb0, hb', hbuf⟩ :=
    (compressRootPathCert a id n rank b hrank x hx hn w hw).property
  refine ⟨_, rfl, b0, b', hb0, hb', ?_⟩
  show (b'.buf.map UInt8.toNat) = UF.compressAll (b0.buf.map UInt8.toNat)
    (UF.findRootF (UFArr b) (rank x + 1) x) (rootPath (UFArr b) (rank x + 1) x)
  rw [hbuf]
  have hr : UF.findRootF (UFArr b) (rank x + 1) x < n :=
    findRootF_lt hrank.1 hx
  exact map_compressBuf (by omega) b0.buf (rootPath (UFArr b) (rank x + 1) x)

/-- The executed full-path compression preserves the partition in both
directions, by transporting `rootPath_compress_same_iff` along the certificate's
final array. -/
theorem compressRootPathCert_same_iff {w : World} {a : AllocId} {id : CapId}
    {n : Nat} {rank : Nat → Nat} {b : Backend} {hrank : Ranked (UFArr b) n rank}
    {x : Nat} (hx : x < n) (hn : n ≤ 256)
    (hw : UFRep w a id n ∧ w.WellFormed ∧ w.heaps a = some b) :
    ∃ w', (compressRootPathCert a id n rank b hrank x hx hn w hw).1.2 = w' ∧
      ∃ b0 b', w.heaps a = some b0 ∧ w'.heaps a = some b' ∧
        ∀ p q, UF.Same (UFArr b') p q ↔ UF.Same (UFArr b0) p q := by
  obtain ⟨w', hw', b0, b', hb0, hb', hcomp⟩ :=
    compressRootPathCert_compressAll hx hn hw
  refine ⟨w', hw', b0, b', hb0, hb', ?_⟩
  have hb0eq : b0 = b := Option.some.inj (hb0.symm.trans hw.2.2)
  have hstop : UF.StopsAt (UFArr b) (rank x + 1) x :=
    stopsAt_of_ranked hrank (rank x + 1) x hx (by omega)
  intro p q
  rw [hcomp, hb0eq]
  exact rootPath_compress_same_iff hw.1 hw.2.2 hrank hx hstop

/-! ### The concrete 64-byte union-find instance -/

/-- The empty 64-byte backend is a zero parent array. -/
theorem uEmpty_step {i : Nat} (hi : i < 64) :
    UF.step (UFArr (Backend.empty 64)) i = 0 := by
  unfold UF.step UF.parentOf UFArr Backend.empty
  rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_replicate]
  simp [hi]

/-- A rank for the zero parent array: node 0 is the root, every other node
steps to it. -/
def zeroRank (i : Nat) : Nat := if i = 0 then 0 else 1

/-- The 64-byte world's owner tree is a whole-share read-write leaf. -/
theorem uWorld_ufRep : UFRep uWorld ⟨0⟩ ⟨1⟩ 64 := by
  refine ⟨uOwner,
    { id := ⟨1⟩, alloc := ⟨0⟩, lo := 0, hi := 64, ordered := Nat.zero_le 64,
      q := 64, pos := by decide, ceiling := .readWrite, state := .active },
    Backend.empty 64, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [uWorld, uOwner, Owner.init, Ctx.findOwner?]
  · simp [uWorld, uOwner, Owner.init, Tree.find?]
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · simp [uWorld]
  · simp [Backend.empty]
  · intro i hi
    refine ⟨0, ?_, by decide⟩
    rw [Backend.empty, List.getElem?_replicate]
    simp [hi]

/-- The zero parent array is a ranked forest of depth one. -/
theorem uWorld_ranked : Ranked (UFArr (Backend.empty 64)) 64 zeroRank := by
  constructor
  · intro i hi
    rw [uEmpty_step hi]
    omega
  · intro i hi
    by_cases h0 : i = 0
    · left
      show UF.step (UFArr (Backend.empty 64)) i = i
      rw [uEmpty_step hi, h0]
    · right
      show zeroRank (UF.step (UFArr (Backend.empty 64)) i) < zeroRank i
      rw [uEmpty_step hi]
      simp [zeroRank, h0]

/-- Full path compression on the branching example: `[0,0,1,2]` with the path
`3 -> 2 -> 1 -> 0` becomes the constant array. -/
theorem compressAll_example :
    UF.compressAll [0, 0, 1, 2] 0 [3, 2, 1] = [0, 0, 0, 0] := by
  decide

/-- Single-node compression of the same start only rewrites node 3. -/
theorem compressSingle_example :
    UF.compress [0, 0, 1, 2] 3 0 = [0, 0, 1, 0] := by
  decide

/-- The concrete 64-byte zero forest is acyclic. -/
theorem uWorld_acyclic : Acyclic (UFArr (Backend.empty 64)) 64 :=
  acyclic_of_ranked uWorld_ranked

/-- The concrete 64-byte zero forest has a construction history. -/
theorem uWorld_built : Built (UFArr (Backend.empty 64)) 64 (fun i => i) := by
  simpa [UFArr, Backend.empty] using Built.zero 64

/-- The concrete 64-byte zero forest's chase through the acyclicity route: with
`n + 1` fuel at node 3 it returns the root 0. -/
theorem uWorld_findRoot_acyclic :
    ∃ r, findRootC uWorld ⟨0⟩ ⟨1⟩ 64 uWorld_ufRep 65 3 (by decide) = some r ∧
      r = 0 := by
  have hbound : ∀ i, i < 64 → UF.step (UFArr (Backend.empty 64)) i < 64 :=
    uWorld_ranked.1
  obtain ⟨r, hr, hroot⟩ :=
    findRootC_acyclic_root (x := 3) uWorld_ufRep (by simp [uWorld]) hbound
      uWorld_acyclic (by decide)
  refine ⟨r, hr, ?_⟩
  have hstop := stopsAt_of_acyclic hbound uWorld_acyclic 3 (by decide)
  have hlt := findRootC_lt (x := 3) uWorld_ufRep (by simp [uWorld]) hbound
    (by decide) hstop hr
  have hstep : UF.step (UFArr (Backend.empty 64)) r = 0 := uEmpty_step hlt
  unfold UF.IsRoot at hroot
  rw [hstep] at hroot
  omega

/-- A sealed union-find runner: a world with the combined invariant, the parent
representation, its backend and the forest rank, again private. -/
structure UFRunner (a : AllocId) (id : CapId) (n : Nat) (rank : Nat → Nat) where
  private mk ::
  private w : World
  private inv : World.FullInv w
  private rep : UFRep w a id n
  private b : Backend
  private hb : w.heaps a = some b
  private hrank : Ranked (UFArr b) n rank

/-- Run find-and-compress on node `x` inside the runner, returning the root. -/
def UFRunner.findRoot {a : AllocId} {id : CapId} {n : Nat}
    {rank : Nat → Nat} (s : UFRunner a id n rank) (x : Nat)
    (hx : x < n) (hn : n ≤ 256) : Nat :=
  (findCompressCert a id n rank x hx hn s.w
    ⟨s.rep, s.inv.1.1, ⟨s.b, s.hb, s.hrank⟩⟩).1.1

/-- Run find-and-compress and return the root together with a copy of the
allocation's bytes: an immutable observation of the sealed state. -/
def UFRunner.findRootSnapshot {a : AllocId} {id : CapId} {n : Nat}
    {rank : Nat → Nat} (s : UFRunner a id n rank) (x : Nat)
    (hx : x < n) (hn : n ≤ 256) : Nat × List UInt8 :=
  let r := findCompressCert a id n rank x hx hn s.w
    ⟨s.rep, s.inv.1.1, ⟨s.b, s.hb, s.hrank⟩⟩
  (r.1.1, ((r.1.2.heaps a).map (·.buf)).getD [])

/-- The concrete runner over the 64-byte zero forest. -/
def ufRunner : UFRunner ⟨0⟩ ⟨1⟩ 64 zeroRank :=
  UFRunner.mk uWorld ⟨uWorld_top, uWorld_loansOK⟩ uWorld_ufRep
    (Backend.empty 64) rfl uWorld_ranked

/-- A closed certified execution: the runner executes find-and-compress at node 3
of the 64-byte zero forest, and the returned root is 0. -/
theorem ufRunner_findRoot :
    ufRunner.findRoot 3 (by decide) (by decide) = 0 := by
  unfold UFRunner.findRoot ufRunner
  let r := (findCompressCert ⟨0⟩ ⟨1⟩ 64 zeroRank 3 (by decide) (by decide)
    uWorld ⟨uWorld_ufRep, uWorld_wf, ⟨Backend.empty 64, rfl, uWorld_ranked⟩⟩)
  change r.1.1 = 0
  have hp := r.property
  obtain ⟨b, b', hb, hb', hrep', hwf', hvlt, hroot, hbuf, hiff⟩ := hp
  have hbE : b = Backend.empty 64 := by
    have h1 : uWorld.heaps ⟨0⟩ = some (Backend.empty 64) := by simp [uWorld]
    rw [h1] at hb
    exact Option.some.inj hb.symm
  subst hbE
  change UF.step (UFArr (Backend.empty 64)) r.1.1 = r.1.1 at hroot
  rw [uEmpty_step hvlt] at hroot
  exact hroot.symm

/-- The closed execution's immutable observation on the zero forest: root 0 and
the unchanged 64 zero bytes. -/
theorem ufRunner_findRootSnapshot :
    ufRunner.findRootSnapshot 3 (by decide) (by decide) = (0, List.replicate 64 0) := by
  unfold UFRunner.findRootSnapshot ufRunner
  let r := (findCompressCert ⟨0⟩ ⟨1⟩ 64 zeroRank 3 (by decide) (by decide)
    uWorld ⟨uWorld_ufRep, uWorld_wf, ⟨Backend.empty 64, rfl, uWorld_ranked⟩⟩)
  change (r.1.1, ((r.1.2.heaps ⟨0⟩).map (·.buf)).getD []) = (0, List.replicate 64 0)
  have hp := r.property
  obtain ⟨b, b', hb, hb', hrep', hwf', hvlt, hroot, hbuf, hiff⟩ := hp
  have hbE : b = Backend.empty 64 := by
    have h1 : uWorld.heaps ⟨0⟩ = some (Backend.empty 64) := by simp [uWorld]
    rw [h1] at hb
    exact Option.some.inj hb.symm
  subst hbE
  have hroot0 : r.1.1 = 0 := by
    change UF.step (UFArr (Backend.empty 64)) r.1.1 = r.1.1 at hroot
    rw [uEmpty_step hvlt] at hroot
    exact hroot.symm
  rw [hroot0] at hbuf
  have hsnap : ((r.1.2.heaps ⟨0⟩).map (·.buf)).getD [] = b'.buf := by
    rw [hb']
    rfl
  rw [hroot0, hsnap, hbuf]
  simp [Backend.empty]

end Cap
