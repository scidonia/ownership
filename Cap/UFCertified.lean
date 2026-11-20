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
import Cap.UFChecked

namespace Cap

/-- A total computation with a permission precondition and a result relation on
the starting world, the value and the final world. -/
abbrev Cert (pre : World → Prop) (α : Type) (post : World → α → World → Prop) :
    Type :=
  ∀ w, pre w → { p : α × World // post w p.1 p.2 }

/-- Read one parent entry through the representation predicate. -/
noncomputable def readParentCert (a : AllocId) (id : CapId) (n x : Nat) (hx : x < n) :
    Cert (fun w => UFRep w a id n ∧ w.WellFormed) Nat
      (fun w0 v w' => w' = w0 ∧ v < n ∧ v < 256 ∧ UFRep w0 a id n ∧
        w0.WellFormed ∧ ∃ b, w0.heaps a = some b ∧ v = UF.step (UFArr b) x) :=
  fun w h => by
    let hrep := h.1
    let hsome := hrep.readParent?_some hx
    let v := Classical.choose hsome
    have hv : readParent? w a id x (hrep.canRead hx) = some v :=
      Classical.choose_spec hsome
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
noncomputable def compressCert (a : AllocId) (id : CapId) (n x r : Nat)
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
    let hok := compressC_ok h.1 h.2 hx u
    let w' := Classical.choose hok
    have hw' : compressC w a id n h.1 x hx u = .ok w' := Classical.choose_spec hok
    have hpost : UFRep w' a id n ∧ w'.WellFormed ∧
        ∃ b b', w.heaps a = some b ∧ w'.heaps a = some b' ∧
          b'.buf = b.buf.set x r.toUInt8 := by
      obtain ⟨b0, b', hb0, hb', hbuf⟩ := compressC_backend hw'
      exact ⟨UFRep.compress_preserves h.1 hx hu hw', compressC_wf hw' h.2,
        b0, b', hb0, hb', hbuf⟩
    exact ⟨((), w'), hpost⟩

/-- The identity computation meets its specification on any world. -/
example : Cert (fun _ => True) Nat (fun w a w' => a = 5 ∧ w' = w) :=
  Cert.pure 5

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
noncomputable def findCompressCert (a : AllocId) (id : CapId) (n : Nat) (rank : Nat → Nat)
    (x : Nat) (hx : x < n) (hn : n ≤ 256) :
    Cert (fun w => UFRep w a id n ∧ w.WellFormed ∧
        ∃ b, w.heaps a = some b ∧ Ranked (UFArr b) n rank) Nat
      (fun w0 v w' => ∃ b b', w0.heaps a = some b ∧ w'.heaps a = some b' ∧
        UFRep w' a id n ∧ w'.WellFormed ∧ UF.IsRoot (UFArr b) v ∧
        b'.buf = b.buf.set x v.toUInt8 ∧
        (∀ p q, UF.Same (UFArr b') p q ↔ UF.Same (UFArr b) p q)) :=
  fun w hpre => by
    let hrep := hpre.1
    let hwf := hpre.2.1
    let hbRank : ∃ b, w.heaps a = some b ∧ Ranked (UFArr b) n rank := hpre.2.2
    let b := Classical.choose hbRank
    have hbR : w.heaps a = some b ∧ Ranked (UFArr b) n rank :=
      Classical.choose_spec hbRank
    let hroot := findRootC_ranked_root hrep hbR.1 hbR.2 hx
    let r := Classical.choose hroot
    have hr := (Classical.choose_spec hroot).1
    have hrootp := (Classical.choose_spec hroot).2
    have hrlt : r < n := by
      have hstop := stopsAt_of_ranked hbR.2 (rank x + 1) x hx (by omega)
      exact Ranked.reach_lt hbR.2 hx (findRootC_reachable hrep hbR.1 hx hstop hr)
    have hr256 : r < 256 := by omega
    let u : UInt8 := r.toUInt8
    have huEq : u.toNat = r := by
      show r.toUInt8.toNat = r
      have hmod : r.toUInt8.toNat = r % 256 := by simp
      omega
    have hu : u.toNat < n := by omega
    let hok := compressC_ok hrep hwf hx u
    let w' := Classical.choose hok
    have hw' : compressC w a id n hrep x hx u = .ok w' := Classical.choose_spec hok
    have hpost : ∃ b b', w.heaps a = some b ∧ w'.heaps a = some b' ∧
        UFRep w' a id n ∧ w'.WellFormed ∧ UF.IsRoot (UFArr b) r ∧
        b'.buf = b.buf.set x r.toUInt8 ∧
        (∀ p q, UF.Same (UFArr b') p q ↔ UF.Same (UFArr b) p q) := by
      obtain ⟨b0, b', hb0, hb', hbuf⟩ := compressC_backend hw'
      have hb0b : b = b0 := Option.some.inj (hbR.1.symm.trans hb0)
      rw [← hb0b] at hbuf
      have hreach : UF.Reach (UFArr b) x r := by
        have hstop := stopsAt_of_ranked hbR.2 (rank x + 1) x hx (by omega)
        exact findRootC_reachable hrep hbR.1 hx hstop hr
      have hxlen : x < (UFArr b).length := by
        unfold UFArr
        rw [List.length_map]
        obtain ⟨-, -, b0', -, -, -, -, -, -, -, hb0', hlen, -⟩ := hrep
        have hbb : b = b0' := by
          have h1 := hbR.1
          rw [hb0'] at h1
          exact (Option.some.inj h1).symm
        rw [hbb, hlen]
        exact hx
      have hiff : ∀ p q, UF.Same (UFArr b') p q ↔ UF.Same (UFArr b) p q := by
        have hroot' : UF.IsRoot (UFArr b) u.toNat := by simpa [huEq] using hrootp
        have hreach' : UF.Reach (UFArr b) x u.toNat := by simpa [huEq] using hreach
        intro p q
        exact compressC_same_iff (w' := w') (p := p) (q := q) hw' hbR.1 hb' hxlen hreach' hroot'
      exact ⟨b, b', hbR.1, hb', UFRep.compress_preserves hrep hx hu hw',
        compressC_wf hw' hwf, hrootp, hbuf, hiff⟩
    exact ⟨(r, w'), hpost⟩

end Cap
