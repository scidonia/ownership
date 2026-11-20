/-
A union-find client of the checked world execution.

Reads are observations: the world's backends are pure data, so finding a root is
a lookup, not a ledger operation. The ownership discipline constrains writes, and
`union` issues them through the checked route (`World.writeChecked`), so every
union preserves the world invariant (`union_wf`). The concrete trace attaches 1
under 0, 3 under 2, then 2 under 0; the final backend parent array is the
functional model's `uf3 = [0,0,0,2]`, and every pair of the four nodes is `Same`
in the functional relation (`ufTrace_partition`).

Scope: one fixed four-node allocation, no path compression in the client (the
compression facts live in `Cap/UFCompress.lean`), and reads-as-observations: the
checked route does not (yet) govern reads.
-/
import Cap.Unified
import Cap.UFPartition

namespace Cap

/-- The union-find backend: parent in `[0,4)`, rank in `[4,8)`, initially the
identity with zero ranks. -/
def ufBackend : Backend :=
  { buf := [0, 1, 2, 3, 0, 0, 0, 0], len := 8, hlen := rfl }

/-- The union-find world: one owner over the 8-byte allocation, root capability
`⟨1⟩`, disposal `⟨2⟩`. -/
def ufWorld : World :=
  { ctx := { owners := [Owner.init ⟨0⟩ 8 64 (by decide) ⟨1⟩ ⟨2⟩], D := 64, nextAlloc := 1,
               issued := [⟨2⟩, ⟨1⟩], loans := .rootOnly },
    heaps := fun a => if a = ⟨0⟩ then some ufBackend else none,
}

/-- The union-find world is well formed. -/
theorem ufWorld_wf : ufWorld.WellFormed := by
  refine ⟨?_, ?_, ?_⟩
  · refine ⟨?_, ?_, ?_⟩
    · refine ⟨?_, ?_⟩
      · intro o ho
        simp [ufWorld] at ho
        rcases ho with rfl
        exact Owner.init_covered ⟨0⟩ 8 64 (by decide) ⟨1⟩ ⟨2⟩
      · simp [ufWorld]
    · intro o ho
      simp [ufWorld] at ho
      rcases ho with rfl
      exact Owner.init_wellFormed ⟨0⟩ 8 64 (by decide) ⟨1⟩ ⟨2⟩
    · decide
  · exact Ctx.functional_of_nodup (by simp [ufWorld])
  · intro a o hfind
    unfold ufWorld at hfind
    simp [Ctx.findOwner?, Owner.init] at hfind
    have ho : o = Owner.init ⟨0⟩ 8 64 (by decide) ⟨1⟩ ⟨2⟩ := hfind.2.symm
    have ha : a = ⟨0⟩ := by
      have h := hfind.1
      exact h.symm
    subst ha
    subst o
    exact ⟨ufBackend, rfl, rfl⟩

/-- Read parent byte `i` of the union-find backend, as a natural number. Reads
are observations of the pure world, not ledger operations. -/
def readParent (w : World) (i : Nat) : Option Nat :=
  (w.heaps ⟨0⟩).bind fun b => (b.read i).map UInt8.toNat

/-- Chase parents with fuel: the root of `i`, or none if the chase runs out of
fuel or leaves the allocation. -/
def find (w : World) : Nat → Nat → Option Nat
  | 0, _ => none
  | fuel + 1, i =>
    match readParent w i with
    | none => none
    | some p => if p = i then some i else find w fuel p

/-- One union step through the checked route: find both roots and, when they
differ, write `parent[ri] := rj` through `World.writeChecked`. -/
def union (w : World) (i j : Nat) : Except String World :=
  match find w 8 i, find w 8 j with
  | some ri, some rj =>
    if ri = rj then .ok w
    else w.writeChecked ⟨0⟩ ⟨1⟩ ri rj.toUInt8
  | _, _ => .error "union: find failed"

/-- A successful union preserves the world invariant: the no-op case returns the
input, and the write case is `writeChecked_wf`. -/
theorem union_wf {w w' : World} {i j : Nat}
    (h : union w i j = .ok w') (hwf : w.WellFormed) : w'.WellFormed := by
  unfold union at h
  split at h
  · rename_i ri rj _ _
    by_cases heq : ri = rj
    · simp [heq] at h
      cases h
      exact hwf
    · simp [heq] at h
      exact World.writeChecked_wf h hwf
  · simp at h

/-- The concrete trace: attach 1 under 0, 3 under 2, then 2 under 0. -/
def ufTrace (w : World) : Except String World := do
  let w ← union w 1 0
  let w ← union w 3 2
  union w 2 0

/-- The trace is accepted. -/
theorem ufTrace_ok : (ufTrace ufWorld).isOk = true := by
  decide

/-- The trace's final world is well formed. -/
theorem ufTrace_wf : ∃ w, ufTrace ufWorld = .ok w ∧ w.WellFormed := by
  have hok : (ufTrace ufWorld).isOk = true := ufTrace_ok
  cases h : ufTrace ufWorld with
  | error e =>
    rw [h] at hok
    cases hok
  | ok w =>
    refine ⟨w, rfl, ?_⟩
    unfold ufTrace at h
    simp only [bind, Except.bind] at h
    split at h
    · simp at h
    · rename_i w1 h1
      split at h
      · simp at h
      · rename_i w2 h2
        exact union_wf h (union_wf h2 (union_wf h1 ufWorld_wf))

/-- The final backend parent array is the functional model's `uf3`. -/
theorem ufTrace_backend :
    (ufTrace ufWorld).toOption.map (fun w => (w.heaps ⟨0⟩).map (fun b => (b.buf.take 4).map UInt8.toNat))
      = some (some [0, 0, 0, 2]) := by
  decide

/-- The final partition: every pair of the four nodes is `Same` in the functional
relation, and the checked-world trace lands on that exact parent array. -/
theorem ufTrace_partition :
    (∃ w', ufTrace ufWorld = .ok w' ∧ w'.WellFormed ∧
      (w'.heaps ⟨0⟩).map (fun b => (b.buf.take 4).map UInt8.toNat) = some [0, 0, 0, 2]) ∧
    ∀ x y, x < 4 → y < 4 → UF.Same [0, 0, 0, 2] x y := by
  refine ⟨?_, fun x y hx hy => UF.uf3_same_all x y hx hy⟩
  obtain ⟨w, h, hwf⟩ := ufTrace_wf
  refine ⟨w, h, hwf, ?_⟩
  have hbe := ufTrace_backend
  rw [h] at hbe
  exact Option.some.inj hbe

end Cap
