/-
Union-find under the ledger's write discipline.

The parent and rank arrays are one allocation, covered by a single read--write
leaf of the whole share. Every array write is `UF.writeParent`, which takes the
owner's `Writable` guard as a proof; the algorithm therefore cannot update an index
outside the footprint or through a partial or read-only claim.

This is an example of the discipline, not a verified union-find: the concrete
three-union run is checked by `decide`, the store length is preserved by every
write, and every write in the run carries the guard. Functional correctness of
`find`/`union` against an equivalence-class model is not proved.
-/
import Cap.Ledger

namespace Cap

/-- The parent and rank arrays of one union-find instance, with an owner over both. -/
structure UF where
  owner : Owner
  parent : List Nat
  rank : List Nat
  hlen : parent.length = rank.length
  D : Nat

/-- The allocation and the single whole-share leaf of the example. -/
def ufAlloc : AllocId := ⟨0⟩

def ufRoot : Leaf :=
  { id := ⟨1⟩, alloc := ufAlloc, lo := 0, hi := 4, ordered := by decide,
    q := 4, pos := by decide, ceiling := .readWrite, state := .active }

def ufOwner : Owner :=
  { alloc := ufAlloc, len := 4, root := .leaf ufRoot, disposal := ⟨2⟩ }

theorem ufRoot_find : (Tree.leaf ufRoot).find? ⟨1⟩ = some ufRoot := by
  simp [Tree.find?, ufRoot]

/-- Every in-range index is writable through the whole share. -/
theorem ufOwner_writable (i : Nat) (h : i < 4) : ufOwner.Writable 4 ⟨1⟩ i := by
  refine ⟨ufRoot, ?_, rfl, rfl, rfl, Nat.zero_le i, h⟩
  simpa [ufOwner, Tree.find?] using ufRoot_find

/-- A write through the owner's guard; the store length is preserved. -/
def UF.writeParent (u : UF) (id : CapId) (i v : Nat)
    (_hg : u.owner.Writable u.D id i) : UF :=
  { owner := u.owner, parent := u.parent.set i v, rank := u.rank,
    hlen := by rw [List.length_set]; exact u.hlen, D := u.D }

theorem UF.writeParent_length {u : UF} {id : CapId} {i v : Nat}
    {hg : u.owner.Writable u.D id i} : (u.writeParent id i v hg).parent.length = u.parent.length := by
  simp [UF.writeParent, List.length_set]

/-- A write at an index outside the footprint has no guard. -/
theorem ufOwner_not_writable_4 : ¬ ufOwner.Writable 4 ⟨1⟩ 4 := by
  intro h
  obtain ⟨c, hc, hstate, hq, hceil, hlo, hhi⟩ := h
  have : c = ufRoot := by
    have hfind : (Tree.leaf ufRoot).find? ⟨1⟩ = some c := by simpa [ufOwner] using hc
    rw [ufRoot_find] at hfind
    exact (Option.some.inj hfind).symm
  subst this
  have hhi' : 4 < 4 := by simpa [ufRoot] using hhi
  omega

/-- A root lookup by parent chasing, with fuel. -/
def UF.findFuel (u : UF) : Nat → Nat → Option Nat
  | 0, _ => none
  | fuel + 1, i =>
    match u.parent[i]? with
    | none => none
    | some p => if p = i then some i else u.findFuel fuel p

def UF.findRoot (u : UF) (i : Nat) : Option Nat := u.findFuel (u.parent.length + 1) i

/-- The initial store of four singletons. -/
def uf0 : UF :=
  { owner := ufOwner, parent := [0, 1, 2, 3], rank := [0, 0, 0, 0], hlen := rfl, D := 4 }

/-- Union by attaching the larger root under the smaller, for the concrete run. -/
def uf1 : UF := uf0.writeParent ⟨1⟩ 1 0 (ufOwner_writable 1 (by decide))
def uf2 : UF := uf1.writeParent ⟨1⟩ 3 2 (ufOwner_writable 3 (by decide))
def uf3 : UF := uf2.writeParent ⟨1⟩ 2 0 (ufOwner_writable 2 (by decide))

theorem uf3_parent : uf3.parent = [0, 0, 0, 2] := by decide

theorem uf3_find_all :
    uf3.findRoot 0 = some 0 ∧ uf3.findRoot 1 = some 0 ∧
      uf3.findRoot 2 = some 0 ∧ uf3.findRoot 3 = some 0 := by
  decide

theorem uf3_lengths : uf3.parent.length = 4 ∧ uf3.rank.length = 4 := by
  decide

end Cap
