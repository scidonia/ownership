/-
A linear-probing hash set under the ledger's write discipline.

The table is one allocation of eight slots, covered by a single whole-share
read--write leaf. Insertion probes from the hash position and writes through the
owner's `Writable` guard; the table's length is preserved by every write. Lookup
is a read-only probe.

This is an example of the discipline, not a verified hash table: the concrete run
inserts colliding keys, checks membership and absence, and the insert path is
length-preserving and guard-carrying. No resizing, deletion, hashing theorem or
complexity claim is made.
-/
import Cap.Ledger

namespace Cap

def hsAlloc : AllocId := ⟨0⟩

def hsRoot : Leaf :=
  { id := ⟨1⟩, alloc := hsAlloc, lo := 0, hi := 8, ordered := by decide,
    q := 8, pos := by decide, ceiling := .readWrite, state := .active }

def hsOwner : Owner :=
  { alloc := hsAlloc, len := 8, root := .leaf hsRoot, disposal := ⟨2⟩ }

theorem hsRoot_find : (Tree.leaf hsRoot).find? ⟨1⟩ = some hsRoot := by
  simp [Tree.find?, hsRoot]

theorem hsOwner_writable (i : Nat) (h : i < 8) : hsOwner.Writable 8 ⟨1⟩ i := by
  refine ⟨hsRoot, ?_, rfl, rfl, rfl, Nat.zero_le i, h⟩
  simpa [hsOwner, Tree.find?] using hsRoot_find

structure Table where
  owner : Owner
  slots : List (Option Nat)
  D : Nat

def Table.empty : Table :=
  { owner := hsOwner, slots := List.replicate 8 none, D := 8 }

def Table.read (t : Table) (i : Nat) : Option Nat := t.slots.getD i none

/-- A slot write through the owner's guard. -/
def Table.write (t : Table) (i : Nat) (v : Option Nat)
    (_hg : t.owner.Writable t.D ⟨1⟩ i) : Table :=
  { t with slots := t.slots.set i v }

theorem Table.write_length {t : Table} {i : Nat} {v : Option Nat}
    {hg : t.owner.Writable t.D ⟨1⟩ i} :
    (t.write i v hg).slots.length = t.slots.length := by
  simp [Table.write, List.length_set]

/-- Insert `x`, probing from `start` for `fuel` steps. Duplicates are a no-op. -/
def Table.insert (t : Table) (x : Nat) (howner : t.owner = hsOwner) (hD : t.D = 8)
    : Nat → Nat → Table
  | 0, _ => t
  | fuel + 1, start =>
    let j := (x + start) % 8
    match t.slots.getD j none with
    | none =>
      t.write j (some x)
        (by rw [howner, hD]; exact hsOwner_writable j (Nat.mod_lt _ (by decide)))
    | some y => if y = x then t else t.insert x howner hD fuel (start + 1)

/-- Membership, probing from `start` for `fuel` steps. -/
def Table.contains (t : Table) (x : Nat) : Nat → Nat → Bool
  | 0, _ => false
  | fuel + 1, start =>
    let j := (x + start) % 8
    match t.slots.getD j none with
    | none => false
    | some y => if y = x then true else t.contains x fuel (start + 1)

theorem Table.insert_length {t : Table} {x : Nat} {howner : t.owner = hsOwner}
    {hD : t.D = 8} {fuel start : Nat} :
    (t.insert x howner hD fuel start).slots.length = t.slots.length := by
  induction fuel generalizing start with
  | zero => rfl
  | succ fuel ih =>
    unfold Table.insert
    dsimp only
    split
    · exact Table.write_length
    · split
      · rfl
      · exact ih

/-- The concrete table after inserting colliding keys 3, 11, 19 (all 3 mod 8). -/
def t0 : Table := Table.empty
def t1 : Table := t0.insert 3 rfl rfl 8 0
def t2 : Table := t1.insert 11 rfl rfl 8 0
def t3 : Table := t2.insert 19 rfl rfl 8 0

theorem t3_slots : t3.slots = [none, none, none, some 3, some 11, some 19, none, none] := by
  decide

theorem t3_contains : t3.contains 11 8 0 = true := by decide

theorem t3_absent : t3.contains 4 8 0 = false := by decide

theorem t3_length : t3.slots.length = 8 := by decide

end Cap
