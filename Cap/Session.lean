/-
A single-owner session: one owner, one reference heap and the budget denominator.

This is the smallest end-to-end state for the acceptance example. It deliberately
has one allocation; the multi-owner context is a later extension. `Session.Realizes`
is the owner's coverage, and the fill transition takes, for every byte it writes,
the ledger's `Writable` guard as a proof. The heap write is the reference model in
`Cap.Bytes`.

The example builds the 64-byte buffer by hand from the split tree, so its guards are
concrete; the dynamic split transitions and their coverage theorems are in
`Cap.Ledger` (`Owner.splitAt_covered`, `Owner.splitFraction_covered`).
-/
import Cap.Ledger
import Cap.Bytes

namespace Cap

structure Session where
  owner : Owner
  heap : Heap
  D : Nat

def Session.Realizes (s : Session) : Prop :=
  s.owner.Covered s.D

def Session.create (a : AllocId) (n D : Nat) (pos : 0 < D) (rootId disposal : CapId) :
    Session :=
  { owner := Owner.init a n D pos rootId disposal,
    heap := Heap.empty.alloc a n,
    D := D }

theorem Session.create_realizes (a : AllocId) (n D : Nat) (pos : 0 < D)
    (rootId disposal : CapId) : (Session.create a n D pos rootId disposal).Realizes := by
  unfold Session.create Session.Realizes
  exact Owner.init_covered a n D pos rootId disposal

def Session.splitAt? (s : Session) (id id1 id2 : CapId) (k : Nat) : Option Session :=
  (s.owner.splitAt? id id1 id2 k).map (fun o => { s with owner := o })

theorem Session.splitAt_realizes {s s' : Session} {id id1 id2 : CapId} {k : Nat}
    (hs : s.splitAt? id id1 id2 k = some s') (hr : s.Realizes) : s'.Realizes := by
  unfold Session.splitAt? at hs
  cases ho : s.owner.splitAt? id id1 id2 k with
  | none => simp [ho] at hs
  | some o =>
    simp [ho] at hs
    cases hs
    exact Owner.splitAt_covered ho hr

/-- Fill a range, taking the ledger guard for every byte it writes. -/
def Session.fill? (s : Session) (id : CapId) (lo hi : Nat) (v : UInt8)
    (hg : ∀ i, lo ≤ i → i < hi → s.owner.Writable s.D id i) :
    Option (Session × Heap) :=
  match s.heap.fill? s.owner.alloc lo hi v with
  | some h' => some (⟨s.owner, h', s.D⟩, h')
  | none => none

theorem Session.fill_realizes {s s' : Session} {h' : Heap} {id : CapId} {lo hi : Nat}
    {v : UInt8} {hg : ∀ i, lo ≤ i → i < hi → s.owner.Writable s.D id i}
    (hf : s.fill? id lo hi v hg = some (s', h')) (hr : s.Realizes) : s'.Realizes := by
  unfold Session.fill? at hf
  cases hb : s.heap.fill? s.owner.alloc lo hi v with
  | none => simp [hb] at hf
  | some h'' =>
    simp [hb] at hf
    obtain ⟨rfl, rfl⟩ := hf
    exact hr

def Session.snapshot? (s : Session) : Option (List UInt8) :=
  s.heap.snapshot? s.owner.alloc

/-- The example's allocation. -/
def exampleAlloc : AllocId := ⟨0⟩

def exampleLeft : Leaf :=
  { id := ⟨3⟩, alloc := exampleAlloc, lo := 0, hi := 32, ordered := by decide,
    q := 64, pos := by decide, ceiling := .readWrite, state := .active }

def exampleRight : Leaf :=
  { id := ⟨4⟩, alloc := exampleAlloc, lo := 32, hi := 64, ordered := by decide,
    q := 64, pos := by decide, ceiling := .readWrite, state := .active }

def exampleOwner : Owner :=
  { alloc := exampleAlloc, len := 64,
    root := .spatial ⟨5⟩ (.leaf exampleLeft) (.leaf exampleRight),
    disposal := ⟨2⟩ }

def exampleSession : Session :=
  { owner := exampleOwner, heap := Heap.empty.alloc exampleAlloc 64, D := 64 }

theorem exampleOwner_realizes : exampleSession.Realizes := by
  intro x hx
  by_cases h32 : x < 32
  · have hx1 : x < 32 := h32
    have hx2 : ¬ (32 ≤ x ∧ x < 64) := by omega
    simp [exampleSession, exampleOwner, exampleLeft, exampleRight, Tree.budget,
      Leaf.budget, hx1, hx2]
  · have hx32 : 32 ≤ x := by omega
    have hx64 : x < 64 := by simpa [exampleSession, exampleOwner] using hx
    have hx1 : ¬ x < 32 := h32
    simp [exampleSession, exampleOwner, exampleLeft, exampleRight, Tree.budget,
      Leaf.budget, hx1, hx32, hx64]

def guardLeft : ∀ i, 0 ≤ i → i < 32 → exampleOwner.Writable 64 ⟨3⟩ i := by
  intro i h1 h2
  refine ⟨exampleLeft, ?_, rfl, rfl, rfl, h1, h2⟩
  simp [exampleOwner, Tree.find?, exampleLeft, exampleRight]

def guardRight : ∀ i, 32 ≤ i → i < 64 → exampleOwner.Writable 64 ⟨4⟩ i := by
  intro i h1 h2
  refine ⟨exampleRight, ?_, rfl, rfl, rfl, h1, h2⟩
  simp [exampleOwner, Tree.find?, exampleLeft, exampleRight]

def exampleRun : Option (List UInt8) :=
  match exampleSession.fill? ⟨3⟩ 0 32 (1 : UInt8) guardLeft with
  | none => none
  | some (_, h1) =>
    let s1 : Session := { exampleSession with heap := h1 }
    match s1.fill? ⟨4⟩ 32 64 (2 : UInt8) guardRight with
    | none => none
    | some (s2, _) => s2.snapshot?

theorem exampleRun_snapshot :
    exampleRun = some (List.replicate 32 (1 : UInt8) ++ List.replicate 32 (2 : UInt8)) := by
  decide

end Cap
