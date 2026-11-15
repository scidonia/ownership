/-
A deep command language over a single owner, with an executable checker.

This is the *deep* form of the ownership layer: a first-order list of commands
(write a byte through a capability, split a capability spatially or fractionally,
do nothing), an interpreter that either returns the resulting owner or an error,
and soundness theorems about accepted programs. It is not the surface syntax, not
a hidden-index Lean elaborator, and not a heap semantics: writes here are checked
against the ledger's `Owner.Writable` guard and leave the owner unchanged, and no
byte is actually stored. Acceptance is therefore checker acceptance of the owner
layer; it is not execution safety for a program that runs against a heap. The
review's R1 records that missing connection. The reference heap, backend and context live in
`Cap.Bytes`, `Cap.Backend` and `Cap.Context`.

The module proves:
* `check_nil` / `checked_nil` — the empty program is accepted by any owner.
* `check_write_error` — a write whose guard fails is refused with an error.
* `write_checked` — an accepted write command carries `Owner.Writable` for the
  owner it was checked against, so the command is only ever accepted under the
  ledger's write guard.
* `splitAt_checked_pre` / `splitFraction_checked_pre` — an accepted split command
  names an existing leaf and satisfies the precondition of the corresponding
  transition (`c.lo ≤ k ≤ c.hi` for `Owner.splitAt?`, `q1 + q2 = c.q` for
  `Owner.splitFraction?`); the checker itself calls those transitions.
* `splitAt_checked` / `splitFraction_checked` — the transition the checker called
  succeeded, hence produced a successor owner.
* `splitAt_checked_fresh` / `splitFraction_checked_fresh` — an accepted split uses
  fresh child capability identifiers: distinct from each other and absent from the
  owner's identifiers, so reusing the parent or repeating a child is refused with
  `msgFresh`.
* `check_covered` — an accepted program maps a covered owner to a covered owner,
  so the byte budget is preserved along a whole run.
* `readOnly_write_refused` / `readOnly_write_not_accepted` — a write through a
  read-only leaf is refused, by computation.
-/
import Cap.Ledger

namespace Cap

/-- A command of the deep language. `splitFraction` stores the positivity proofs
the transition needs so that a command carries the same precondition as the
transition it invokes. -/
inductive Cmd where
  | write (id : CapId) (i : Nat)
  | splitAt (id id1 id2 : CapId) (k : Nat)
  | splitFraction (id id1 id2 : CapId) (q1 q2 : Nat) (p1 : 0 < q1) (p2 : 0 < q2)
  | nop

/-- Decision procedure for the ledger's write guard: the leaf named by `id` must
be active, hold the whole share `D`, allow writes, and contain the index. -/
def Owner.writableB (o : Owner) (D : Nat) (id : CapId) (i : Nat) : Bool :=
  match o.root.find? id with
  | none => false
  | some c =>
    decide (c.state = .active ∧ c.q = D ∧ c.ceiling = .readWrite ∧ c.lo ≤ i ∧ i < c.hi)

/-- A positive decision by `writableB` is the ledger's `Writable` guard. -/
theorem Owner.writableB_sound {o : Owner} {D : Nat} {id : CapId} {i : Nat}
    (h : o.writableB D id i = true) : o.Writable D id i := by
  unfold Owner.writableB at h
  cases hf : o.root.find? id with
  | none => simp [hf] at h
  | some c =>
    simp only [hf] at h
    exact ⟨c, hf, of_decide_eq_true h⟩

/-- The error reported for a write whose guard does not hold. -/
def msgWrite : String := "write refused: capability is not writable at this index"

/-- The error reported for a split whose child capability identifiers are not fresh. -/
def msgFresh : String := "split refused: capability identifiers are not fresh"

/-- The error reported for a spatial split the transition rejects. -/
def msgSplitAt : String := "splitAt refused: no such capability or split point out of range"

/-- The error reported for a fractional split the transition rejects. -/
def msgSplitFraction : String :=
  "splitFraction refused: no such capability or shares do not add up"

/-- The executable checker: interpret the commands, stopping at the first one the
ledger's transitions refuse. Writes consult `Owner.writableB`; splits call
`Owner.splitAt?` and `Owner.splitFraction?` directly. -/
def check (o : Owner) (D : Nat) : List Cmd → Except String Owner
  | [] => .ok o
  | .nop :: cs => check o D cs
  | .write id i :: cs =>
    if o.writableB D id i then check o D cs else .error msgWrite
  | .splitAt id id1 id2 k :: cs =>
    if hfresh : o.FreshIds id1 id2 then
      match o.splitAt? id id1 id2 k with
      | some o' => check o' D cs
      | none => .error msgSplitAt
    else .error msgFresh
  | .splitFraction id id1 id2 q1 q2 p1 p2 :: cs =>
    if hfresh : o.FreshIds id1 id2 then
      match o.splitFraction? id id1 id2 q1 q2 p1 p2 with
      | some o' => check o' D cs
      | none => .error msgSplitFraction
    else .error msgFresh

/-- A program is accepted from the given owner and budget. -/
def Checked (o : Owner) (D : Nat) (cs : List Cmd) : Prop := (check o D cs).isOk = true

/-- The empty program is accepted by every owner. -/
theorem check_nil (o : Owner) (D : Nat) : check o D [] = .ok o := rfl

/-- The empty program is accepted. -/
theorem checked_nil (o : Owner) (D : Nat) : Checked o D [] := rfl

/-- A write whose guard does not hold is refused with an error. -/
theorem check_write_error {o : Owner} {D : Nat} {id : CapId} {i : Nat} {cs : List Cmd}
    (hw : o.writableB D id i = false) :
    check o D (Cmd.write id i :: cs) = .error msgWrite := by
  simp [check, hw]

/-- An accepted write command carries the ledger's write guard for the owner it
was checked against. -/
theorem write_checked (o o' : Owner) (D : Nat) (cs : List Cmd) (id : CapId) (i : Nat)
    (h : check o D (Cmd.write id i :: cs) = .ok o') : o.Writable D id i := by
  cases hw : o.writableB D id i with
  | true => exact Owner.writableB_sound hw
  | false =>
    rw [check_write_error hw] at h
    cases h

/-- An accepted spatial-split command invokes a transition that succeeds. -/
theorem splitAt_checked {o o' : Owner} {D : Nat} {id id1 id2 : CapId} {k : Nat}
    {cs : List Cmd}
    (h : check o D (Cmd.splitAt id id1 id2 k :: cs) = .ok o') :
    ∃ o'', o.splitAt? id id1 id2 k = some o'' := by
  by_cases hfresh : o.FreshIds id1 id2
  · cases hs : o.splitAt? id id1 id2 k with
    | none => simp [check, hfresh, hs] at h
    | some o'' => exact ⟨o'', rfl⟩
  · simp [check, hfresh] at h

/-- An accepted split uses fresh child capability identifiers. -/
theorem splitAt_checked_fresh {o o' : Owner} {D : Nat} {id id1 id2 : CapId} {k : Nat}
    {cs : List Cmd}
    (h : check o D (Cmd.splitAt id id1 id2 k :: cs) = .ok o') :
    o.FreshIds id1 id2 := by
  by_cases hfresh : o.FreshIds id1 id2
  · exact hfresh
  · simp [check, hfresh] at h

/-- An accepted spatial-split command names an existing leaf and a split point
inside that leaf's footprint: the precondition of `Owner.splitAt?`. -/
theorem splitAt_checked_pre {o o' : Owner} {D : Nat} {id id1 id2 : CapId} {k : Nat}
    {cs : List Cmd}
    (h : check o D (Cmd.splitAt id id1 id2 k :: cs) = .ok o') :
    ∃ c, o.root.find? id = some c ∧ c.lo ≤ k ∧ k ≤ c.hi := by
  obtain ⟨o'', hs⟩ := splitAt_checked h
  unfold Owner.splitAt? at hs
  cases hf : o.root.find? id with
  | none => simp [hf] at hs
  | some c =>
    cases hsp : c.splitSpatial? id1 id2 k with
    | none => simp [hf, hsp] at hs
    | some t =>
      obtain ⟨h1, h2, _⟩ := Leaf.splitSpatial?_some hsp
      exact ⟨c, rfl, h1, h2⟩

/-- An accepted fractional-split command invokes a transition that succeeds. -/
theorem splitFraction_checked {o o' : Owner} {D : Nat} {id id1 id2 : CapId}
    {q1 q2 : Nat} {p1 : 0 < q1} {p2 : 0 < q2} {cs : List Cmd}
    (h : check o D (Cmd.splitFraction id id1 id2 q1 q2 p1 p2 :: cs) = .ok o') :
    ∃ o'', o.splitFraction? id id1 id2 q1 q2 p1 p2 = some o'' := by
  by_cases hfresh : o.FreshIds id1 id2
  · cases hs : o.splitFraction? id id1 id2 q1 q2 p1 p2 with
    | none => simp [check, hfresh, hs] at h
    | some o'' => exact ⟨o'', rfl⟩
  · simp [check, hfresh] at h

/-- An accepted fractional split uses fresh child capability identifiers. -/
theorem splitFraction_checked_fresh {o o' : Owner} {D : Nat} {id id1 id2 : CapId}
    {q1 q2 : Nat} {p1 : 0 < q1} {p2 : 0 < q2} {cs : List Cmd}
    (h : check o D (Cmd.splitFraction id id1 id2 q1 q2 p1 p2 :: cs) = .ok o') :
    o.FreshIds id1 id2 := by
  by_cases hfresh : o.FreshIds id1 id2
  · exact hfresh
  · simp [check, hfresh] at h

/-- A successful fractional split tree carries the shares precondition. -/
theorem Leaf.splitFractionTree_shares {c : Leaf} {id1 id2 : CapId} {q1 q2 : Nat}
    {p1 : 0 < q1} {p2 : 0 < q2} {t : Tree}
    (h : c.splitFractionTree id1 id2 q1 q2 p1 p2 = some t) : q1 + q2 = c.q := by
  by_cases hq : q1 + q2 = c.q
  · exact hq
  · simp [Leaf.splitFractionTree, hq] at h

/-- An accepted fractional-split command names an existing leaf whose share is
exactly the sum of the two requested shares: the precondition of
`Owner.splitFraction?`. -/
theorem splitFraction_checked_pre {o o' : Owner} {D : Nat} {id id1 id2 : CapId}
    {q1 q2 : Nat} {p1 : 0 < q1} {p2 : 0 < q2} {cs : List Cmd}
    (h : check o D (Cmd.splitFraction id id1 id2 q1 q2 p1 p2 :: cs) = .ok o') :
    ∃ c, o.root.find? id = some c ∧ q1 + q2 = c.q := by
  obtain ⟨o'', hs⟩ := splitFraction_checked h
  unfold Owner.splitFraction? at hs
  cases hf : o.root.find? id with
  | none => simp [hf] at hs
  | some c =>
    cases hst : c.splitFractionTree id1 id2 q1 q2 p1 p2 with
    | none => simp [hf, hst] at hs
    | some t => exact ⟨c, rfl, Leaf.splitFractionTree_shares hst⟩

/-- An accepted program maps a fully covered owner to a fully covered owner: the
byte budget is preserved along a whole run. -/
theorem check_covered (cs : List Cmd) :
    ∀ (o o' : Owner) (D : Nat),
      check o D cs = .ok o' → o.Covered D → o'.Covered D := by
  induction cs with
  | nil =>
    intro o o' D h hc
    simp [check] at h
    cases h
    exact hc
  | cons c cs ih =>
    intro o o' D h hc
    cases c with
    | write id i =>
      by_cases hw : o.writableB D id i
      · simp [check, hw] at h
        exact ih o o' D h hc
      · simp [check, hw] at h
    | splitAt id id1 id2 k =>
      by_cases hfresh : o.FreshIds id1 id2
      · cases hs : o.splitAt? id id1 id2 k with
        | none => simp [check, hfresh, hs] at h
        | some o'' =>
          simp [check, hfresh, hs] at h
          exact ih o'' o' D h (Owner.splitAt_covered hs hc)
      · simp [check, hfresh] at h
    | splitFraction id id1 id2 q1 q2 p1 p2 =>
      by_cases hfresh : o.FreshIds id1 id2
      · cases hs : o.splitFraction? id id1 id2 q1 q2 p1 p2 with
        | none => simp [check, hfresh, hs] at h
        | some o'' =>
          simp [check, hfresh, hs] at h
          exact ih o'' o' D h (Owner.splitFraction_covered hs hc)
      · simp [check, hfresh] at h
    | nop =>
      simp [check] at h
      exact ih o o' D h hc

/- Concrete runs: an eight-byte allocation with budget eight. -/

/-- One eight-byte allocation, fully described by its single read-write leaf. -/
def coreExampleOwner : Owner :=
  { alloc := ⟨0⟩, len := 8,
    root := .leaf
      { id := ⟨0⟩, alloc := ⟨0⟩, lo := 0, hi := 8, ordered := by decide,
        q := 8, pos := by decide, ceiling := .readWrite, state := .active },
    disposal := ⟨0⟩ }

/-- The same allocation behind a read-only leaf. -/
def readOnlyOwner : Owner :=
  { alloc := ⟨0⟩, len := 8,
    root := .leaf
      { id := ⟨0⟩, alloc := ⟨0⟩, lo := 0, hi := 8, ordered := by decide,
        q := 8, pos := by decide, ceiling := .readOnly, state := .active },
    disposal := ⟨0⟩ }

/-- Split at four, write both halves, fractionally split the left half into
shares three and five, then stop. -/
def exampleProgram : List Cmd :=
  [ .splitAt ⟨0⟩ ⟨1⟩ ⟨2⟩ 4,
    .write ⟨1⟩ 2,
    .write ⟨2⟩ 5,
    .splitFraction ⟨1⟩ ⟨3⟩ ⟨4⟩ 3 5 (by decide) (by decide),
    .nop ]

theorem exampleProgram_checked : Checked coreExampleOwner 8 exampleProgram := by
  unfold Checked
  decide

theorem exampleProgram_covered : coreExampleOwner.Covered 8 := by
  unfold coreExampleOwner
  exact Owner.init_covered (a := ⟨0⟩) (n := 8) (D := 8) (pos := by decide)
    (rootId := ⟨0⟩) (disposal := ⟨0⟩)

/-- The same run preserves coverage. -/
theorem exampleProgram_run_covered :
    ∀ o', check coreExampleOwner 8 exampleProgram = .ok o' → o'.Covered 8 := by
  intro o' h
  exact check_covered exampleProgram coreExampleOwner o' 8 h exampleProgram_covered

/-- A write through the read-only leaf fails the guard. -/
theorem readOnly_writableB_false : readOnlyOwner.writableB 8 ⟨0⟩ 3 = false := by decide

/-- The read-only write is refused with the guard's error. -/
theorem readOnly_write_refused :
    check readOnlyOwner 8 [Cmd.write ⟨0⟩ 3] = .error msgWrite :=
  check_write_error readOnly_writableB_false

/-- No owner results from the refused write. -/
theorem readOnly_write_not_accepted :
    ¬ ∃ o', check readOnlyOwner 8 [Cmd.write ⟨0⟩ 3] = .ok o' := by
  rintro ⟨o', h⟩
  rw [readOnly_write_refused] at h
  cases h

/-- The ledger's guard is likewise false there, so the refusal is not a quirk of
the decision procedure. -/
theorem readOnly_not_writable (i : Nat) : ¬ readOnlyOwner.Writable 8 ⟨0⟩ i := by
  rintro ⟨c, hc, _, _, hceil, _, _⟩
  simp [readOnlyOwner, Tree.find?] at hc
  subst hc
  cases hceil

end Cap
