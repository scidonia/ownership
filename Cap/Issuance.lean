/-
Historical capability issuance.

A capability identity, once issued, is never issued again in the same run. The
context records the issuance history in `Ctx.issued`, every authority-producing
transition extends it, and the checker refuses a transition whose new
identifiers occur in it. This closes the reuse hole: freshness against the set of
*currently live* capabilities does not exclude a retired name, so a split could
otherwise hand a live child the identifier of its own parent's retired
predecessor.

The tests below drive the raw checker from the canonical empty world. The first
program is the review's regression: split the root into `⟨3⟩`/`⟨4⟩`, then split
`⟨3⟩` giving the retired root identifier `⟨1⟩` to a new child. The second is the
same program with a fresh child identifier.
-/
import Cap.Runner

namespace Cap

/-- A program that reuses the retired root capability `⟨1⟩` as a split child. -/
def reuseSplitProgram : List UCmd :=
  [ .alloc 8 ⟨1⟩ ⟨2⟩,
    .splitAt ⟨0⟩ ⟨1⟩ ⟨3⟩ ⟨4⟩ 4,
    .splitAt ⟨0⟩ ⟨3⟩ ⟨1⟩ ⟨5⟩ 2 ]

/-- The prefix is accepted: the program does reach the second split, so the
refusal below is the history check and not an earlier failure. -/
theorem reuseSplit_prefix_ok :
    (checkWorld World.emptyWorld
      [ .alloc 8 ⟨1⟩ ⟨2⟩, .splitAt ⟨0⟩ ⟨1⟩ ⟨3⟩ ⟨4⟩ 4 ]).isOk = true := by
  decide

/-- The regression is refused: `⟨1⟩` is in the context's issuance history. -/
theorem reuseSplit_refused :
    (checkWorld World.emptyWorld reuseSplitProgram).isOk = false := by
  decide

/-- The control: the same two splits with a fresh child identifier are accepted. -/
def reuseSplitControl : List UCmd :=
  [ .alloc 8 ⟨1⟩ ⟨2⟩,
    .splitAt ⟨0⟩ ⟨1⟩ ⟨3⟩ ⟨4⟩ 4,
    .splitAt ⟨0⟩ ⟨3⟩ ⟨6⟩ ⟨5⟩ 2 ]

theorem reuseSplitControl_ok :
    (checkWorld World.emptyWorld reuseSplitControl).isOk = true := by
  decide

/-- A checked spatial split only grows the issuance history. -/
theorem World.splitAtChecked_issued_sub {w w' : World} {a : AllocId}
    {id id1 id2 : CapId} {k : Nat}
    (h : w.splitAtChecked a id id1 id2 k = .ok w') :
    ∀ c ∈ w.ctx.issued, c ∈ w'.ctx.issued := by
  unfold World.splitAtChecked at h
  split at h
  · simp at h
  · rename_i o hf
    split at h
    · rename_i hfr
      split at h
      · rename_i C' hs
        simp only [Except.ok.injEq] at h
        cases h
        intro c hc
        exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hc)
      · simp at h
    · simp at h

/-- A checked fractional join only grows the issuance history. -/
theorem World.joinChecked_issued_sub {w w' : World} {a : AllocId}
    {node newId : CapId} (h : w.joinChecked a node newId = .ok w') :
    ∀ c ∈ w.ctx.issued, c ∈ w'.ctx.issued := by
  unfold World.joinChecked at h
  split at h
  · simp at h
  · rename_i o hf'
    split at h
    · rename_i hfresh
      split at h
      · rename_i C' hs
        simp only [Except.ok.injEq] at h
        cases h
        intro c hc
        exact List.mem_cons_of_mem _ hc
      · simp at h
    · simp at h

end Cap
