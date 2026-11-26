/-
Trace properties of accepted executions.

`writeChecked_sound` states the guard an individual accepted write held. This
module lifts that to command lists: from any accepted trace, a write occurring at
any position held the guard at the world reached just before it. It also records
the single-step decomposition of an accepted trace, which is what makes the
induction work.

The theorem concerns the *checker's* trace language, which carries no access
evidence by design: the guard is checked at run time, and this is the property
that check has. The evidence-bearing client is `IProg`/`Owned`/`Cert`.
-/
import Cap.Runner

namespace Cap

/-- An accepted trace splits at its first command: the command is accepted and
the remainder runs from its result. -/
theorem checkWorld_cons_ok {w w' : World} {c : UCmd} {rest : List UCmd}
    (h : checkWorld w (c :: rest) = .ok w') :
    ∃ w1, checkWorld w [c] = .ok w1 ∧ checkWorld w1 rest = .ok w' := by
  cases c with
  | nop =>
    refine ⟨w, ?_, ?_⟩
    · simp [checkWorld]
    · simpa [checkWorld] using h
  | write a id i v =>
    cases hw : w.writeChecked a id i v with
    | error e => simp [checkWorld, hw] at h
    | ok w1 =>
      refine ⟨w1, ?_, ?_⟩
      · simp [checkWorld, hw]
      · simpa [checkWorld, hw] using h
  | splitAt a id id1 id2 k =>
    cases hw : w.splitAtChecked a id id1 id2 k with
    | error e => simp [checkWorld, hw] at h
    | ok w1 =>
      refine ⟨w1, ?_, ?_⟩
      · simp [checkWorld, hw]
      · simpa [checkWorld, hw] using h
  | splitFraction a id id1 id2 q1 q2 =>
    by_cases hq : 0 < q1 ∧ 0 < q2
    · cases hw : w.splitFractionChecked a id id1 id2 q1 q2 hq.1 hq.2 with
      | error e => simp [checkWorld, hq, hw] at h
      | ok w1 =>
        refine ⟨w1, ?_, ?_⟩
        · simp [checkWorld, hq, hw]
        · simpa [checkWorld, hq, hw] using h
    · simp [checkWorld, hq] at h
  | join a node newId =>
    cases hw : w.joinChecked a node newId with
    | error e => simp [checkWorld, hw] at h
    | ok w1 =>
      refine ⟨w1, ?_, ?_⟩
      · simp [checkWorld, hw]
      · simpa [checkWorld, hw] using h
  | free a d =>
    cases hw : w.freeChecked a d with
    | error e => simp [checkWorld, hw] at h
    | ok w1 =>
      refine ⟨w1, ?_, ?_⟩
      · simp [checkWorld, hw]
      · simpa [checkWorld, hw] using h
  | alloc n rootId disposal =>
    by_cases hpos : 0 < w.ctx.D
    · cases hw : w.allocChecked n rootId disposal hpos with
      | error e => simp [checkWorld, hpos, hw] at h
      | ok w1 =>
        refine ⟨w1, ?_, ?_⟩
        · simp [checkWorld, hpos, hw]
        · simpa [checkWorld, hpos, hw] using h
    · simp [checkWorld, hpos] at h
  | beginBorrow a lender borrower loanId =>
    cases hw : w.beginBorrowChecked a lender borrower loanId with
    | error e => simp [checkWorld, hw] at h
    | ok w1 =>
      refine ⟨w1, ?_, ?_⟩
      · simp [checkWorld, hw]
      · simpa [checkWorld, hw] using h
  | endBorrow a loanId =>
    cases hw : w.endBorrowChecked a loanId with
    | error e => simp [checkWorld, hw] at h
    | ok w1 =>
      refine ⟨w1, ?_, ?_⟩
      · simp [checkWorld, hw]
      · simpa [checkWorld, hw] using h

/-- In any accepted trace, a write held its guard at the world reached just
before it. -/
theorem checkWorld_write_guard (pre post : List UCmd) (a : AllocId) (id : CapId)
    (i : Nat) (v : UInt8) (w w' : World)
    (h : checkWorld w (pre ++ UCmd.write a id i v :: post) = .ok w') :
    ∃ wm, checkWorld w pre = .ok wm ∧
      ∃ o, wm.ctx.findOwner? a = some o ∧ o.Writable wm.ctx.D id i := by
  induction pre generalizing w with
  | nil =>
    simp only [List.nil_append] at h
    cases hw : w.writeChecked a id i v with
    | error e => simp [checkWorld, hw] at h
    | ok w1 =>
      obtain ⟨o, b, b', hfind, hguard, -, -, -, -⟩ := World.writeChecked_sound hw
      exact ⟨w, by simp [checkWorld], o, hfind, hguard⟩
  | cons c cs ih =>
    simp only [List.cons_append] at h
    obtain ⟨w1, hstep, hrest⟩ := checkWorld_cons_ok h
    obtain ⟨wm, hpre, o, hfind, hguard⟩ := ih w1 hrest
    refine ⟨wm, ?_, o, hfind, hguard⟩
    have hsplit := checkWorld_append [c] cs w w1 hstep
    simpa using hsplit.trans hpre

end Cap
