/-
A unified checked execution for the command language.

One instruction language with value operands, a checker that is also the
interpreter over a `World`, and preservation of the world relation. Acceptance
therefore yields the executed world, not a separate permission certificate.

The language covers writes, both splits, joins, free, allocation, loan begin/end
and no-op. Snapshot observation and the sealed runner's full-path state threading
remain outside this module.
-/
import Cap.World
import Cap.Backend
import Cap.Core
import Cap.WorldInvariant

namespace Cap

/-- A value-carrying execution command. -/
inductive UCmd where
  | write (a : AllocId) (id : CapId) (i : Nat) (v : UInt8)
  | splitAt (a : AllocId) (id id1 id2 : CapId) (k : Nat)
  | splitFraction (a : AllocId) (id id1 id2 : CapId) (q1 q2 : Nat)
  | join (a : AllocId) (node newId : CapId)
  | free (a : AllocId) (d : CapId)
  | alloc (n : Nat) (rootId disposal : CapId)
  | beginLoan (a : AllocId) (lender : CapId) (loanId : LoanId)
  | endLoan (a : AllocId) (loanId : LoanId)
  | nop

namespace World

/-- Check and execute one write: the owner guard and the backend must both accept,
and the backend is replaced at the allocation. -/
def writeChecked (w : World) (a : AllocId) (id : CapId) (i : Nat) (v : UInt8) :
    Except String World :=
  match w.ctx.findOwner? a with
  | none => .error "write: no owner for the allocation"
  | some o =>
    match w.heaps a with
    | none => .error "write: no backend for the allocation"
    | some b =>
      if _hw : o.writableB w.ctx.D id i then
        match b.write i v with
        | none => .error "write: index out of range"
        | some b' =>
          .ok { w with heaps := fun x => if x = a then some b' else w.heaps x }
      else .error "write: capability is not writable at this index"

/-- An accepted write names the owner, its ledger guard, the backend and the
replacement. -/
theorem writeChecked_sound {w w' : World} {a : AllocId} {id : CapId} {i : Nat}
    {v : UInt8} (h : w.writeChecked a id i v = .ok w') :
    ∃ o b b', w.ctx.findOwner? a = some o ∧ o.Writable w.ctx.D id i ∧
      w.heaps a = some b ∧ b.write i v = some b' ∧
      w'.ctx = w.ctx ∧
      w'.heaps = (fun x => if x = a then some b' else w.heaps x) := by
  unfold World.writeChecked at h
  cases hf : w.ctx.findOwner? a with
  | none => simp [hf] at h
  | some o =>
    cases hb : w.heaps a with
    | none => simp [hf, hb] at h
    | some b =>
      by_cases hw : o.writableB w.ctx.D id i
      · cases hbw : b.write i v with
        | none => simp [hf, hb, hw, hbw] at h
        | some b' =>
          simp [hf, hb, hw, hbw] at h
          cases h
          exact ⟨o, b, b', rfl, Owner.writableB_sound hw, rfl, hbw, rfl, rfl⟩
      · simp [hf, hb, hw] at h

/-- Acceptance preserves the world relation. -/
theorem writeChecked_rel {w w' : World} {a : AllocId} {id : CapId} {i : Nat}
    {v : UInt8} (h : w.writeChecked a id i v = .ok w') (hr : w.Rel) : w'.Rel := by
  obtain ⟨o, b, b', hf, _hw, hb, hbw, hctx, hheaps⟩ := writeChecked_sound h
  refine ⟨?_, ?_⟩
  · rw [hctx]; exact hr.1
  · intro o' ho'
    rw [hctx] at ho'
    obtain ⟨b0, hb0, hlen⟩ := hr.2 o' ho'
    by_cases hx : o'.alloc = a
    · have hb0a : w.heaps a = some b0 := by simpa [hx] using hb0
      have hb_eq : b0 = b := by
        rw [hb] at hb0a
        exact (Option.some.inj hb0a).symm
      subst hb_eq
      refine ⟨b', ?_, ?_⟩
      · simp [hheaps, hx]
      · rw [Backend.write_preserves_len hbw]; exact hlen
    · refine ⟨b0, ?_, hlen⟩
      simp [hheaps, hx, hb0]

/-- An accepted write preserves the world invariant: the context is unchanged
and the backend is replaced by one of the same length. -/
theorem writeChecked_wf {w w' : World} {a : AllocId} {id : CapId} {i : Nat}
    {v : UInt8} (h : w.writeChecked a id i v = .ok w') (hwf : w.WellFormed) :
    w'.WellFormed := by
  obtain ⟨o, b, b', hf, _hw, hb, hbw, hctx, hheaps⟩ := writeChecked_sound h
  refine ⟨?_, ?_, ?_⟩
  · rw [hctx]; exact hwf.1
  · rw [hctx]; exact hwf.2.1
  · intro a' o' hfind
    rw [hctx] at hfind
    obtain ⟨b0, hb0, hlen⟩ := hwf.2.2 a' o' hfind
    by_cases ha : a' = a
    · subst a'
      have hb_eq : b0 = b := by
        rw [hb] at hb0
        exact (Option.some.inj hb0).symm
      subst hb_eq
      refine ⟨b', ?_, ?_⟩
      · simp [hheaps]
      · rw [Backend.write_preserves_len hbw, hlen]
    · refine ⟨b0, ?_, hlen⟩
      simp [hheaps, ha, hb0]

/-- Begin an exclusive-suspension loan: the lender's leaf must exist and be
active, the loan identifier must be fresh, and the root lifetime `⟨0⟩` must be
live. The lender's leaf is retired — so the write guard refuses through it
while the loan is outstanding — and the loan is recorded against the root
lifetime. The borrower is the lender's own capability identifier: this slice
implements exclusive suspension, not a reborrow capability, so the distinct
lender/borrower side condition of `LoanCtx.begin` does not apply and the loan
list is extended directly. -/
def beginLoanChecked (w : World) (a : AllocId) (lender : CapId) (loanId : LoanId) :
    Except String World :=
  match w.ctx.findOwner? a with
  | none => .error "beginLoan: no owner for the allocation"
  | some o =>
    match o.root.find? lender with
    | none => .error "beginLoan: no such lender capability"
    | some c =>
      if c.state = .active then
        if loanId ∉ w.ctx.loans.loans.map (·.id) then
          if w.ctx.loans.live ⟨0⟩ then
            match o.suspendLeaf? lender with
            | none => .error "beginLoan: suspension refused"
            | some o' =>
              .ok { w with
                    ctx := { (w.ctx.update o.alloc o') with
                      loans := { w.ctx.loans with
                        loans := w.ctx.loans.loans ++
                          [{ id := loanId, alloc := a, lender := lender, borrower := lender,
                             lifetime := ⟨0⟩ }] } } }
          else .error "beginLoan: the root lifetime is not live"
        else .error "beginLoan: loan identifier is not fresh"
      else .error "beginLoan: lender capability is not active"

/-- A successful loan beginning preserves the world invariant: the loans field
does not enter the invariant and the context change is the suspension. -/
theorem beginLoanChecked_wf {w w' : World} {a : AllocId} {lender : CapId}
    {loanId : LoanId} (h : w.beginLoanChecked a lender loanId = .ok w')
    (hwf : w.WellFormed) : w'.WellFormed := by
  unfold World.beginLoanChecked at h
  cases hf : w.ctx.findOwner? a with
  | none => simp [hf] at h
  | some o =>
    cases hfl : o.root.find? lender with
    | none => simp [hf, hfl] at h
    | some c =>
      simp only [hf, hfl] at h
      by_cases hst : c.state = .active
      · rw [ite_eq_left hst] at h
        by_cases hfresh : loanId ∉ w.ctx.loans.loans.map (·.id)
        · rw [ite_eq_left hfresh] at h
          by_cases hlive : w.ctx.loans.live ⟨0⟩ = true
          · rw [ite_eq_left hlive] at h
            cases hs : o.suspendLeaf? lender with
            | none => simp [hs] at h
            | some o' =>
              simp only [hs, Except.ok.injEq] at h
              subst h
              exact World.suspend_update_wf hwf hf hs
          · rw [ite_eq_right hlive] at h
            simp at h
        · rw [ite_eq_right hfresh] at h
          simp at h
      · rw [ite_eq_right hst] at h
        simp at h

/-- End a loan: the loan must be recorded, and the owner of `a` must still hold
the lender's leaf, which is restored to active. The record is removed by a list
filter rather than `LoanCtx.endLoan`: every loan of this slice is bound to the
shared root lifetime `⟨0⟩`, which must stay live for later loans, so no
lifetime is ended here. Refuses if the owner or the leaf is gone. -/
def endLoanChecked (w : World) (a : AllocId) (loanId : LoanId) : Except String World :=
  match w.ctx.loans.findLoan? loanId with
  | none => .error "endLoan: no such loan"
  | some loan =>
    match w.ctx.findOwner? a with
    | none => .error "endLoan: no owner for the allocation"
    | some o =>
      match o.resumeLeaf? loan.lender with
      | none => .error "endLoan: lender is missing or not suspended"
      | some o' =>
        .ok { w with
              ctx := { (w.ctx.update o.alloc o') with
                loans := { w.ctx.loans with
                  loans := w.ctx.loans.loans.filter (fun l => l.id ≠ loanId) } } }

/-- A successful loan ending preserves the world invariant: the loans field
does not enter the invariant and the context change is the resumption. -/
theorem endLoanChecked_wf {w w' : World} {a : AllocId} {loanId : LoanId}
    (h : w.endLoanChecked a loanId = .ok w') (hwf : w.WellFormed) : w'.WellFormed := by
  unfold World.endLoanChecked at h
  cases hl : w.ctx.loans.findLoan? loanId with
  | none => simp [hl] at h
  | some loan =>
    cases hf : w.ctx.findOwner? a with
    | none => simp [hl, hf] at h
    | some o =>
      cases hr : o.resumeLeaf? loan.lender with
      | none => simp [hl, hf, hr] at h
      | some o' =>
        simp only [hl, hf, hr, Except.ok.injEq] at h
        subst h
        exact World.resume_update_wf hwf hf hr

end World

/-- The checker is the interpreter: an accepted program returns the world it
executed. -/
def checkWorld : World → List UCmd → Except String World
  | w, [] => .ok w
  | w, .nop :: cs => checkWorld w cs
  | w, .write a id i v :: cs =>
    match w.writeChecked a id i v with
    | .ok w' => checkWorld w' cs
    | .error e => .error e
  | w, .splitAt a id id1 id2 k :: cs =>
    match w.splitAtChecked a id id1 id2 k with
    | .ok w' => checkWorld w' cs
    | .error e => .error e
  | w, .splitFraction a id id1 id2 q1 q2 :: cs =>
    if hq : 0 < q1 ∧ 0 < q2 then
      match w.splitFractionChecked a id id1 id2 q1 q2 hq.1 hq.2 with
      | .ok w' => checkWorld w' cs
      | .error e => .error e
    else .error "split: non-positive share"
  | w, .join a node newId :: cs =>
    match w.joinChecked a node newId with
    | .ok w' => checkWorld w' cs
    | .error e => .error e
  | w, .free a d :: cs =>
    match w.freeChecked a d with
    | .ok w' => checkWorld w' cs
    | .error e => .error e
  | w, .alloc n rootId disposal :: cs =>
    if hpos : 0 < w.ctx.D then
      match w.allocChecked n rootId disposal hpos with
      | .ok w' => checkWorld w' cs
      | .error e => .error e
    else .error "alloc: non-positive denominator"
  | w, .beginLoan a lender loanId :: cs =>
    match w.beginLoanChecked a lender loanId with
    | .ok w' => checkWorld w' cs
    | .error e => .error e
  | w, .endLoan a loanId :: cs =>
    match w.endLoanChecked a loanId with
    | .ok w' => checkWorld w' cs
    | .error e => .error e

/-- An accepted execution preserves the world invariant. -/
theorem checkWorld_wf : ∀ (w w' : World) (cs : List UCmd),
    checkWorld w cs = .ok w' → w.WellFormed → w'.WellFormed := by
  intro w w' cs
  induction cs generalizing w with
  | nil =>
    intro h hwf
    simp [checkWorld] at h
    cases h
    exact hwf
  | cons c cs ih =>
    intro h hwf
    cases c with
    | nop =>
      simp [checkWorld] at h
      exact ih w h hwf
    | write a id i v =>
      cases hw : w.writeChecked a id i v with
      | error e => simp [checkWorld, hw] at h
      | ok w'' =>
        simp [checkWorld, hw] at h
        exact ih w'' h (World.writeChecked_wf hw hwf)
    | splitAt a id id1 id2 k =>
      cases hw : w.splitAtChecked a id id1 id2 k with
      | error e => simp [checkWorld, hw] at h
      | ok w'' =>
        simp [checkWorld, hw] at h
        exact ih w'' h (World.splitAtChecked_wf hw hwf)
    | splitFraction a id id1 id2 q1 q2 =>
      by_cases hq : 0 < q1 ∧ 0 < q2
      · cases hw : w.splitFractionChecked a id id1 id2 q1 q2 hq.1 hq.2 with
        | error e => simp [checkWorld, hq, hw] at h
        | ok w'' =>
          simp [checkWorld, hq, hw] at h
          exact ih w'' h (World.splitFractionChecked_wf hw hwf)
      · simp [checkWorld, hq] at h
    | join a node newId =>
      cases hw : w.joinChecked a node newId with
      | error e => simp [checkWorld, hw] at h
      | ok w'' =>
        simp [checkWorld, hw] at h
        exact ih w'' h (World.joinChecked_wf hw hwf)
    | free a d =>
      cases hw : w.freeChecked a d with
      | error e => simp [checkWorld, hw] at h
      | ok w'' =>
        simp [checkWorld, hw] at h
        exact ih w'' h (World.freeChecked_wf hw hwf)
    | alloc n rootId disposal =>
      by_cases hpos : 0 < w.ctx.D
      · cases hw : w.allocChecked n rootId disposal hpos with
        | error e => simp [checkWorld, hpos, hw] at h
        | ok w'' =>
          simp [checkWorld, hpos, hw] at h
          exact ih w'' h (World.allocChecked_wf hw hwf)
      · simp [checkWorld, hpos] at h
    | beginLoan a lender loanId =>
      cases hw : w.beginLoanChecked a lender loanId with
      | error e => simp [checkWorld, hw] at h
      | ok w'' =>
        simp [checkWorld, hw] at h
        exact ih w'' h (World.beginLoanChecked_wf hw hwf)
    | endLoan a loanId =>
      cases hw : w.endLoanChecked a loanId with
      | error e => simp [checkWorld, hw] at h
      | ok w'' =>
        simp [checkWorld, hw] at h
        exact ih w'' h (World.endLoanChecked_wf hw hwf)

/-- An accepted execution preserves the world relation, provided the input world
is well formed. -/
theorem checkWorld_rel : ∀ (w w' : World) (cs : List UCmd),
    checkWorld w cs = .ok w' → w.WellFormed → w'.Rel := by
  intro w w' cs h hwf
  exact World.rel_of_wellFormed (checkWorld_wf w w' cs h hwf)

/-- The concrete owner: one 64-byte whole-share leaf. -/
def uOwner : Owner := Owner.init ⟨0⟩ 64 64 (by decide) ⟨1⟩ ⟨2⟩

/-- The concrete world: one 64-byte owner and its backend. -/
def uWorld : World :=
  { ctx := { owners := [uOwner], D := 64, nextAlloc := 1, issued := [⟨2⟩, ⟨1⟩], loans := .rootOnly },
    heaps := fun a => if a = ⟨0⟩ then some (Backend.empty 64) else none,
}

/-- The concrete 64-byte world is well formed. -/
theorem uWorld_wf : uWorld.WellFormed := by
  refine ⟨?_, ?_, ?_⟩
  · -- Ctx.WellFormed
    refine ⟨?_, ?_, ?_⟩
    · refine ⟨?_, ?_⟩
      · intro o ho
        simp [uWorld] at ho
        rcases ho with rfl
        exact Owner.init_covered ⟨0⟩ 64 64 (by decide) ⟨1⟩ ⟨2⟩
      · simp [uWorld]
    · intro o ho
      simp [uWorld] at ho
      rcases ho with rfl
      exact Owner.init_wellFormed ⟨0⟩ 64 64 (by decide) ⟨1⟩ ⟨2⟩
    · decide
  · exact Ctx.functional_of_nodup (by simp [uWorld])
  · intro a o hfind
    unfold uWorld at hfind
    simp [Ctx.findOwner?, uOwner] at hfind
    have ho : o = uOwner := hfind.2.symm
    have ha : a = uOwner.alloc := hfind.1.symm
    subst ha
    subst o
    exact ⟨Backend.empty 64, rfl, rfl⟩

theorem uWorld_rel : uWorld.Rel := by

  refine ⟨?_, ?_⟩
  · refine ⟨?_, ?_⟩
    · intro o ho
      simp [uWorld] at ho
      rcases ho with rfl
      exact Owner.init_covered ⟨0⟩ 64 64 (by decide) ⟨1⟩ ⟨2⟩
    · simp [uWorld]
  · intro o ho
    simp [uWorld] at ho
    rcases ho with rfl
    refine ⟨Backend.empty 64, ?_, ?_⟩
    · rfl
    · rfl

/-- Fill `n` bytes from `lo` with `v` through one capability. -/
def fillCmds (id : CapId) (lo n : Nat) (v : UInt8) : List UCmd :=
  (List.range n).map (fun k => UCmd.write ⟨0⟩ id (lo + k) v)

def uProgram : List UCmd := fillCmds ⟨1⟩ 0 32 1 ++ fillCmds ⟨1⟩ 32 32 2

def uRun : Option (List UInt8) :=
  match checkWorld uWorld uProgram with
  | .ok w => (w.heaps ⟨0⟩).map (fun b => b.buf)
  | .error _ => none

theorem uRun_snapshot :
    uRun = some (List.replicate 32 (1 : UInt8) ++ List.replicate 32 (2 : UInt8)) := by
  decide
/-- The concrete program is accepted. -/
theorem uProgram_ok : (checkWorld uWorld uProgram).isOk = true := by
  decide
theorem uProgram_rel : ∃ w, checkWorld uWorld uProgram = .ok w ∧ w.Rel := by
  have hok : (checkWorld uWorld uProgram).isOk = true := by decide
  cases h : checkWorld uWorld uProgram with
  | error e =>
    have hfalse : (checkWorld uWorld uProgram).isOk = false := by
      rw [h]
      rfl
    rw [hfalse] at hok
    cases hok
  | ok w => exact ⟨w, rfl, checkWorld_rel uWorld w uProgram h uWorld_wf⟩

/-- A lifecycle program through the unified route: allocate a fresh 4-byte
owner, write one byte, split it spatially, write the left half, split it
fractionally, join the halves, write again, then dispose it. The pre-existing
64-byte owner is untouched. -/
def uLifecycle : List UCmd :=
  [ .alloc 4 ⟨3⟩ ⟨4⟩,
    .write ⟨1⟩ ⟨3⟩ 0 7,
    .splitAt ⟨1⟩ ⟨3⟩ ⟨5⟩ ⟨6⟩ 2,
    .write ⟨1⟩ ⟨5⟩ 0 8,
    .splitFraction ⟨1⟩ ⟨5⟩ ⟨7⟩ ⟨8⟩ 32 32,
    .join ⟨1⟩ ⟨7⟩ ⟨9⟩,
    .write ⟨1⟩ ⟨9⟩ 1 9,
    .free ⟨1⟩ ⟨4⟩ ]

/-- The lifecycle program is accepted and preserves the pre-existing snapshot. -/
def uLifecycleSnapshot : Option (Option (List UInt8)) :=
  match checkWorld uWorld uLifecycle with
  | .ok w => some ((w.heaps ⟨0⟩).map (fun b => b.buf))
  | .error _ => none

/-- The lifecycle leaves the pre-existing 64-byte backend at its initial value:
the commands act only on the freshly allocated owner. -/
theorem uLifecycle_snapshot :
    uLifecycleSnapshot = some (some (List.replicate 64 (0 : UInt8))) := by
  decide

/-- The lifecycle program is accepted. -/
theorem uLifecycle_ok : (checkWorld uWorld uLifecycle).isOk = true := by
  decide

/-- The lifecycle program's final world is well formed. -/
theorem uLifecycle_wf : ∃ w, checkWorld uWorld uLifecycle = .ok w ∧ w.WellFormed := by
  have hok : (checkWorld uWorld uLifecycle).isOk = true := uLifecycle_ok
  cases h : checkWorld uWorld uLifecycle with
  | error e =>
    rw [h] at hok
    cases hok
  | ok w => exact ⟨w, rfl, checkWorld_wf uWorld w uLifecycle h uWorld_wf⟩

/-- The loan prefix: allocate a fresh 4-byte owner and write one byte through
its root capability. -/
def uLoanPre : List UCmd := [.alloc 4 ⟨3⟩ ⟨4⟩, .write ⟨1⟩ ⟨3⟩ 0 7]

/-- Positive control: the write at index 1 is accepted before the loan
begins. -/
theorem uLoan_write_before :
    (checkWorld uWorld (uLoanPre ++ [.write ⟨1⟩ ⟨3⟩ 1 9])).isOk = true := by
  decide

/-- While the loan is outstanding the lender's leaf is retired, so the same
write through it is refused. -/
theorem uLoan_suspended_write_refused :
    (checkWorld uWorld
      (uLoanPre ++ [.beginLoan ⟨1⟩ ⟨3⟩ ⟨0⟩, .write ⟨1⟩ ⟨3⟩ 1 9])).isOk = false := by
  decide

/-- The loan run: allocate and write, begin a loan on the root capability, end
it, write again — accepted now that the leaf is active — and dispose. -/
def uLoanRun : List UCmd :=
  uLoanPre ++
    [.beginLoan ⟨1⟩ ⟨3⟩ ⟨0⟩, .endLoan ⟨1⟩ ⟨0⟩, .write ⟨1⟩ ⟨3⟩ 1 9, .free ⟨1⟩ ⟨4⟩]

/-- The loan run is accepted. -/
theorem uLoanRun_ok : (checkWorld uWorld uLoanRun).isOk = true := by
  decide

/-- The loan run's final world is well formed. -/
theorem uLoanRun_wf : ∃ w, checkWorld uWorld uLoanRun = .ok w ∧ w.WellFormed := by
  have hok : (checkWorld uWorld uLoanRun).isOk = true := uLoanRun_ok
  cases h : checkWorld uWorld uLoanRun with
  | error e =>
    rw [h] at hok
    cases hok
  | ok w => exact ⟨w, rfl, checkWorld_wf uWorld w uLoanRun h uWorld_wf⟩

/-- The loan run's snapshot of the pre-existing 64-byte backend. -/
def uLoanSnapshot : Option (Option (List UInt8)) :=
  match checkWorld uWorld uLoanRun with
  | .ok w => some ((w.heaps ⟨0⟩).map (fun b => b.buf))
  | .error _ => none

/-- The loan run leaves the pre-existing 64-byte backend at its initial value:
the commands act only on the freshly allocated owner. -/
theorem uLoan_snapshot :
    uLoanSnapshot = some (some (List.replicate 64 (0 : UInt8))) := by
  decide

end Cap
