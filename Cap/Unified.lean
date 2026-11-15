/-
A unified certified execution for byte writes.

This is the first slice of the review's R1: one instruction language with a value
operand, a checker that is also the interpreter over a `World`, and preservation of
the world relation. Acceptance therefore yields the executed world, not a separate
permission certificate.

Scope: writes and no-ops only. Splits, joins, loans and disposal still live in the
owner layer (`Cap.Core`, `Cap.Ledger`, `Cap.Context`) and are not yet part of this
language; that is the next slice.
-/
import Cap.World
import Cap.Backend
import Cap.Core

namespace Cap

/-- A value-carrying execution command. -/
inductive UCmd where
  | write (a : AllocId) (id : CapId) (i : Nat) (v : UInt8)
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

/-- An accepted execution preserves the world relation. -/
theorem checkWorld_rel : ∀ (w w' : World) (cs : List UCmd),
    checkWorld w cs = .ok w' → w.Rel → w'.Rel := by
  intro w w' cs
  induction cs generalizing w with
  | nil =>
    intro h hr
    simp [checkWorld] at h
    cases h
    exact hr
  | cons c cs ih =>
    intro h hr
    cases c with
    | nop =>
      simp [checkWorld] at h
      exact ih w h hr
    | write a id i v =>
      cases hw : w.writeChecked a id i v with
      | error e => simp [checkWorld, hw] at h
      | ok w'' =>
        simp [checkWorld, hw] at h
        exact ih w'' h (w.writeChecked_rel hw hr)

/-- The concrete owner: one 64-byte whole-share leaf. -/
def uOwner : Owner := Owner.init ⟨0⟩ 64 64 (by decide) ⟨1⟩ ⟨2⟩

/-- The concrete world: one 64-byte owner and its backend. -/
def uWorld : World :=
  { ctx := { owners := [uOwner], D := 64, nextAlloc := 1 },
    heaps := fun a => if a = ⟨0⟩ then some (Backend.empty 64) else none }

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
  | ok w => exact ⟨w, rfl, checkWorld_rel uWorld w uProgram h uWorld_rel⟩

end Cap
