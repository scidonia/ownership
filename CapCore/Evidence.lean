import CapCore.Context

namespace CapCore

/-- The semantic read permission: a capability with this id is current. -/
def CanRead (c : Ctx) (id : Nat) : Prop :=
  ∃ cap, c.find? id = some cap

/-- The semantic write permission: a current whole-share capability contains the
offset. -/
def CanWrite (c : Ctx) (id off : Nat) : Prop :=
  ∃ cap, c.find? id = some cap ∧ cap.q = c.D ∧
    cap.region.lo ≤ off ∧ off < cap.region.hi

theorem readAllowed_iff {c : Ctx} {id : Nat} :
    c.readAllowed id = true ↔ CanRead c id := by
  unfold Ctx.readAllowed CanRead
  cases h : c.find? id <;> simp_all

theorem canWrite_of_writeAllowed {c : Ctx} {id off : Nat}
    (h : c.writeAllowed id off = true) : CanWrite c id off := by
  unfold Ctx.writeAllowed at h
  cases hfind : c.find? id with
  | none => simp [hfind] at h
  | some cap =>
      simp [hfind] at h
      exact ⟨cap, hfind, h.1.1, h.1.2, h.2⟩

theorem canRead_of_readAllowed {c : Ctx} {id : Nat}
    (h : c.readAllowed id = true) : CanRead c id :=
  readAllowed_iff.mp h

theorem readAllowed_of_canRead {c : Ctx} {id : Nat}
    (h : CanRead c id) : c.readAllowed id = true :=
  readAllowed_iff.mpr h

end CapCore
