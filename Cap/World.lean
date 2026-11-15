/-
A world of owners and mutable backends.

The heap map is a function from allocations to backends, which keeps the update and
frame facts small. `World.Rel` combines the context invariant with a length
agreement: every owner has a backend at its allocation whose buffer length is the
owner's length. Write dispatch takes the owner's `Writable` guard as a proof;
disposal is dispatched through the context's disposal check and clears the backend.

This is a pure world of backends with a length/coverage relation. It is not an
interpreter (see `Cap.Exec`), not an FFI path and not a concurrency claim.
-/
import Cap.Context
import Cap.Backend

namespace Cap

structure World where
  ctx : Ctx
  heaps : AllocId → Option Backend

def World.Rel (w : World) : Prop :=
  Ctx.Realizes w.ctx ∧
    ∀ o ∈ w.ctx.owners, ∃ b, w.heaps o.alloc = some b ∧ b.buf.length = o.len

/-- Write through the owner guard, replacing the backend at the allocation. The
caller supplies the guard for the owner found at `a`. -/
def World.write? (w : World) (a : AllocId) (id : CapId) (i : Nat) (v : UInt8)
    (_hg : ∀ o, w.ctx.findOwner? a = some o → o.Writable w.ctx.D id i) : Option World :=
  match w.ctx.findOwner? a with
  | none => none
  | some o =>
    match w.heaps a with
    | none => none
    | some b =>
      match b.write i v with
      | none => none
      | some b' => some { w with heaps := fun x => if x = a then some b' else w.heaps x }

/-- Disposal through the recorded disposal capability; the backend is cleared. -/
def World.freeWith? (w : World) (a : AllocId) (d : CapId) : Option World :=
  match w.ctx.freeWith? a d with
  | none => none
  | some ctx' => some { ctx := ctx', heaps := fun x => if x = a then none else w.heaps x }

theorem World.write_rel {w w' : World} {a : AllocId} {id : CapId} {i : Nat}
    {v : UInt8} {hg : ∀ o, w.ctx.findOwner? a = some o → o.Writable w.ctx.D id i}
    (h : w.write? a id i v hg = some w') (hr : w.Rel) : w'.Rel := by
  unfold World.write? at h
  cases hf : w.ctx.findOwner? a with
  | none => simp [hf] at h
  | some o =>
    cases hb : w.heaps a with
    | none => simp [hf, hb] at h
    | some b =>
      cases hbw : b.write i v with
      | none => simp [hf, hb, hbw] at h
      | some b' =>
        simp [hf, hb, hbw] at h
        cases h
        refine ⟨hr.1, ?_⟩
        intro o' ho'
        obtain ⟨b0, hb0, hlen⟩ := hr.2 o' ho'
        by_cases hx : o'.alloc = a
        · have hb0a : w.heaps a = some b0 := by simpa [hx] using hb0
          have hb_eq : b0 = b := by
            rw [hb] at hb0a
            exact (Option.some.inj hb0a).symm
          subst hb_eq
          refine ⟨b', by simp [hx], ?_⟩
          rw [Backend.write_preserves_len hbw]
          exact hlen
        · refine ⟨b0, ?_, hlen⟩
          simp [hx, hb0]

theorem World.freeWith_rel {w w' : World} {a : AllocId} {d : CapId}
    (h : w.freeWith? a d = some w') (hr : w.Rel) : w'.Rel := by
  unfold World.freeWith? at h
  cases hc : w.ctx.freeWith? a d with
  | none => simp [hc] at h
  | some ctx' =>
    simp [hc] at h
    cases h
    have hrel : Ctx.Realizes ctx' := Ctx.freeWith?_realizes hc hr.1
    unfold Ctx.freeWith? at hc
    cases hf : w.ctx.findOwner? a with
    | none => simp [hf] at hc
    | some o =>
      by_cases hd : o.disposal = d
      · simp [hf, hd] at hc
        cases hc
        refine ⟨hrel, ?_⟩
        intro o' ho'
        dsimp [Ctx.free] at ho'
        obtain ⟨hmem, hne⟩ := List.mem_filter.mp ho'
        have hne' : ¬ o'.alloc = a := of_decide_eq_true hne
        obtain ⟨b0, hb0, hlen⟩ := hr.2 o' hmem
        refine ⟨b0, ?_, hlen⟩
        simp [hne', hb0]
      · simp [hf, hd] at hc

end Cap
