/-
Access predicates: the evidence a certified read or write carries.

`Ctx.CanWrite Γ a id i` and `Ctx.CanRead Γ a id i` say that, in context `Γ`, the
capability `id` may act at index `i` of allocation `a`: the owner is found, and
the ledger's guard (or readability predicate) accepts. A world that realises the
context and satisfies the invariant supplies the backing allocation and bounds,
so a certified access cannot be refused, and two certified writes at one byte
name the same capability.
-/
import Cap.Ledger
import Cap.Share
import Cap.Core
import Cap.Invariant
import Cap.Exclusivity
import Cap.WorldInvariant

namespace Cap

/-- The capability `id` may write index `i` of allocation `a` in context `Γ`. -/
def Ctx.CanWrite (Γ : Ctx) (a : AllocId) (id : CapId) (i : Nat) : Prop :=
  ∃ o, Γ.findOwner? a = some o ∧ o.writableB Γ.D id i = true

/-- The capability `id` may read index `i` of allocation `a` in context `Γ`. -/
def Ctx.CanRead (Γ : Ctx) (a : AllocId) (id : CapId) (i : Nat) : Prop :=
  ∃ o, Γ.findOwner? a = some o ∧ o.Readable id i

/-- A certified read cannot be refused: a matching world has the backend byte. -/
theorem World.read_succeeds {w : World} {Γ : Ctx} {a : AllocId} {id : CapId}
    {i : Nat} (h : Ctx.CanRead Γ a id i) (hΓ : w.ctx = Γ) (hwf : w.WellFormed) :
    ∃ v, (w.heaps a).bind (·.read i) = some v := by
  obtain ⟨o, hfind, c, hfc, _hact, _hq, _hlo, hhi⟩ := h
  rw [← hΓ] at hfind
  have hmem : o ∈ w.ctx.owners := List.mem_of_find?_eq_some hfind
  have hown : o.WellFormed w.ctx.D := hwf.1.2.1 o hmem
  have hle : c.hi ≤ o.len := (hown.2.1 id c hfc).2
  obtain ⟨b, hb, hlen⟩ := hwf.2.2 a o hfind
  refine ⟨b.buf[i], ?_⟩
  rw [hb]
  show (b.read i) = some b.buf[i]
  rw [Backend.read, List.getElem?_eq_getElem (by omega)]

/-- Two certified writes at one byte of one allocation name the same capability:
the program-level form of write exclusivity. -/
theorem World.no_two_canwrite {w : World} {a : AllocId} {id1 id2 : CapId} {i : Nat}
    (hwf : w.WellFormed)
    (h1 : Ctx.CanWrite w.ctx a id1 i) (h2 : Ctx.CanWrite w.ctx a id2 i) :
    id1 = id2 := by
  obtain ⟨o1, hf1, hw1⟩ := h1
  obtain ⟨o2, hf2, hw2⟩ := h2
  have hmem2 : o2 ∈ w.ctx.owners := List.mem_of_find?_eq_some hf2
  have ho2a : o2.alloc = a := by
    have h := hf2
    unfold Ctx.findOwner? at h
    have hs := List.find?_some h
    simpa using (of_decide_eq_true hs)
  have ho : o2 = o1 := hwf.2.1 a o1 o2 hf1 hmem2 ho2a
  rw [ho] at hw2
  exact Owner.no_two_writable (hwf.1.2.1 o1 (List.mem_of_find?_eq_some hf1)) hw1 hw2

end Cap
