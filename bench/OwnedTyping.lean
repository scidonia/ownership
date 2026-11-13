/-
Fractional splitting as the context transition of the ownership judgement.

A context assigns each handle a number of shares of its unit permission, out of a
common denominator `d`. A write needs the whole unit (`d` shares); a read needs a
positive number. The split relation is the context transition of a binary rule,
`Γ h = Γ₁ h + Γ₂ h` at every handle. The arithmetic is the point: a unit context
cannot be split into two writable ones, which is why the checker's one-transfer
rule is not a syntactic convention but the shadow of the fraction.
-/
import Lean

namespace OwnedTyping

/-- A context: shares per handle, out of the denominator `d`. -/
abbrev Ctx := Nat → Nat

/-- `Γ` splits into `Γ₁` and `Γ₂`: the two subterms' shares add up to the whole. -/
def Split (Γ Γ₁ Γ₂ : Ctx) : Prop := ∀ h, Γ h = Γ₁ h + Γ₂ h

/-- A write needs the whole permission. -/
def Writable (d : Nat) (Γ : Ctx) (h : Nat) : Prop := d ≤ Γ h

/-- A read needs a positive share. -/
def Readable (Γ : Ctx) (h : Nat) : Prop := 0 < Γ h

/-- Two writable halves cannot split a unit context. -/
theorem no_two_writes {d : Nat} {Γ Γ₁ Γ₂ : Ctx} {h : Nat} (_hd : 0 < d)
    (hs : Split Γ Γ₁ Γ₂) (h1 : Writable d Γ₁ h) (h2 : Writable d Γ₂ h)
    (hΓ : Γ h = d) : False := by
  have := hs h
  unfold Writable at h1 h2
  omega

/-- A unit context split as `1 = 0 + 1` (or `1 + 0`) admits one write, not two. -/
theorem one_write {d : Nat} {Γ Γ₁ Γ₂ : Ctx} {h : Nat}
    (hs : Split Γ Γ₁ Γ₂) (_h1 : Writable d Γ₁ h) (h0 : Γ₂ h = 0) (hΓ : Γ h = d) :
    Γ₁ h = d := by
  have := hs h
  omega

/-- Two reads can share a unit context: the shares are positive, not whole. -/
theorem two_reads {Γ Γ₁ Γ₂ : Ctx} {h : Nat} (hs : Split Γ Γ₁ Γ₂)
    (h1 : Readable Γ₁ h) (h2 : Readable Γ₂ h) (hΓ : Γ h = 2) :
    Γ₁ h = 1 ∧ Γ₂ h = 1 := by
  unfold Readable at h1 h2
  have := hs h
  omega

end OwnedTyping
