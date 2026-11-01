/-
Environment-side ownership accounting for the checker's context.

The model's `Inv` relates the heap count to `Ctx.mult`, but it does not count the
owning variables in the environment. `OwnersAccounted` supplies the missing
environment-side fact for the count-one reading of the designated write:

* a reference with multiplicity zero has no owning variable;
* a reference with multiplicity one has at most one owning variable.

The predicate is not derivable from `Inv`: `alias_not_accounted` shows the
two-owner configuration produced by `Ctx.bindOwned` violates it even though the
raw `Inv` is preserved. The preservation lemmas below therefore carry the
preconditions the checker operations need; they do not silently assume the
desired exclusivity. The heap incoming-edge and runtime-count side remains an
implementation assumption, not a theorem of this module.
-/
import Ownership.Runner

namespace Ownership

/-- The environment-side count-one accounting fact. -/
def OwnersAccounted (c : Ctx) : Prop :=
  (∀ r x, c.mult r = 0 → c.us x = .owned → c.refOf x = some r → False) ∧
    (∀ r, c.mult r = 1 → ∀ x y,
      c.us x = .owned → c.us y = .owned →
        c.refOf x = some r → c.refOf y = some r → x = y)

namespace OwnersAccounted

/-- Setting a variable to a non-owning use preserves the accounting. -/
theorem setUs {c : Ctx} {x : Var} {u : U}
    (h : OwnersAccounted c) (hu : u ≠ .owned) :
    OwnersAccounted (c.setUs x u) := by
  constructor
  · intro r z hm hz hr
    by_cases hzx : z = x
    · subst z
      rw [Ctx.setUs_self] at hz
      exact absurd hz hu
    · exact h.1 r z (by simpa [Ctx.setUs] using hm)
        (by simpa [Ctx.setUs, hzx] using hz)
        (by simpa [Ctx.setUs, hzx] using hr)
  · intro r hm a b ha hb hra hrb
    apply h.2 r
    · simpa [Ctx.setUs] using hm
    · by_cases hax : a = x
      · subst a
        rw [Ctx.setUs_self] at ha
        exfalso
        exact absurd ha hu
      · simpa [Ctx.setUs, hax] using ha
    · by_cases hbx : b = x
      · subst b
        rw [Ctx.setUs_self] at hb
        exfalso
        exact absurd hb hu
      · simpa [Ctx.setUs, hbx] using hb
    · by_cases hax : a = x
      · subst a
        simpa using hra
      · simpa [Ctx.setUs, hax] using hra
    · by_cases hbx : b = x
      · subst b
        simpa using hrb
      · simpa [Ctx.setUs, hbx] using hrb

/-- Binding a fresh owned variable preserves the accounting only when the target
has no existing owner. The checker's take-out has to establish that premise;
`c.mult e = 1` alone does not imply it. -/
theorem bindOwned {c : Ctx} {x : Var} {e : Ref}
    (h : OwnersAccounted c) (he : c.mult e = 1)
    (hno : ∀ y, c.us y = .owned → c.refOf y = some e → False) :
    OwnersAccounted (c.bindOwned x e) := by
  constructor
  · intro r z hm hz hr
    by_cases hzx : z = x
    · subst z
      rw [Ctx.bindOwned_us_self] at hz
      rw [Ctx.bindOwned_refOf_self] at hr
      have her : e = r := Option.some.inj hr
      subst her
      have hm0 : c.mult e = 0 := by simpa [Ctx.bindOwned] using hm
      rw [he] at hm0
      omega
    · exact h.1 r z (by simpa [Ctx.bindOwned] using hm)
        (by simpa [Ctx.bindOwned, hzx] using hz)
        (by simpa [Ctx.bindOwned, hzx] using hr)
  · intro r hm a b ha hb hra hrb
    by_cases hax : a = x
    · subst a
      by_cases hbx : b = x
      · subst b; rfl
      · exfalso
        rw [Ctx.bindOwned_refOf_self] at hra
        have her : e = r := Option.some.inj hra
        subst her
        have hb' : c.us b = .owned := by
          simpa [Ctx.bindOwned, hbx] using hb
        have hrb' : c.refOf b = some e := by
          simpa [Ctx.bindOwned, hbx] using hrb
        exact hno b hb' hrb'
    · by_cases hbx : b = x
      · subst b
        exfalso
        rw [Ctx.bindOwned_refOf_self] at hrb
        have her : e = r := Option.some.inj hrb
        subst her
        have ha' : c.us a = .owned := by
          simpa [Ctx.bindOwned, hax] using ha
        have hra' : c.refOf a = some e := by
          simpa [Ctx.bindOwned, hax] using hra
        exact hno a ha' hra'
      · exact h.2 r (by simpa [Ctx.bindOwned] using hm) a b
          (by simpa [Ctx.bindOwned, hax] using ha)
          (by simpa [Ctx.bindOwned, hbx] using hb)
          (by simpa [Ctx.bindOwned, hax] using hra)
          (by simpa [Ctx.bindOwned, hbx] using hrb)

/-- An increment cannot create a new owner; it preserves the accounting. -/
theorem inc {c : Ctx} {r : Ref} {n : Nat} (h : OwnersAccounted c) :
    OwnersAccounted (c.inc r n) := by
  constructor
  · intro r' z hm hz hr
    by_cases hrr : r' = r
    · subst r'
      have hm0 : c.mult r = 0 := by
        have hzero : c.mult r + n = 0 := by simpa [Ctx.inc] using hm
        omega
      exact h.1 r z hm0 (by simpa [Ctx.inc] using hz) (by simpa [Ctx.inc] using hr)
    · exact h.1 r' z (by simpa [Ctx.inc, hrr] using hm)
        (by simpa [Ctx.inc] using hz) (by simpa [Ctx.inc] using hr)
  · intro r' hm a b ha hb hra hrb
    by_cases hrr : r' = r
    · subst r'
      have hm1 : c.mult r + n = 1 := by simpa [Ctx.inc] using hm
      by_cases hn : n = 0
      · subst n
        have hmr : c.mult r = 1 := by omega
        exact h.2 r hmr a b
          (by simpa [Ctx.inc] using ha) (by simpa [Ctx.inc] using hb)
          (by simpa [Ctx.inc] using hra) (by simpa [Ctx.inc] using hrb)
      · have hmr : c.mult r = 0 := by omega
        exact (h.1 r a hmr (by simpa [Ctx.inc] using ha)
          (by simpa [Ctx.inc] using hra)).elim
    · exact h.2 r' (by simpa [Ctx.inc, hrr] using hm) a b
        (by simpa [Ctx.inc] using ha) (by simpa [Ctx.inc] using hb)
        (by simpa [Ctx.inc] using hra) (by simpa [Ctx.inc] using hrb)

/-- A decrement preserves the accounting only when the decremented reference has
at most one owner other than the consumed variable. `n < c.mult r` alone does not
imply that; the checker's `dec` rule has to carry the side condition. -/
theorem dec {c : Ctx} {x : Var} {r : Ref} {n : Nat}
    (h : OwnersAccounted c) (_hx : c.us x = .owned)
    (hr : c.refOf x = some r) (hn : n < c.mult r)
    (hother : ∀ a b, a ≠ x → b ≠ x →
      c.us a = .owned → c.us b = .owned →
        c.refOf a = some r → c.refOf b = some r → a = b) :
    OwnersAccounted ((c.dec r n).setUs x .dead) := by
  constructor
  · intro r' z hm hz hr'
    by_cases hrr : r' = r
    · subst r'
      -- The decremented reference keeps positive multiplicity.
      have hm0 : c.mult r - n = 0 := by simpa [Ctx.dec] using hm
      have hpos : 0 < c.mult r - n := Nat.sub_pos_of_lt hn
      omega
    · have hm' : c.mult r' = 0 := by
        simpa [Ctx.dec, hrr] using hm
      by_cases hzx : z = x
      · subst z
        rw [Ctx.setUs_self] at hz
        simp at hz
      · exact h.1 r' z hm' (by simpa [Ctx.setUs, hzx] using hz)
          (by simpa [Ctx.dec, hrr] using hr')
  · intro r' hm a b ha hb hra hrb
    by_cases hrr : r' = r
    · subst r'
      simp [Ctx.dec] at hm
      apply hother a b
      · intro hax; subst a; rw [Ctx.setUs_self] at ha; simp at ha
      · intro hbx; subst b; rw [Ctx.setUs_self] at hb; simp at hb
      · by_cases hax : a = x
        · subst a; rw [Ctx.setUs_self] at ha; simp at ha
        · simpa [Ctx.setUs, hax] using ha
      · by_cases hbx : b = x
        · subst b; rw [Ctx.setUs_self] at hb; simp at hb
        · simpa [Ctx.setUs, hbx] using hb
      · by_cases hax : a = x
        · subst a; simpa using hr
        · simpa [Ctx.dec] using hra
      · by_cases hbx : b = x
        · subst b; simpa using hr
        · simpa [Ctx.dec] using hrb
    · have hm' : c.mult r' = 1 := by
        simpa [Ctx.dec, hrr] using hm
      apply h.2 r' hm' a b
      · by_cases hax : a = x
        · subst a; rw [Ctx.setUs_self] at ha; simp at ha
        · simpa [Ctx.setUs, hax] using ha
      · by_cases hbx : b = x
        · subst b; rw [Ctx.setUs_self] at hb; simp at hb
        · simpa [Ctx.setUs, hbx] using hb
      · by_cases hax : a = x
        · subst a
          exfalso
          have hxr : c.refOf x = some r' := by simpa [Ctx.setUs] using hra
          exact hrr (Option.some.inj (by rw [hr] at hxr; exact hxr)).symm
        · simpa [Ctx.dec, hrr] using hra
      · by_cases hbx : b = x
        · subst b
          exfalso
          have hxr : c.refOf x = some r' := by simpa [Ctx.setUs] using hrb
          exact hrr (Option.some.inj (by rw [hr] at hxr; exact hxr)).symm
        · simpa [Ctx.dec, hrr] using hrb

/-- Moving a handle from `x` to `y` preserves the accounting when `x` owns it. -/
theorem move {c : Ctx} {x y : Var}
    (h : OwnersAccounted c) (hx : c.us x = .owned) :
    OwnersAccounted (c.move x y) := by
  constructor
  · intro r z hm hz hr
    by_cases hzy : z = y
    · subst z
      rw [Ctx.move_us_y] at hz
      rw [Ctx.move_refOf_y] at hr
      exact h.1 r x (by simpa [Ctx.move] using hm) hx hr
    · by_cases hzx : z = x
      · subst z
        simp [Ctx.move, hzy] at hz
      · exact h.1 r z (by simpa [Ctx.move] using hm)
          (by simpa [Ctx.move, hzy, hzx] using hz)
          (by simpa [Ctx.move, hzy] using hr)
  · intro r hm a b ha hb hra hrb
    by_cases hay : a = y
    · subst a
      by_cases hby : b = y
      · subst b; rfl
      · by_cases hbx : b = x
        · subst b
          simp [Ctx.move, hby] at hb
        · exfalso
          rw [Ctx.move_refOf_y] at hra
          have hb' : c.us b = .owned := by
            simpa [Ctx.move, hby, hbx] using hb
          have hrb' : c.refOf b = some r := by
            simpa [Ctx.move, hby] using hrb
          exact hbx (h.2 r (by simpa [Ctx.move] using hm) x b hx hb' hra hrb').symm
    · by_cases hby : b = y
      · subst b
        by_cases hax : a = x
        · subst a
          simp [Ctx.move, hay] at ha
        · exfalso
          rw [Ctx.move_refOf_y] at hrb
          have ha' : c.us a = .owned := by
            simpa [Ctx.move, hay, hax] using ha
          have hra' : c.refOf a = some r := by
            simpa [Ctx.move, hay] using hra
          exact hax (h.2 r (by simpa [Ctx.move] using hm) x a hx ha' hrb hra').symm
      · by_cases hax : a = x
        · subst a
          simp [Ctx.move, hay, hby] at ha
        · by_cases hbx : b = x
          · subst b
            simp [Ctx.move, hay, hby] at hb
          · exact h.2 r (by simpa [Ctx.move] using hm) a b
              (by simpa [Ctx.move, hay, hax] using ha)
              (by simpa [Ctx.move, hby, hbx] using hb)
              (by simpa [Ctx.move, hay] using hra)
              (by simpa [Ctx.move, hby] using hrb)

end OwnersAccounted


/-- Heap edges into `r`, counted over the live reference range. -/
def IncomingCount (H : Heap) (r : Ref) : Nat :=
  ((List.range H.next).map fun q =>
    match H.cells q with
    | some o => (o.fields.toList.filter (fun v => v = .ref r)).length
    | none => 0).sum

/-- Owning environment variables in the supplied support list. -/
def EnvOwnerCount (c : Ctx) (vars : List Var) (r : Ref) : Nat :=
  (vars.filter (fun x => c.us x = .owned ∧ c.refOf x = some r)).length

/-- The heap/runtime count side of the accounting: the object's count is its
incoming heap edges plus the owning environment variables. This is the
implementation assumption the model does not prove; it is stated, not hidden. -/
def CountFidelity (H : Heap) (c : Ctx) (vars : List Var) : Prop :=
  ∀ r, H.rc r = IncomingCount H r + EnvOwnerCount c vars r


/-- The alias configuration is not accounted: `Inv` preserves it, but
`OwnersAccounted` rejects it. -/
theorem alias_not_accounted (n : Nat) :
    ¬ OwnersAccounted
        ((Runner.initCtx (Runner.initHeap n).1).bindOwned 1 (Runner.initHeap n).1) := by
  intro h
  let r : Ref := (Runner.initHeap n).1
  have hm : (Runner.initCtx r).mult r = 1 := by simp [Runner.initCtx]
  have hpost : ((Runner.initCtx r).bindOwned 1 r).mult r = 1 := by
    simpa [Ctx.bindOwned] using hm
  have h01 : (0 : Var) = 1 := h.2 r hpost 0 1
    (by simp [Ctx.bindOwned, Runner.initCtx])
    (by simp [Ctx.bindOwned])
    (by
      rw [Ctx.bindOwned_refOf_other]
      · simp [Runner.initCtx]
        rfl
      · decide)
    (by
      rw [Ctx.bindOwned_refOf_self])
  exact Nat.zero_ne_one h01

end Ownership
