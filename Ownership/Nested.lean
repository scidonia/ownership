/-
The nested take-out path: array check → take-out → extracted-element check →
recursive summary → put-back.

This is the formal counterpart of the measured `setAt` `Path.index` shape
(`checkArray=3, takeOut=5, checkElem=7, setAt=8, putBack=9`). The take-out is
modelled as a contract: the array has the element `e` in the selected slot, the
element is exclusive, and the take-out binds two fresh variables to the array
and the element. The value identity of the element is abstracted; the ownership
shape is what is proved. `TakeOutsOK` is the heap premise the checker cannot
see; the entry/initializer provides it for the concrete heap.
-/
import Ownership.Soundness

namespace Ownership
namespace Nested

inductive NCode where
  | base (c : Code)
  | takeOut (a i fst snd : Var) (e : Ref) (k : NCode)
  | putBack (a e i result : Var) (k : NCode)
  | callAt (state path x result : Var) (k : NCode)
  | ret (x : Var)

/-- No take-out in the continuation after the one modelled take-out. The
measured `setAt` `Path.index` has exactly one, so this is the fragment the
theorem covers; recursive/nested take-outs are the next extension. -/
def NoTakeOut : NCode → Prop
  | .base _ | .ret _ => True
  | .takeOut .. => False
  | .putBack _ _ _ _ k | .callAt _ _ _ _ k => NoTakeOut k

/-- The runtime premise of a take-out: the array's selected slot holds the
exclusive element `e`, and `e` is not the array itself. -/
def TakeOutOK (H : Heap) (env : Env) (a i : Var) (e : Ref) : Prop :=
  ∃ r o idx, env a = some (.ref r) ∧ env i = some (.scalar idx) ∧
    H.cells r = some o ∧ o.fields[idx]? = some (.ref e) ∧ e ≠ r

def TakeOutsOK (H : Heap) (env : Env) : NCode → Prop
  | .base _ | .ret _ => True
  | .takeOut a i _ _ e k => TakeOutOK H env a i e ∧ NoTakeOut k
  | .putBack _ _ _ _ k | .callAt _ _ _ _ k => NoTakeOut k

def runN : NCode → Env → Heap → Res
  | .base c, env, H => run c env H
  | .takeOut a i fst snd e k, env, H =>
      match env a, env i with
      | some (.ref r), some (.scalar idx) =>
          match H.cells r with
          | some o =>
              match o.fields[idx]? with
              | some (.ref e') =>
                  if e' = e then
                    let H' := H.set r { o with fields := o.fields.setIfInBounds idx (.scalar 0) }
                    runN k ((env.set fst (.ref r)).set snd (.ref e)) H'
                  else .fault H env (.badVar i) []
              | _ => .fault H env (.badVar i) []
          | none => .fault H env (.noCell r) []
      | _, _ => .fault H env (.badVar a) []
  | .putBack a e i result k, env, H =>
      match env a, env e, env i with
      | some (.ref r), some (.ref e'), some (.scalar idx) =>
          match H.cells r with
          | some o =>
              let H' := H.set r { o with fields := o.fields.set! idx (.ref e') }
              runN k (env.set result (.ref r)) H'
          | none => .fault H env (.noCell r) []
      | _, _, _ => .fault H env (.badVar a) []
  | .callAt state path x result k, env, H =>
      match env state, env path, env x with
      | some (.ref r), some (.scalar _), some (.scalar _) =>
          if H.exclusive? r then
            (runN k (env.set result (.ref r)) H).addWrite (r, true)
          else .fault H env (.notExclusive r) []
      | _, _, _ => .fault H env (.badVar state) []
  | .ret x, env, H => .done H env (env x |>.getD .erased) []

def checkN : Ctx → NCode → Option Ctx
  | c, .base code => check c code
  | c, .takeOut a i fst snd e k =>
      if c.us a = .owned ∧ c.multOf a = 1 ∧ c.us i = .scalar ∧ c.mult e = 1 then
        match c.refOf a with
        | some r =>
            if e = r then none else checkN ((c.move a fst).bindOwned snd e) k
        | none => none
      else none
  | c, .putBack a e i result k =>
      if c.us a = .owned ∧ c.multOf a = 1 ∧ c.us e = .owned ∧
          c.multOf e = 1 ∧ c.us i = .scalar ∧ e ≠ a ∧ e ≠ result then
        match c.refOf a with
        | some r => checkN ((c.move a result).setUs e .dead) k
        | none => none
      else none
  | c, .callAt state path x result k =>
      if c.us state = .owned ∧ c.multOf state = 1 ∧ c.us path = .scalar ∧ c.us x = .scalar then
        match c.refOf state with
        | some r => checkN (c.move state result) k
        | none => none
      else none
  | c, .ret x => if c.us x = .owned ∨ c.us x = .scalar then some c else none

theorem checkN_takeOut (c : Ctx) (a i fst snd : Var) (e : Ref) (k : NCode) (r : Ref)
    (hx : c.us a = .owned ∧ c.multOf a = 1 ∧ c.us i = .scalar ∧ c.mult e = 1)
    (hr : c.refOf a = some r) (hne : e ≠ r) :
    checkN c (.takeOut a i fst snd e k) = checkN ((c.move a fst).bindOwned snd e) k := by
  simp [checkN, hx, hr, hne]

theorem checkN_putBack (c : Ctx) (a e i result : Var) (k : NCode) (r : Ref)
    (hx : c.us a = .owned ∧ c.multOf a = 1 ∧ c.us e = .owned ∧
          c.multOf e = 1 ∧ c.us i = .scalar ∧ e ≠ a ∧ e ≠ result)
    (hr : c.refOf a = some r) :
    checkN c (.putBack a e i result k) = checkN ((c.move a result).setUs e .dead) k := by
  simp [checkN, hx, hr]

theorem checkN_callAt (c : Ctx) (state path x result : Var) (k : NCode) (r : Ref)
    (hx : c.us state = .owned ∧ c.multOf state = 1 ∧ c.us path = .scalar ∧ c.us x = .scalar)
    (hr : c.refOf state = some r) :
    checkN c (.callAt state path x result k) = checkN (c.move state result) k := by
  simp [checkN, hx, hr]

theorem NoTakeOut.toTakeOutsOK {c : NCode} {H : Heap} {env : Env}
    (h : NoTakeOut c) : TakeOutsOK H env c := by
  induction c with
  | base _ => trivial
  | ret _ => trivial
  | takeOut a i fst snd e k => exact False.elim h
  | putBack a e i result k ih => exact h
  | callAt state path x result k ih => exact h

/-- Soundness of the nested checker, under the take-out heap premise. -/
theorem checkN_sound {c : NCode} {ctx ctx' : Ctx} {H : Heap} {env : Env}
    (hc : checkN ctx c = some ctx') (hi : Inv H env ctx)
    (hok : TakeOutsOK H env c) :
    ∃ H' env' v ws, runN c env H = .done H' env' v ws ∧
      (∀ w ∈ ws, w.2 = true) ∧ Inv H' env' ctx' := by
  induction c generalizing ctx ctx' H env with
  | base code =>
      simp only [checkN] at hc
      obtain ⟨H', env', v, ws, hrun, hws, hinv⟩ := check_sound hc hi
      exact ⟨H', env', v, ws, by simpa [runN] using hrun, hws, hinv⟩
  | takeOut a i fst snd e k ih =>
      by_cases hx : ctx.us a = .owned ∧ ctx.multOf a = 1 ∧
          ctx.us i = .scalar ∧ ctx.mult e = 1
      · have hx_all := hx
        obtain ⟨ha, hm, hi_us, he⟩ := hx
        cases hr : ctx.refOf a with
        | none => simp [checkN, hr] at hc
        | some r =>
            by_cases hne : e = r
            · simp [checkN, hr, hne] at hc
            · have hc' : checkN ((ctx.move a fst).bindOwned snd e) k = some ctx' := by
                simpa [checkN_takeOut _ _ _ _ _ _ _ _ hx_all hr hne] using hc
              obtain ⟨⟨r', o, idx, ha', hi', hcell, hfield, hne'⟩, hno⟩ := hok
              have henv_a : env a = some (.ref r) := (hi.owned a r ha hr).1
              have hr' : r' = r := by
                rw [henv_a] at ha'
                cases ha'
                rfl
              cases hr'
              have hidx : env i = some (.scalar idx) := hi'
              have hmul : ctx.mult e = 1 := he
              have hi_move : Inv H (env.set fst (.ref r)) (ctx.move a fst) :=
                Inv.move hi ha hr
              have hi_bind : Inv H ((env.set fst (.ref r)).set snd (.ref e))
                  ((ctx.move a fst).bindOwned snd e) :=
                Inv.bindOwned hi_move hmul
              let H' := H.set r { o with fields := o.fields.setIfInBounds idx (.scalar 0) }
              have hi_bind' : Inv H' ((env.set fst (.ref r)).set snd (.ref e))
                  ((ctx.move a fst).bindOwned snd e) :=
                Inv.setFields hi_bind hcell
              obtain ⟨H'', env'', v, ws, hrun, hws, hinv⟩ :=
                ih (ctx := (ctx.move a fst).bindOwned snd e) (ctx' := ctx')
                   (H := H') (env := (env.set fst (.ref r)).set snd (.ref e))
                   hc' hi_bind' (NoTakeOut.toTakeOutsOK hno)
              have hrun' : runN k ((env.set fst (.ref r)).set snd (.ref e)) H' =
                  .done H'' env'' v ws := hrun
              refine ⟨H'', env'', v, ws, ?_, hws, hinv⟩
              simp only [runN, henv_a, hidx, hcell, hfield]
              change runN k ((env.set fst (.ref r)).set snd (.ref e)) H' =
                .done H'' env'' v ws
              exact hrun' 
      · simp [checkN, hx] at hc
  | putBack a e i result k ih =>
      by_cases hx : ctx.us a = .owned ∧ ctx.multOf a = 1 ∧ ctx.us e = .owned ∧
          ctx.multOf e = 1 ∧ ctx.us i = .scalar ∧ e ≠ a ∧ e ≠ result
      · have hx_all := hx
        obtain ⟨ha, hm, he_us, he_m, hi_us, hne_a, hne_res⟩ := hx
        have hno : NoTakeOut k := by simpa [TakeOutsOK] using hok
        cases hr : ctx.refOf a with
        | none => simp [checkN, hr] at hc
        | some r =>
            have hc' : checkN ((ctx.move a result).setUs e .dead) k = some ctx' := by
              simpa [checkN_putBack _ _ _ _ _ _ _ hx_all hr] using hc
            obtain ⟨re, hre, hmul_e⟩ := Ctx.multOf_eq_one he_m
            have henv_a : env a = some (.ref r) := (hi.owned a r ha hr).1
            have henv_e : env e = some (.ref re) := (hi.owned e re he_us hre).1
            obtain ⟨idx, hidx⟩ := hi.scalar i hi_us
            obtain ⟨o, hcell⟩ := hi.cell_of_ref (Or.inl ha) hr
            let H' := H.set r { o with fields := o.fields.setIfInBounds idx (.ref re) }
            have hi_move : Inv H (env.set result (.ref r)) (ctx.move a result) :=
              Inv.move hi ha hr
            have hi_fields : Inv H' (env.set result (.ref r)) (ctx.move a result) :=
              Inv.setFields hi_move hcell
            have hi_dead : Inv H' (env.set result (.ref r))
                ((ctx.move a result).setUs e .dead) := Inv.setDead hi_fields
            obtain ⟨H'', env'', v, ws, hrun, hws, hinv⟩ :=
              ih (ctx := (ctx.move a result).setUs e .dead) (ctx' := ctx')
                 (H := H') (env := env.set result (.ref r)) hc' hi_dead
                 (NoTakeOut.toTakeOutsOK hno)
            refine ⟨H'', env'', v, ws, ?_, hws, hinv⟩
            simp only [runN, henv_a, henv_e, hidx, hcell]
            change runN k (env.set result (.ref r)) H' = .done H'' env'' v ws
            exact hrun
      · simp [checkN, hx] at hc
  | callAt state path x result k ih =>
      by_cases hx : ctx.us state = .owned ∧ ctx.multOf state = 1 ∧
          ctx.us path = .scalar ∧ ctx.us x = .scalar
      · have hx_all := hx
        obtain ⟨hs, hm, hp, hxus⟩ := hx
        have hno : NoTakeOut k := by simpa [TakeOutsOK] using hok
        cases hr : ctx.refOf state with
        | none => simp [checkN, hr] at hc
        | some r =>
            have hc' : checkN (ctx.move state result) k = some ctx' := by
              simpa [checkN_callAt _ _ _ _ _ _ _ hx_all hr] using hc
            have henv_s : env state = some (.ref r) := (hi.owned state r hs hr).1
            obtain ⟨_, hp'⟩ := hi.scalar path hp
            obtain ⟨_, hx'⟩ := hi.scalar x hxus
            have hmul : ctx.mult r = 1 := by
              simpa [Ctx.multOf, hr] using hm
            have hex : Heap.Exclusive H r := hi.exclusive hmul
            have htrue : H.exclusive? r = true := (Heap.exclusive?_eq_true).mpr hex
            have hi_move : Inv H (env.set result (.ref r)) (ctx.move state result) :=
              Inv.move hi hs hr
            obtain ⟨H'', env'', v, ws, hrun, hws, hinv⟩ :=
              ih (ctx := ctx.move state result) (ctx' := ctx')
                 (H := H) (env := env.set result (.ref r)) hc' hi_move
                 (NoTakeOut.toTakeOutsOK hno)
            refine ⟨H'', env'', v, (r, true) :: ws, ?_, ?_, hinv⟩
            · simp [runN, henv_s, hp', hx', htrue, Res.addWrite]
              exact congrArg (fun res => res.addWrite (r, true)) hrun
            · intro w hw
              simp only [List.mem_cons] at hw
              rcases hw with rfl | hw
              · rfl
              · exact hws w hw
      · simp [checkN, hx] at hc
  | ret x =>
      by_cases hx : ctx.us x = .owned ∨ ctx.us x = .scalar
      · simp only [checkN, hx, if_true] at hc
        have hctx : ctx' = ctx := by simpa using hc.symm
        subst hctx
        exact ⟨H, env, env x |>.getD .erased, [], rfl, by simp, hi⟩
      · simp [checkN, hx] at hc

end Nested
end Ownership
