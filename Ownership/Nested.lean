/-
The nested take-out path: array check → take-out → extracted-element check →
recursive summary → put-back.

This is the formal counterpart of the measured `setAt` `Path.index` shape
(`checkArray=3, takeOut=5, checkElem=7, setAt=8, putBack=9`). The take-out is
modelled as a contract: the array has the element `e` in the selected slot, the
element is exclusive, and the take-out binds two *distinct* fresh variables to
the array and the element. The value identity of the element is abstracted; the
ownership shape is what is proved.

The checker keeps an extraction frame stack. Each take-out records the array,
the index variable and the element it opened, and a put-back must match the
innermost open frame exactly before that frame is popped. A second take-out from
an array that already has an open frame (per array, not per slot: reopening an
array before restoring it is outside one recursive path), a restoration into a
different array, and a straight-line block while a frame is open are refused.

The exit is conservative. With no open frame an owned or scalar handle may be
returned. With exactly one open frame only that frame's extracted element may
return, and only as an owned handle; the emptied parent, any other value, and a
deeper stack of open frames are refused until the frames are restored. Returning
the parent would hand back an array whose selected slot still holds the
take-out's placeholder, which is not the array the caller left.

`TakeOutsOK` is the heap premise the checker cannot see. It is indexed by the
state each step reaches, so a nested take-out's obligation is stated on the heap
its parent take-out left and a put-back's on the heap the nested take-out left.
The entry/initializer provides it for the concrete heap.

The module states the ownership shape of this modelled fragment. It is not a
certificate for the emitted `setAt` LCNF; that link remains the build-checked
shape and digest. The one-pair `Path.left/right` reset/reuse branches are a
separate model in `Ownership/Pair.lean`; generic joins, callbacks and the
emitted-AST link remain outside this module.
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

/-- An open extraction frame: the array whose selected slot a take-out emptied,
the index variable that names that slot, and the extracted element. The checker
keeps a stack of frames, innermost first. -/
structure Frame where
  arr : Ref
  idx : Var
  elem : Ref
  deriving DecidableEq, Repr

/-- Is `r` the array of an open frame? The checker refuses any take-out from an
array that already has an open frame. This is per array, not per slot: reopening
an array before restoring it is outside one recursive path, so the checker
rejects it instead of tracking per-slot state. -/
def openRef : List Frame → Ref → Bool
  | [], _ => false
  | f :: fs, r => if f.arr = r then true else openRef fs r

/-- The runtime premise of a single take-out: the array's selected slot holds the
element `e`, and `e` is not the array itself. -/
def TakeOutOK (H : Heap) (env : Env) (a i : Var) (e : Ref) : Prop :=
  ∃ r o idx, env a = some (.ref r) ∧ env i = some (.scalar idx) ∧
    H.cells r = some o ∧ o.fields[idx]? = some (.ref e) ∧ e ≠ r

/-- The state-indexed heap premise: every step actually reached must find what
the runtime will read on the heap and environment the previous step left. A
nested take-out's obligation is thus stated after its parent's slot holds a
scalar, and a put-back's after the nested slot was emptied; `TakeOutOK` is the
one-step instance. The checker cannot see these facts; the entry/initializer
provides them for the concrete heap. -/
def TakeOutsOK (H : Heap) (env : Env) : NCode → Prop
  | .base _ | .ret _ => True
  | .takeOut a i fst snd e k =>
      ∃ r o idx, env a = some (.ref r) ∧ env i = some (.scalar idx) ∧
        H.cells r = some o ∧ o.fields[idx]? = some (.ref e) ∧ e ≠ r ∧
        TakeOutsOK (H.set r { o with fields := o.fields.setIfInBounds idx (.scalar 0) })
          ((env.set fst (.ref r)).set snd (.ref e)) k
  | .putBack a e i result k =>
      ∃ r re o idx, env a = some (.ref r) ∧ env e = some (.ref re) ∧
        env i = some (.scalar idx) ∧ H.cells r = some o ∧
        TakeOutsOK (H.set r { o with fields := o.fields.set! idx (.ref re) })
          (env.set result (.ref r)) k
  | .callAt state path x result k =>
      ∃ r, env state = some (.ref r) ∧ H.exclusive? r = true ∧
        TakeOutsOK H (env.set result (.ref r)) k

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

/-- The checker's worker. `fs` is the extraction frame stack, innermost first;
the client-facing `checkN` starts it empty. A straight-line block is admitted
only with no open frame, because `check` cannot see which array a write names.
A take-out binds the array and the element to two different variables, and the
exit admits only the return value the open frames allow. -/
def checkNF (c : Ctx) (fs : List Frame) : NCode → Option Ctx
  | .base code => if fs = [] then check c code else none
  | .takeOut a i fst snd e k =>
      if c.us a = .owned ∧ c.multOf a = 1 ∧ c.us i = .scalar ∧ c.mult e = 1 ∧
          c.us fst = .dead ∧ c.us snd = .dead ∧ fst ≠ snd then
        match c.refOf a with
        | some r =>
            if e = r then none
            else if openRef fs r then none
            else checkNF ((c.move a fst).bindOwned snd e)
                   ({ arr := r, idx := i, elem := e } :: fs) k
        | none => none
      else none
  | .putBack a e i result k =>
      if c.us a = .owned ∧ c.multOf a = 1 ∧ c.us e = .owned ∧ c.multOf e = 1 ∧
          c.us i = .scalar ∧ c.us result = .dead ∧ e ≠ a ∧ e ≠ result then
        match c.refOf a, c.refOf e, fs with
        | some r, some re, f :: rest =>
            if f.arr = r ∧ f.idx = i ∧ f.elem = re then
              checkNF ((c.move a result).setUs e .dead) rest k
            else none
        | _, _, _ => none
      else none
  | .callAt state path x result k =>
      if c.us state = .owned ∧ c.multOf state = 1 ∧ c.us path = .scalar ∧
          c.us x = .scalar ∧ c.us result = .dead then
        match c.refOf state with
        | some r =>
            if openRef fs r then none
            else checkNF (c.move state result) fs k
        | none => none
      else none
  | .ret x =>
      match fs with
      | [] => if c.us x = .owned ∨ c.us x = .scalar then some c else none
      | [f] => if c.us x = .owned ∧ c.refOf x = some f.elem then some c else none
      | _ => none

/-- The client-facing checker: the program is admissible when the whole block is
checked from an empty frame stack. A program that restores every frame exits
through the ordinary rule; a program that ends with one open frame may return
only that frame's extracted element, and a deeper open stack must be restored
before the exit. -/
def checkN (c : Ctx) (code : NCode) : Option Ctx := checkNF c [] code

theorem checkNF_takeOut (c : Ctx) (fs : List Frame) (a i fst snd : Var) (e : Ref)
    (k : NCode) (r : Ref)
    (hx : c.us a = .owned ∧ c.multOf a = 1 ∧ c.us i = .scalar ∧ c.mult e = 1 ∧
          c.us fst = .dead ∧ c.us snd = .dead ∧ fst ≠ snd)
    (hr : c.refOf a = some r) (hne : e ≠ r) (hopen : openRef fs r = false) :
    checkNF c fs (.takeOut a i fst snd e k) =
      checkNF ((c.move a fst).bindOwned snd e) ({ arr := r, idx := i, elem := e } :: fs) k := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := hx
  simp [checkNF, h1, h2, h3, h4, h5, h6, h7, hr, hne, hopen]

theorem checkNF_putBack (c : Ctx) (fs : List Frame) (f : Frame) (rest : List Frame)
    (a e i result : Var) (k : NCode) (r re : Ref)
    (hx : c.us a = .owned ∧ c.multOf a = 1 ∧ c.us e = .owned ∧ c.multOf e = 1 ∧
          c.us i = .scalar ∧ c.us result = .dead ∧ e ≠ a ∧ e ≠ result)
    (hr : c.refOf a = some r) (hre : c.refOf e = some re)
    (hf : f.arr = r ∧ f.idx = i ∧ f.elem = re) :
    checkNF c (f :: rest) (.putBack a e i result k) =
      checkNF ((c.move a result).setUs e .dead) rest k := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := hx
  obtain ⟨hf1, hf2, hf3⟩ := hf
  simp [checkNF, h1, h2, h3, h4, h5, h6, h7, h8, hr, hre, hf1, hf2, hf3]

theorem checkNF_callAt (c : Ctx) (fs : List Frame) (state path x result : Var)
    (k : NCode) (r : Ref)
    (hx : c.us state = .owned ∧ c.multOf state = 1 ∧ c.us path = .scalar ∧
          c.us x = .scalar ∧ c.us result = .dead)
    (hr : c.refOf state = some r) (hopen : openRef fs r = false) :
    checkNF c fs (.callAt state path x result k) =
      checkNF (c.move state result) fs k := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := hx
  simp [checkNF, h1, h2, h3, h4, h5, hr, hopen]

/-- Soundness of the nested checker, under the state-indexed heap premise. -/
theorem checkNF_sound {c : NCode} {ctx ctx' : Ctx} {fs : List Frame} {H : Heap} {env : Env}
    (hc : checkNF ctx fs c = some ctx') (hi : Inv H env ctx)
    (hok : TakeOutsOK H env c) :
    ∃ H' env' v ws, runN c env H = .done H' env' v ws ∧
      (∀ w ∈ ws, w.2 = true) ∧ Inv H' env' ctx' := by
  induction c generalizing ctx ctx' fs H env with
  | base code =>
      by_cases hfs : fs = []
      · subst hfs
        obtain ⟨H', env', v, ws, hrun, hws, hinv⟩ :=
          check_sound (by simpa [checkNF] using hc) hi
        exact ⟨H', env', v, ws, by simpa [runN] using hrun, hws, hinv⟩
      · simp [checkNF, hfs] at hc
  | takeOut a i fst snd e k ih =>
      by_cases hx : ctx.us a = .owned ∧ ctx.multOf a = 1 ∧ ctx.us i = .scalar ∧
          ctx.mult e = 1 ∧ ctx.us fst = .dead ∧ ctx.us snd = .dead ∧ fst ≠ snd
      · obtain ⟨ha, hm, hi_us, he, hfst, hsnd, hfs⟩ := hx
        obtain ⟨r, o, idx, ha', hi', hcell, hfield, hne, hok'⟩ := hok
        cases hr : ctx.refOf a with
        | none => simp [checkNF, ha, hm, hi_us, he, hfst, hsnd, hfs, hr] at hc
        | some r0 =>
            have henv_a : env a = some (.ref r0) := (hi.owned a r0 ha hr).1
            have hreq : r = r0 := by
              rw [henv_a] at ha'
              cases ha'
              rfl
            rw [hreq] at hok' hcell
            by_cases hne' : e = r0
            · simp [checkNF, ha, hm, hi_us, he, hfst, hsnd, hfs, hr, hne'] at hc
            · by_cases hopen : openRef fs r0 = true
              · simp [checkNF, ha, hm, hi_us, he, hfst, hsnd, hfs, hr, hne', hopen] at hc
              · have hopenf : openRef fs r0 = false := by
                  cases h : openRef fs r0 with
                  | false => rfl
                  | true => exact absurd h hopen
                have hc' : checkNF ((ctx.move a fst).bindOwned snd e)
                      ({ arr := r0, idx := i, elem := e } :: fs) k = some ctx' := by
                  rw [checkNF_takeOut ctx fs a i fst snd e k r0
                        ⟨ha, hm, hi_us, he, hfst, hsnd, hfs⟩ hr hne' hopenf] at hc
                  exact hc
                have hi_move : Inv H (env.set fst (.ref r0)) (ctx.move a fst) :=
                  Inv.move hi ha hr
                have hi_bind : Inv H ((env.set fst (.ref r0)).set snd (.ref e))
                    ((ctx.move a fst).bindOwned snd e) :=
                  Inv.bindOwned hi_move he
                let H' := H.set r0 { o with fields := o.fields.setIfInBounds idx (.scalar 0) }
                have hi_bind' : Inv H' ((env.set fst (.ref r0)).set snd (.ref e))
                    ((ctx.move a fst).bindOwned snd e) :=
                  Inv.setFields hi_bind hcell
                obtain ⟨H'', env'', v, ws, hrun, hws, hinv⟩ :=
                  ih (ctx := (ctx.move a fst).bindOwned snd e) (ctx' := ctx')
                     (fs := { arr := r0, idx := i, elem := e } :: fs)
                     (H := H') (env := (env.set fst (.ref r0)).set snd (.ref e))
                     hc' hi_bind' hok'
                refine ⟨H'', env'', v, ws, ?_, hws, hinv⟩
                simpa [runN, henv_a, hi', hcell, hfield] using hrun
      · simp [checkNF, hx] at hc
  | putBack a e i result k ih =>
      by_cases hx : ctx.us a = .owned ∧ ctx.multOf a = 1 ∧ ctx.us e = .owned ∧
          ctx.multOf e = 1 ∧ ctx.us i = .scalar ∧ ctx.us result = .dead ∧
          e ≠ a ∧ e ≠ result
      · obtain ⟨ha, hm, he_us, he_m, hi_us, hres, hne_a, hne_res⟩ := hx
        obtain ⟨r, re, o, idx, ha', he', hi', hcell, hok'⟩ := hok
        cases hr : ctx.refOf a with
        | none =>
            simp [checkNF, ha, hm, he_us, he_m, hi_us, hres, hne_a, hne_res, hr] at hc
        | some r0 =>
            cases hre : ctx.refOf e with
            | none =>
                simp [checkNF, ha, hm, he_us, he_m, hi_us, hres, hne_a, hne_res, hr, hre]
                  at hc
            | some re0 =>
                have henv_a : env a = some (.ref r0) := (hi.owned a r0 ha hr).1
                have henv_e : env e = some (.ref re0) := (hi.owned e re0 he_us hre).1
                have hrq : r = r0 := by
                  rw [henv_a] at ha'
                  cases ha'
                  rfl
                have hreq : re = re0 := by
                  rw [henv_e] at he'
                  cases he'
                  rfl
                rw [hrq] at hok' hcell
                rw [hreq] at hok'
                cases fs with
                | nil =>
                    simp [checkNF, ha, hm, he_us, he_m, hi_us, hres, hne_a, hne_res, hr,
                      hre] at hc
                | cons f rest =>
                    by_cases hf : f.arr = r0 ∧ f.idx = i ∧ f.elem = re0
                    · obtain ⟨hf1, hf2, hf3⟩ := hf
                      have hc' : checkNF ((ctx.move a result).setUs e .dead) rest k = some ctx' := by
                        rw [checkNF_putBack ctx (f :: rest) f rest a e i result k r0 re0
                              ⟨ha, hm, he_us, he_m, hi_us, hres, hne_a, hne_res⟩ hr hre
                              ⟨hf1, hf2, hf3⟩] at hc
                        exact hc
                      have hi_move : Inv H (env.set result (.ref r0)) (ctx.move a result) :=
                        Inv.move hi ha hr
                      have hi_fields : Inv (H.set r0 { o with fields := o.fields.set! idx (.ref re0) })
                          (env.set result (.ref r0)) (ctx.move a result) :=
                        Inv.setFields hi_move hcell
                      have hi_dead : Inv (H.set r0 { o with fields := o.fields.set! idx (.ref re0) })
                          (env.set result (.ref r0))
                          ((ctx.move a result).setUs e .dead) :=
                        Inv.setDead hi_fields
                      obtain ⟨H'', env'', v, ws, hrun, hws, hinv⟩ :=
                        ih (ctx := (ctx.move a result).setUs e .dead) (ctx' := ctx')
                           (fs := rest)
                           (H := H.set r0 { o with fields := o.fields.set! idx (.ref re0) })
                           (env := env.set result (.ref r0))
                           hc' hi_dead hok'
                      refine ⟨H'', env'', v, ws, ?_, hws, hinv⟩
                      simpa [runN, henv_a, henv_e, hi', hcell] using hrun
                    · simp [checkNF, ha, hm, he_us, he_m, hi_us, hres, hne_a, hne_res, hr,
                        hre, hf] at hc
      · simp [checkNF, hx] at hc
  | callAt state path x result k ih =>
      by_cases hx : ctx.us state = .owned ∧ ctx.multOf state = 1 ∧
          ctx.us path = .scalar ∧ ctx.us x = .scalar ∧ ctx.us result = .dead
      · obtain ⟨hs, hm, hp, hxus, hres⟩ := hx
        obtain ⟨r, henv_s', hex, hok'⟩ := hok
        cases hr : ctx.refOf state with
        | none =>
            simp [checkNF, hs, hm, hp, hxus, hres, hr] at hc
        | some r0 =>
            have henv_s : env state = some (.ref r0) := (hi.owned state r0 hs hr).1
            have hrq : r = r0 := by
              rw [henv_s] at henv_s'
              cases henv_s'
              rfl
            rw [hrq] at hex hok'
            by_cases hopen : openRef fs r0 = true
            · simp [checkNF, hs, hm, hp, hxus, hres, hr, hopen] at hc
            · have hopenf : openRef fs r0 = false := by
                cases h : openRef fs r0 with
                | false => rfl
                | true => exact absurd h hopen
              have hc' : checkNF (ctx.move state result) fs k = some ctx' := by
                rw [checkNF_callAt ctx fs state path x result k r0
                      ⟨hs, hm, hp, hxus, hres⟩ hr hopenf] at hc
                exact hc
              obtain ⟨_, hp'⟩ := hi.scalar path hp
              obtain ⟨_, hx'⟩ := hi.scalar x hxus
              have hi_move : Inv H (env.set result (.ref r0)) (ctx.move state result) :=
                Inv.move hi hs hr
              obtain ⟨H'', env'', v, ws, hrun, hws, hinv⟩ :=
                ih (ctx := ctx.move state result) (ctx' := ctx') (fs := fs)
                   (H := H) (env := env.set result (.ref r0)) hc' hi_move hok'
              refine ⟨H'', env'', v, (r0, true) :: ws, ?_, ?_, hinv⟩
              · simp [runN, henv_s, hp', hx', hex, Res.addWrite]
                exact congrArg (fun res => res.addWrite (r0, true)) hrun
              · intro w hw
                simp only [List.mem_cons] at hw
                rcases hw with rfl | hw
                · rfl
                · exact hws w hw
      · simp [checkNF, hx] at hc
  | ret x =>
      cases fs with
      | nil =>
          by_cases hx : ctx.us x = .owned ∨ ctx.us x = .scalar
          · simp only [checkNF, hx, if_true] at hc
            have hctx : ctx' = ctx := by simpa using hc.symm
            subst hctx
            exact ⟨H, env, env x |>.getD .erased, [], rfl, by simp, hi⟩
          · simp [checkNF, hx] at hc
      | cons f rest =>
          cases rest with
          | nil =>
              by_cases hx : ctx.us x = .owned ∧ ctx.refOf x = some f.elem
              · simp only [checkNF, hx] at hc
                have hctx : ctx' = ctx := by simpa using hc.symm
                subst hctx
                exact ⟨H, env, env x |>.getD .erased, [], rfl, by simp, hi⟩
              · simp [checkNF, hx] at hc
          | cons g rest' => simp [checkNF] at hc

/-- Soundness of the client-facing nested checker. -/
theorem checkN_sound {c : NCode} {ctx ctx' : Ctx} {H : Heap} {env : Env}
    (hc : checkN ctx c = some ctx') (hi : Inv H env ctx)
    (hok : TakeOutsOK H env c) :
    ∃ H' env' v ws, runN c env H = .done H' env' v ws ∧
      (∀ w ∈ ws, w.2 = true) ∧ Inv H' env' ctx' :=
  checkNF_sound (fs := []) hc hi hok

end Nested
end Ownership
