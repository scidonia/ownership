/-
The nested take-out path: array check → take-out → extracted-element check →
recursive summary → put-back, and the recursive summary call itself.

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

`callAt` is a genuine recursive call: it carries the embedded program `body`
that the summary runs. The checker checks `body` as its own program from an
isolated context that exposes only the call's own state, path and index — every
other variable is dead — so a body cannot name a handle a suspended parent frame
still owns. The body must exit through a variable that still denotes the
reference the call was given, and it must neither duplicate nor consume a
handle, so the caller's counted heap is what the caller's context records. At
runtime the body runs in an environment that exposes only those three variables,
on the same heap, so the heap really changes through the body's own extraction,
restoration and write steps; the call's result denotes that same reference.

The exit is conservative. With no open frame an owned or scalar handle may be
returned. With exactly one open frame only that frame's extracted element may
return, and only as an owned handle; the emptied parent, any other value, and a
deeper stack of open frames are refused until the frames are restored. Returning
the parent would hand back an array whose selected slot still holds the
take-out's placeholder, which is not the array the caller left.

`TakeOutsOK` is the heap premise the checker cannot see: which cell lives in
which slot, what each annotation denotes, and which counted handles exist. It is
indexed by the state each step reaches, so a nested take-out's obligation is
stated on the heap its parent take-out left and a put-back's on the heap the
nested take-out left; a recursive call's continuation obligation is stated on
whatever heap the body actually leaves. `callAt_frame_sound` is the recursive
call's own contract: an admitted body runs fault-free, writes only exclusively,
and returns the reference the call was given. Its confinement half — that the
body touches no cell outside the state's own mutable footprint — needs the
entry module's footprint relation and the annotation premise, so
`Ownership.Entry.callAt_frame_confined` states the whole contract.

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
  /-- A recursive summary call: `state` is the extracted array the body works on,
  `path` and `x` are its scalar arguments, `result` receives the returned
  reference, and `body` is the recursive program the summary runs. -/
  | callAt (state path x result : Var) (body : NCode) (k : NCode)
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

/-- The variable a straight-line block exits through. -/
def codeRetVar : Code → Option Var
  | .let _ _ k => codeRetVar k
  | .inc _ _ k => codeRetVar k
  | .dec _ _ k => codeRetVar k
  | .check _ k => codeRetVar k
  | .setArr _ _ _ k => codeRetVar k
  | .ret x => some x

/-- The variable a nested program exits through. A recursive body exits through
this variable, and the checker requires it to still denote the reference the call
was given. -/
def retVar : NCode → Option Var
  | .base code => codeRetVar code
  | .takeOut _ _ _ _ _ k => retVar k
  | .putBack _ _ _ _ k => retVar k
  | .callAt _ _ _ _ _ k => retVar k
  | .ret x => some x

/-- A straight-line block that neither duplicates nor consumes a handle: it
leaves the counted heap's multiplicities alone. -/
def countFreeCode : Code → Bool
  | .let _ _ k => countFreeCode k
  | .inc _ _ _ => false
  | .dec _ _ _ => false
  | .check _ k => countFreeCode k
  | .setArr _ _ _ k => countFreeCode k
  | .ret _ => true

/-- A nested program that neither duplicates nor consumes a handle: its heap
effects are slot and field updates, so the caller's multiplicities still describe
the heap after it returns. -/
def CountFree : NCode → Bool
  | .base code => countFreeCode code
  | .takeOut _ _ _ _ _ k => CountFree k
  | .putBack _ _ _ _ k => CountFree k
  | .callAt _ _ _ _ body k => CountFree body && CountFree k
  | .ret _ => true

/-- The recursive body's checker context: only the call's own state, path and
index are exposed and every other variable is dead, so a body cannot name a
handle a suspended frame still owns. The multiplicities are the caller's, because
they are a fact about the counted heap rather than about which variables the body
may name. -/
def isolatedCtx (c : Ctx) (state path x : Var) (r : Ref) : Ctx :=
  { us := fun z => if z = state then .owned
                   else if z = path then .scalar
                   else if z = x then .scalar
                   else .dead
    refOf := fun z => if z = state then some r else none
    mult := c.mult }

/-- The recursive body's environment: only the three arguments the call hands it
are visible, so the body cannot rebind a suspended parent frame's variables. -/
def isolateEnv (env : Env) (state path x : Var) : Env :=
  fun z => if z = state then env z
           else if z = path then env z
           else if z = x then env z
           else none

/-- Append a run's writes to an already-completed continuation. A recursive
call's body runs first, so its writes precede the continuation's. -/
def addWrites (r : Res) (ws : List Write) : Res :=
  match r with
  | .done H env v ws' => .done H env v (ws ++ ws')
  | .fault H env f ws' => .fault H env f (ws ++ ws')

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
  | .callAt state path x result body k, env, H =>
      match env state, env path, env x with
      | some (.ref r), some (.scalar _), some (.scalar _) =>
          if H.exclusive? r then
            match runN body (isolateEnv env state path x) H with
            | .done H' _ _ ws =>
                addWrites (runN k (env.set result (.ref r)) H') ws
            | .fault H' env' f ws => .fault H' env' f ws
          else .fault H env (.notExclusive r) []
      | _, _, _ => .fault H env (.badVar state) []
  | .ret x, env, H => .done H env (env x |>.getD .erased) []

/-- The state-indexed heap premise: every step actually reached must find what
the runtime will read on the heap and environment the previous step left. A
nested take-out's obligation is thus stated after its parent's slot holds a
scalar, and a put-back's after the nested slot was emptied; `TakeOutOK` is the
one-step instance. The checker cannot see these facts. A recursive call's
continuation obligation is stated on whatever heap the body leaves, because that
is the heap the continuation runs on. -/
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
  | .callAt state path x result body k =>
      ∃ r, env state = some (.ref r) ∧ H.exclusive? r = true ∧
        TakeOutsOK H (isolateEnv env state path x) body ∧
        (∀ H' envb vb wsb, runN body (isolateEnv env state path x) H =
            .done H' envb vb wsb →
          TakeOutsOK H' (env.set result (.ref r)) k)

/-- The heap/program agreement: what the runtime must hold for the program's own
annotations to be meaningful. A take-out's annotated element is the object the
array's selected slot actually holds, and a recursive call's annotations hold on
the environment it hands its body and on whatever heap the body leaves. This is
the part of `TakeOutsOK` that no entry or checker fact implies: the checker
cannot see which object a slot holds, so the agreement is a separate premise.
`Ownership.Entry.takeOutsOK_of_inv` adds the existence and multiplicity facts the
invariant does supply. -/
def Agrees (H : Heap) (env : Env) : NCode → Prop
  | .base _ | .ret _ => True
  | .takeOut a i fst snd e k =>
      ∃ r o idx, env a = some (.ref r) ∧ env i = some (.scalar idx) ∧
        H.cells r = some o ∧ o.fields[idx]? = some (.ref e) ∧
        Agrees (H.set r { o with fields := o.fields.setIfInBounds idx (.scalar 0) })
          ((env.set fst (.ref r)).set snd (.ref e)) k
  | .putBack a e i result k =>
      ∃ r re o idx, env a = some (.ref r) ∧ env e = some (.ref re) ∧
        env i = some (.scalar idx) ∧ H.cells r = some o ∧
        Agrees (H.set r { o with fields := o.fields.set! idx (.ref re) })
          (env.set result (.ref r)) k
  | .callAt state path x result body k =>
      ∃ r, env state = some (.ref r) ∧
        Agrees H (isolateEnv env state path x) body ∧
        (∀ H' envb vb wsb, runN body (isolateEnv env state path x) H =
            .done H' envb vb wsb →
          Agrees H' (env.set result (.ref r)) k)

/-- The checker's worker. `fs` is the extraction frame stack, innermost first;
the client-facing `checkN` starts it empty. A straight-line block is admitted
only with no open frame, because `check` cannot see which array a write names.
A take-out binds the array and the element to two different variables, and the
exit admits only the return value the open frames allow. A recursive call checks
its body as its own program from the isolated context, and then continues with
the caller's context, in which the extracted array's handle has moved to the
result variable. -/
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
  | .callAt state path x result body k =>
      if c.us state = .owned ∧ c.multOf state = 1 ∧ c.us path = .scalar ∧
          c.us x = .scalar ∧ c.us result = .dead ∧ CountFree body = true then
        match c.refOf state with
        | some r =>
            if openRef fs r then none
            else
              match checkNF (isolatedCtx c state path x r) [] body with
              | none => none
              | some cb =>
                  match retVar body with
                  | none => none
                  | some y =>
                      if cb.us y = .owned ∧ cb.refOf y = some r then
                        checkNF (c.move state result) fs k
                      else none
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

/-- Extracting the facts a successful recursive call's check carries. -/
theorem checkNF_callAt_some {c : Ctx} {fs : List Frame} {state path x result : Var}
    {body k : NCode} {ctx' : Ctx} {r : Ref}
    (hx : c.us state = .owned ∧ c.multOf state = 1 ∧ c.us path = .scalar ∧
          c.us x = .scalar ∧ c.us result = .dead ∧ CountFree body = true)
    (hr : c.refOf state = some r) (hopen : openRef fs r = false)
    (hc : checkNF c fs (.callAt state path x result body k) = some ctx') :
    ∃ cb y, checkNF (isolatedCtx c state path x r) [] body = some cb ∧
      retVar body = some y ∧ cb.us y = .owned ∧ cb.refOf y = some r ∧
      checkNF (c.move state result) fs k = some ctx' := by
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hx
  have hguard : c.us state = .owned ∧ c.multOf state = 1 ∧ c.us path = .scalar ∧
      c.us x = .scalar ∧ c.us result = .dead ∧ CountFree body = true :=
    ⟨h1, h2, h3, h4, h5, h6⟩
  unfold checkNF at hc
  rw [if_pos hguard] at hc
  cases hcell : c.refOf state with
  | none => simp only [hcell] at hc; simp at hc
  | some r0 =>
      have hr0 : r0 = r := by
        rw [hcell] at hr
        exact Option.some.inj hr
      subst r0
      simp only [hcell] at hc
      rw [if_neg (by rw [hopen]; simp)] at hc
      cases hb : checkNF (isolatedCtx c state path x r) [] body with
      | none => simp only [hb] at hc; simp at hc
      | some cb =>
          simp only [hb] at hc
          cases hy : retVar body with
          | none => simp only [hy] at hc; simp at hc
          | some y =>
              simp only [hy] at hc
              by_cases hexit : cb.us y = .owned ∧ cb.refOf y = some r
              · rw [if_pos hexit] at hc
                exact ⟨cb, y, rfl, rfl, hexit.1, hexit.2, hc⟩
              · rw [if_neg hexit] at hc; simp at hc

/-! ## Heap facts the recursive call's contract needs -/

/-- Setting a cell never removes another cell. -/
theorem Heap.cells_none_of_set {H : Heap} {r : Ref} {o : Obj} {q : Ref}
    (h : (H.set r o).cells q = none) : H.cells q = none := by
  by_cases hq : q = r
  · subst hq; rw [Heap.set_self] at h; simp at h
  · rw [Heap.set_other _ _ _ _ hq] at h; exact h

/-- Counting up or down never removes a cell. -/
theorem Heap.cells_none_of_inc {H : Heap} {r : Ref} {n : Nat} {q : Ref}
    (h : (H.inc r n).cells q = none) : H.cells q = none := by
  unfold Heap.inc at h
  split at h
  · exact h
  · exact Heap.cells_none_of_set h

theorem Heap.cells_none_of_dec {H : Heap} {r : Ref} {n : Nat} {q : Ref}
    (h : (H.dec r n).cells q = none) : H.cells q = none := by
  unfold Heap.dec at h
  split at h
  · exact h
  · exact Heap.cells_none_of_set h

/-- Allocation adds one cell and leaves the rest where they were. -/
theorem Heap.cells_none_of_alloc {H : Heap} {fields : Array Val} {q : Ref}
    (h : (H.alloc fields).2.cells q = none) : H.cells q = none := by
  by_cases hq : q = H.next
  · subst hq; rw [Heap.alloc_cells_self] at h; simp at h
  · rw [Heap.alloc_cells_other hq] at h; exact h

/-- Replacing a cell's fields keeps its count. -/
theorem Heap.rc_set_fields {H : Heap} {r : Ref} {o : Obj} {f : Array Val} {q : Ref}
    (hcell : H.cells r = some o) : (H.set r { o with fields := f }).rc q = H.rc q := by
  by_cases hq : q = r
  · subst hq; rw [Heap.rc_set_self, Heap.rc, hcell]; rfl
  · rw [Heap.rc_set_other hq]

/-- A completed run that `addWrite` extended was itself a completed run with the
same heap, environment and value. -/
theorem addWrite_done {r : Res} {w : Write} {H' : Heap} {env' : Env} {v : Val}
    {ws : List Write} (h : r.addWrite w = .done H' env' v ws) :
    ∃ ws0, r = .done H' env' v ws0 := by
  cases r with
  | done H0 env0 v0 ws0 =>
      simp only [Res.addWrite] at h
      injection h with h1 h2 h3 _
      subst h1; subst h2; subst h3
      exact ⟨ws0, rfl⟩
  | fault H0 env0 f0 ws0 => simp [Res.addWrite] at h

theorem addWrites_done {r : Res} {ws : List Write} {H' : Heap} {env' : Env}
    {v : Val} {ws' : List Write} (h : addWrites r ws = .done H' env' v ws') :
    ∃ ws0, r = .done H' env' v ws0 := by
  cases r with
  | done H0 env0 v0 ws0 =>
      unfold addWrites at h
      injection h with h1 h2 h3 _
      subst h1; subst h2; subst h3
      exact ⟨ws0, rfl⟩
  | fault H0 env0 f0 ws0 => simp [addWrites] at h

/-! ## Exit variables of a completed run -/

/-- A block that exits through `y` returns the value `y` denotes. The binder is
read with `getD erased`, so an unbound exit variable returns the erased value. -/
theorem run_codeRetVar {code : Code} {env : Env} {H : Heap} {H' : Heap}
    {env' : Env} {v : Val} {ws : List Write} {y : Var}
    (hret : codeRetVar code = some y) (hrun : run code env H = .done H' env' v ws) :
    v = (env' y).getD .erased := by
  induction code generalizing env H H' env' v ws y with
  | «let» x w k ih =>
      cases w with
      | lit n =>
          simp only [codeRetVar] at hret
          exact ih hret (by simpa [run] using hrun)
      | size a =>
          simp only [codeRetVar] at hret
          unfold run at hrun
          split at hrun
          · split at hrun
            · exact ih hret hrun
            · simp at hrun
          · simp at hrun
      | isShared z =>
          simp only [codeRetVar] at hret
          unfold run at hrun
          split at hrun
          · exact ih hret hrun
          · simp at hrun
      | checkAlias z =>
          simp only [codeRetVar] at hret
          unfold run at hrun
          split at hrun
          · split at hrun
            · exact ih hret hrun
            · simp at hrun
          · simp at hrun
  | inc x n k ih =>
      simp only [codeRetVar] at hret
      unfold run at hrun
      split at hrun
      · exact ih hret hrun
      · simp at hrun
  | dec x n k ih =>
      simp only [codeRetVar] at hret
      unfold run at hrun
      split at hrun
      · exact ih hret hrun
      · simp at hrun
  | check x k ih =>
      simp only [codeRetVar] at hret
      unfold run at hrun
      split at hrun
      · split at hrun
        · exact ih hret hrun
        · simp at hrun
      · simp at hrun
  | setArr x i v' k ih =>
      simp only [codeRetVar] at hret
      unfold run at hrun
      split at hrun
      · split at hrun
        · simp at hrun
        · split at hrun
          · obtain ⟨ws0, hrun'⟩ := addWrite_done hrun
            exact ih hret hrun'
          · obtain ⟨ws0, hrun'⟩ := addWrite_done hrun
            exact ih hret hrun'
      · simp at hrun
  | ret x =>
      simp only [codeRetVar, Option.some.injEq] at hret
      subst y
      simp only [run] at hrun
      injection hrun with h1 h2 hv _
      subst h1; subst h2
      exact hv.symm

theorem runN_retVar {c : NCode} {env : Env} {H : Heap} {H' : Heap} {env' : Env}
    {v : Val} {ws : List Write} {y : Var} (hret : retVar c = some y)
    (hrun : runN c env H = .done H' env' v ws) : v = (env' y).getD .erased := by
  induction c generalizing env H H' env' v ws y with
  | base code => exact run_codeRetVar hret hrun
  | takeOut a i fst snd e k ih =>
      simp only [retVar] at hret
      unfold runN at hrun
      split at hrun
      · split at hrun
        · split at hrun
          · split at hrun
            · exact ih hret hrun
            · simp at hrun
          · simp at hrun
        · simp at hrun
      · simp at hrun
  | putBack a e i result k ih =>
      simp only [retVar] at hret
      unfold runN at hrun
      split at hrun
      · split at hrun
        · exact ih hret hrun
        · simp at hrun
      · simp at hrun
  | callAt state path x result body k ihbody ihk =>
      simp only [retVar] at hret
      unfold runN at hrun
      split at hrun
      · split at hrun
        · split at hrun
          · rename_i hb
            obtain ⟨ws0, hws⟩ := addWrites_done hrun
            exact ihk hret hws
          · simp at hrun
        · simp at hrun
      · simp at hrun
  | ret x =>
      simp only [retVar, Option.some.injEq] at hret
      subst y
      simp only [runN] at hrun
      injection hrun with h1 h2 hv _
      subst h1; subst h2
      exact hv.symm

/-! ## Cell existence through a run -/

theorem run_cells_none {code : Code} {env H H' env' v ws}
    (hrun : run code env H = .done H' env' v ws) :
    ∀ q, H'.cells q = none → H.cells q = none := by
  induction code generalizing env H H' env' v ws with
  | «let» x w k ih =>
      cases w with
      | lit n => exact ih (by simpa [run] using hrun)
      | size a =>
          unfold run at hrun
          split at hrun
          · split at hrun
            · exact ih hrun
            · simp at hrun
          · simp at hrun
      | isShared z =>
          unfold run at hrun
          split at hrun
          · exact ih hrun
          · simp at hrun
      | checkAlias z =>
          unfold run at hrun
          split at hrun
          · split at hrun
            · exact ih hrun
            · simp at hrun
          · simp at hrun
  | inc x n k ih =>
      intro q hq
      unfold run at hrun
      split at hrun
      · rename_i r
        exact Heap.cells_none_of_inc (ih hrun q hq)
      · simp at hrun
  | dec x n k ih =>
      intro q hq
      unfold run at hrun
      split at hrun
      · rename_i r
        exact Heap.cells_none_of_dec (ih hrun q hq)
      · simp at hrun
  | check x k ih =>
      intro q hq
      unfold run at hrun
      split at hrun
      · split at hrun
        · exact ih hrun q hq
        · simp at hrun
      · simp at hrun
  | setArr x i v' k ih =>
      intro q hq
      unfold run at hrun
      split at hrun
      · split at hrun
        · simp at hrun
        · split at hrun
          · obtain ⟨ws0, hrun'⟩ := addWrite_done hrun
            exact Heap.cells_none_of_set (ih hrun' q hq)
          · obtain ⟨ws0, hrun'⟩ := addWrite_done hrun
            exact Heap.cells_none_of_alloc (Heap.cells_none_of_dec (ih hrun' q hq))
      · simp at hrun
  | ret x =>
      intro q hq
      simp only [run] at hrun
      injection hrun with h1 h2 h3 _
      subst h1; subst h2; subst h3
      exact hq

theorem runN_cells_none {c : NCode} {env H H' env' v ws}
    (hrun : runN c env H = .done H' env' v ws) :
    ∀ q, H'.cells q = none → H.cells q = none := by
  induction c generalizing env H H' env' v ws with
  | base code => exact run_cells_none hrun
  | takeOut a i fst snd e k ih =>
      intro q hq
      unfold runN at hrun
      split at hrun
      · split at hrun
        · split at hrun
          · split at hrun
            · exact Heap.cells_none_of_set (ih hrun q hq)
            · simp at hrun
          · simp at hrun
        · simp at hrun
      · simp at hrun
  | putBack a e i result k ih =>
      intro q hq
      unfold runN at hrun
      split at hrun
      · split at hrun
        · exact Heap.cells_none_of_set (ih hrun q hq)
        · simp at hrun
      · simp at hrun
  | callAt state path x result body k ihbody ihk =>
      intro q hq
      unfold runN at hrun
      split at hrun
      · split at hrun
        · split at hrun
          · rename_i hb
            obtain ⟨ws0, hws⟩ := addWrites_done hrun
            exact ihbody hb q (ihk hws q hq)
          · simp at hrun
        · simp at hrun
      · simp at hrun
  | ret x =>
      intro q hq
      simp only [runN] at hrun
      injection hrun with h1 h2 h3 _
      subst h1; subst h2; subst h3
      exact hq

/-! ## Multiplicities across a count-free check -/

theorem countFreeCode_check_mult {c : Code} :
    ∀ {ctx ctx' : Ctx}, countFreeCode c = true → check ctx c = some ctx' →
      ∀ q, ctx'.mult q = ctx.mult q := by
  induction c with
  | «let» x w k ih =>
      intro ctx ctx' hcf hc q
      simp only [countFreeCode] at hcf
      cases w with
      | lit n =>
          exact ih (ctx := ctx.setUs x .scalar) hcf (by simpa [check] using hc) q
      | size a =>
          unfold check at hc
          split at hc
          · split at hc
            · exact ih (ctx := ctx.setUs x .scalar) hcf hc q
            · simp at hc
          · simp at hc
      | isShared z =>
          unfold check at hc
          split at hc
          · split at hc
            · exact ih (ctx := ctx.setUs x .scalar) hcf hc q
            · simp at hc
          · simp at hc
      | checkAlias z =>
          unfold check at hc
          split at hc
          · exact ih (ctx := ctx.move z x) hcf hc q
          · simp at hc
  | inc x n k ih => intro ctx ctx' hcf hc q; simp [countFreeCode] at hcf
  | dec x n k ih => intro ctx ctx' hcf hc q; simp [countFreeCode] at hcf
  | check x k ih =>
      intro ctx ctx' hcf hc q
      simp only [countFreeCode] at hcf
      unfold check at hc
      split at hc
      · exact ih (ctx := ctx) hcf hc q
      · simp at hc
  | setArr x i v' k ih =>
      intro ctx ctx' hcf hc q
      simp only [countFreeCode] at hcf
      unfold check at hc
      split at hc
      · exact ih (ctx := ctx) hcf hc q
      · simp at hc
  | ret x =>
      intro ctx ctx' hcf hc q
      unfold check at hc
      split at hc
      · simp only [Option.some.injEq] at hc
        subst hc
        rfl
      · simp at hc

theorem countFree_check_mult {c : NCode} :
    ∀ {ctx ctx' : Ctx} {fs : List Frame}, CountFree c = true →
      checkNF ctx fs c = some ctx' → ∀ q, ctx'.mult q = ctx.mult q := by
  induction c with
  | base code =>
      intro ctx ctx' fs hcf hc q
      by_cases hfs : fs = []
      · subst hfs
        exact countFreeCode_check_mult (ctx := ctx) hcf (by simpa [checkNF] using hc) q
      · simp [checkNF, hfs] at hc
  | takeOut a i fst snd e k ih =>
      intro ctx ctx' fs hcf hc q
      simp only [CountFree] at hcf
      unfold checkNF at hc
      split at hc
      · split at hc
        · split at hc
          · simp at hc
          · split at hc
            · simp at hc
            · exact ih (ctx := (ctx.move a fst).bindOwned snd e) hcf hc q
        · simp at hc
      · simp at hc
  | putBack a e i result k ih =>
      intro ctx ctx' fs hcf hc q
      simp only [CountFree] at hcf
      unfold checkNF at hc
      split at hc
      · split at hc
        · split at hc
          · exact ih (ctx := (ctx.move a result).setUs e .dead) hcf hc q
          · simp at hc
        · simp at hc
      · simp at hc
  | callAt state path x result body k ihbody ihk =>
      intro ctx ctx' fs hcf hc q
      simp only [CountFree, Bool.and_eq_true] at hcf
      obtain ⟨hcfb, hcfk⟩ := hcf
      unfold checkNF at hc
      split at hc
      · split at hc
        · split at hc
          · simp at hc
          · split at hc
            · simp at hc
            · split at hc
              · simp at hc
              · split at hc
                · exact ihk (ctx := ctx.move state result) hcfk hc q
                · simp at hc
        · simp at hc
      · simp at hc
  | ret x =>
      intro ctx ctx' fs hcf hc q
      unfold checkNF at hc
      split at hc
      · split at hc
        · simp only [Option.some.injEq] at hc
          subst hc
          rfl
        · simp at hc
      · split at hc
        · simp only [Option.some.injEq] at hc
          subst hc
          rfl
        · simp at hc
      · simp at hc

/-! ## The invariant across the isolation -/

theorem isolatedCtx_us_owned {c : Ctx} {state path x : Var} {r : Ref} {z : Var} :
    (isolatedCtx c state path x r).us z = .owned ↔ z = state := by
  by_cases h : z = state
  · subst z; simp [isolatedCtx]
  · by_cases h2 : z = path
    · subst z; simp [isolatedCtx, h]
    · by_cases h3 : z = x
      · subst z; simp [isolatedCtx, h, h2]
      · simp [isolatedCtx, h, h2, h3]

theorem isolatedCtx_us_scalar {c : Ctx} {state path x : Var} {r : Ref} {z : Var} :
    (isolatedCtx c state path x r).us z = .scalar ↔ z ≠ state ∧ (z = path ∨ z = x) := by
  by_cases h : z = state
  · subst z; simp [isolatedCtx]
  · by_cases h2 : z = path
    · subst z; simp [isolatedCtx, h]
    · by_cases h3 : z = x
      · subst z; simp [isolatedCtx, h, h2]
      · simp [isolatedCtx, h, h2, h3]

theorem isolatedCtx_us_ne_borrow {c : Ctx} {state path x : Var} {r : Ref} {z : Var} :
    (isolatedCtx c state path x r).us z ≠ .borrow := by
  by_cases h : z = state
  · subst z; simp [isolatedCtx]
  · by_cases h2 : z = path
    · subst z; simp [isolatedCtx, h]
    · by_cases h3 : z = x
      · subst z; simp [isolatedCtx, h, h2]
      · simp [isolatedCtx, h, h2, h3]

theorem inv_isolated {H : Heap} {env : Env} {c : Ctx} {state path x : Var} {r : Ref}
    (hi : Inv H env c) (hs : c.us state = .owned) (hr : c.refOf state = some r)
    (hp : c.us path = .scalar) (hx : c.us x = .scalar) :
    Inv H (isolateEnv env state path x) (isolatedCtx c state path x r) := by
  have hpne : path ≠ state := by
    intro h; rw [h, hs] at hp; simp at hp
  have hxne : x ≠ state := by
    intro h; rw [h, hs] at hx; simp at hx
  refine ⟨?_, ?_, ?_, ?_, hi.nonPersistent⟩
  · intro q; exact hi.rc_eq q
  · intro z q hz hzo
    have hzs : z = state := isolatedCtx_us_owned.mp hz
    subst z
    have hzr : (isolatedCtx c state path x r).refOf state = some r := by simp [isolatedCtx]
    rw [hzr] at hzo
    have hqr : q = r := (Option.some.inj hzo).symm
    rw [hqr]
    have henv : isolateEnv env state path x state = env state := by simp [isolateEnv]
    exact ⟨by rw [henv]; exact (hi.owned state r hs hr).1,
      by simpa [isolatedCtx] using (hi.owned state r hs hr).2⟩
  · intro z q hz hzo
    exact absurd hz isolatedCtx_us_ne_borrow
  · intro z hz
    obtain ⟨hne, hzcases⟩ := isolatedCtx_us_scalar.mp hz
    by_cases hzp : z = path
    · subst z
      obtain ⟨n, hn⟩ := hi.scalar path hp
      exact ⟨n, by simp [isolateEnv, hpne, hn]⟩
    · have hzx : z = x := hzcases.resolve_left hzp
      subst z
      obtain ⟨n, hn⟩ := hi.scalar x hx
      exact ⟨n, by simp [isolateEnv, hne, hzp, hn]⟩

/-- The invariant transfers to a heap that kept the caller's multiplicities,
never lost a cell, and whose cells are non-persistent. -/
theorem inv_of_rc_cells {H Hb : Heap} {env : Env} {c : Ctx}
    (hi : Inv H env c) (hrc : ∀ q, Hb.rc q = c.mult q)
    (hmono : ∀ q, Hb.cells q = none → H.cells q = none)
    (hnp : ∀ q o, Hb.cells q = some o → o.persistent = false) :
    Inv Hb env c := by
  refine ⟨hrc, ?_, ?_, ?_, hnp⟩
  · intro z q hz hzo; exact hi.owned z q hz hzo
  · intro z q hz hzo
    obtain ⟨hzr, hcell⟩ := hi.borrow z q hz hzo
    refine ⟨hzr, ?_⟩
    intro hnone
    exact hcell (hmono q hnone)
  · exact hi.scalar

/-! ## Soundness -/

/-- Soundness of the nested checker, under the state-indexed heap premise. A
recursive call's body is checked and run as its own program from the isolated
context and environment, and the caller's continuation then runs on the heap the
body left. -/
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
              exact (Val.ref.inj (Option.some.inj ha')).symm
            subst r
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
                  exact (Val.ref.inj (Option.some.inj ha')).symm
                have hreq : re = re0 := by
                  rw [henv_e] at he'
                  exact (Val.ref.inj (Option.some.inj he')).symm
                subst r
                subst re
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
  | callAt state path x result body k ihbody ihk =>
      by_cases hx : ctx.us state = .owned ∧ ctx.multOf state = 1 ∧
          ctx.us path = .scalar ∧ ctx.us x = .scalar ∧ ctx.us result = .dead ∧
          CountFree body = true
      · obtain ⟨hs, hm, hp, hxus, hres, hcf⟩ := hx
        obtain ⟨r, henv_s, hex, hokb, hokk⟩ := hok
        cases hr : ctx.refOf state with
        | none =>
            simp [checkNF, hs, hm, hp, hxus, hres, hcf, hr] at hc
        | some r0 =>
            have henv_s0 : env state = some (.ref r0) := (hi.owned state r0 hs hr).1
            have hrq : r = r0 := by
              rw [henv_s0] at henv_s
              exact (Val.ref.inj (Option.some.inj henv_s)).symm
            subst r
            by_cases hopen : openRef fs r0 = true
            · simp [checkNF, hs, hm, hp, hxus, hres, hcf, hr, hopen] at hc
            · have hopenf : openRef fs r0 = false := by
                cases h : openRef fs r0 with
                | false => rfl
                | true => exact absurd h hopen
              obtain ⟨cb, y, hcbody, hret, hcbus, hcbref, hc'⟩ :=
                checkNF_callAt_some (c := ctx) (fs := fs) (r := r0) (k := k) (body := body)
                  ⟨hs, hm, hp, hxus, hres, hcf⟩ hr hopenf hc
              have hi_iso : Inv H (isolateEnv env state path x)
                  (isolatedCtx ctx state path x r0) :=
                inv_isolated hi hs hr hp hxus
              obtain ⟨Hb, envb, vb, wsb, hrunb, hwsb, hinvb⟩ :=
                ihbody (ctx := isolatedCtx ctx state path x r0) (ctx' := cb) (fs := [])
                  (H := H) (env := isolateEnv env state path x) hcbody hi_iso hokb
              have hcbm : ∀ q, cb.mult q = ctx.mult q :=
                countFree_check_mult (ctx := isolatedCtx ctx state path x r0) hcf hcbody
              have hi_ctx : Inv Hb env ctx :=
                inv_of_rc_cells hi (fun q => by rw [hinvb.rc_eq q, hcbm q])
                  (fun q hq => runN_cells_none hrunb q hq) hinvb.nonPersistent
              have hi_cont : Inv Hb (env.set result (.ref r0)) (ctx.move state result) :=
                Inv.move hi_ctx hs hr
              obtain ⟨H'', env'', v, ws, hrun, hws, hinv⟩ :=
                ihk (ctx := ctx.move state result) (ctx' := ctx') (fs := fs) (H := Hb)
                  (env := env.set result (.ref r0)) hc' hi_cont (hokk Hb envb vb wsb hrunb)
              refine ⟨H'', env'', v, wsb ++ ws, ?_, ?_, hinv⟩
              · obtain ⟨pn, hp'⟩ := hi.scalar path hp
                obtain ⟨xn, hx'⟩ := hi.scalar x hxus
                simp [runN, henv_s0, hp', hx', hex, hrunb, hrun, addWrites]
              · intro w hw
                rcases List.mem_append.mp hw with hw | hw
                · exact hwsb w hw
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

/-- The recursive call's contract: a body the checker admits from the isolated
context runs fault-free, every write in its trace selects the exclusive branch,
and it exits through a variable that still denotes exactly the reference the call
was given. The body runs in its own environment, so a suspended parent frame's
variables are untouched, and the heap it leaves is the heap the caller's
continuation runs on. -/
theorem callAt_frame_sound {c : Ctx} {state path x : Var} {r : Ref} {body : NCode}
    {H : Heap} {env : Env} {cb : Ctx}
    (hc : checkNF (isolatedCtx c state path x r) [] body = some cb)
    (hret : ∃ y, retVar body = some y ∧ cb.us y = .owned ∧ cb.refOf y = some r)
    (hi : Inv H env (isolatedCtx c state path x r))
    (hok : TakeOutsOK H env body) :
    ∃ H' env' v ws, runN body env H = .done H' env' v ws ∧
      (∀ w ∈ ws, w.2 = true) ∧ v = .ref r := by
  obtain ⟨y, hrv, hus, href⟩ := hret
  obtain ⟨H', env', v, ws, hrun, hws, hinv⟩ := checkN_sound hc hi hok
  refine ⟨H', env', v, ws, hrun, hws, ?_⟩
  rw [runN_retVar hrv hrun]
  have h := (hinv.owned y r hus href).1
  simp [h]

end Nested
end Ownership
