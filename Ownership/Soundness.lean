/-
Soundness of the checker for the straight-line fragment.

`check_sound` says: if the checker accepts the code from a context `ctx`, and
the runtime state satisfies `Inv` at `ctx`, then the run is fault-free, every
write in its trace is an exclusive (mutate-branch) write, and the final state
satisfies `Inv` at the checker's output context.

The key fact is the review's correction: `Inv.owned` is a handle obligation;
exclusivity is `mult r = 1` plus `rc_eq` plus non-persistence
(`Inv.exclusive`). A write's checker rule requires `multOf x = 1`; that, not the
`owned` annotation, is what proves the target exclusive.
-/
import Ownership.Code

namespace Ownership

namespace Inv

theorem setScalar {H : Heap} {env : Env} {c : Ctx} {x : Var} {n : Nat}
    (hi : Inv H env c) :
    Inv H (env.set x (.scalar n)) (c.setUs x .scalar) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro r; exact hi.rc_eq r
  · intro y r hy href
    have hyx : y ≠ x := by
      intro h; subst h; simp [Ctx.setUs] at hy
    have hc : c.us y = .owned := by simpa [Ctx.setUs, hyx] using hy
    have hro : c.refOf y = some r := by simpa [Ctx.setUs] using href
    have h := hi.owned y r hc hro
    exact ⟨by simpa [Env.set, hyx] using h.1, h.2⟩
  · intro y r hy href
    have hyx : y ≠ x := by
      intro h; subst h; simp [Ctx.setUs] at hy
    have hc : c.us y = .borrow := by simpa [Ctx.setUs, hyx] using hy
    have hro : c.refOf y = some r := by simpa [Ctx.setUs] using href
    have h := hi.borrow y r hc hro
    exact ⟨by simpa [Env.set, hyx] using h.1, h.2⟩
  · intro y hy
    by_cases hyx : y = x
    · subst hyx
      exact ⟨n, by simp [Env.set]⟩
    · have hc : c.us y = .scalar := by simpa [Ctx.setUs, hyx] using hy
      obtain ⟨m, hm⟩ := hi.scalar y hc
      exact ⟨m, by simpa [Env.set, hyx] using hm⟩
  · exact hi.nonPersistent

/-- The target ref of a live handle has a cell. -/
theorem cell_of_ref {H : Heap} {env : Env} {c : Ctx} {x : Var} {r : Ref}
    (hi : Inv H env c) (hu : c.us x = .owned ∨ c.us x = .borrow)
    (hr : c.refOf x = some r) : ∃ o, H.cells r = some o := by
  rcases hu with hu | hu
  · have hlt := (hi.owned x r hu hr).2
    have hne := hi.rc_ne_zero hlt
    cases h : H.cells r with
    | none => exact absurd h hne
    | some o => exact ⟨o, rfl⟩
  · have hne := (hi.borrow x r hu hr).2
    cases h : H.cells r with
    | none => exact absurd h hne
    | some o => exact ⟨o, rfl⟩

theorem inc {H : Heap} {env : Env} {c : Ctx} {x : Var} {r : Ref} {n : Nat}
    (hi : Inv H env c) (hx : c.us x = .owned) (hr : c.refOf x = some r) :
    Inv (H.inc r n) env (c.inc r n) := by
  have h1 : 1 ≤ c.mult r := (hi.owned x r hx hr).2
  have hne : H.cells r ≠ none := hi.rc_ne_zero h1
  cases hc : H.cells r with
  | none => exact absurd hc hne
  | some o =>
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · intro r'
      by_cases h : r' = r
      · cases h
        rw [Heap.rc_inc_self hc, Ctx.inc_self, hi.rc_eq r]
      · rw [Heap.rc_inc_other h, Ctx.inc_other (c := c) (r := r) (r' := r') (n := n) h]
        exact hi.rc_eq r'
    · intro y r' hy href
      have h := hi.owned y r' hy href
      refine ⟨h.1, ?_⟩
      by_cases hrr : r' = r
      · cases hrr
        rw [Ctx.inc_self]
        omega
      · rw [Ctx.inc_other (c := c) (r := r) (r' := r') (n := n) hrr]
        exact h.2
    · intro y r' hy href
      have h := hi.borrow y r' hy href
      refine ⟨h.1, ?_⟩
      by_cases hrr : r' = r
      · cases hrr
        simp [Heap.inc, hc, Heap.set]
      · rw [Heap.inc_other hrr]
        exact h.2
    · exact hi.scalar
    · exact nonPersistent_inc hi

theorem dec {H : Heap} {env : Env} {c : Ctx} {x : Var} {r : Ref} {n : Nat}
    (hi : Inv H env c) (hx : c.us x = .owned) (hr : c.refOf x = some r)
    (hn : n < c.mult r) :
    Inv (H.dec r n) (env.erase x) ((c.dec r n).setUs x .dead) := by
  have h1 : 1 ≤ c.mult r := (hi.owned x r hx hr).2
  have hne : H.cells r ≠ none := hi.rc_ne_zero h1
  cases hc : H.cells r with
  | none => exact absurd hc hne
  | some o =>
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · intro r'
      by_cases h : r' = r
      · cases h
        rw [Heap.rc_dec_self]
        simp [Ctx.dec, hi.rc_eq r]
      · rw [Heap.rc_dec_other h]
        simp only [Ctx.setUs_mult]
        rw [Ctx.dec_other (c := c) (r := r) (r' := r') (n := n) h]
        exact hi.rc_eq r'
    · intro y r' hy href
      by_cases hyx : y = x
      · subst hyx
        simp [Ctx.setUs] at hy
      · have hc' : c.us y = .owned := by simpa [Ctx.setUs, hyx] using hy
        have hro : c.refOf y = some r' := by simpa [Ctx.setUs] using href
        have h := hi.owned y r' hc' hro
        refine ⟨by simpa [Env.erase, hyx] using h.1, ?_⟩
        by_cases hrr : r' = r
        · cases hrr
          simp [Ctx.dec]
          omega
        · simp only [Ctx.setUs_mult]
          rw [Ctx.dec_other (c := c) (r := r) (r' := r') (n := n) hrr]
          exact h.2
    · intro y r' hy href
      by_cases hyx : y = x
      · subst hyx
        simp [Ctx.setUs] at hy
      · have hc' : c.us y = .borrow := by simpa [Ctx.setUs, hyx] using hy
        have hro : c.refOf y = some r' := by simpa [Ctx.setUs] using href
        have h := hi.borrow y r' hc' hro
        refine ⟨by simpa [Env.erase, hyx] using h.1, ?_⟩
        by_cases hrr : r' = r
        · cases hrr
          simp [Heap.dec, hc, Heap.set]
        · rw [Heap.dec_other hrr]
          exact h.2
    · intro y hy
      by_cases hyx : y = x
      · subst hyx
        simp [Ctx.setUs] at hy
      · have hc' : c.us y = .scalar := by simpa [Ctx.setUs, hyx] using hy
        obtain ⟨m, hm⟩ := hi.scalar y hc'
        exact ⟨m, by simpa [Env.erase, hyx] using hm⟩
    · exact nonPersistent_dec hi

theorem move {H : Heap} {env : Env} {c : Ctx} {x y : Var} {r : Ref}
    (hi : Inv H env c) (hx : c.us x = .owned) (hr : c.refOf x = some r) :
    Inv H (env.set y (.ref r)) (c.move x y) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro r'; exact hi.rc_eq r'
  · intro z r' hz hro
    by_cases hzy : z = y
    · subst hzy
      have hro' : c.refOf x = some r' := by simpa using hro
      rw [hr] at hro'
      have hEq : r = r' := Option.some.inj hro'
      subst hEq
      have h := hi.owned x r hx hr
      exact ⟨by simp [Env.set], h.2⟩
    · by_cases hzx : z = x
      · subst hzx
        simp [Ctx.move, hzy] at hz
      · have hz' : c.us z = .owned := by simpa [Ctx.move, hzy, hzx] using hz
        have hro' : c.refOf z = some r' := by simpa [Ctx.move, hzy] using hro
        have h := hi.owned z r' hz' hro'
        exact ⟨by simpa [Env.set, hzy] using h.1, h.2⟩
  · intro z r' hz hro
    by_cases hzy : z = y
    · subst hzy
      have hx' : c.us x = .borrow := by simpa using hz
      rw [hx] at hx'
      simp at hx'
    · by_cases hzx : z = x
      · subst hzx
        simp [Ctx.move, hzy] at hz
      · have hz' : c.us z = .borrow := by simpa [Ctx.move, hzy, hzx] using hz
        have hro' : c.refOf z = some r' := by simpa [Ctx.move, hzy] using hro
        have h := hi.borrow z r' hz' hro'
        exact ⟨by simpa [Env.set, hzy] using h.1, h.2⟩
  · intro z hz
    by_cases hzy : z = y
    · subst hzy
      have hx' : c.us x = .scalar := by simpa using hz
      rw [hx] at hx'
      simp at hx'
    · by_cases hzx : z = x
      · subst hzx
        simp [Ctx.move, hzy] at hz
      · have hz' : c.us z = .scalar := by simpa [Ctx.move, hzy, hzx] using hz
        obtain ⟨n, hn⟩ := hi.scalar z hz'
        exact ⟨n, by simpa [Env.set, hzy] using hn⟩
  · exact hi.nonPersistent

theorem setArr {H : Heap} {env : Env} {c : Ctx} {x : Var} {r : Ref}
    {o : Obj} {idx : Nat} {val : Nat}
    (hi : Inv H env c) (hx : c.us x = .owned) (hr : c.refOf x = some r)
    (hcell : H.cells r = some o) :
    Inv (H.set r { o with fields := o.fields.set! idx (.scalar val) })
        (env.set x (.ref r)) c := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro r'
    by_cases h : r' = r
    · cases h
      rw [Heap.rc_set_self]
      simpa [Heap.rc, hcell] using hi.rc_eq r
    · rw [Heap.rc_set_other h]
      exact hi.rc_eq r'
  · intro y r' hy href
    have h := hi.owned y r' hy href
    refine ⟨?_, h.2⟩
    by_cases hyx : y = x
    · subst hyx
      have hEq : r' = r := by
        rw [hr] at href
        exact (Option.some.inj href).symm
      cases hEq
      simp [Env.set]
    · simpa [Env.set, hyx] using h.1
  · intro y r' hy href
    have h := hi.borrow y r' hy href
    have hyx : y ≠ x := by
      intro hxy
      subst hxy
      rw [hx] at hy
      simp at hy
    refine ⟨by simpa [Env.set, hyx] using h.1, ?_⟩
    by_cases hrr : r' = r
    · cases hrr
      simp [Heap.set]
    · simp only [Heap.set, if_neg hrr]
      exact h.2
  · intro y hy
    have hyx : y ≠ x := by
      intro hxy
      subst hxy
      rw [hx] at hy
      simp at hy
    obtain ⟨m, hm⟩ := hi.scalar y hy
    exact ⟨m, by simpa [Env.set, hyx] using hm⟩
  · exact nonPersistent_set hi.nonPersistent
      (by simpa using hi.nonPersistent r o hcell)

theorem bindOwned {H : Heap} {env : Env} {c : Ctx} {x : Var} {e : Ref}
    (hi : Inv H env c) (hm : c.mult e = 1) :
    Inv H (env.set x (.ref e)) (c.bindOwned x e) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro r; exact hi.rc_eq r
  · intro y r hy hro
    by_cases hyx : y = x
    · subst hyx
      have hro' : e = r := by simpa using hro
      subst hro'
      refine ⟨by simp [Env.set], ?_⟩
      rw [Ctx.bindOwned_mult]
      omega
    · have hy' : c.us y = .owned := by simpa [Ctx.bindOwned, hyx] using hy
      have hro' : c.refOf y = some r := by simpa [Ctx.bindOwned, hyx] using hro
      have h := hi.owned y r hy' hro'
      exact ⟨by simpa [Env.set, hyx] using h.1, h.2⟩
  · intro y r hy hro
    by_cases hyx : y = x
    · subst hyx
      simp [Ctx.bindOwned] at hy
    · have hy' : c.us y = .borrow := by simpa [Ctx.bindOwned, hyx] using hy
      have hro' : c.refOf y = some r := by simpa [Ctx.bindOwned, hyx] using hro
      have h := hi.borrow y r hy' hro'
      exact ⟨by simpa [Env.set, hyx] using h.1, h.2⟩
  · intro y hy
    by_cases hyx : y = x
    · subst hyx
      simp [Ctx.bindOwned] at hy
    · have hy' : c.us y = .scalar := by simpa [Ctx.bindOwned, hyx] using hy
      obtain ⟨n, hn⟩ := hi.scalar y hy'
      exact ⟨n, by simpa [Env.set, hyx] using hn⟩
  · exact hi.nonPersistent

theorem setDead {H : Heap} {env : Env} {c : Ctx} {x : Var}
    (hi : Inv H env c) : Inv H env (c.setUs x .dead) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro r; exact hi.rc_eq r
  · intro y r hy hro
    by_cases hyx : y = x
    · subst hyx
      simp [Ctx.setUs] at hy
    · have hy' : c.us y = .owned := by simpa [Ctx.setUs, hyx] using hy
      have hro' : c.refOf y = some r := by simpa [Ctx.setUs] using hro
      exact hi.owned y r hy' hro'
  · intro y r hy hro
    by_cases hyx : y = x
    · subst hyx
      simp [Ctx.setUs] at hy
    · have hy' : c.us y = .borrow := by simpa [Ctx.setUs, hyx] using hy
      have hro' : c.refOf y = some r := by simpa [Ctx.setUs] using hro
      exact hi.borrow y r hy' hro'
  · intro y hy
    by_cases hyx : y = x
    · subst hyx
      simp [Ctx.setUs] at hy
    · have hy' : c.us y = .scalar := by simpa [Ctx.setUs, hyx] using hy
      obtain ⟨n, hn⟩ := hi.scalar y hy'
      exact ⟨n, by simpa [Ctx.setUs, hyx] using hn⟩
  · exact hi.nonPersistent

/-- Replacing an object's fields (same count, same persistence) preserves the
invariant. The take-out/put-back steps change only fields. -/
theorem setFields {H : Heap} {env : Env} {c : Ctx} {r : Ref} {o : Obj}
    {fields : Array Val} (hi : Inv H env c) (hcell : H.cells r = some o) :
    Inv (H.set r { o with fields := fields }) env c := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro r'
    by_cases h : r' = r
    · cases h
      rw [Heap.rc_set_self]
      have hrc := hi.rc_eq r
      rw [Heap.rc, hcell] at hrc
      simpa using hrc
    · rw [Heap.rc_set_other h]
      exact hi.rc_eq r'
  · intro x r' hx hr
    exact hi.owned x r' hx hr
  · intro x r' hx hr
    have h := hi.borrow x r' hx hr
    refine ⟨h.1, ?_⟩
    by_cases h' : r' = r
    · cases h'
      simp [Heap.set]
    · rw [Heap.set_other _ _ _ _ h']
      exact h.2
  · exact hi.scalar
  · intro r' o' hcell'
    by_cases h' : r' = r
    · exact nonPersistent_set (H := H) (r := r) (o := { o with fields := fields })
        hi.nonPersistent (by simpa using hi.nonPersistent r o hcell) r' o' hcell'
    · rw [Heap.set_other _ _ _ _ h'] at hcell'
      exact hi.nonPersistent r' o' hcell'

end Inv

/-- If the checker accepts `c`, then from any state satisfying `Inv` the run is
fault-free, every recorded write is exclusive, and the final state satisfies the
checker's output context. -/
theorem check_sound {c : Code} {ctx ctx' : Ctx} {H : Heap} {env : Env}
    (hc : check ctx c = some ctx') (hi : Inv H env ctx) :
    ∃ H' env' v ws, run c env H = .done H' env' v ws ∧
      (∀ w ∈ ws, w.2 = true) ∧ Inv H' env' ctx' := by
  induction c generalizing ctx ctx' H env with
  | «let» x v k ih =>
      cases v with
      | lit n =>
          simp only [check] at hc
          obtain ⟨H', env', v', ws, hrun, hws, hinv⟩ :=
            ih (ctx := ctx.setUs x .scalar) (ctx' := ctx') (H := H)
               (env := env.set x (.scalar n)) hc (hi.setScalar (n := n))
          exact ⟨H', env', v', ws, by simpa [run] using hrun, hws, hinv⟩
      | size a =>
          cases hr : ctx.refOf a with
          | none => simp [check, hr] at hc
          | some r =>
              by_cases hu : ctx.us a = .owned ∨ ctx.us a = .borrow
              · simp only [check, hr, hu, if_true] at hc
                obtain ⟨o, ho⟩ := hi.cell_of_ref hu hr
                obtain ⟨H', env', v', ws, hrun, hws, hinv⟩ :=
                  ih (ctx := ctx.setUs x .scalar) (ctx' := ctx') (H := H)
                     (env := env.set x (.scalar o.fields.size)) hc
                     (hi.setScalar (n := o.fields.size))
                refine ⟨H', env', v', ws, ?_, hws, hinv⟩
                simpa [run, hi.isRef hu hr, ho] using hrun
              · simp [check, hr, hu] at hc
      | isShared y =>
          cases hr : ctx.refOf y with
          | none => simp [check, hr] at hc
          | some r =>
              by_cases hu : ctx.us y = .owned ∨ ctx.us y = .borrow
              · simp only [check, hr, hu, if_true] at hc
                let b := if H.rc r > 1 then 1 else 0
                obtain ⟨H', env', v', ws, hrun, hws, hinv⟩ :=
                  ih (ctx := ctx.setUs x .scalar) (ctx' := ctx') (H := H)
                     (env := env.set x (.scalar b)) hc (hi.setScalar (n := b))
                refine ⟨H', env', v', ws, ?_, hws, hinv⟩
                simpa [run, hi.isRef hu hr, b] using hrun
              · simp [check, hr, hu] at hc
      | checkAlias src =>
          by_cases hx : ctx.us src = .owned ∧ ctx.multOf src = 1
          · simp only [check, hx, if_true] at hc
            obtain ⟨hx', hm⟩ := hx
            obtain ⟨r, hr, hmul⟩ := Ctx.multOf_eq_one hm
            have hex : Heap.Exclusive H r := hi.exclusive hmul
            have htrue : H.exclusive? r = true := (Heap.exclusive?_eq_true).mpr hex
            obtain ⟨H', env', v', ws, hrun, hws, hinv⟩ :=
              ih (ctx := ctx.move src x) (ctx' := ctx') (H := H)
                 (env := env.set x (.ref r)) hc (hi.move hx' hr)
            refine ⟨H', env', v', ws, ?_, hws, hinv⟩
            simpa [run, hi.isRef (Or.inl hx') hr, htrue] using hrun
          · simp [check, hx] at hc
  | inc x n k ih =>
      cases hr : ctx.refOf x with
      | none => simp [check, hr] at hc
      | some r =>
          by_cases hx : ctx.us x = .owned
          · simp only [check, hr, hx, if_true] at hc
            obtain ⟨H', env', v', ws, hrun, hws, hinv⟩ :=
              ih (ctx := ctx.inc r n) (ctx' := ctx') (H := H.inc r n) (env := env)
                 hc (hi.inc hx hr)
            refine ⟨H', env', v', ws, ?_, hws, hinv⟩
            simpa [run, hi.isRef (Or.inl hx) hr] using hrun
          · simp [check, hr, hx] at hc
  | dec x n k ih =>
      cases hr : ctx.refOf x with
      | none => simp [check, hr] at hc
      | some r =>
          by_cases hx : ctx.us x = .owned ∧ n < ctx.mult r
          · simp only [check, hr, hx, if_true] at hc
            obtain ⟨hx', hn⟩ := hx
            obtain ⟨H', env', v', ws, hrun, hws, hinv⟩ :=
              ih (ctx := (ctx.dec r n).setUs x .dead) (ctx' := ctx')
                 (H := H.dec r n) (env := env.erase x) hc (hi.dec hx' hr hn)
            refine ⟨H', env', v', ws, ?_, hws, hinv⟩
            simpa [run, hi.isRef (Or.inl hx') hr] using hrun
          · simp [check, hr, hx] at hc
  | check x k ih =>
      by_cases hx : ctx.us x = .owned ∧ ctx.multOf x = 1
      · simp only [check, hx, if_true] at hc
        obtain ⟨hx', hm⟩ := hx
        obtain ⟨r, hr, hmul⟩ := Ctx.multOf_eq_one hm
        have hex : Heap.Exclusive H r := hi.exclusive hmul
        have htrue : H.exclusive? r = true := (Heap.exclusive?_eq_true).mpr hex
        obtain ⟨H', env', v', ws, hrun, hws, hinv⟩ :=
          ih (ctx := ctx) (ctx' := ctx') (H := H) (env := env) hc hi
        refine ⟨H', env', v', ws, ?_, hws, hinv⟩
        simpa [run, hi.isRef (Or.inl hx') hr, htrue] using hrun
      · simp [check, hx] at hc
  | setArr x i v k ih =>
      by_cases hx : ctx.us x = .owned ∧ ctx.multOf x = 1 ∧
          ctx.us i = .scalar ∧ ctx.us v = .scalar
      · simp only [check, hx, if_true] at hc
        obtain ⟨hx', hm, hi', hv'⟩ := hx
        obtain ⟨r, hr, hmul⟩ := Ctx.multOf_eq_one hm
        have hex : Heap.Exclusive H r := hi.exclusive hmul
        have htrue : H.exclusive? r = true := (Heap.exclusive?_eq_true).mpr hex
        obtain ⟨o, ho⟩ := hi.cell_of_ref (Or.inl hx') hr
        obtain ⟨idx, hidx⟩ := hi.scalar i hi'
        obtain ⟨val, hval⟩ := hi.scalar v hv'
        obtain ⟨H', env', v', ws, hrun, hws, hinv⟩ :=
          ih (ctx := ctx) (ctx' := ctx')
             (H := H.set r { o with fields := o.fields.set! idx (.scalar val) })
             (env := env.set x (.ref r)) hc (hi.setArr hx' hr ho)
        refine ⟨H', env', v', (r, true) :: ws, ?_, ?_, hinv⟩
        · simpa [run, hi.isRef (Or.inl hx') hr, hidx, hval, ho, htrue, Res.addWrite] using
            congrArg (fun res => res.addWrite (r, true)) hrun
        · intro w hw
          simp only [List.mem_cons] at hw
          rcases hw with rfl | hw
          · rfl
          · exact hws w hw
      · simp [check, hx] at hc
  | ret x =>
      by_cases hx : ctx.us x = .owned ∨ ctx.us x = .scalar
      · simp only [check, hx, if_true] at hc
        have hctx : ctx' = ctx := by simpa using hc.symm
        subst hctx
        exact ⟨H, env, env x |>.getD .erased, [], rfl, by simp, hi⟩
      · simp [check, hx] at hc

/-- The artifact certificate, stated without the final context: accepted code
runs without a fault and every designated write is exclusive. -/
theorem accepted_no_fault_and_exclusive_writes {c : Code} {ctx : Ctx}
    {H : Heap} {env : Env} (hc : check ctx c = some ctx')
    (hi : Inv H env ctx) :
    ∃ H' env' v ws, run c env H = .done H' env' v ws ∧
      (∀ w ∈ ws, w.2 = true) := by
  obtain ⟨H', env', v, ws, hrun, hws, _⟩ := check_sound hc hi
  exact ⟨H', env', v, ws, hrun, hws⟩

end Ownership
