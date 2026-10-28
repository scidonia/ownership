/-
The consolidated path results on the depth-three certificate's own path.

`Ownership/PathConsolidation.lean` derives what the path theory used to take as
premises. This module instantiates each derivation on the concrete path of
`OwnershipTest/PathSafety.lean`, so the certificate's hand-built pieces are
replaced by applications of the general theorems:

* `checkN_derived` derives the checker's acceptance of the built program from the
  level contexts, the level shapes and the leaf body's own acceptance, and lands
  on the same final context the certificate computes by `rfl`.
* `leafBody_derived` derives the leaf body's agreement from the tip's slot facts
  instead of asserting it.
* `confined_derived` derives `ChildConfined` for all three levels.
* `consolidated` runs `path_consolidated`, which additionally derives the
  post-state footprint's non-growth and the client's separation at the post heap.
* `obsSeparated`, `observation_retained` and `observation_preserved_concrete`
  carry client retention to the interface's observation — the client's handles
  plus a produced reference.
* `pair_outside` places the extraction's temporary pair outside the state's
  mutable footprint through `Ownership.CountedPair`'s protocol.

What the certificate still supplies is the heap shape: `Acyclic` (the tip cannot
reach back up to an emptied level) and `Closed` (the entry footprint is closed
under field references), both proved below cell by cell, and the leaf body's own
checker acceptance and write annotation.
-/
import OwnershipTest.PathSafety
import Ownership.PathConsolidation

open Ownership
open Ownership.Nested
open Ownership.Entry
open Ownership.Path
open Ownership.PathSafety
open Ownership.PathConsolidation
open OwnershipTest.PathSafety

namespace OwnershipTest.PathConsolidation

/-! ## The level variable discipline -/

/-- The variable discipline at l0. -/
theorem vars0 : Vars pathVar valueVar l0 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide

/-- The variable discipline at l1. -/
theorem vars1 : Vars pathVar valueVar l1 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide

/-- The variable discipline at l2. -/
theorem vars2 : Vars pathVar valueVar l2 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide

/-! ## The contexts the built program is checked from -/

/-- The entry context satisfies the first level's context discipline. -/
theorem levelCtx0 : LevelCtx pathVar valueVar ctx0 l0 := by
  refine ⟨vars0, by decide, by decide, by decide, by decide, by decide, by decide,
    by decide, by decide, by decide, by decide, by decide⟩

/-- The child level's shape: the recursive call re-exposes its handle, and its
selected index is the call's path scalar. -/
theorem shape1 : LevelShape pathVar valueVar l1 :=
  ⟨vars1, Or.inl rfl⟩

/-- The grandchild level's shape. -/
theorem shape2 : LevelShape pathVar valueVar l2 :=
  ⟨vars2, Or.inl rfl⟩

theorem shapes : Shapes pathVar valueVar [l1, l2] :=
  ⟨shape1, shape2, trivial⟩

/-- Every array and extracted child is counted once, derived from the entry
condition's unique tree and the path's own footprint membership. -/
theorem arrs_mem_path : ∀ m ∈ [l0, l1, l2], MutableFootprint H 0 m.arr := by
  intro m hm
  simp at hm
  rcases hm with rfl | rfl | rfl
  · exact MutableFootprint.root H_cells_zero (by simp [rootObj])
  · exact H_fp1
  · exact H_fp2

theorem children_mem_path : ∀ m ∈ [l0, l1, l2], MutableFootprint H 0 m.child := by
  intro m hm
  simp at hm
  rcases hm with rfl | rfl | rfl
  · exact H_fp1
  · exact H_fp2
  · exact H_fp3

theorem counts0 : Counts ctx0.mult [l0, l1, l2] :=
  counts_of_path [l1, l2] l0 entry0.uniqueTree entry0.rc_eq arrs_mem_path
    children_mem_path

/-- The leaf body's checker acceptance, at the context the innermost call hands
it. The tail contexts are the certificate's own isolated contexts. -/
theorem checkBody : checkNF (tailCtx pathVar valueVar ctx0 [l0, l1, l2]) [] body =
    some ctxBody := by
  have h : tailCtx pathVar valueVar ctx0 [l0, l1, l2] = ctxIso2 := rfl
  rw [h]
  exact checkNF_body

/-- The leaf body's exit variable denotes the extracted tip. -/
theorem body_exit : retVar body = some 25 ∧ ctxBody.us 25 = .owned ∧
    ctxBody.refOf 25 = some 3 :=
  ⟨rfl, rfl, rfl⟩

/-- The leaf body is count-free. -/
theorem body_countFree : CountFree body = true := rfl

/-- Checker acceptance of the built program, derived rather than computed: the
level contexts, the level shapes, the counting facts and the leaf's own
acceptance give the certificate's final context. -/
theorem checkN_derived : checkN ctx0 code = some ctxF :=
  checkNF_build [l1, l2] l0 levelCtx0 shapes counts0.2.2 chained checkBody
    body_exit.1 body_exit.2.1 body_exit.2.2 endsAtAll body_countFree

/-- The leaf body's agreement, derived from the tip's slot facts. -/
theorem leafBody_derived : Agrees H3 env3 body := by
  have hbody : body = .takeOut 16 10 22 23 40
      (.putBack 22 23 10 24
        (.base (.let 25 (.checkAlias 24) (.let 26 (.lit 7) (.setArr 25 11 26
          (.ret 25)))))) := rfl
  rw [hbody]
  refine agrees_extract_restore (H := H3) (env := env3) (r := 3) (o := tipObj)
    (idx := 0) (e := 40) (a := 16) (i := 10) (fst := 22) (snd := 23) (result := 24)
    ?_ ?_ ?_ ?_ (by decide) (by decide) (by decide)
  · simp [env3, isolateEnv, bindLevel, l2]
  · simp [env3, env2, env1, env0, isolateEnv, bindLevel, Env.set, l0, l1, l2,
      pathVar]
  · exact H3_cells_three
  · decide

/-! ## The heap shape the path still needs -/

/-- The tip's mutable footprint is its own cell and the extracted leaf: the tip's
other slot is a scalar and the leaf's fields hold no reference. -/
theorem tip_footprint {Ht : Heap} {q : Ref} (h3 : Ht.cells 3 = some tipObj)
    (h40 : Ht.cells 40 = some leafObj) (h : MutableFootprint Ht 3 q) :
    q = 3 ∨ q = 40 := by
  induction h with
  | root _ _ => exact Or.inl rfl
  | step hr hcell hpers hmem hcell' hpers' ih =>
      rcases ih with rfl | rfl
      · rw [h3] at hcell
        have ho : tipObj = _ := Option.some.inj hcell
        subst ho
        simp [fieldRefs, refsOf, tipObj] at hmem
        exact Or.inr hmem
      · rw [h40] at hcell
        have ho : leafObj = _ := Option.some.inj hcell
        subst ho
        simp [fieldRefs, refsOf, leafObj] at hmem

/-- The tip cannot reach back up to the root the path emptied. -/
theorem noBack0 : ¬ MutableFootprint H 3 0 := by
  intro h
  rcases tip_footprint H_cells_three H_cells_leaf h with h | h <;> simp_all

/-- The tip cannot reach the root level's array from the first take-out heap. -/
theorem noBack1 : ¬ MutableFootprint H1 3 1 := by
  intro h
  rcases tip_footprint H1_cells_three H1_cells_leaf h with h | h <;> simp_all

/-- The tip cannot reach the child level's array from the second take-out heap. -/
theorem noBack2 : ¬ MutableFootprint H2 3 2 := by
  intro h
  rcases tip_footprint H2_cells_three H2_cells_leaf h with h | h <;> simp_all

/-- The heap-shape fact the path theory needs, at the depth-three certificate. -/
theorem acyclic : Acyclic 3 H [l0, l1, l2] :=
  ⟨sepRoot, noBack0, sepChild, noBack1, sepGrand, noBack2, trivial⟩

/-- The entry heap's footprint is closed under field references: each footprint
cell's reference slots name the next cell of the chain. -/
theorem closed0 : Closed H 0 := by
  intro q o z hq hcell hz
  rcases H_footprint hq with rfl | rfl | rfl | rfl | rfl
  · rw [H_cells_zero] at hcell
    have ho : o = rootObj := (Option.some.inj hcell).symm
    subst ho
    have hl : fieldRefs rootObj = [1] := by decide
    rw [hl] at hz
    have hz1 : z = 1 := by simpa using hz
    subst hz1
    exact H_fp1
  · rw [H_cells_one] at hcell
    have ho : o = childObj := (Option.some.inj hcell).symm
    subst ho
    have hl : fieldRefs childObj = [2] := by decide
    rw [hl] at hz
    have hz1 : z = 2 := by simpa using hz
    subst hz1
    exact H_fp2
  · rw [H_cells_two] at hcell
    have ho : o = grandObj := (Option.some.inj hcell).symm
    subst ho
    have hl : fieldRefs grandObj = [3] := by decide
    rw [hl] at hz
    have hz1 : z = 3 := by simpa using hz
    subst hz1
    exact H_fp3
  · rw [H_cells_three] at hcell
    have ho : o = tipObj := (Option.some.inj hcell).symm
    subst ho
    have hl : fieldRefs tipObj = [40] := by decide
    rw [hl] at hz
    have hz1 : z = 40 := by simpa using hz
    subst hz1
    exact H_fp40
  · rw [H_cells_leaf] at hcell
    have ho : o = leafObj := (Option.some.inj hcell).symm
    subst ho
    have hl : fieldRefs leafObj = [] := by decide
    rw [hl] at hz
    simp at hz

/-! ## The leaf body's write account -/

/-- The environments the innermost body runs in are the certificate's. -/
theorem tailEnv_eq : tailEnv pathVar valueVar env0 [l0, l1, l2] = env3 := rfl

/-- The leaf body writes only the extracted leaf, which is a footprint member. -/
theorem writes0 : WritesIn H 0 (tailEnv pathVar valueVar env0 [l0, l1, l2]) body := by
  rw [tailEnv_eq]
  have hbody : body = .takeOut 16 10 22 23 40
      (.putBack 22 23 10 24
        (.base (.let 25 (.checkAlias 24) (.let 26 (.lit 7) (.setArr 25 11 26
          (.ret 25)))))) := rfl
  rw [hbody]
  refine ⟨3, ?_, ⟨?_, fun _ _ => trivial⟩⟩
  · simp [env3, isolateEnv, bindLevel, l2]
  · intro re hre
    simp only [Env.set_self, Option.some.injEq, Val.ref.injEq] at hre
    subst hre
    exact H_fp40

/-- The leaf agreement at the state the innermost call hands its body: the
certificate's take-out heap and environment. -/
theorem leafAgreesH : leafAgrees pathVar valueVar body (blankLevel H l0)
    (isolateEnv (bindLevel env0 l0) l0.childVar pathVar valueVar) [l1, l2] := by
  show Agrees H3 env3 body
  exact leafBody_derived

/-! ## The derived contracts -/

/-- `ChildConfined` at every level, derived rather than built by hand. -/
theorem confined_derived : ChildConfined pathVar valueVar body H env0 [l0, l1, l2] :=
  childConfined_of_path [l1, l2] l0 slots chained distinct envok leafAgreesH
    levelCtx0 shapes counts0.2.2 acyclic liveTip annBody checkBody body_exit.1
    body_exit.2.1 body_exit.2.2 endsAtAll body_countFree entry0.toInv

/-- The consolidated run: checker acceptance, the child contract and the leaf's
annotation derived, and the post-state footprint's non-growth obtained from the
write account rather than supplied as three heap facts. -/
theorem consolidated :
    ∃ H' env' v ws,
      runN code env0 H = .done H' env' v ws ∧
        (∀ w ∈ ws, w.2 = true) ∧ Inv H' env' ctxF ∧ Outside H' H 0 ∧
        (∀ r, ClientReachable H' client r → ¬ MutableFootprint H 0 r) ∧
        (∀ r, MutableFootprint H' 0 r → MutableFootprint H 0 r) ∧
        ClientSeparated H' 0 client :=
  path_consolidated [l1, l2] l0 slots chained distinct envok shapes levelCtx0 acyclic
    leafAgreesH writes0 checkBody body_exit.1 body_exit.2.1 body_exit.2.2 endsAtAll
    liveTip annBody body_countFree entry0 rfl hnoBorrow closed0

/-! ## Observations -/

/-- The client's own leaf, a produced reference, is a separated handle. -/
theorem clientLeaf_separated : ClientSeparated H 0 [52] := by
  have hreach : ∀ r, ClientReachable H [52] r → r = 52 := by
    intro r hr
    induction hr with
    | direct h => simpa using h
    | step hr hcell hmem ih =>
        rw [ih, H_cells_52] at hcell
        have ho : clientLeaf = _ := Option.some.inj hcell
        subst ho
        simp [fieldRefs, refsOf, clientLeaf] at hmem
  intro r hr
  rw [hreach r hr]
  intro hfp
  rcases H_footprint hfp with g | g | g | g | g <;> simp_all

/-- The observation — the client's handles plus the produced reference — is
separated at the entry heap. -/
theorem obsSeparated : ObsSeparated H 0 (obsOf client (.ref 52)) :=
  obsSeparated_of_separated entry0.separated clientLeaf_separated

/-- The interface's direct production premise holds for that reference. -/
theorem obsProduces : ProducesOutside H 0 (.ref 52) :=
  producesOutside_of_separated clientLeaf_separated

/-- Retention over the observation: no reference the client can reach after the
run — including the produced one — is in the entry footprint. -/
theorem observation_retained :
    ∃ H', ∀ r, ClientReachable H' (client ++ producedRefs (.ref 52)) r →
      ¬ MutableFootprint H 0 r := by
  obtain ⟨H', -, -, -, -, -, -, hout, -, -, -⟩ := consolidated
  exact ⟨H', observation_retention obsSeparated hout⟩

/-- The observation is separated again at the post heap, now without the three
heap facts the certificate supplied by hand. -/
theorem observation_preserved_concrete :
    ∃ H', ObsSeparated H' 0 (obsOf client (.ref 52)) := by
  obtain ⟨H', -, -, -, -, -, -, hout, -, hwithin, -⟩ := consolidated
  exact ⟨H', observation_preserved obsSeparated hout hwithin⟩

/-- Callback traffic that is separated at the entry heap stays separated across
the run. -/
theorem callback_traffic : CallbackTrafficOutside H 0 [52] := clientLeaf_separated

/-- The callback-traffic account at the post heap, through `callback_retention`:
the client's handles and the traffic it exchanged stay separated. -/
theorem callback_preserved : ∃ H', ClientSeparated H' 0 (client ++ [52]) := by
  obtain ⟨H', -, -, -, -, -, -, hout, -, hwithin, -⟩ := consolidated
  exact ⟨H', callback_retention obsSeparated hout hwithin⟩

/-! ## The temporary pair -/

/-- Which objects the entry heap's cells hold. -/
theorem H_cells_cases {q : Ref} {o : Obj} (h : H.cells q = some o) :
    o = rootObj ∨ o = childObj ∨ o = grandObj ∨ o = tipObj ∨ o = leafObj ∨
      o = clientWrap ∨ o = clientMid ∨ o = clientLeaf := by
  by_cases h0 : q = 0
  · subst h0
    exact Or.inl (Option.some.inj (by simpa [H] using h)).symm
  · by_cases h1 : q = 1
    · subst h1
      exact Or.inr (Or.inl (Option.some.inj (by simpa [H, h0] using h)).symm)
    · by_cases h2 : q = 2
      · subst h2
        exact Or.inr (Or.inr (Or.inl
          (Option.some.inj (by simpa [H, h0, h1] using h)).symm))
      · by_cases h3 : q = 3
        · subst h3
          exact Or.inr (Or.inr (Or.inr (Or.inl
            (Option.some.inj (by simpa [H, h0, h1, h2] using h)).symm)))
        · by_cases h40 : q = 40
          · subst h40
            exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
              (Option.some.inj (by simpa [H, h0, h1, h2, h3] using h)).symm))))
          · by_cases h50 : q = 50
            · subst h50
              exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
                (Option.some.inj
                  (by simpa [H, h0, h1, h2, h3, h40] using h)).symm)))))
            · by_cases h51 : q = 51
              · subst h51
                exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
                  (Option.some.inj
                    (by simpa [H, h0, h1, h2, h3, h40, h50] using h)).symm))))))
              · by_cases h52 : q = 52
                · subst h52
                  exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
                    (Option.some.inj (by simpa [H] using h)).symm))))))
                · rw [show H.cells q = none by
                    simp [H, h0, h1, h2, h3, h40, h50, h51, h52]] at h
                  exact absurd h (by simp)

/-- The entry heap's fresh name is unused and unnamed: no cell lives at it and no
cell's field mentions it. -/
theorem freshName : FreshName H := by
  refine ⟨by simp [H], ?_⟩
  intro q o hcell
  rcases H_cells_cases hcell with h | h | h | h | h | h | h | h <;> subst h <;> decide

/-- The extraction's temporary pair is outside the state's mutable footprint. -/
theorem pair_outside :
    ¬ MutableFootprint (CountedPair.protocol H 0 1 0).2 0 H.next :=
  pair_outside_footprint (l := l0) freshName H_cells_zero H_cells_one
    (by decide) (by decide) (by decide) (by decide)

/-- The counted extraction writes the same parent cell the model's take-out does. -/
theorem protocol_cell0 :
    (CountedPair.protocol H 0 1 0).2.cells 0 = (blankLevel H l0).cells 0 :=
  protocol_parent_cell (l := l0) H_cells_zero H_cells_one (by decide) (by decide)
    (by decide)

/-- On every session cell the counted extraction agrees with the model's
take-out. -/
theorem protocol_session_cells :
    ∀ q, q ≠ H.next →
      (CountedPair.protocol H 0 1 0).2.cells q = (blankLevel H l0).cells q :=
  protocol_cells (l := l0) H_cells_zero H_cells_one (by decide) (by decide) (by decide)

/-! ## The finite level list -/

/-- The certificate's program has one call site per level. -/
theorem calls_code : calls code = 3 := by
  have hb : calls body = 0 := rfl
  rw [show code = build pathVar valueVar body [l0, l1, l2] from rfl, calls_build, hb]
  simp

/-- The certificate's program extracts once per level on top of the leaf body's
own extraction. -/
theorem extractions_code : extractions code = 4 := by
  have hb : extractions body = 1 := rfl
  rw [show code = build pathVar valueVar body [l0, l1, l2] from rfl, extractions_build, hb]
  simp

/-- The certificate's outermost call runs the remaining two levels: the
recursive target is a list tail, not a declaration. -/
theorem callBody_code : callBody? code = some (build pathVar valueVar body [l1, l2]) := rfl

/-! ## Axiom dependencies -/

#print axioms Ownership.PathConsolidation.checkNF_build
#print axioms Ownership.PathConsolidation.childConfined_of_path
#print axioms Ownership.PathConsolidation.agrees_extract_restore
#print axioms Ownership.PathConsolidation.slotRefs_runN
#print axioms Ownership.PathConsolidation.path_consolidated
#print axioms Ownership.PathConsolidation.pair_outside_footprint
#print axioms Ownership.PathConsolidation.observation_retention
#print axioms OwnershipTest.PathConsolidation.checkN_derived
#print axioms OwnershipTest.PathConsolidation.leafBody_derived
#print axioms OwnershipTest.PathConsolidation.confined_derived
#print axioms OwnershipTest.PathConsolidation.consolidated
#print axioms OwnershipTest.PathConsolidation.pair_outside
#print axioms Ownership.PathConsolidation.calls_build
#print axioms Ownership.PathConsolidation.extractions_build
#print axioms Ownership.PathConsolidation.callBody_build
#print axioms OwnershipTest.PathConsolidation.calls_code
#print axioms OwnershipTest.PathConsolidation.extractions_code

end OwnershipTest.PathConsolidation
