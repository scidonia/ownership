/-
Reachability across a nested extraction path.

`Ownership.Entry` defines the transitive mutable footprint and transitive client
reachability; this module proves both relations transitive and builds the path
view that the nested model's agreement and confinement premises need. A path is a
list of levels: each level is an array whose selected slot holds the next
reference, together with the six variables the emitted shape binds at that level
(the array handle, the selected index, the extracted array and element, the
recursive call's result and the put-back's result). `build` reads the nested
program off the path — take-out, recursive call and put-back at every level, with
an opaque body at the innermost call.

Two results compose the premises the nested model takes as given:

* `agrees_of_path` derives the heap/program agreement of the built program from
  the path's slot facts, the binder discipline of each level's environment, the
  parent/child separation and the child-call contract's outside-footprint
  preservation. The innermost body's agreement stays a hypothesis: the emitted
  recursive callee's body is not captured, so the theorem says what a path yields
  given the body's own agreement, not that the recursive declaration agrees.
* `annotationsIn_of_path` derives the extraction annotations' reachability: every
  reference the program extracts is in the root's mutable footprint, so the leaf
  body's annotations lift from the innermost state's footprint by transitivity.

The path is a model-level description. It relates the runtime heap's slots, the
model's variables and the extraction annotations; it says nothing about the
emitted `FVarId` layout, the extraction pairs, the reified node indices or the
reference-count traffic those steps perform.
-/
import Ownership.Nested
import Ownership.Entry

namespace Ownership
namespace Entry

open Ownership.Nested

/-- Transitivity of the mutable footprint: a reference reachable from a footprint
member is in the root's footprint. -/
theorem MutableFootprint.trans {H : Heap} {root mid r : Ref}
    (h1 : MutableFootprint H root mid) (h2 : MutableFootprint H mid r) :
    MutableFootprint H root r := by
  induction h2 with
  | root _ _ => exact h1
  | step _ hcell hpers hmem hcell' hpers' ih =>
      exact MutableFootprint.step ih hcell hpers hmem hcell' hpers'

/-- Transitivity of client reachability: whatever a reachable reference reaches
is reachable from the client's handles. -/
theorem ClientReachable.trans {H : Heap} {client : List Ref} {mid r : Ref}
    (h1 : ClientReachable H client mid) (h2 : ClientReachable H [mid] r) :
    ClientReachable H client r := by
  induction h2 with
  | direct h =>
      simp only [List.mem_singleton] at h
      subst h
      exact h1
  | step hr hcell hmem ih =>
      exact ClientReachable.step ih hcell hmem

/-- A program whose extraction annotations name cells in `child`'s footprint has
them in `root`'s footprint when `child` is itself reachable. -/
theorem AnnotationsIn.trans {H : Heap} {root child : Ref} :
    ∀ {code : NCode}, MutableFootprint H root child → AnnotationsIn H child code →
      AnnotationsIn H root code := by
  intro code
  induction code with
  | base _ => intro _ _; trivial
  | ret _ => intro _ _; trivial
  | takeOut a i fst snd e k ih =>
      intro hfp h
      obtain ⟨he, hk⟩ := h
      exact ⟨hfp.trans he, ih hfp hk⟩
  | putBack a e i result k ih =>
      intro hfp h
      exact ih hfp h
  | callAt state path x result body k ihbody ihk =>
      intro hfp h
      obtain ⟨hb, hk⟩ := h
      exact ⟨ihbody hfp hb, ihk hfp hk⟩

end Entry

namespace Path

open Entry
open Ownership.Nested

/-- One level of a nested extraction path: the array the take-out reads, the
object its cell holds, the selected slot, the reference that slot holds, and the
six variables the emitted shape binds at this level. `arrayVar` is the handle the
take-out reads, `indexVar` the selected index, `parentVar` and `childVar` the two
binders the take-out fills, `resultVar` the recursive call's result and
`restoredVar` the put-back's result. -/
structure Level where
  arr : Ref
  obj : Obj
  idx : Nat
  child : Ref
  arrayVar : Var
  indexVar : Var
  parentVar : Var
  childVar : Var
  resultVar : Var
  restoredVar : Var
  deriving Repr

/-- A live non-persistent cell: the shape a footprint step needs of its target. -/
def Live (H : Heap) (r : Ref) : Prop :=
  ∃ o, H.cells r = some o ∧ o.persistent = false

/-- Every reference a slot holds is a field reference of its object. -/
theorem mem_fieldRefs {o : Obj} {i : Nat} {r : Ref}
    (h : o.fields[i]? = some (.ref r)) : r ∈ fieldRefs o := by
  refine List.mem_flatMap.mpr ⟨.ref r, ?_, by simp [refsOf]⟩
  rw [Array.mem_toList_iff, Array.mem_iff_getElem?]
  exact ⟨i, h⟩

/-- A footprint cell whose selected slot holds a live reference puts that
reference in the footprint. -/
theorem MutableFootprint.step_of_slot {H : Heap} {root r r' : Ref} {o o' : Obj}
    {i : Nat} (hr : MutableFootprint H root r) (hcell : H.cells r = some o)
    (hpers : o.persistent = false) (hslot : o.fields[i]? = some (.ref r'))
    (hcell' : H.cells r' = some o') (hpers' : o'.persistent = false) :
    MutableFootprint H root r' :=
  MutableFootprint.step hr hcell hpers (mem_fieldRefs hslot) hcell' hpers'

/-- The heap a take-out at this level leaves: the selected slot holds the
placeholder scalar. -/
def blankLevel (H : Heap) (l : Level) : Heap :=
  H.set l.arr { l.obj with fields := l.obj.fields.setIfInBounds l.idx (.scalar 0) }

/-- The take-out heap holds the placeholder in the level's selected slot. -/
theorem blankLevel_cells (H : Heap) (l : Level) :
    (blankLevel H l).cells l.arr =
      some { l.obj with fields := l.obj.fields.setIfInBounds l.idx (.scalar 0) } :=
  Heap.set_self _ _ _

/-- Emptying one level's slot leaves every other cell as it was. -/
theorem blankLevel_cells_ne {H : Heap} {l : Level} {q : Ref} (h : q ≠ l.arr) :
    (blankLevel H l).cells q = H.cells q :=
  Heap.set_other _ _ _ _ h

/-- The environment a take-out at this level leaves: the extracted array and the
extracted element are bound to the two fresh variables. -/
def bindLevel (env : Env) (l : Level) : Env :=
  (env.set l.parentVar (.ref l.arr)).set l.childVar (.ref l.child)

/-- The take-out binds the extracted child to the child variable. -/
theorem bindLevel_child (env : Env) (l : Level) :
    (bindLevel env l) l.childVar = some (.ref l.child) := by
  simp [bindLevel]

/-- The take-out binds the extracted array to the parent variable, which the
child variable does not shadow. -/
theorem bindLevel_parent {env : Env} {l : Level} (h : l.childVar ≠ l.parentVar) :
    (bindLevel env l) l.parentVar = some (.ref l.arr) := by
  simp only [bindLevel]
  rw [Env.set_other _ _ _ _ (Ne.symm h), Env.set_self]

/-- The slot facts a path reads at its input heap: each level's array is a live
non-persistent cell whose selected slot holds the next reference. -/
def Slots (H : Heap) (ls : List Level) : Prop :=
  ∀ l ∈ ls, H.cells l.arr = some l.obj ∧ l.obj.fields[l.idx]? = some (.ref l.child) ∧
    l.obj.persistent = false

/-- The path is chained: each level's extracted child is the next level's array,
and the variable that names the child is the one the next take-out reads. -/
def Chained : List Level → Prop
  | [] => True
  | [_] => True
  | l :: m :: rest => l.child = m.arr ∧ l.childVar = m.arrayVar ∧ Chained (m :: rest)

/-- The arrays along the path are pairwise distinct, so emptying one level's slot
leaves every later level's cell and slot as the input heap had them. -/
def DistinctArrays : List Level → Prop
  | [] => True
  | l :: rest => (∀ m ∈ rest, m.arr ≠ l.arr) ∧ DistinctArrays rest

/-- The last level's selected slot holds the array the innermost call hands its
body. -/
def EndsAt (tip : Ref) : List Level → Prop
  | [] => True
  | [l] => l.child = tip
  | _ :: rest => EndsAt tip rest

/-- The variables one level reads, at the environment its take-out starts from:
the array handle, the selected index and the call's two exposed scalars are
bound, and the binder discipline keeps the extracted array, the selected index
and the exposed scalars readable after the call's result is bound. -/
def LevelEnv (path value : Var) (env : Env) (l : Level) : Prop :=
  env l.arrayVar = some (.ref l.arr) ∧
  env l.indexVar = some (.scalar l.idx) ∧
  (∃ n, env path = some (.scalar n)) ∧
  (∃ n, env value = some (.scalar n)) ∧
  l.childVar ≠ l.parentVar ∧
  l.resultVar ≠ l.parentVar ∧
  l.indexVar ≠ l.parentVar ∧ l.indexVar ≠ l.childVar ∧ l.indexVar ≠ l.resultVar ∧
  path ≠ l.parentVar ∧ path ≠ l.childVar ∧
  value ≠ l.parentVar ∧ value ≠ l.childVar

/-- The environments a path reads, level by level. After a level's take-out the
recursive call exposes only the extracted child, the path and the value, so the
rest of the path is read from the isolated environment. -/
def EnvOK (path value : Var) (env : Env) : List Level → Prop
  | [] => True
  | l :: rest =>
      LevelEnv path value env l ∧
        EnvOK path value (isolateEnv (bindLevel env l) l.childVar path value) rest

/-- The nested program a path emits: extract at each level, hand the extracted
child to the recursive call, restore the slot from the call's result, and run the
opaque body at the innermost call. -/
def build (path value : Var) (body : NCode) : List Level → NCode
  | [] => body
  | l :: rest =>
      .takeOut l.arrayVar l.indexVar l.parentVar l.childVar l.child
        (.callAt l.childVar path value l.resultVar (build path value body rest)
          (.putBack l.parentVar l.resultVar l.indexVar l.restoredVar
            (.ret l.restoredVar)))

/-- The leaf body's agreement at the state the innermost call hands it, carried
down the path: a level's take-out moves the heap to the one it leaves and the
environment to the one its call exposes to its body. The empty tail is the
innermost call's body, which runs in exactly that environment. -/
def leafAgrees (path value : Var) (body : NCode) (H : Heap) (env : Env) :
    List Level → Prop
  | [] => Agrees H env body
  | l :: rest =>
      leafAgrees path value body (blankLevel H l)
        (isolateEnv (bindLevel env l) l.childVar path value) rest

/-- The child-call contract level by level: the parent array is outside the
extracted child's mutable footprint, and the program the level hands its call
leaves every cell outside that footprint as the take-out left it. -/
def ChildConfined (path value : Var) (body : NCode) (H : Heap) (env : Env) :
    List Level → Prop
  | [] => True
  | l :: rest =>
      ¬ MutableFootprint (blankLevel H l) l.child l.arr ∧
      (∀ H' envb vb wsb,
        runN (build path value body rest)
            (isolateEnv (bindLevel env l) l.childVar path value) (blankLevel H l) =
            .done H' envb vb wsb →
          ∀ q, ¬ MutableFootprint (blankLevel H l) l.child q →
            H'.cells q = (blankLevel H l).cells q) ∧
      ChildConfined path value body (blankLevel H l)
        (isolateEnv (bindLevel env l) l.childVar path value) rest

/-! ## Slot facts survive the outer take-outs -/

/-- Emptying a level's slot preserves the slot facts of every other level. -/
theorem Slots.blank {H : Heap} {ls : List Level} {l : Level}
    (hslots : Slots H ls) (hne : ∀ m ∈ ls, m.arr ≠ l.arr) :
    Slots (blankLevel H l) ls := by
  intro m hm
  obtain ⟨hcell, hslot, hpers⟩ := hslots m hm
  exact ⟨by rw [blankLevel_cells_ne (hne m hm)]; exact hcell, hslot, hpers⟩

/-! ## The path is in the root's mutable footprint -/

/-- Along a chained path every array is reachable from the first level's array:
each level's child is the next level's array, so the path only ever moves one
slot down. -/
theorem arrs_mem {H : Heap} {tip : Ref} :
    ∀ (rest : List Level) (l : Level), Slots H (l :: rest) → Chained (l :: rest) →
      EndsAt tip (l :: rest) → ∀ m ∈ (l :: rest), MutableFootprint H l.arr m.arr := by
  intro rest
  induction rest with
  | nil =>
      intro l hslots _ _ m hm
      have hml : m = l := by simpa using hm
      rw [hml]
      obtain ⟨hcell, -, hpers⟩ := hslots l (by simp)
      exact MutableFootprint.root hcell hpers
  | cons m rest' ih =>
      intro l hslots hchain hends q hq
      obtain ⟨hcell, hslot, hpers⟩ := hslots l (by simp)
      obtain ⟨hchild, hcv, hchainTail⟩ := hchain
      have hstep : MutableFootprint H l.arr m.arr := by
        refine MutableFootprint.step_of_slot (i := l.idx)
          (MutableFootprint.root hcell hpers) hcell hpers ?_
          (hslots m (by simp)).1 (hslots m (by simp)).2.2
        simpa [hchild] using hslot
      rcases List.mem_cons.mp hq with rfl | hq
      · exact MutableFootprint.root hcell hpers
      · exact MutableFootprint.trans hstep
          (ih m (fun k hk => hslots k (List.mem_cons_of_mem _ hk)) hchainTail hends q hq)

/-- Every reference the path extracts is reachable from the first level's array,
including the innermost array the leaf body works on. -/
theorem children_mem {H : Heap} {tip : Ref} (htip : Live H tip) :
    ∀ (rest : List Level) (l : Level), Slots H (l :: rest) → Chained (l :: rest) →
      EndsAt tip (l :: rest) → ∀ m ∈ (l :: rest), MutableFootprint H l.arr m.child := by
  intro rest
  induction rest with
  | nil =>
      intro l hslots _ hends q hq
      have hql : q = l := by simpa using hq
      rw [hql]
      obtain ⟨hcell, hslot, hpers⟩ := hslots l (by simp)
      have hchild : l.child = tip := hends
      obtain ⟨oT, hcellT, hpersT⟩ := htip
      have hslot' : l.obj.fields[l.idx]? = some (.ref tip) := by
        rw [hchild] at hslot
        exact hslot
      have hstep := MutableFootprint.step_of_slot (i := l.idx) (r' := tip)
        (MutableFootprint.root hcell hpers) hcell hpers hslot' hcellT hpersT
      simpa [hchild] using hstep
  | cons m rest' ih =>
      intro l hslots hchain hends q hq
      obtain ⟨hchild, hcv, hchainTail⟩ := hchain
      have harr : MutableFootprint H l.arr m.arr :=
        arrs_mem (m :: rest') l hslots ⟨hchild, hcv, hchainTail⟩ hends m (by simp)
      rcases List.mem_cons.mp hq with rfl | hq
      · simpa [hchild] using harr
      · exact MutableFootprint.trans harr
          (ih m (fun k hk => hslots k (List.mem_cons_of_mem _ hk)) hchainTail hends q hq)

/-! ## Agreement -/

/-- The continuation a level's call hands the put-back: the extracted array's
cell is still present, and the environment still binds the parent handle, the
selected index and the call's result. -/
theorem agrees_putBack {H' : Heap} {env : Env} {l : Level} {path value : Var}
    (henv : LevelEnv path value env l)
    (hcell : H'.cells l.arr =
      some { l.obj with fields := l.obj.fields.setIfInBounds l.idx (.scalar 0) }) :
    Agrees H' ((bindLevel env l).set l.resultVar (.ref l.child))
      (.putBack l.parentVar l.resultVar l.indexVar l.restoredVar (.ret l.restoredVar)) := by
  obtain ⟨-, henvI, -, -, hcv, hrv, hiv1, hiv2, hiv3, -, -, -, -⟩ := henv
  have hpar : ((bindLevel env l).set l.resultVar (.ref l.child)) l.parentVar =
      some (.ref l.arr) := by
    rw [Env.set_other _ _ _ _ (Ne.symm hrv)]
    exact bindLevel_parent hcv
  have hres : ((bindLevel env l).set l.resultVar (.ref l.child)) l.resultVar =
      some (.ref l.child) := by
    rw [Env.set_self]
  have hidx : ((bindLevel env l).set l.resultVar (.ref l.child)) l.indexVar =
      some (.scalar l.idx) := by
    rw [Env.set_other _ _ _ _ hiv3, bindLevel]
    rw [Env.set_other _ _ _ _ hiv2, Env.set_other _ _ _ _ hiv1]
    exact henvI
  exact ⟨l.arr, l.child, _, l.idx, hpar, hres, hidx, hcell, trivial⟩

/-- Agreement of the built program, derived from the path. The premises are the
path's slot facts at the input heap, the chain linkage, the distinctness of the
arrays along the path, each level's environment facts, the leaf body's own
agreement at the state the innermost call hands it, and the child-call contract
level by level. The leaf body's agreement is not derived: the emitted recursive
callee's body is not captured, so the theorem states what a path yields given that
body's own agreement.

The entry condition is not a premise. Agreement is a statement about the heap's
slots, the call's exposed environment and the extraction annotations, all of which
the path's own facts supply; `EntryInv` enters on the checker's side, where
`Ownership.Entry.takeOutsOK_of_entryInv` turns the same agreement into the
state-indexed heap premise and `checkN_sound` runs the program. -/
theorem agrees_of_path {path value : Var} {body : NCode} :
    ∀ (rest : List Level) (l : Level) {H : Heap} {env : Env},
      Slots H (l :: rest) → Chained (l :: rest) → DistinctArrays (l :: rest) →
      EnvOK path value env (l :: rest) →
      leafAgrees path value body (blankLevel H l)
        (isolateEnv (bindLevel env l) l.childVar path value) rest →
      ChildConfined path value body H env (l :: rest) →
      Agrees H env (build path value body (l :: rest)) := by
  intro rest
  induction rest with
  | nil =>
      intro l H env hslots _ _ henv hleaf hconf
      obtain ⟨hcell, hslot, hpers⟩ := hslots l (by simp)
      obtain ⟨henv0, -⟩ := henv
      have hlev : LevelEnv path value env l := henv0
      obtain ⟨henvA, henvI, -, -, -, -, -, -, -, -, -, -, -⟩ := henv0
      obtain ⟨hsep, hpres, -⟩ := hconf
      simp only [build]
      refine ⟨l.arr, l.obj, l.idx, henvA, henvI, hcell, hslot, ?_⟩
      refine ⟨l.child, bindLevel_child env l, ?_, ?_⟩
      · simpa [leafAgrees, build, blankLevel, bindLevel] using hleaf
      · intro H' envb vb wsb hrun
        refine agrees_putBack hlev ?_
        rw [hpres H' envb vb wsb hrun l.arr hsep]
        exact blankLevel_cells H l
  | cons m rest' ih =>
      intro l H env hslots hchain hdist henv hleaf hconf
      obtain ⟨hcell, hslot, hpers⟩ := hslots l (by simp)
      obtain ⟨henv0, henvRest⟩ := henv
      have hlev : LevelEnv path value env l := henv0
      obtain ⟨henvA, henvI, -, -, -, -, -, -, -, -, -, -, -⟩ := henv0
      obtain ⟨hsep, hpres, hconfRest⟩ := hconf
      obtain ⟨hchild, hcv, hchainTail⟩ := hchain
      obtain ⟨hdistL, hdistRest⟩ := hdist
      have hslotsRest : Slots (blankLevel H l) (m :: rest') :=
        Slots.blank (fun k hk => hslots k (List.mem_cons_of_mem _ hk)) hdistL
      simp only [build]
      refine ⟨l.arr, l.obj, l.idx, henvA, henvI, hcell, hslot, ?_⟩
      refine ⟨l.child, bindLevel_child env l, ?_, ?_⟩
      · refine ih m hslotsRest hchainTail hdistRest henvRest ?_ hconfRest
        simpa only [leafAgrees, blankLevel, bindLevel] using hleaf
      · intro H' envb vb wsb hrun
        refine agrees_putBack hlev ?_
        rw [hpres H' envb vb wsb hrun l.arr hsep]
        exact blankLevel_cells H l

/-! ## Annotation reachability -/

/-- Annotation reachability along the path: every reference the built program
extracts is in the root's mutable footprint, and the leaf body's annotations lift
from the innermost state's footprint by transitivity. -/
theorem annotationsIn_of_path {H : Heap} {body : NCode} {path value : Var} :
    ∀ (rest : List Level) (l : Level) (root tip : Ref),
      Slots H (l :: rest) → Chained (l :: rest) → l.arr = root →
      EndsAt tip (l :: rest) → Live H tip → AnnotationsIn H tip body →
      AnnotationsIn H root (build path value body (l :: rest)) := by
  intro rest
  induction rest with
  | nil =>
      intro l root tip hslots hchain harr hends htip hann
      have hchild : l.child = tip := hends
      have hfp : MutableFootprint H root l.child := by
        rw [← harr]
        exact children_mem htip [] l hslots hchain hends l (by simp)
      rw [hchild] at hfp
      simp only [build]
      exact ⟨by rw [hchild]; exact hfp, AnnotationsIn.trans hfp hann, trivial⟩
  | cons m rest' ih =>
      intro l root tip hslots hchain harr hends htip hann
      obtain ⟨hchild, hcv, hchainTail⟩ := hchain
      have hslotsTail : Slots H (m :: rest') :=
        fun k hk => hslots k (List.mem_cons_of_mem _ hk)
      have htail : AnnotationsIn H m.arr (build path value body (m :: rest')) :=
        ih m m.arr tip hslotsTail hchainTail rfl hends htip hann
      have harrMem : MutableFootprint H root m.arr := by
        rw [← harr]
        exact arrs_mem (m :: rest') l hslots ⟨hchild, hcv, hchainTail⟩ hends m (by simp)
      have hchildMem : MutableFootprint H root l.child := by
        rw [← harr]
        exact children_mem htip (m :: rest') l hslots ⟨hchild, hcv, hchainTail⟩ hends l
          (by simp)
      simp only [build]
      exact ⟨hchildMem, AnnotationsIn.trans harrMem htail, trivial⟩

end Path
end Ownership
