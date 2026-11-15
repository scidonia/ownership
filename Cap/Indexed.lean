/-
World-indexed computations.

`Ix pre α post` is a computation that starts in the world `pre`, returns an `α`,
and ends in the world `post a` for its result `a`. Composition (`bind`) requires
the continuation's precondition to be the first computation's postcondition, so
the worlds are threaded by the type. `writeIx` carries the ledger guard and the
backend write as hypotheses, and its post-index is the world the guarded write
produces.

Closed instances evaluate at elaboration: `prog_run` below computes a two-write
program's run. The indices are ordinary `World` values, not a new runtime state;
the executable route remains `Cap.Unified`'s `checkWorld`, and `prog_sound`
connects the indexed run to it for the concrete program.

This is a *specification* type: its `run` field does not, by itself, establish a
post-relation for an arbitrary inhabitant, and a client can build one with an
unrelated `run`. The certificate-carrying form is `Cap/Prog.lean`/`Cap/Runner.lean`,
where the syntax is packaged with `checkWorld`'s derivation.
-/
import Cap.Unified

namespace Cap

/-- The world after replacing the backend at `a` by `b'`. -/
def World.writePure (w : World) (a : AllocId) (b' : Backend) : World :=
  { w with heaps := fun x => if x = a then some b' else w.heaps x }

/-- A checked write whose conditions hold lands exactly on `writePure`. -/
theorem World.writeChecked_pure {w : World} {a : AllocId} {id : CapId} {i : Nat}
    {v : UInt8} {o : Owner} {b b' : Backend}
    (hf : w.ctx.findOwner? a = some o) (hw : o.writableB w.ctx.D id i = true)
    (hb : w.heaps a = some b) (hbw : b.write i v = some b') :
    w.writeChecked a id i v = .ok (w.writePure a b') := by
  simp [World.writeChecked, World.writePure, hf, hb, hw, hbw]

/-- A computation from `pre` returning `α` and ending in `post a`. -/
structure Ix (pre : World) (α : Type) (post : α → World) where
  run : (w : World) → w = pre → Option α

namespace Ix

/-- A value, leaving the world unchanged. -/
def ret (w : World) (a : α) : Ix w α (fun _ => w) where
  run _ _ := some a

/-- Sequential composition: the continuation starts in the world the first
computation produced. -/
def bind {pre : World} {α β : Type} {post : α → World} {post' : β → World}
    (m : Ix pre α post) (k : (a : α) → Ix (post a) β post') :
    Ix pre β post' where
  run w hw :=
    match m.run w hw with
    | none => none
    | some a => (k a).run (post a) rfl

end Ix

/-- A guarded write as an indexed computation. Its post-index is the world the
write produces. -/
def writeIx (pre : World) (a : AllocId) (id : CapId) (i : Nat) (v : UInt8)
    (o : Owner) (b b' : Backend)
    (hf : pre.ctx.findOwner? a = some o) (hw : o.writableB pre.ctx.D id i = true)
    (hb : pre.heaps a = some b) (hbw : b.write i v = some b') :
    Ix pre Unit (fun _ => pre.writePure a b') where
  run _ _ :=
    match pre.writeChecked a id i v with
    | .ok _ => some ()
    | .error _ => none

/-- The concrete first write: allocation 0, capability 1, index 0, value 1. -/
def ixOwner : Owner := uOwner

theorem ixFind : uWorld.ctx.findOwner? ⟨0⟩ = some ixOwner := by
  simp [uWorld, uOwner, ixOwner, Ctx.findOwner?, Owner.init]

theorem ixGuard : ixOwner.writableB 64 ⟨1⟩ 0 = true := by
  decide

theorem ixHeap : uWorld.heaps ⟨0⟩ = some (Backend.empty 64) := by
  simp [uWorld]

def b1 : Backend := (Backend.empty 64).write 0 1 |>.getD (Backend.empty 64)

theorem ixWrite1 : (Backend.empty 64).write 0 (1 : UInt8) = some b1 := by
  decide

def post1 : World := uWorld.writePure ⟨0⟩ b1

/-- The first step, indexed from `uWorld` to `post1`. -/
def step1 : Ix uWorld Unit (fun _ => post1) :=
  writeIx uWorld ⟨0⟩ ⟨1⟩ 0 1 ixOwner (Backend.empty 64) b1
    ixFind ixGuard ixHeap ixWrite1

/-- The second step starts in `post1`. -/
theorem ixFind2 : (uWorld.writePure ⟨0⟩ b1).ctx.findOwner? ⟨0⟩ = some ixOwner := by
  simp [World.writePure, ixFind]

theorem ixGuard2 : ixOwner.writableB 64 ⟨1⟩ 1 = true := by
  decide

theorem ixHeap2 : (uWorld.writePure ⟨0⟩ b1).heaps ⟨0⟩ = some b1 := by
  simp [World.writePure]

def b2 : Backend := b1.write 1 2 |>.getD b1

theorem ixWrite2 : b1.write 1 (2 : UInt8) = some b2 := by
  decide

def post2 : World := (uWorld.writePure ⟨0⟩ b1).writePure ⟨0⟩ b2

def step2 : Ix (uWorld.writePure ⟨0⟩ b1) Unit (fun _ => post2) :=
  writeIx (uWorld.writePure ⟨0⟩ b1) ⟨0⟩ ⟨1⟩ 1 2 ixOwner b1 b2
    ixFind2 ixGuard2 ixHeap2 ixWrite2

/-- The composed program: `bind` forces the second step's pre-world to be
`post1`. -/
def prog : Ix uWorld Unit (fun _ => post2) :=
  step1.bind (fun _ => step2)

theorem prog_run : prog.run uWorld rfl = some () := by
  simp only [prog, Ix.bind, step1, step2, writeIx]
  rw [World.writeChecked_pure ixFind ixGuard ixHeap ixWrite1]
  dsimp only
  rw [World.writeChecked_pure ixFind2 ixGuard2 ixHeap2 ixWrite2]

/-- The executable route reaches the same two worlds and therefore the post-index. -/
theorem prog_sound :
    checkWorld uWorld
      [UCmd.write ⟨0⟩ ⟨1⟩ 0 1, UCmd.write ⟨0⟩ ⟨1⟩ 1 2] = .ok post2 := by
  simp only [checkWorld]
  rw [World.writeChecked_pure ixFind ixGuard ixHeap ixWrite1]
  dsimp only
  rw [World.writeChecked_pure ixFind2 ixGuard2 ixHeap2 ixWrite2]
  rfl

end Cap
