# Encapsulation, duplication, and the runner-owned ledger

Status: argument for supervisor review. Lean fragments marked **repository** are
from the checked tree and build under `nix develop -c lake build Cap`; fragments
marked **illustrative** are the smallest shape of the idea and are not claimed to
compile verbatim.

## The question

Does an opaque handle type, whose use must be authorised by a ledger of the same
kind, close the "use the same value twice" hole? Concretely: is Rust-like
ownership/borrowing enforceable as an embedded discipline in Lean, without a
linear host type system?

## The claim

Yes, with a precise location for the guarantee.

1. **True encapsulation of the representation is possible** in Lean: private
   constructors/fields at a module boundary, or an `opaque` type with an interface.
   This closes extraction and construction.
2. **Encapsulation does not close duplication.** Lean copies values freely, and an
   interface function can be applied to each copy. Closed: construction and
   observation. Open: usage multiplicity.
3. **A ledger handed to the client as a value does not close it either.** Copy the
   ledger, obtain two authorisations; or keep a proof issued before a state change
   and replay it on the stale value.
4. **A ledger owned by the runner does close it**, because the client cannot name
   the current state: authority is a position in the runner's threaded ledger, and a
   duplicated handle is only a duplicated name. Duplicating the *program* is
   harmless: each run starts from a fresh ledger.
5. The guarantee therefore lives in the checker/runner (or a linear host, or a
   runtime consumed-flag), not in the opacity of the type.

## 1. The `Sigma` is not encapsulated

```lean
-- illustrative
def pkg : Sigma (fun R : Type => R) := ⟨Nat, 0⟩

def extract : Nat := pkg.2   -- `.1` and `.2` are public
```

Making it `Exists` (a `Prop`) hides the representation but forbids eliminating the
value into computation, so the payload cannot be used at all. Data must live in
`Type`, and `Type`-level pairs project.

## 2. Private fields encapsulate the payload, not its use

**Repository:** `bench/OwnedStatic.lean`

```lean
structure Owned (α : Type) where
  private mk ::
  private val : Array α
```

A different module cannot name `.val` or the constructor; the observed diagnostic
in `bench/OwnedNoAccess.lean` is

```text
error: Field 'val' from structure 'Owned' is private
```

But duplication is still legal in Lean:

```lean
-- illustrative; the same shape as the earlier probe
def dup (a : Owned α) : Owned α × Owned α := (a, a)
```

and a public operation can be applied to both copies. The payload is safe; the
usage is not counted.

`opaque` is stronger for abstraction:

```lean
-- illustrative
opaque Owned (α : Type) : Type
def new (a : α) : Owned α := ...
def op  (o : Owned α) : α := ...
```

No constructor, field or pattern match is visible, but `let b := a` still copies
the value and `op` can be called twice.

**Repository confirmation:** the prototype pairs the private payload with either a
shared used-flag (`bench/OwnedDemo.lean`, runtime refusal) or the reflective
one-transfer check (`bench/OwnedStatic.lean`, elaboration-time refusal). Neither
is a property of the opaque type itself.

## 3. A ledger or proof handed to the client is copyable

```lean
-- illustrative
opaque Ledger : Type
opaque Cap : Type

def authorize : Ledger → Cap → Option Proof
```

The client can write

```lean
-- illustrative
let l₂ := l₁
match authorize l₁ c, authorize l₂ c with
| some p₁, some p₂ => (use p₁, use p₂)
| _, _ => ...
```

The second authorisation is manufactured from a copy of the state. The same applies
to a proof-valued argument:

```lean
-- illustrative
def write (l : Ledger) (c : Cap) (p : Allowed l c) : Result
```

`Allowed` is a proposition, so `p` is duplicable, and `l` is a value. A stale `p`
also applies to the old `l` after the runner has advanced. Lean has no linearity
to consume either.

**Repository correspondence.** `Owner.Writable D id i` is exactly such a
proposition, about an immutable `Owner`:

```lean
-- repository: Cap/Ledger.lean
def Owner.Writable (o : Owner) (D : Nat) (id : CapId) (i : Nat) : Prop :=
  ∃ c, o.root.find? id = some c ∧ c.state = .active ∧ c.q = D ∧
    c.ceiling = .readWrite ∧ c.lo ≤ i ∧ i < c.hi
```

It can be reused on the old `o`, which is why the pure model alone is not
encapsulation. The model is a statement about runs, not a capability the host
cannot copy.

## 4. The runner-owned ledger

The ledger is not a client value; the only surface is a program run by an
interpreter that threads it.

```lean
-- illustrative
opaque Ledger : Type
opaque Cap : Type

-- not exported
def step : Ledger → Op → Option (Ledger × Result)

-- the only public execution entry point
def run : Program → Result
```

Properties:

- A `Cap` in client hands is an inert name. Copying it yields two names for the
  same entry; it does not yield two entries.
- Permission is a judgment on the current ledger at each `step`, not a proof the
  client keeps.
- A duplicated *program* is a duplicated description; `run` gives each execution a
  fresh ledger (the design's fresh-arena rule).
- No `runWith (arena)` and no cast from a claimed context to a realised state.

**Repository correspondence.**

```lean
-- repository: Cap/Unified.lean
def World.writeChecked (w : World) (a : AllocId) (id : CapId) (i : Nat) (v : UInt8) :
    Except String World :=
  match w.ctx.findOwner? a with
  | none => .error "write: no owner for the allocation"
  | some o =>
    match w.heaps a with
    | none => .error "write: no backend for the allocation"
    | some b =>
      if _hw : o.writableB w.ctx.D id i then
        match b.write i v with
        | none => .error "write: index out of range"
        | some b' =>
          .ok { w with heaps := fun x => if x = a then some b' else w.heaps x }
      else .error "write: capability is not writable at this index"

def checkWorld : World → List UCmd → Except String World
```

`checkWorld` is checker and interpreter at once: an accepted program returns the
world it executed. `World.writeChecked_sound` names the owner, its `Writable`
guard, the backend and the replacement; `checkWorld_rel` preserves `World.Rel`.
The 64-byte run through this route is checked at elaboration:

```lean
-- repository: Cap/Unified.lean
theorem uRun_snapshot :
    uRun = some (List.replicate 32 (1 : UInt8) ++ List.replicate 32 (2 : UInt8))
```

Security boundary, stated honestly: `World` is currently a public pure value, so a
client can copy it and branch. That is acceptable for a pure model, but it is not
the encapsulation the final runner must provide. The review's point stands: module
privacy over a `Ctx` a client can copy is not the foundation; the runner must own
the state.

## 5. World-indexed computations are the type-level companion

**Repository:** `Cap/Indexed.lean`

```lean
structure Ix (pre : World) (α : Type) (post : α → World) where
  run : (w : World) → w = pre → Option α
```

`bind` forces the continuation's pre-world to be the first computation's
post-world; `writeIx` carries the guard and indexes the world the write produces;
`prog_sound` shows that `checkWorld` reaches the same post-world. The indices are
ordinary `World` values, so closed instances evaluate at elaboration; there is no
elaborator inferring them for symbolic programs, and the runtime mutation is still
performed by the execution route.

## 6. What is not claimed

- Not that Lean's type system enforces linearity over arbitrary Lean code.
- Not that the current `Cap` API is encapsulated: `World` is a public pure value.
- Not that the checker and execution cover a complete program: `UCmd` currently has
  only writes and no-ops; splits, snapshot, free and loans are not in it.
- Not that logical permission implies RC = 1, no copying, or speed. In particular, a
  split array implemented as two Lean array views may still copy; that needs a
  backend representation contract (one backing allocation with checked slices, or a
  dedicated mutable buffer) plus a refinement theorem. The pure backend model and
  the timings do not establish it.

## 7. The argument in one line

Encapsulation gives you an interface; a runner-owned ledger gives you the
per-use check; together they close the duplication hole in Lean, while linearity
over arbitrary host code and speed guarantees remain outside what is proved.

## Review questions

1. Is the location of the guarantee (runner/checker, not opacity) the right one?
2. Is the public pure `World` acceptable as a model, with encapsulation deferred to
   the runner, or should the model itself hide the state?
3. Should the final surface expose only `run`-style entry points, with
   `Ledger`/`Ctx` unexported, and no `Ledger → ...` queries?
4. Is the fresh-ledger-per-run rule the right answer to program duplication?
