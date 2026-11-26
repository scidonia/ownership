/-
The one-byte store kernel, from C through clang into the LeanLLVM model.

`c/store8.c` is

```c
void store8(uint8_t *p, uint64_t i, uint8_t v) { p[i] = v; }
```

`scripts/emit-ir.sh` compiles it with the worker's clang and stores two files:
`ir/store8.raw.ll` is the emission verbatim, and `ir/store8.ll` is the same
emission projected onto the textual surface `LeanLLVM.Parser` accepts.  The
projection is mechanical (`scripts/project-ir.sed`: the function attribute
group, the parameter attributes, the metadata attachments, the `nuw` modifier,
the module-level header lines, and the absent entry label).  `store8Text` is
`ir/store8.ll`, and the `#guard` below pins the parsed AST against the literal
`store8IR`, so the theorems are statements about the emitted body rather than
about a transcription.

What is proved:

* `runFuel_store8IR_succ` — one control step from any state binding the three
  parameters runs the block and leaves exactly one byte written.
* `runFuel_store8IR` — the same at `initState` for the argument list the kernel
  is called with.
* `Beh_store8IR_iff` — the compiled body's behaviour set at a pointer/index/byte
  argument list is exactly the reference store's single outcome: the returned
  value is `none` (the C function is `void`) and the memory is the model store's.
  There is no `ub` run and no divergent run at that argument list, so the
  relation's `ub`/divergence handling is discharged rather than assumed.
* `store8IR_refines_model` and `store8IR_completes` — the two halves: every
  behaviour is the model's, and the model's outcome is a behaviour.
* `store8IR_byte`, `store8IR_frame` and `store8Model_replay_read` — the
  observable byte, the framed view outside the written address, and the replay
  policy at the observation level.
* `store8IR_refines_store8Ref` — the same inclusion against an authored
  reference kernel that *calls* the model store through a `Calls` environment,
  for every pointer, `i64` index and `i8` byte (the reference is undefined
  exactly when it does not model the index, which the relation admits).

What is not proved here: anything about the ownership discipline.  The closing
section records exactly which `Cap` predicate the observable corresponds to and
which obligations remain.  No `Cap` module is imported: this package builds
against `LeanLLVM` at Lean `v4.35.0`, while `Cap` is built at the ownership
repository's toolchain, and mixing the two would be a different boundary than
the one this file states.
-/
import LeanLLVM.Parser
import LeanLLVM.Frames

namespace LlvmBridge

open LeanLLVM

/-! ### The emitted body -/

/-- `ir/store8.ll`: clang's emission for `c/store8.c`, in the parser's surface. -/
def store8Text : String := include_str "../ir/store8.ll"

/-- The first function of a parsed module, or `none`. -/
def firstFunction (src : String) : Option Function :=
  match parseModule src with
  | .ok m => m.functions.head?
  | .error _ => none

/-- `ir/store8.ll` as an AST.  Register `%4` is the numbering clang gives the
`getelementptr` result; the parameters are `%0`, `%1` and `%2`. -/
def store8IR : Function :=
  { name := "store8"
    retTy := .void
    params := [("%0", .ptr), ("%1", .int 64), ("%2", .int 8)]
    blocks :=
      [{ name := "entry"
         instrs :=
           [ .gep "%4" (.int 8) (.reg "%0") (.reg "%1"),
             .store (.int 8) (.reg "%2") (.reg "%4") ]
         term := .ret .void none }] }

-- The committed text parses to the committed AST.  `#guard` rather than `rfl`:
-- the parser is written on `String` primitives, which the kernel does not reduce.
#guard decide (firstFunction store8Text = some store8IR)

/-! ### The reference store -/

/-- The byte `storeValue` writes for an `i8` value `x`: `natToBytes x.toNat 1` is
this byte's singleton list. -/
def byteOf (x : BitVec 8) : UInt8 := UInt8.ofNat (x.toNat % 256)

/-- The reference semantics: write one byte at `base + off` of the model memory. -/
def store8Model (m : Mem) (base off : Nat) (b : UInt8) : Mem :=
  writeByte m (base + off) b

/-- The argument list the kernel is called with: a pointer, an `i64` index and
the byte.  The index is kept as the bitvector the run reads, so the model's
sign-extended address `(x.signExtend 64).toNat` is the one the semantics uses. -/
def store8Args (p : Nat) (x : BitVec 64) (v : BitVec 8) : List Value :=
  [.ptr p, .int 64 x, .int 8 v]

/-- The address the model's `getelementptr i8` binds in its adding case.  At the
model's pointer width `(x.signExtend 64).toNat` is `x.toNat`, and the adding case
is exactly `x.toNat < 2 ^ 63`. -/
def store8Addr (p : Nat) (x : BitVec 64) : Nat := p + x.toNat

/-- Binding a register does not touch the memory. -/
@[simp] theorem State.bind_mem (s : State) (n : String) (v : Value) :
    (s.bind n v).mem = s.mem := rfl

/-- Binding a register conses its cell onto the environment. -/
@[simp] theorem State.bind_env (s : State) (n : String) (v : Value) :
    (s.bind n v).env = (n, v) :: s.env := rfl

/-! ### One instruction at a time

`evalInstr` reads the register environment through `lookupName`; these two
lemmas state the two instructions of the block at a state whose environment the
caller supplies, so the block's evaluation never copies a symbolic environment. -/

/-- The `getelementptr i8` of the emitted body, in its adding case.  That case is
the one a non-negative index reaches; the subtracting case (an index at or above
`2 ^ 63`) is the model's signed reading of an index, and the reference kernel
below is undefined there rather than approximating it. -/
theorem evalInstr_gep_store8 (calls : Calls) (s : State) (p : Nat) (x : BitVec 64)
    (h0 : lookupName s.env "%0" = some (.ptr p))
    (h1 : lookupName s.env "%1" = some (.int 64 x))
    (hpos : x.toNat < 2 ^ 63) :
    evalInstr calls s (.gep "%4" (.int 8) (.reg "%0") (.reg "%1")) =
      some (s.bind "%4" (.ptr (store8Addr p x))) := by
  have hpos' : (x.signExtend 64).toNat < 2 ^ 63 := by simpa using hpos
  rw [evalInstr_gep_i8 (evalOperand_reg_of h0) (evalOperand_reg_of h1) hpos']
  simp [store8Addr]

/-- The `store i8` of the emitted body, at a state whose `%4` holds the address
and whose `%2` holds the byte. -/
theorem evalInstr_store8 (calls : Calls) (s : State) (a : Nat) (v : BitVec 8)
    (h2 : lookupName s.env "%2" = some (.int 8 v))
    (h4 : lookupName s.env "%4" = some (.ptr a)) :
    evalInstr calls s (.store (.int 8) (.reg "%2") (.reg "%4")) =
      some { s with mem := writeBytes s.mem a (natToBytes v.toNat 1) } := by
  have h2' : evalOperand s (.reg "%2") = some (.int 8 v) := evalOperand_reg_of h2
  have h4' : evalOperand s (.reg "%4") = some (.ptr a) := evalOperand_reg_of h4
  simp only [evalInstr, h2', h4']
  simp [storeValue, natToBytes]

/-! ### The block and the step -/

/-- The block's instruction sequence, evaluated. -/
theorem denoteCode_store8 (s : State) (p : Nat) (x : BitVec 64) (v : BitVec 8)
    (h0 : lookupName s.env "%0" = some (.ptr p))
    (h1 : lookupName s.env "%1" = some (.int 64 x))
    (h2 : lookupName s.env "%2" = some (.int 8 v))
    (hpos : x.toNat < 2 ^ 63) :
    denoteCode noCalls
        [ .gep "%4" (.int 8) (.reg "%0") (.reg "%1"),
          .store (.int 8) (.reg "%2") (.reg "%4") ] s =
      some { (s.bind "%4" (.ptr (store8Addr p x))) with
               mem := writeBytes s.mem (store8Addr p x) (natToBytes v.toNat 1) } := by
  rw [denoteCode_cons_of noCalls _ _ _ _
    (evalInstr_gep_store8 noCalls s p x h0 h1 hpos)]
  rw [denoteCode_cons_of noCalls _ _ _ _
    (evalInstr_store8 noCalls _
      (a := store8Addr p x) (v := v)
      (by rw [State.bind_env, lookupName_cons_ne _ _ (by decide)]; exact h2)
      (by rw [State.bind_env, lookupName_cons_self]))]
  simp [denoteCode, denoteRun, State.bindAll]

/-- The one control step the block takes. -/
theorem step_store8IR (s : State) (p : Nat) (x : BitVec 64) (v : BitVec 8)
    (hpc : s.pc = "entry")
    (h0 : lookupName s.env "%0" = some (.ptr p))
    (h1 : lookupName s.env "%1" = some (.int 64 x))
    (h2 : lookupName s.env "%2" = some (.int 8 v))
    (hpos : x.toNat < 2 ^ 63) :
    step noCalls store8IR s =
      .ret none { (s.bind "%4" (.ptr (store8Addr p x))) with
                    mem := writeBytes s.mem (store8Addr p x) (natToBytes v.toNat 1) } := by
  have hfind : store8IR.findBlock "entry" =
      some { name := "entry"
             instrs :=
               [ .gep "%4" (.int 8) (.reg "%0") (.reg "%1"),
                 .store (.int 8) (.reg "%2") (.reg "%4") ]
             term := .ret .void none } := by
    simp [store8IR, Function.findBlock, findBlockList]
  simp only [step, hpc, hfind, denoteCode_store8 s p x v h0 h1 h2 hpos]
  simp [execTerm]

/-! ### The runs -/

/-- Writing the one-byte list `natToBytes x.toNat 1` is writing the byte
`byteOf x`. -/
theorem writeBytes_natToBytes_one (m : Mem) (addr : Nat) (x : BitVec 8) :
    writeBytes m addr (natToBytes x.toNat 1) = writeByte m addr (byteOf x) := rfl

/-- From any state binding the three parameters, one control step of the emitted
body leaves the reference store's memory and returns nothing. -/
theorem runFuel_store8IR_succ (s : State) (p : Nat) (x : BitVec 64) (v : BitVec 8)
    (hpc : s.pc = "entry")
    (h0 : lookupName s.env "%0" = some (.ptr p))
    (h1 : lookupName s.env "%1" = some (.int 64 x))
    (h2 : lookupName s.env "%2" = some (.int 8 v))
    (hpos : x.toNat < 2 ^ 63) (n : Nat) :
    runFuel noCalls (n + 1) store8IR s =
      some (.ret none (writeByte s.mem (store8Addr p x) (byteOf v))) := by
  simp [runFuel, step_store8IR s p x v hpc h0 h1 h2 hpos,
    writeBytes_natToBytes_one]

/-- The emitted body at the kernel's call site: the block's one step writes the
byte at `store8Addr p x`. -/
theorem runFuel_store8IR (p : Nat) (x : BitVec 64) (v : BitVec 8)
    (hpos : x.toNat < 2 ^ 63) (n : Nat) :
    runFuel noCalls (n + 1) store8IR (initState store8IR (store8Args p x v)) =
      some (.ret none (writeByte [] (store8Addr p x) (byteOf v))) := by
  have hpc : (initState store8IR (store8Args p x v)).pc = "entry" := rfl
  have h0 : lookupName (initState store8IR (store8Args p x v)).env "%0" =
      some (.ptr p) := by
    simp [initState, store8IR, store8Args]
  have h1 : lookupName (initState store8IR (store8Args p x v)).env "%1" =
      some (.int 64 x) := by
    simp [initState, store8IR, store8Args, lookupName]
  have h2 : lookupName (initState store8IR (store8Args p x v)).env "%2" =
      some (.int 8 v) := by
    simp [initState, store8IR, store8Args, lookupName]
  simpa [initState] using
    runFuel_store8IR_succ (initState store8IR (store8Args p x v)) p x v
      hpc h0 h1 h2 hpos n

/-! ### The refinement

`Beh` is `LeanLLVM`'s behaviour set: an outcome is reachable when a finite run
returns it, or when a run reaches `ub` on some prefix (which admits every
outcome).  A run that never finishes contributes nothing.  The statement below
therefore covers the relation's `ub` direction — no prefix of the emitted body
is `ub` at this argument list — and its divergence direction — the one outcome
is produced at fuel one, on every budget. -/

/-- The emitted body's behaviour at the kernel's call site is exactly the
reference store's single outcome. -/
theorem Beh_store8IR_iff (p : Nat) (x : BitVec 64) (v : BitVec 8)
    (hpos : x.toNat < 2 ^ 63) (out : Outcome) :
    Beh noCalls store8IR (store8Args p x v) out ↔
      out = .ret none (store8Model [] p x.toNat (byteOf v)) := by
  constructor
  · rintro (⟨n, hn⟩ | ⟨n, hn⟩)
    · rcases n with _ | m
      · simp [runFuel] at hn
      · rw [runFuel_store8IR p x v hpos m] at hn
        simp at hn
    · rcases n with _ | m
      · simp [runFuel] at hn
      · rw [runFuel_store8IR p x v hpos m] at hn
        exact (Option.some.inj hn).symm
  · intro h
    subst h
    exact Or.inr ⟨1, runFuel_store8IR p x v hpos 0⟩

/-- Every behaviour of the emitted body is the reference store's outcome: the
inclusion half of the refinement, stated at `Beh`. -/
theorem store8IR_refines_model (p : Nat) (x : BitVec 64) (v : BitVec 8)
    (hpos : x.toNat < 2 ^ 63) :
    ∀ out, Beh noCalls store8IR (store8Args p x v) out →
      out = .ret none (store8Model [] p x.toNat (byteOf v)) :=
  fun out h => (Beh_store8IR_iff p x v hpos out).mp h

/-- The reference store's outcome is a behaviour of the emitted body: the
completion half, so divergence is not being bought by an empty behaviour set. -/
theorem store8IR_completes (p : Nat) (x : BitVec 64) (v : BitVec 8)
    (hpos : x.toNat < 2 ^ 63) :
    Beh noCalls store8IR (store8Args p x v)
      (.ret none (store8Model [] p x.toNat (byteOf v))) :=
  (Beh_store8IR_iff p x v hpos _).mpr rfl

/-! ### The observable byte, the frame and replay -/

/-- The written byte is observable at the address the kernel computed. -/
theorem store8Model_read_at (m : Mem) (p off : Nat) (b : UInt8) :
    readByte (store8Model m p off b) (p + off) = some b := by
  simp [store8Model, readByte_writeByte_same]

/-- Outside the written address the reference store leaves every byte as it was,
which is `AgreesOutsideMem` at the one-address frame. -/
theorem store8Model_frame (m : Mem) (p off : Nat) (b : UInt8) :
    AgreesOutsideMem (store8Model m p off b) m (fun a => a = p + off) := by
  intro c hc
  rw [show readByte (store8Model m p off b) c
        = readByte (writeByte m (p + off) b) c from rfl]
  rw [readByte_writeByte_other m b (by intro h; exact hc h.symm)]

/-- A second identical store observes exactly what the first one left: the
kernel is replayable at the observation level. -/
theorem store8Model_replay_read (m : Mem) (p off : Nat) (b : UInt8) (a : Nat) :
    readByte (store8Model (store8Model m p off b) p off b) a
      = readByte (store8Model m p off b) a := by
  by_cases h : a = p + off
  · subst h
    simp [store8Model, readByte_writeByte_same]
  · have hne : p + off ≠ a := by intro hc; exact h hc.symm
    simp [store8Model, readByte_writeByte_other, hne]

/-- The compiled run's observable byte: at the kernel's call site the byte the
emitted body leaves at its address is the argument byte. -/
theorem store8IR_byte (p : Nat) (x : BitVec 64) (v : BitVec 8) :
    readByte (store8Model [] p x.toNat (byteOf v))
      (store8Addr p x) = some (byteOf v) :=
  store8Model_read_at [] p x.toNat (byteOf v)

/-- The compiled run's frame: every address other than the written one still
reads as the memory the run started from. -/
theorem store8IR_frame (m : Mem) (p off : Nat) (b : UInt8) :
    AgreesOutsideMem (store8Model m p off b) m (fun a => a = p + off) :=
  store8Model_frame m p off b

/-! ### A reference kernel that calls the model store

The reference side is an AST too: one `call void @store8.model(...)` and a
`void` return.  Its meaning is the `Calls` environment below, which writes the
byte the model store writes.  The refinement is then an inclusion between the
compiled body's behaviours and the reference kernel's — the shape `Refines`
compares, with the target in the empty call environment and the reference in
the model environment.  The index's subtracting case (an index at or above
`2 ^ 63`) is not modelled by the reference: there the reference is undefined,
which admits every compiled behaviour, so the inclusion still holds. -/

/-- The reference kernel: call the model store, return. -/
def store8Ref : Function :=
  { name := "store8.ref"
    retTy := .void
    params := [("%0", .ptr), ("%1", .int 64), ("%2", .int 8)]
    blocks :=
      [{ name := "entry"
         instrs :=
           [ .callVoid "store8.model"
               [ (.ptr, .reg "%0"), (.int 64, .reg "%1"), (.int 8, .reg "%2") ] ]
         term := .ret .void none }] }

/-- The model store as a call environment: `store8.model` writes one byte at
`store8Addr p x` in the index's adding case, and is unresolved outside it. -/
def store8Calls : Calls
  | "store8.model", [.ptr p, .int 64 x, .int 8 v], m, next =>
      if x.toNat < 2 ^ 63 then
        some ⟨.int 8 0,
          writeBytes m (store8Addr p x) (natToBytes v.toNat 1), next⟩
      else none
  | _, _, _, _ => none

/-- One control step of the reference kernel: the call writes the byte and
leaves the allocator where it found it, and the `void` return discards the
call's value. -/
theorem runFuel_store8Ref_succ (s : State) (p : Nat) (x : BitVec 64) (v : BitVec 8)
    (hpc : s.pc = "entry")
    (h0 : lookupName s.env "%0" = some (.ptr p))
    (h1 : lookupName s.env "%1" = some (.int 64 x))
    (h2 : lookupName s.env "%2" = some (.int 8 v))
    (hpos : x.toNat < 2 ^ 63) (n : Nat) :
    runFuel store8Calls (n + 1) store8Ref s =
      some (.ret none (writeByte s.mem (store8Addr p x) (byteOf v))) := by
  have hfind : store8Ref.findBlock "entry" =
      some { name := "entry"
             instrs :=
               [ .callVoid "store8.model"
                   [ (.ptr, .reg "%0"), (.int 64, .reg "%1"), (.int 8, .reg "%2") ] ]
             term := .ret .void none } := by
    simp [store8Ref, Function.findBlock, findBlockList]
  have h0' : evalOperand s (.reg "%0") = some (.ptr p) := evalOperand_reg_of h0
  have h1' : evalOperand s (.reg "%1") = some (.int 64 x) := evalOperand_reg_of h1
  have h2' : evalOperand s (.reg "%2") = some (.int 8 v) := evalOperand_reg_of h2
  simp only [runFuel, step, hpc, hfind, denoteCode, denoteRun, evalInstr,
    evalOperands, h0', h1', h2', State.bindAll, store8Calls, hpos, ite_eq_left,
    execTerm, writeBytes_natToBytes_one]

/-- The reference kernel is undefined — one step reaching `ub` — when the index
is not in the model store's adding case. -/
theorem runFuel_store8Ref_ub (s : State) (p : Nat) (x : BitVec 64) (v : BitVec 8)
    (hpc : s.pc = "entry")
    (h0 : lookupName s.env "%0" = some (.ptr p))
    (h1 : lookupName s.env "%1" = some (.int 64 x))
    (h2 : lookupName s.env "%2" = some (.int 8 v))
    (hneg : ¬ x.toNat < 2 ^ 63) :
    runFuel store8Calls 1 store8Ref s = some .ub := by
  have hfind : store8Ref.findBlock "entry" =
      some { name := "entry"
             instrs :=
               [ .callVoid "store8.model"
                   [ (.ptr, .reg "%0"), (.int 64, .reg "%1"), (.int 8, .reg "%2") ] ]
             term := .ret .void none } := by
    simp [store8Ref, Function.findBlock, findBlockList]
  have h0' : evalOperand s (.reg "%0") = some (.ptr p) := evalOperand_reg_of h0
  have h1' : evalOperand s (.reg "%1") = some (.int 64 x) := evalOperand_reg_of h1
  have h2' : evalOperand s (.reg "%2") = some (.int 8 v) := evalOperand_reg_of h2
  simp [runFuel, step, hpc, hfind, denoteCode, denoteRun, evalInstr, evalOperands,
    h0', h1', h2', State.bindAll, store8Calls, hneg]

/-- The reference kernel's behaviour at the call site: the model store's one
outcome, with no `ub` and no divergence. -/
theorem Beh_store8Ref_iff (p : Nat) (x : BitVec 64) (v : BitVec 8)
    (hpos : x.toNat < 2 ^ 63) (out : Outcome) :
    Beh store8Calls store8Ref (store8Args p x v) out ↔
      out = .ret none (store8Model [] p x.toNat (byteOf v)) := by
  have hpc : (initState store8Ref (store8Args p x v)).pc = "entry" := rfl
  have h0 : lookupName (initState store8Ref (store8Args p x v)).env "%0" =
      some (.ptr p) := by
    simp [initState, store8Ref, store8Args]
  have h1 : lookupName (initState store8Ref (store8Args p x v)).env "%1" =
      some (.int 64 x) := by
    simp [initState, store8Ref, store8Args, lookupName]
  have h2 : lookupName (initState store8Ref (store8Args p x v)).env "%2" =
      some (.int 8 v) := by
    simp [initState, store8Ref, store8Args, lookupName]
  have hrun : ∀ n, runFuel store8Calls (n + 1) store8Ref
      (initState store8Ref (store8Args p x v)) =
        some (.ret none (store8Model [] p x.toNat (byteOf v))) := by
    intro n
    simpa only [initState, store8Model, store8Addr] using
      runFuel_store8Ref_succ (initState store8Ref (store8Args p x v)) p x v
        hpc h0 h1 h2 hpos n
  constructor
  · rintro (⟨n, hn⟩ | ⟨n, hn⟩)
    · rcases n with _ | m
      · simp [runFuel] at hn
      · rw [hrun m] at hn
        simp at hn
    · rcases n with _ | m
      · simp [runFuel] at hn
      · rw [hrun m] at hn
        exact (Option.some.inj hn).symm
  · intro h
    subst h
    exact Or.inr ⟨1, hrun 0⟩

/-- When the reference does not model the index it is undefined, so it admits
every outcome the compiled body can produce. -/
theorem Beh_store8Ref_ub (p : Nat) (x : BitVec 64) (v : BitVec 8)
    (hneg : ¬ x.toNat < 2 ^ 63) (out : Outcome) :
    Beh store8Calls store8Ref (store8Args p x v) out := by
  have hpc : (initState store8Ref (store8Args p x v)).pc = "entry" := rfl
  have h0 : lookupName (initState store8Ref (store8Args p x v)).env "%0" =
      some (.ptr p) := by
    simp [initState, store8Ref, store8Args]
  have h1 : lookupName (initState store8Ref (store8Args p x v)).env "%1" =
      some (.int 64 x) := by
    simp [initState, store8Ref, store8Args, lookupName]
  have h2 : lookupName (initState store8Ref (store8Args p x v)).env "%2" =
      some (.int 8 v) := by
    simp [initState, store8Ref, store8Args, lookupName]
  exact Or.inl ⟨1, by
    simpa only [initState] using
      runFuel_store8Ref_ub (initState store8Ref (store8Args p x v)) p x v
        hpc h0 h1 h2 hneg⟩

/-- The compiled body refines the reference kernel: every behaviour the
clang-emitted `store8` produces at a pointer/index/byte argument list is a
behaviour of the reference kernel whose meaning is the model store. -/
theorem store8IR_refines_store8Ref (p : Nat) (x : BitVec 64) (v : BitVec 8) :
    ∀ out, Beh noCalls store8IR (store8Args p x v) out →
      Beh store8Calls store8Ref (store8Args p x v) out := by
  intro out h
  by_cases hpos : x.toNat < 2 ^ 63
  · rw [Beh_store8Ref_iff p x v hpos out]
    exact (Beh_store8IR_iff p x v hpos out).mp h
  · exact Beh_store8Ref_ub p x v hpos out

/-! ### Concrete controls -/

-- A concrete run of the emitted body: byte `7` lands at address `103`.
#guard run noCalls store8IR (store8Args 100 (BitVec.ofNat 64 3) (BitVec.ofNat 8 7)) 8 =
  some (.ret none (writeByte [] 103 (UInt8.ofNat 7)))

-- The same run through the reference kernel.
#guard run store8Calls store8Ref (store8Args 100 (BitVec.ofNat 64 3)
    (BitVec.ofNat 8 7)) 8 =
  some (.ret none (writeByte [] 103 (UInt8.ofNat 7)))

-- The observable byte of that run.
#guard readByte (store8Model [] 100 3 (UInt8.ofNat 7)) 103 = some (UInt8.ofNat 7)

/-! ### The axiom footprint

The standard floor, not a new axiom: `propext` and `Quot.sound` arrive with the
`Option`/`Refines` vocabulary the relation is stated in, and `Classical.choice`
from the same library surface `RefinesWithin` already pays.  No `sorryAx`, no
`native_decide`, no bit-blasting axiom. -/

/--
info: 'LlvmBridge.Beh_store8IR_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms LlvmBridge.Beh_store8IR_iff

/--
info: 'LlvmBridge.store8IR_refines_model' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms LlvmBridge.store8IR_refines_model

/--
info: 'LlvmBridge.store8IR_frame' depends on axioms: [propext]
-/
#guard_msgs in
#print axioms LlvmBridge.store8IR_frame

/--
info: 'LlvmBridge.store8IR_refines_store8Ref' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms LlvmBridge.store8IR_refines_store8Ref

/-! ### The remaining relation to the ownership model

Nothing in this file mentions `Cap`, and no `Cap` theorem is composed with
these.  What corresponds, precisely:

* **The observable byte.**  `readByte` on the model memory is the flat view.
  The ownership model's byte observation is `Cap.State.read?` (in
  `Cap.Integrated`), which resolves through `Cap.Heap.read?` and the backend's
  `Cap.Backend.read` at `(alloc, offset)`.  Matching the two needs an address
  map `addr = base alloc + offset` that neither development formalizes; the
  loader's `Globals` in `LeanLLVM` and `AllocId` in `Cap` are the two ends of
  it.
* **The byte update.**  `store8Model` is `writeByte`; the corresponding
  ownership operation is `Cap.Backend.write` at one index, whose refinement of
  the reference heap is `Cap.Backend.write_refines`.
* **The access obligation.**  `LeanLLVM` has no permissions: a `store` writes
  whatever address it is given, appending a cell when none exists.  The
  ownership-side predicate that would have to hold at the call site is the
  guard of `Cap.World.write?` — the owner's `Writable` capability at that
  index — together with the reachability state `Cap.World.Rel` requires.  This
  kernel refinement neither assumes nor establishes it.
* **The frame.**  `store8IR_frame`'s `{p + off}` frame corresponds to
  `Cap.Footprint.View.Within` (the interval inside the allocation) and to
  `Cap.Heap.write_ne` (a write at one index leaves other reads alone).
* **Allocation failure, cleanup, snapshots.**  The kernel allocates nothing
  (`alloca`-free; the reference environment returns `next` unchanged) and frees
  nothing, so allocation failure and cleanup have no path here.  Snapshots are
  `Cap.Heap.snapshot?`'s copy; a snapshot taken before the write is unaffected
  by it, which is `Cap.Bytes.snapshot_independent` and is not restated over the
  flat memory here.
* **Replay and physical aliasing.**  `store8Model_replay_read` states that a
  repeated identical write is unobservable.  That is a statement about the
  model memory, not about two `Cap` values addressing one physical allocation:
  the physical-mutation boundary `F8` names (a sealed value copied by a Lean
  client, both copies reaching one mutable C allocation) is untouched.

So the exact remaining relation is: *the ownership invariant is not related to
this memory at all*.  A composed theorem would need (i) an address map from
`AllocId × Nat` into the flat memory with a proof that a live allocation's bytes
are exactly the backend's buffer, (ii) a call-site `Writable` guard discharged
by a `Cap` run, and (iii) preservation of `Cap.State.Inv` (and so `FullInv`)
across the call.  None of the three is proved, and the compiled-code claim here
stops at the model's byte memory.
-/

end LlvmBridge
