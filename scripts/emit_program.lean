/-
Emit a checked model program as Lean source.

This is the other direction of the bridge: instead of reflecting Lean into the
model, a `Ownership.Code` program is first accepted by the discipline's checker
and then emitted as Lean, so the binary that runs is derived from the checked
program rather than hand-written.

Run from the repository root:

    nix develop -c lake env lean scripts/emit_program.lean

It writes `bench/Generated.lean`, builds via the `generated` target of the bench
package, and prints the model interpreter's result for comparison.
-/
import Ownership.Code

open Ownership

namespace EmitProgram

/-- The checker's context for the program: variable 0 owns the array, variables
1-4 are scalars, and the array's multiplicity is one. -/
def ctx : Ctx :=
  { us := fun x => if x = 0 then .owned else if x ≤ 4 then .scalar else .dead
    refOf := fun x => if x = 0 then some 0 else none
    mult := fun r => if r = 0 then 1 else 0 }

def obj : Obj :=
  { fields := #[.scalar 0, .scalar 0, .scalar 0, .scalar 0], rc := 1, persistent := false }

def heap : Heap := { cells := fun r => if r = 0 then some obj else none, next := 1 }

/-- The environment: variable 0 names the array, 1 and 3 are the two indices,
2 and 4 the two values. -/
def env : Env := fun x =>
  match x with
  | 0 => some (.ref 0) | 1 => some (.scalar 1) | 2 => some (.scalar 7)
  | 3 => some (.scalar 3) | 4 => some (.scalar 9) | _ => none

/-- Two in-place writes into the owned array, then return it. -/
def prog : Code := .setArr 0 1 2 (.setArr 0 3 4 (.ret 0))

/-- Emit the program body. Ownership operations (`inc`, `dec`, `check`) have no
source-level counterpart: Lean's reference counting inserts them itself, so they
are dropped. `isShared` has no faithful source form here and is not used. -/
def emitBody : Code → String
  | .ret x => s!"v{x}"
  | .setArr x i v k => s!"(let v{x} := v{x}.set! v{i} v{v}; {emitBody k})"
  | .let x (.lit n) k => s!"(let v{x} := {n}; {emitBody k})"
  | .let x (.size a) k => s!"(let v{x} := v{a}.size; {emitBody k})"
  | .let x (.checkAlias a) k => s!"(let v{x} := v{a}; {emitBody k})"
  | .let _ (.isShared _) _ => "sorry"
  | .inc _ _ k => emitBody k
  | .dec _ _ k => emitBody k
  | .check _ k => emitBody k

def source : String :=
  "def program (v0 : Array Nat) (v1 v2 v3 v4 : Nat) : Array Nat :=\n  " ++
    emitBody prog ++ "\n\n" ++
  "def main : IO Unit := do\n" ++
  "  let a := #[0, 0, 0, 0]\n" ++
  "  IO.println s!\"{program a 1 7 3 9}\"\n"

def modelOut : String :=
  match run prog env heap with
  | .done H _ _ _ => s!"model result: {repr ((H.cells 0).map (fun o => o.fields.toList))}"
  | .fault _ _ f _ => s!"model fault: {repr f}"

def main : IO Unit := do
  IO.println s!"checker accepts: {(check ctx prog).isSome}"
  IO.println modelOut
  IO.FS.writeFile "bench/Generated.lean" source
  IO.println "wrote bench/Generated.lean"

end EmitProgram

#eval EmitProgram.main
