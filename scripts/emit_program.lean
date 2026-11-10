/-
Emit checked model programs as Lean, for timing.

A program in `Ownership.Code` is accepted by the discipline's checker and emitted
as Lean, so the binary that runs is derived from the checked program rather than
hand-written.

The family is a sequence of in-place writes into the owned array, alternating two
scalar indices. Because the checker requires the array's multiplicity to be one at
every write, every emitted program is a certified in-place path; there is no
certified shared variant to compare against. Unrolling is bounded: the compiler
elaborates the nested `let` chain, so very large write counts are slow to build.

Run from the repository root:

    nix develop -c lake env lean scripts/emit_program.lean

then

    cd bench && nix develop -c lake build generated && ./.lake/build/bin/generated
-/
import Ownership.Code

open Ownership

namespace EmitProgram

def ctx : Ctx :=
  { us := fun x => if x = 0 then .owned else if x ≤ 4 then .scalar else .dead
    refOf := fun x => if x = 0 then some 0 else none
    mult := fun r => if r = 0 then 1 else 0 }

/-- `m` sequential writes: alternate slots 1 and 3 with values 2 and 4. -/
def progN : Nat → Code
  | 0 => .ret 0
  | m + 1 =>
    if m % 2 == 0 then .setArr 0 1 2 (progN m) else .setArr 0 3 4 (progN m)

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

def programDef (m : Nat) : String :=
  s!"def program{m} (v0 : Array Nat) (v1 v2 v3 v4 : Nat) : Array Nat :=\n  " ++
    emitBody (progN m) ++ "\n"

/-- 200, 1000 and 4000 writes: enough to see per-write cost and to keep the
elaborator's time reasonable. -/
def sizes : List Nat := [200, 1000, 4000]

def timingMain : String :=
  "def main : IO Unit := do\n" ++
  "  let n := 1 <<< 20\n" ++
  "  let mk (n : Nat) : Array Nat := (List.replicate n 0).toArray\n" ++
  "  let cases : List (String × Nat × (Array Nat → Nat → Nat → Nat → Nat → Array Nat)) :=\n" ++
  "    [ " ++
    String.intercalate ",\n      "
      (sizes.map fun m => s!"(\"{m}\", {m}, program{m})") ++ " ]\n" ++
  "  IO.println \"writes,n,milliseconds,nanoseconds_per_write\"\n" ++
  "  for (label, m, f) in cases do\n" ++
  "    let mut best := 18446744073709551615\n" ++
  "    let mut size_ok := true\n" ++
  "    for _ in [0:3] do\n" ++
  "      let a := mk n\n" ++
  "      let t0 ← IO.monoNanosNow\n" ++
  "      let b := f a 1 7 3 9\n" ++
  "      let t1 ← IO.monoNanosNow\n" ++
  "      size_ok := size_ok && (b.size == n)\n" ++
  "      if t1 - t0 < best then best := t1 - t0\n" ++
  "    IO.println s!\"{label},{n},{best / 1000000},{best / m}\"\n" ++
  "    if !size_ok then IO.println \"size changed by the update\"\n"

def source : String :=
  "set_option maxRecDepth 200000\n\n" ++
    String.join (sizes.map (fun m => programDef m)) ++ "\n" ++ timingMain

def main : IO Unit := do
  for m in sizes do
    IO.println s!"checker accepts {m} writes: {(check ctx (progN m)).isSome}"
  IO.FS.writeFile "bench/Generated.lean" source
  IO.println "wrote bench/Generated.lean"

end EmitProgram

#eval EmitProgram.main
