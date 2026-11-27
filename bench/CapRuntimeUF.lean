import CapRuntime.UF

open CapRuntime

/- Runtime-only union-find benchmark. It imports no ghost `Cap` module. -/
namespace CapRuntime.UFBench

def parent (i : Nat) : Nat := if i = 0 then 0 else i - 1

def chainBytes (n : Nat) : UF.ParentArray :=
  { bytes := ByteArray.mk ((Array.range n).map (fun i => UInt8.ofNat (parent i))) }

partial def nativeFind (p : Array Nat) (x : Nat) : Nat × Array Nat :=
  let px := p.getD x 0
  if px = x then (x, p)
  else
    let (r, p') := nativeFind p px
    (r, p'.set! x r)

def timeNative (n : Nat) : IO Nat := do
  let p := (Array.range n).map parent
  let t0 ← IO.monoNanosNow
  let (r, p') := nativeFind p (n - 1)
  let t1 ← IO.monoNanosNow
  unless r = 0 && p'.getD (n - 1) 0 = 0 do
    throw (IO.userError s!"native wrong result at n={n}")
  return t1 - t0

def timeRuntime (n : Nat) : IO Nat := do
  let p := chainBytes n
  let t0 ← IO.monoNanosNow
  let (r, p') := p.findCompress (n - 1)
  let t1 ← IO.monoNanosNow
  unless r = 0 && p'.parent (n - 1) = 0 do
    throw (IO.userError s!"runtime wrong result at n={n}")
  return t1 - t0

def minimum : List Nat → Nat
  | [] => 0
  | x :: xs => xs.foldl Nat.min x

def runCase (name : String) (n reps : Nat) (trial : Nat → IO Nat) : IO Unit := do
  for _ in [0:5] do
    let _ ← trial n
  let mut times := []
  for _ in [0:reps] do
    times := (← trial n) :: times
  let best := minimum times
  let total := times.foldl (· + ·) 0
  IO.println s!"{name},{n},{reps},{best},{total / reps}"

def main : IO Unit := do
  IO.println "implementation,n,reps,best_ns,mean_ns"
  for n in [32, 128, 256] do
    runCase "lean-array" n 200 timeNative
    runCase "bytearray-runtime" n 200 timeRuntime

end CapRuntime.UFBench

def main : IO Unit := CapRuntime.UFBench.main
