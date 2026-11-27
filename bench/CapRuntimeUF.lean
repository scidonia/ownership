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


/-- Direct Lean `ByteArray` parent access with no capability/runtime wrapper. -/
def directParent (p : ByteArray) (i : Nat) : Nat :=
  if h : i < p.size then (p.get i h).toNat else i

partial def directFindRoot (p : ByteArray) (x : Nat) : Nat :=
  let px := directParent p x
  if px = x then x else directFindRoot p px

partial def directCompressTo (p : ByteArray) (root x fuel : Nat) : ByteArray :=
  match fuel with
  | 0 => p
  | fuel + 1 =>
      let px := directParent p x
      if px = x then p
      else directCompressTo (p.set! x (UInt8.ofNat root)) root px fuel

def directFindCompress (p : ByteArray) (x : Nat) : Nat × ByteArray :=
  let root := directFindRoot p x
  (root, directCompressTo p root x (p.size + 1))

def timeDirect (n : Nat) : IO Nat := do
  let p := (chainBytes n).bytes
  let t0 ← IO.monoNanosNow
  let (r, p') := directFindCompress p (n - 1)
  let t1 ← IO.monoNanosNow
  unless r = 0 && directParent p' (n - 1) = 0 do
    throw (IO.userError s!"direct wrong result at n={n}")
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


/-- The compression path for the chain: n-1, n-2, ..., 1. -/
def chainPath (n : Nat) : List Nat := (List.range (n - 1)).map (· + 1) |>.reverse

def compressArrUnique (p : Array Nat) (path : List Nat) : Array Nat :=
  path.foldl (fun p x => p.set! x 0) p

def compressArrVersioned (p : Array Nat) (path : List Nat) : Array Nat × Nat :=
  path.foldl (fun (p, acc) x =>
    let snap := p
    let p' := p.set! x 0
    (p', acc + snap.getD x 0)) (p, 0)

def compressBytesUnique (p : ByteArray) (path : List Nat) : ByteArray :=
  path.foldl (fun p x => p.set! x 0) p

def compressBytesVersioned (p : ByteArray) (path : List Nat) : ByteArray × Nat :=
  path.foldl (fun (p, acc) x =>
    let snap := p
    let p' := p.set! x 0
    (p', acc + (snap.get! x).toNat)) (p, 0)

def compressRuntimeUnique (p : UF.ParentArray) (path : List Nat) : UF.ParentArray :=
  path.foldl (fun p x => { bytes := p.bytes.set! x 0 }) p

def compressRuntimeVersioned (p : UF.ParentArray) (path : List Nat) :
    UF.ParentArray × Nat :=
  path.foldl (fun (p, acc) x =>
    let snap := p
    let p' : UF.ParentArray := { bytes := p.bytes.set! x 0 }
    (p', acc + snap.parent x)) (p, 0)

def timeCompression (name : String) (n : Nat)
    (trial : Nat → IO Nat) : IO Unit := do
  for _ in [0:5] do
    let _ ← trial n
  let mut times := []
  for _ in [0:200] do
    times := (← trial n) :: times
  let best := minimum times
  let total := times.foldl (· + ·) 0
  IO.println s!"{name},{n},200,{best},{total / 200}"

def mainCompression : IO Unit := do
  IO.println "compression,n,reps,best_ns,mean_ns"
  for n in [32, 128, 256] do
    let _ ← timeCompression "array-unique" n (fun n => do
      let p := (Array.range n).map parent
      let path := chainPath n
      let t0 ← IO.monoNanosNow
      let p' := compressArrUnique p path
      let t1 ← IO.monoNanosNow
      unless p'.getD (n - 1) 0 = 0 do throw (IO.userError "array-unique")
      pure (t1 - t0))
    let _ ← timeCompression "array-versioned" n (fun n => do
      let p := (Array.range n).map parent
      let path := chainPath n
      let t0 ← IO.monoNanosNow
      let (p', acc) := compressArrVersioned p path
      let t1 ← IO.monoNanosNow
      unless p'.getD (n - 1) 0 = 0 && acc >= 0 do throw (IO.userError "array-versioned")
      pure (t1 - t0))
    let _ ← timeCompression "bytearray-unique" n (fun n => do
      let p := (chainBytes n).bytes
      let path := chainPath n
      let t0 ← IO.monoNanosNow
      let p' := compressBytesUnique p path
      let t1 ← IO.monoNanosNow
      unless p'.get! (n - 1) = 0 do throw (IO.userError "bytearray-unique")
      pure (t1 - t0))
    let _ ← timeCompression "bytearray-versioned" n (fun n => do
      let p := (chainBytes n).bytes
      let path := chainPath n
      let t0 ← IO.monoNanosNow
      let (p', acc) := compressBytesVersioned p path
      let t1 ← IO.monoNanosNow
      unless p'.get! (n - 1) = 0 && acc >= 0 do throw (IO.userError "bytearray-versioned")
      pure (t1 - t0))
    let _ ← timeCompression "runtime-unique" n (fun n => do
      let p := chainBytes n
      let path := chainPath n
      let t0 ← IO.monoNanosNow
      let p' := compressRuntimeUnique p path
      let t1 ← IO.monoNanosNow
      unless p'.parent (n - 1) = 0 do throw (IO.userError "runtime-unique")
      pure (t1 - t0))
    let _ ← timeCompression "runtime-versioned" n (fun n => do
      let p := chainBytes n
      let path := chainPath n
      let t0 ← IO.monoNanosNow
      let (p', acc) := compressRuntimeVersioned p path
      let t1 ← IO.monoNanosNow
      unless p'.parent (n - 1) = 0 && acc >= 0 do throw (IO.userError "runtime-versioned")
      pure (t1 - t0))

def main : IO Unit := do
  mainCompression
  IO.println ""

  IO.println "implementation,n,reps,best_ns,mean_ns"
  for n in [32, 128, 256] do
    runCase "lean-array-nat" n 200 timeNative
    runCase "bytearray-direct" n 200 timeDirect
    runCase "bytearray-runtime" n 200 timeRuntime

end CapRuntime.UFBench

def main : IO Unit := CapRuntime.UFBench.main
