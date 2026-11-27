import CapRuntime.View
import CapRuntime.Owned
import CapRuntime.SealedOwned

/- A recursive split/recurse/join benchmark over one byte array.

The runtime path hands two live disjoint views of one backing `ByteArray` to the
recursive calls; writes do not copy the backing array. The immutable-slice path
keeps the same logical views but each write returns a new `Array`, and the
recursive results are merged. The index-range path is idiomatic Lean using one
unique `Array`.
-/

open CapRuntime

namespace CapRuntime.TransformBench

/-- Set every byte in [lo, hi) to 1, using one unique Array. -/
partial def arrayRange (p : Array UInt8) (lo hi : Nat) : Array UInt8 :=
  if hi <= lo + 1 then
    if lo < hi then p.set! lo 1 else p
  else
    let mid := (lo + hi) / 2
    arrayRange (arrayRange p lo mid) mid hi

/-- Immutable slice: every write and merge can copy the whole backing array. -/
structure Slice where
  data : Array UInt8
  off : Nat
  len : Nat

def Slice.write (s : Slice) (i : Nat) (v : UInt8) : Slice :=
  if i < s.len then { s with data := s.data.set! (s.off + i) v } else s

partial def sliceRange (s : Slice) : Array UInt8 :=
  if s.len <= 1 then
    if s.len = 1 then (s.write 0 1).data else s.data
  else
    let mid := s.len / 2
    let l : Slice := { s with len := mid }
    let r : Slice := { s with off := s.off + mid, len := s.len - mid }
    let ld := sliceRange l
    let rd := sliceRange r
    Id.run do
      let mut out := ld
      for i in [0:r.len] do
        out := out.set! (r.off + i) (rd.getD (r.off + i) 0)
      return out

/-- Runtime path: split a view and recurse; writes share the one backing ByteArray. -/
partial def viewRange (s : State) (v : View) : Except String State :=
  if v.len <= 64 then
    v.fill? s 1
  else
    match v.split (v.len / 2) with
    | none => .error "split refused"
    | some (l, r) =>
        match viewRange s l with
        | .ok s => viewRange s r
        | .error e => .error e

def timeArray (n reps : Nat) : IO Nat := do
  let mut best := 18446744073709551615
  for _ in [0:reps] do
    let p := (Array.replicate n (0 : UInt8))
    let t0 ← IO.monoNanosNow
    let p' := arrayRange p 0 n
    let t1 ← IO.monoNanosNow
    unless p'.foldl (fun a x => a + x.toNat) 0 = n do
      throw (IO.userError "array checksum")
    if t1 - t0 < best then best := t1 - t0
  return best

def timeSlice (n reps : Nat) : IO Nat := do
  let mut best := 18446744073709551615
  for _ in [0:reps] do
    let s : Slice := { data := Array.replicate n (0 : UInt8), off := 0, len := n }
    let t0 ← IO.monoNanosNow
    let p' := sliceRange s
    let t1 ← IO.monoNanosNow
    unless p'.foldl (fun a x => a + x.toNat) 0 = n do
      throw (IO.userError "slice checksum")
    if t1 - t0 < best then best := t1 - t0
  return best

def readView (s : State) (v : View) (generation i : Nat) : Nat :=
  match CapRuntime.State.read? s
      { alloc := v.alloc, generation := generation, offset := i } with
  | some b => b.toNat
  | none => 0

def timeView (n reps : Nat) : IO Nat := do
  let (s, h) := State.empty.alloc n
  let v : View := { alloc := h.alloc, offset := 0, len := n }
  let mut best := 18446744073709551615
  for _ in [0:reps] do
    let s0 := s
    let t0 ← IO.monoNanosNow
    match viewRange s0 v with
    | .error e => throw (IO.userError e)
    | .ok s' =>
        let t1 ← IO.monoNanosNow
        let total := (List.range n).foldl
          (fun a i => a + readView s' v h.generation i) 0
        unless total = n do
          throw (IO.userError "view checksum")
        if t1 - t0 < best then best := t1 - t0
  return best


def arrayFillLoop (p : Array UInt8) (v : UInt8) : Array UInt8 :=
  Id.run do
    let mut p := p
    for i in [0:p.size] do
      p := p.set! i v
    return p

def byteFillLoop (p : ByteArray) (v : UInt8) : ByteArray :=
  Id.run do
    let mut p := p
    for i in [0:p.size] do
      p := p.set! i v
    return p

def timeArrayFill (n reps : Nat) : IO Nat := do
  let mut best := 18446744073709551615
  for _ in [0:reps] do
    let p := Array.replicate n (0 : UInt8)
    let t0 ← IO.monoNanosNow
    let p' := arrayFillLoop p 1
    let t1 ← IO.monoNanosNow
    unless p'.foldl (fun a x => a + x.toNat) 0 = n do
      throw (IO.userError "array-fill checksum")
    if t1 - t0 < best then best := t1 - t0
  return best

def timeByteFill (n reps : Nat) : IO Nat := do
  let mut best := 18446744073709551615
  for _ in [0:reps] do
    let p := (ByteArray.mk (Array.replicate n (0 : UInt8)))
    let t0 ← IO.monoNanosNow
    let p' := byteFillLoop p 1
    let t1 ← IO.monoNanosNow
    let total := Id.run do
      let mut a := 0
      for i in [0:n] do a := a + (p'.get! i).toNat
      return a
    unless total = n do
      throw (IO.userError "byte-fill checksum")
    if t1 - t0 < best then best := t1 - t0
  return best


def timeOwned (n reps : Nat) : IO Nat := do
  let mut best := 18446744073709551615
  for _ in [0:reps] do
    let o := Owned.new n
    let t0 ← IO.monoNanosNow
    let o' := Owned.fillRange o 0 n 1
    let t1 ← IO.monoNanosNow
    let total := Id.run do
      let mut a := 0
      for i in [0:n] do
        a := a + ((o'.read? i).getD 0).toNat
      return a
    unless total = n do
      throw (IO.userError "owned checksum")
    if t1 - t0 < best then best := t1 - t0
  return best


def timeSealedOwned (n reps : Nat) : IO Nat := do
  let mut best := 18446744073709551615
  for _ in [0:reps] do
    let o ← SealedOwned.new n
    let t0 ← IO.monoNanosNow
    let o' ← SealedOwned.fillRange o 0 n 1
    let t1 ← IO.monoNanosNow
    let total := Id.run do
      let mut a := 0
      for i in [0:n] do
        a := a + ((o'.read? i).getD 0).toNat
      return a
    unless total = n do
      throw (IO.userError "sealed-owned checksum")
    if t1 - t0 < best then best := t1 - t0
  return best

def main : IO Unit := do
  IO.println "implementation,n,reps,best_ns"
  for n in [256, 1024, 4096] do
    IO.println s!"array-range,{n},20,{(← timeArray n 20)}"
    IO.println s!"array-fill-loop,{n},20,{(← timeArrayFill n 20)}"
    IO.println s!"bytearray-fill-loop,{n},20,{(← timeByteFill n 20)}"
    IO.println s!"immutable-slice,{n},20,{(← timeSlice n 20)}"
    IO.println s!"runtime-view,{n},20,{(← timeView n 20)}"
    IO.println s!"runtime-owned,{n},20,{(← timeOwned n 20)}"
    IO.println s!"runtime-sealed-owned,{n},20,{(← timeSealedOwned n 20)}"

end CapRuntime.TransformBench

def main : IO Unit := CapRuntime.TransformBench.main
