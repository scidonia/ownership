import CapRuntime.Types

namespace CapRuntime

/-- Look up an allocation by index. -/
def State.allocation? (s : State) (i : Nat) : Option Allocation :=
  s.allocations[i]?

/-- Check a handle against liveness, generation and bounds. -/
def State.validHandle (s : State) (h : Handle) (offset : Nat := 0) : Bool :=
  match s.allocation? h.alloc with
  | none => false
  | some a =>
      a.live && a.generation == h.generation &&
        offset < a.bytes.size

/-- Read a byte through a valid handle. -/
def State.read? (s : State) (h : Handle) : Option UInt8 :=
  match s.allocation? h.alloc with
  | none => none
  | some a =>
      if a.live && a.generation == h.generation then
        a.bytes.data[h.offset]?
      else none

/-- Write a byte through a valid handle. Updates the `ByteArray` in place when
the array is uniquely referenced; no ghost state is involved. -/
def State.write? (s : State) (h : Handle) (v : UInt8) : Except String State :=
  match s.allocation? h.alloc with
  | none => .error "write denied: unknown allocation"
  | some a =>
      if h.generation != a.generation then
        .error "write denied: stale handle"
      else if !a.live then
        .error "write denied: allocation is not live"
      else if h.offset >= a.bytes.size then
        .error "write denied: offset out of bounds"
      else
        let a' := { a with bytes := a.bytes.set! h.offset v }
        .ok { s with allocations := s.allocations.set! h.alloc a' }

/-- Fresh allocation of `n` zero bytes. -/
def State.alloc (s : State) (n : Nat) : State × Handle :=
  let generation := s.nextGeneration
  let a : Allocation :=
    { bytes := ByteArray.mk (Array.replicate n (0 : UInt8))
      live := true
      generation := generation }
  let i := s.allocations.size
  let s' :=
    { s with
      allocations := s.allocations.push a
      nextGeneration := s.nextGeneration + 1 }
  (s', { alloc := i, generation := generation, offset := 0 })

/-- Mark an allocation retired. -/
def State.free? (s : State) (h : Handle) : Except String State :=
  match s.allocation? h.alloc with
  | none => .error "free denied: unknown allocation"
  | some a =>
      if h.generation != a.generation then
        .error "free denied: stale handle"
      else if !a.live then
        .error "free denied: allocation is not live"
      else
        let a' := { a with live := false }
        .ok { s with allocations := s.allocations.set! h.alloc a' }

end CapRuntime
