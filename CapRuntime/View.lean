import CapRuntime.Bytes

namespace CapRuntime

/-- A live disjoint byte range inside one runtime allocation. -/
structure View where
  alloc : Nat
  offset : Nat
  len : Nat
  deriving Repr, DecidableEq, BEq

/-- Construct a view only if the allocation is live and the range is in bounds. -/
def State.view? (s : State) (alloc offset len : Nat) : Option View :=
  match s.allocation? alloc with
  | none => none
  | some a =>
      if a.live && offset + len <= a.bytes.size then
        some { alloc, offset, len }
      else none

/-- Split a view into two adjacent disjoint views. -/
def View.split (v : View) (mid : Nat) : Option (View × View) :=
  if mid <= v.len then
    some
      ({ v with len := mid },
       { v with offset := v.offset + mid, len := v.len - mid })
  else none

/-- Read a byte relative to a view. -/
def View.read? (s : State) (v : View) (i : Nat) : Option UInt8 :=
  if i < v.len then
    match s.allocation? v.alloc with
    | none => none
    | some a =>
        s.read? { alloc := v.alloc, generation := a.generation,
                  offset := v.offset + i }
  else none

/-- Write a byte relative to a view. This is a direct `ByteArray` update; no
backing-array copy is required while the view is the only writer of that range. -/
def View.write? (s : State) (v : View) (i : Nat) (val : UInt8) :
    Except String State :=
  if i >= v.len then
    .error "view write denied: offset outside the view"
  else
    match s.allocation? v.alloc with
    | none => .error "view write denied: unknown allocation"
    | some a =>
        let h : Handle :=
          { alloc := v.alloc, generation := a.generation, offset := v.offset + i }
        s.write? h val


/-- Fill a whole view with one value using a single allocation lookup and a
direct `ByteArray` loop. -/
def View.fill? (s : State) (v : View) (val : UInt8) : Except String State :=
  match s.allocation? v.alloc with
  | none => .error "fill denied: unknown allocation"
  | some a =>
      if v.offset + v.len > a.bytes.size then
        .error "fill denied: view outside allocation"
      else
        let b :=
          Id.run do
            let mut b := a.bytes
            for i in [v.offset:v.offset + v.len] do
              b := b.set! i val
            return b
        .ok { s with allocations := s.allocations.set! v.alloc { a with bytes := b } }

end CapRuntime
