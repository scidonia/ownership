import CapRuntime.Bytes

namespace CapRuntime

/-- Dynamically sealed whole-buffer handle. A copy shares the `used` flag, so a
second use through either copy is refused. This is the runtime-guarded variant;
the compile-time checker remains the zero-overhead path. -/
structure SealedOwned where
  private bytes : ByteArray
  private used : IO.Ref Bool

namespace SealedOwned

/-- Fresh zero-initialised sealed buffer. -/
def new (n : Nat) : IO SealedOwned := do
  let used ← IO.mkRef false
  pure ⟨ByteArray.mk (Array.replicate n (0 : UInt8)), used⟩

/-- Consume the handle and return its bytes. Refuses if this or any copy was
already consumed. -/
def take (o : SealedOwned) : IO ByteArray := do
  if ← o.used.get then
    throw (IO.userError "sealed owned handle used twice")
  o.used.set true
  pure o.bytes

/-- Number of bytes. -/
def size (o : SealedOwned) : Nat := o.bytes.size

/-- Read without consuming. -/
def read? (o : SealedOwned) (i : Nat) : Option UInt8 :=
  if i < o.bytes.size then some (o.bytes.get! i) else none

/-- One-byte write; consumes the input handle and returns a fresh unused handle. -/
def write (o : SealedOwned) (i : Nat) (v : UInt8) : IO SealedOwned := do
  let b ← take o
  let used ← IO.mkRef false
  pure ⟨if i < b.size then b.set! i v else b, used⟩

/-- Fill a range in one operation; consumes input and returns a fresh handle. -/
def fillRange (o : SealedOwned) (lo hi : Nat) (v : UInt8) : IO SealedOwned := do
  let b ← take o
  let used ← IO.mkRef false
  let b' := Id.run do
    let mut b := b
    for i in [lo:hi] do
      if i < b.size then b := b.set! i v
    return b
  pure ⟨b', used⟩

end SealedOwned

end CapRuntime
