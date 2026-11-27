import CapRuntime.Bytes

namespace CapRuntime

/-- A whole-buffer unique handle. The representation is private; client code
uses `write`, `read?` and `fillRange`. This is the runtime form of the
whole-share capability, with no ghost state. -/
structure Owned where
  private mk ::
  private bytes : ByteArray

namespace Owned

/-- Fresh zero-initialised whole buffer. -/
def new (n : Nat) : Owned :=
  ⟨ByteArray.mk (Array.replicate n (0 : UInt8))⟩

/-- Number of bytes. -/
def size (o : Owned) : Nat := o.bytes.size

/-- Read a byte. -/
def read? (o : Owned) (i : Nat) : Option UInt8 :=
  if i < o.bytes.size then some (o.bytes.get! i) else none

/-- Write one byte. The `ByteArray` is in place when uniquely referenced. -/
def write (o : Owned) (i : Nat) (v : UInt8) : Owned :=
  if i < o.bytes.size then ⟨o.bytes.set! i v⟩ else o

/-- Fill a range with one value; one `ByteArray` update loop, no state lookup. -/
def fillRange (o : Owned) (lo hi : Nat) (v : UInt8) : Owned :=
  Id.run do
    let mut b := o.bytes
    for i in [lo:hi] do
      if i < b.size then b := b.set! i v
    return ⟨b⟩

end Owned

end CapRuntime
