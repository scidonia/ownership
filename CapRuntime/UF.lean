import CapRuntime.Bytes

namespace CapRuntime.UF

/-- One byte per parent pointer in the current 256-node domain. -/
structure ParentArray where
  bytes : ByteArray

/-- Parent byte, with out-of-range treated as a root (the runtime caller checks
bounds before constructing the handle). -/
def ParentArray.parent (p : ParentArray) (i : Nat) : Nat :=
  if h : i < p.bytes.size then (p.bytes.get i h).toNat else i

/-- Follow parent pointers to a fixed point. -/
partial def ParentArray.findRoot (p : ParentArray) (x : Nat) : Nat :=
  let px := p.parent x
  if px = x then x else p.findRoot px

/-- Write `root` at every node on the path from `x` until the root. -/
partial def ParentArray.compressTo (p : ParentArray) (root : Nat) (x : Nat)
    (fuel : Nat) : ParentArray :=
  match fuel with
  | 0 => p
  | fuel + 1 =>
      let px := p.parent x
      if px = x then p
      else
        let p' : ParentArray := { bytes := p.bytes.set! x (UInt8.ofNat root) }
        p'.compressTo root px fuel

/-- Full-path find-and-compress over raw bytes. No ghost state, no list heap. -/
def ParentArray.findCompress (p : ParentArray) (x : Nat) : Nat × ParentArray :=
  let root := p.findRoot x
  (root, p.compressTo root x (p.bytes.size + 1))

end CapRuntime.UF
