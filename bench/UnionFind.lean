/-
A union-find benchmark on the array path the development is about.

The development does not certify this program: its fragment is a recognised
`setAt` shape, and union-find has a data-dependent loop. What this program does
show is the runtime phenomenon the discipline is designed to explain: Lean's
array update mutates in place while the array is unshared, and copies when a
second reference is live.

Two variants over the same algorithm (path halving, union by size):

* `unique`  -- the loop carries the only reference to the parent array, so every
  `set!` is in place;
* `shared`  -- a snapshot of the current array is taken each iteration and read
  after the update, so the array is still shared at the write and every `set!`
  copies.

The checksum is returned so neither loop can be discarded as dead code.
-/
import Std

namespace UnionFindBench

abbrev Arr := Array Nat

def ids (n : Nat) : Arr := (List.range n).toArray

def ones (n : Nat) : Arr := (List.replicate n 1).toArray

/-- Deterministic pseudo-random step, so runs are comparable. -/
def nextSeed (s : Nat) : Nat := (s * 1103515245 + 12345) % 2147483648

/-- Path halving, updating the array in place when it is unique. -/
partial def find (parent : Arr) (x : Nat) : Nat × Arr :=
  let px := parent.getD x 0
  if px = x then (x, parent)
  else
    let gx := parent.getD px 0
    find (parent.set! x gx) gx

/-- Union by size over the two arrays. `share` takes a snapshot of the parent
array each iteration and reads it after the write, which keeps the array shared
at the `set!` and forces the copy branch. -/
partial def loop (parent sizes : Arr) (fuel : Nat) (seed : Nat) (share : Bool) :
    Nat × Arr × Arr :=
  match fuel with
  | 0 => (0, parent, sizes)
  | f + 1 =>
    let s1 := nextSeed seed
    let a := s1 % parent.size
    let s2 := nextSeed s1
    let b := s2 % parent.size
    let (ra, parent) := find parent a
    let (rb, parent) := find parent b
    if ra = rb then
      loop parent sizes f s2 share
    else
      let sa := sizes.getD ra 1
      let sb := sizes.getD rb 1
      if share then
        -- a snapshot live across the write keeps the array shared, so the
        -- update takes the copy branch
        let snapshot := parent
        let parent :=
          if sa < sb then parent.set! ra rb else parent.set! rb ra
        let sizes :=
          if sa < sb then sizes.set! rb (sa + sb) else sizes.set! ra (sa + sb)
        let extra := snapshot.getD (f % parent.size) 0
        let (acc, parent, sizes) := loop parent sizes f s2 share
        (acc + extra, parent, sizes)
      else
        let parent :=
          if sa < sb then parent.set! ra rb else parent.set! rb ra
        let sizes :=
          if sa < sb then sizes.set! rb (sa + sb) else sizes.set! ra (sa + sb)
        let (acc, parent, sizes) := loop parent sizes f s2 share
        (acc, parent, sizes)

/-- The union-find state's checksum, and the liveness device's accumulator,
separately: the first must agree between the two variants, the second keeps the
snapshot used so the copy branch is taken. -/
def run (n m : Nat) (share : Bool) : Nat × Nat :=
  let (acc, parent, sizes) := loop (ids n) (ones n) m 12345 share
  (parent.foldl (fun a x => a + x) 0 + sizes.foldl (fun a x => a + x) 0, acc)

def main : IO Unit := do
  -- The first block compares the two variants at the same n and m, which is the
  -- only like-for-like comparison: same array sizes, same operation count.
  -- The second block grows n for the unique variant to show how the total
  -- scales with the operation count.
  let cases : List (String × Nat × Nat × Bool) :=
    [ ("unique", 2000, 8000, false)
    , ("shared", 2000, 8000, true)
    , ("unique", 4000, 16000, false)
    , ("shared", 4000, 16000, true)
    , ("unique", 8000, 32000, false)
    , ("shared", 8000, 32000, true)
    , ("unique", 16000, 64000, false)
    , ("shared", 16000, 64000, true)
    , ("unique", 100000, 400000, false)
    , ("unique", 400000, 1600000, false)
    , ("unique", 1600000, 6400000, false) ]
  IO.println "mode,n,m,milliseconds,nanoseconds_per_op,uf_checksum,liveness_sum"
  for (mode, n, m, share) in cases do
    -- three repetitions, minimum; the small cases are sub-millisecond otherwise
    let mut best := 18446744073709551615
    let mut uf := 0
    let mut extra := 0
    for _ in [0:3] do
      let t0 ← IO.monoNanosNow
      let (u, e) := run n m share
      let t1 ← IO.monoNanosNow
      uf := u; extra := e
      if t1 - t0 < best then best := t1 - t0
    IO.println s!"{mode},{n},{m},{best / 1000000},{best / m},{uf},{extra}"

end UnionFindBench

def main : IO Unit := UnionFindBench.main
