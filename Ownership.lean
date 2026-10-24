/-
The root module of the ownership development.

The result this repository is being built for is stated in `PLAN.md`: the
sealed command surface of the sibling library never gives client code access to
the session's mutable footprint, and the fixed interpreter's emitted LCNF is
checked against an ownership judgment whose soundness theorem says every
designated write of an accepted program runs at a reference count of one. The
judgment is conditional on a concrete entry invariant, and it separates an
owned handle from an exclusive object; see the review dispositions in
`PLAN.md` §0. No linear type is added to Lean's core theory: the surface is an
ordinary sealed type, and the linearity is a predicate on the compiler's
output.

The toy declarations imported here are the smoke test's input; the script
`scripts/probe-lcnf.lean` reads their LCNF in a separate process. The real
modules named in the plan replace this import as they land.
-/
import Ownership.Toy
import Ownership.Runner
import Ownership.Entry
import Ownership.Nested
import Ownership.Pair
