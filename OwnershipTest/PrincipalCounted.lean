/-
The code-level instance of the whole counted fragment.

`OwnershipLcnf.principal_counted_fragment` concludes the counted interpreter's
whole trace at one level; `OwnershipLcnf.execCounted_full_fragment` is the
statement it consumes. This module instantiates the former on the same reified
transcription of the captured `setAt._redArg` that
`OwnershipTest/Principal.lean` reifies, reusing its declaration, layout, heaps,
level, entry accounting, machine and child call, so the recognition premise is
still a kernel-checked verdict on a concrete `Code` value.

The instance is closed: it has no hypotheses, and its type is inferred from the
theorem application, so its conclusion is the theorem's conclusion at the
captured arguments without a second, concrete copy of the 21-conjunct type.
`#print axioms` below witnesses the instance and its footprint. The retained-parent
controls remain in `OwnershipTest.Principal` and `OwnershipTest.CountedNested`;
a T1-specific `HeapCompat` control is a separate fixture item.

This module is separate from `OwnershipTest.Principal` because the two fixtures
are elaborated independently: each carries its own large proposition, and one
module elaborating both together exhausted memory.
-/
import OwnershipTest.Principal

open Lean
open Lean.Compiler.LCNF
open Ownership

namespace OwnershipTest

/-! ## The whole counted fragment at the reified declaration -/

/-- The closed instance of the whole-fragment theorem: every premise of
`principal_counted_fragment` is supplied at the recogniser's layout on the
reified declaration, so the conclusion has no hypotheses. The counted
interpreter's entry point runs `capturedPrefix.fragment` to a completed state, the
model's run of the one-level path reports the same result and write trace, and the
two outcomes are heap-compatible. The type is inferred from the theorem, avoiding
a second concrete copy of the conclusion. -/
def counted_fragment_instance :=
  OwnershipLcnf.principal_counted_fragment setAtName takeOutName captured_hproj layout
    pathVar valueVar body [] l machine entryEnv H 0 parentObj 0 7 1 1 levelMatch agrees
    entryCtx 1 cb 4 hpath entryAccounted countedCall

#print axioms counted_fragment_instance
