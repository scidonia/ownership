# Review disposition

The review under `docs/notes/OWNERSHIP_ITP_REVIEW.md` was written against revision
`04bbf39` (3 November 2026). This file records, item by item, what was changed in
response, where, and what remains open. Statuses are checkable against the
revision this file is committed with.

| Status | Meaning |
| --- | --- |
| addressed | the change the review asked for is in the manuscript or the development |
| partial | the substance is present, one requested form or detail is not |
| open | not addressed |

## Recommendation-level

The review's weak reject rested on positioning: a static guarantee advertised over
existing IR while the strongest proved execution is an interpretation of a
recognised trace. The response is not to narrow the claim but to make the boundary
exact and to strengthen the two places it was thin.

- The correspondence is now cut into four separately stated layers --- structural
  recognition, decoding consistency, interpreter correspondence, supplied meanings
  --- with recognition explicitly not mistaken for execution adequacy (‑ addressed,
  \S6).
- The counted child contract no longer assumes the caller's post-call accounting.
  It carries an `EdgePreserved` effect, and `accounted_of_edges` derives the
  accounting (‑ addressed, `Ownership/CountedNested.lean`).
- The chain's net edge effect is proved (`counted_nested_chain_edges`) and spent as
  the enclosing call's effect, composing two counted levels
  (`counted_nested_chain_two_levels`) (‑ addressed).
- The title's unobservability claim now has a theorem behind it at a stated
  boundary: `Observed` and `NestedOutcome.Compat.observed_iff` (‑ addressed, \S6).

## Major concerns

| Item | Status | Where / what |
| --- | --- | --- |
| M1 compiler connection exact | addressed | \S6 four-layer paragraph; intro says "a recognised emitted declaration's trace is interpreted and related to the model"; "connection checked" removed |
| M1 separate recognition, decoding, correspondence, implementation | addressed | \S6 layer paragraph, same order |
| M1 which instruction meanings defined / supplied | addressed | `docs/notes/ownership-theorem-map.md`, "Modelled instruction meanings": every `NestedOp` with its `execCounted` meaning, and the three that stand in for the compiler (array read/write/allocation primitives, recursive callee) |
| M2 deeper-index limitation | addressed | \S6.2 states the exclusion in the same terms as `PathRecursion`'s header |
| M3 child contract specification | addressed | \S5.2 unfolds the contract and says which facts the path induction derives and which the counted contract adds |
| M3 what is automatic vs manual | addressed | \S7 workflow paragraph: the client facts are the manual step |
| M3 model body, callee obligation | addressed | \S5.2 and the trust-boundary paragraph |
| M3 counted composition lemma, two levels | withdrawn | `counted_nested_chain_edges` stands; `counted_nested_chain_two_levels` was shown to have an inconsistent isolated-accounting premise by the review at `aaaa0aa`, and `OwnershipTest/IsolatedAccounting.lean` proves the impossibility |
| M4 pair-live live owners | addressed | \S5.3 names the interpretation, the take-out's obligations, the pair as an unowned heap cell, and the finer relation that was not taken |
| M5 novelty comparison | addressed | \S8 item-by-item comparison plus the reusable-insight sentence |
| M6 evidence coverage explicit | addressed | \S7 prose coverage of the five evidence layers, each with its scope |
| M6 family is not a parameterised recognition instance | addressed | \S7 says so explicitly |
| M6 worked user workflow | addressed | \S7 four-step workflow |

## Additional observations

| Item | Status | Where |
| --- | --- | --- |
| all-exclusive trace is not every protocol store | addressed | \S5.3 trace paragraph |
| flat and nested guarantees take different premises | addressed | \S6.2 |
| `Supported` stronger than checker acceptance; store restriction covers the old slot | addressed | \S2.2 and \S4.2 |
| unobservability needs an observation boundary | addressed | `Observed`, `Compat.observed_iff`, and the paragraph after the principal theorem |

## Formalisation and artifact

| Item | Status | Where |
| --- | --- | --- |
| one clean-checkout entry command | addressed | `scripts/check_all.sh`, with `--require-sibling` and the pinned provisioning commands |
| distinct scopes of the checks | addressed | the script prints the sibling-dependent gates as skipped rather than passing them off |
| immutable release identifier | addressed | annotated tag `itp-submission` on the revision that contains this file |

## Presentation and minor corrections

| Item | Status |
| --- | --- |
| `NCode` declaration together on one page | addressed (`samepage`, footnotesize) |
| concise mathematical principal theorem before the Lean signature | addressed (claim in words; the abbreviated signature was removed) |
| "count of one is not one owner" explained as a failure of the raw invariant | addressed (\S1) |
| replace "nothing in between is accounted" | addressed |
| distinguish `Runtime.RHeap` from the linked runtime | addressed |
| `paper/README.md` page footprint | addressed (16 body pages, bibliography on 17) |
| remove revision-process instructions from the paper | addressed (publisher-policy reminder removed) |
| no invented proceedings metadata | unchanged (placeholders, annotated in source) |

## Questions to the author

| Question | Status |
| --- | --- |
| 1. semantic claim beyond recognition | answered in \S6 (four layers) |
| 2. pair-live actual vs abstract roots | answered in \S5.3 |
| 3. generic condition for caller accounting | answered: `EdgePreserved`, with the counterexample that shows the boundary alone is insufficient |
| 4. two levels without instance-specific reconstruction | withdrawn: the two-level statement's premise is inconsistent; only the net edge effect is claimed |
| 5. theorem behind unobservability | answered: `Observed`/`observed_iff` at the stated boundary |
| 6. automation and manual work | answered in \S7 (client facts are manual) |

## Priorities

| Priority | Item | Status |
| --- | --- | --- |
| P0 | deeper-index explanation | done |
| P0 | semantic connection visibly separated | done |
| P0 | child contract exposed | done |
| P0 | intermediate-root explanation | done |
| P1 | technical novelty | done (comparison + insight) |
| P1 | compositional demonstration | net edge effect only; the two-level composition is recorded as a regression |
| P1 | usable certificate workflow | done |
| P2 | compress and polish | done (body 16 pages, references additional) |

## Open items

None. The two items recorded here previously are closed: the release identifier is
the annotated tag `itp-submission`, and the instruction meanings are enumerated in
`docs/notes/ownership-theorem-map.md` under "Modelled instruction meanings".
