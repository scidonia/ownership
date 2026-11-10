#!/usr/bin/env bash
#
# Claim census: every Lean name the paper displays denotes something the
# development contains, and everything the development is cited for is displayed.
#
#   bash scripts/check_claims.sh              check the paper against the map
#   bash scripts/check_claims.sh --generate   rewrite docs/notes/claim-map.md from
#                                             the classification below
#   bash scripts/check_claims.sh --self-test  negative controls: a paper token
#                                             with no row, a row no token cites,
#                                             and a row naming no declaration
#
# The map is generated from the tables in this file, so a fresh checkout rebuilds
# it with `--generate` and the checked-in copy is compared byte for byte.
# `--generate` writes the file itself rather than printing it, so a dev-shell
# banner on stdout cannot end up inside the table.
#
# Two directions, both required:
#   * every distinct `\lean{...}` token in the paper has exactly one row;
#   * every row's token occurs in the paper.
#
# Per row:
#   * declaration          -> `#check <qualified>` in a temporary Lean file that
#                             imports the modules the declaration rows name,
#                             compiled by `nix develop -c lake env lean`; any
#                             error, unknown identifier, or non-zero exit fails;
#   * module               -> the named path exists in the repository;
#   * runtime-primitive,
#     concept, expression  -> the token is in ALLOWLIST below and its reason is
#                             non-empty. A new unexplained row cannot pass.
#
# Temporary files are written outside the repository (in $TMPDIR).
set -euo pipefail

root="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/.." && pwd)"
exec python3 - "$root" "$@" <<'PY'
import os
import re
import subprocess
import sys
import tempfile

ROOT = sys.argv[1]
ARGV = sys.argv[2:]
PAPER = os.path.join(ROOT, "paper", "ownership-skeleton.tex")
MAP = os.path.join(ROOT, "docs", "notes", "claim-map.md")
KINDS = ("declaration", "module", "runtime-primitive", "concept", "expression")

# --------------------------------------------------------------------------
# Declarations: token -> (Lean name, module that declares it[, reason]).
#
# The token is the paper's spelling after unescaping; the Lean name is the
# constant `#check` is run on. A reason is present where the paper's spelling
# alone does not determine the name (a constructor displayed with a dot, a
# short name that several namespaces carry, a declaration the paper names by
# its bare local name).
# --------------------------------------------------------------------------
DECLARATIONS = {
    ".dec": ("Ownership.Code.dec", "Ownership/Code.lean",
             "constructor of `Ownership.Code`, displayed with its leading dot"),
    ".inc": ("Ownership.Code.inc", "Ownership/Code.lean",
             "constructor of `Ownership.Code`, displayed with its leading dot"),
    ".let": ("Ownership.Code.let", "Ownership/Code.lean",
             "constructor of `Ownership.Code`, displayed with its leading dot"),
    ".mutate": ("Ownership.PutBack.mutate", "Ownership/PutBack.lean",
                "constructor of `Ownership.PutBack.Disposition`, displayed with its leading dot"),
    "Accounted": ("Ownership.Accounted", "Ownership/CompleteAccounting.lean"),
    "Accounted.decOne": ("Ownership.Accounted.decOne", "Ownership/CompleteAccounting.lean"),
    "Accounted.move": ("Ownership.Accounted.move", "Ownership/CompleteAccounting.lean"),
    "Accounted.setArrInPlace": ("Ownership.Accounted.setArrInPlace", "Ownership/CompleteAccounting.lean"),
    "setArrInPlace": ("Ownership.Accounted.setArrInPlace", "Ownership/CompleteAccounting.lean"),
    "inPlace_of_exclusive": ("Ownership.PutBack.inPlace_of_exclusive", "Ownership/PutBack.lean"),
    "Accounted.setScalar": ("Ownership.Accounted.setScalar", "Ownership/CompleteAccounting.lean"),
    "AccountedAlong": ("Ownership.AccountedAlong", "Ownership/Preservation.lean"),
    "AnnotationsIn": ("Ownership.Entry.AnnotationsIn", "Ownership/Entry.lean"),
    "Array.markLinear": ("Array.markLinear", "Init"),
    "ChildCall.separated": ("Ownership.PutBack.ChildCall.separated", "Ownership/PutBack.lean"),
    "ChildContract": ("OwnershipLcnf.ChildContract", "OwnershipLcnf/NestedSemantics.lean"),
    "Code": ("Ownership.Code", "Ownership/Code.lean"),
    "Corr": ("OwnershipLcnf.Runtime.Corr", "OwnershipLcnf/RuntimeModel.lean",
             "the runtime correspondence relation inside `OwnershipLcnf.Runtime`; the model-side `OwnershipLcnf.Agrees` is a different relation"),
    "CountFidelity": ("Ownership.CountFidelity", "Ownership/Accounting.lean"),
    "CountedChildCall": ("Ownership.CountedChildCall", "Ownership/CountedNested.lean"),
    "EnvOwnerCount": ("Ownership.EnvOwnerCount", "Ownership/Accounting.lean"),
    "Heap": ("Ownership.Heap", "Ownership/Heap.lean"),
    "Heap.Exclusive": ("Ownership.Heap.Exclusive", "Ownership/Heap.lean"),
    "HeapCompat": ("Ownership.HeapCompat", "Ownership/CountedNested.lean"),
    "HeapCompat.eq_of_cursor_eq": ("Ownership.HeapCompat.eq_of_cursor_eq", "Ownership/CountedNested.lean"),
    "IncomingCount": ("Ownership.IncomingCount", "Ownership/Accounting.lean"),
    "Inv": ("Ownership.Inv", "Ownership/Code.lean"),
    "Inv.owned": ("Ownership.Inv.owned", "Ownership/Code.lean"),
    "Inv.rc_eq": ("Ownership.Inv.rc_eq", "Ownership/Code.lean"),
    "LetF": ("Ownership.LetF", "Ownership/Code.lean"),
    "NCode": ("Ownership.Nested.NCode", "Ownership/Nested.lean",
              "the nested language lives in `Ownership.Nested`; `Ownership.Code` is the flat one"),
    "Nat": ("Nat", "Init"),
    "NestedOutcome": ("OwnershipLcnf.NestedOutcome", "OwnershipLcnf/NestedSemantics.lean"),
    "NestedOutcome.Compat": ("OwnershipLcnf.NestedOutcome.Compat", "OwnershipLcnf/CountedTrace.lean"),
    "NestedOutcome.Compat.observed_iff": ("OwnershipLcnf.NestedOutcome.Compat.observed_iff", "OwnershipLcnf/CountedTrace.lean"),
    "Observed": ("OwnershipLcnf.Observed", "OwnershipLcnf/CountedTrace.lean"),
    "OwnersAccounted": ("Ownership.OwnersAccounted", "Ownership/Accounting.lean"),
    "Path.build": ("Ownership.Path.build", "Ownership/Path.lean"),
    "Prefix.toModel_supported": ("OwnershipLcnf.Prefix.toModel_supported", "OwnershipLcnf/Principal.lean"),
    "Runtime.setAt_inPlace_of_entryInv": ("OwnershipLcnf.Runtime.setAt_inPlace_of_entryInv", "OwnershipLcnf/RuntimeModel.lean"),
    "StoreSlots": ("Ownership.StoreSlots", "Ownership/Preservation.lean"),
    "Supported": ("Ownership.Supported", "Ownership/CompleteAccounting.lean"),
    "TakeOutsOK": ("Ownership.Nested.TakeOutsOK", "Ownership/Nested.lean"),
    "Val": ("Ownership.Val", "Ownership/Heap.lean"),
    "EdgePreserved": ("Ownership.EdgePreserved", "Ownership/CountedNested.lean",
                      "the call-effect relation; `Ownership.HeapCompat` is the boundary relation"),
    "accounted_of": ("Ownership.accounted_of_edges", "Ownership/CountedNested.lean",
                     "the derivation `Ownership.CountedChildCall.accounted_of` is its structure form"),
    "edges": ("Ownership.CountedChildCall.edges", "Ownership/CountedNested.lean",
              "the field, not a free-standing declaration; `Ownership.CountedChildCall.call` is its sibling"),
    "alias_not_accounted": ("Ownership.alias_not_accounted", "Ownership/Accounting.lean"),
    "at_most_one_owner": ("Ownership.Accounted.at_most_one_owner", "Ownership/CompleteAccounting.lean"),
    "bindAlias": ("Ownership.Supported.bindAlias", "Ownership/CompleteAccounting.lean",
                  "constructor of `Ownership.Supported`, not `Ownership.Ctx.bindOwned`"),
    "bindLit": ("Ownership.Supported.bindLit", "Ownership/CompleteAccounting.lean",
                "constructor of `Ownership.Supported`"),
    "bindOwned": ("Ownership.Ctx.bindOwned", "Ownership/Code.lean",
                  "context update; the paper lists it with `setUs`, `move`, `inc` and `dec`"),
    "bindShared": ("Ownership.Supported.bindShared", "Ownership/CompleteAccounting.lean",
                   "constructor of `Ownership.Supported`"),
    "bindSize": ("Ownership.Supported.bindSize", "Ownership/CompleteAccounting.lean",
                 "constructor of `Ownership.Supported`"),
    "borrow": ("Ownership.Inv.borrow", "Ownership/Code.lean",
               "field of `Ownership.Inv`; `Ownership.U.borrow` is the usage tag of the same name"),
    "call": ("Ownership.CountedChildCall.call", "Ownership/CountedNested.lean",
             "the field, not `Ownership.PutBack.ChildCall`"),
    "callAt_frame_confined": ("Ownership.Entry.callAt_frame_confined", "Ownership/Entry.lean"),
    "calledAccounted": ("OwnershipTest.calledAccounted", "OwnershipTest/Principal.lean",
                        "the closed principal instance's discharge; `OwnershipTest.CountedFamily.calledAccounted` and `OwnershipTest.CountedNested.calledAccounted` are same-named siblings for other instances"),
    "check": ("Ownership.check", "Ownership/Code.lean"),
    "checkN": ("Ownership.Nested.checkN", "Ownership/Nested.lean"),
    "checkNF": ("Ownership.Nested.checkNF", "Ownership/Nested.lean"),
    "childContracts_of_path": ("OwnershipLcnf.childContracts_of_path", "OwnershipLcnf/PathRecursion.lean"),
    "count_one_dichotomy": ("Ownership.Accounted.count_one_dichotomy", "Ownership/CompleteAccounting.lean"),
    "countedPrefix": ("OwnershipLcnf.countedPrefix", "OwnershipLcnf/CountedTrace.lean"),
    "countedSuffix": ("OwnershipLcnf.countedSuffix", "OwnershipLcnf/CountedTrace.lean"),
    "counted_nested_chain": ("Ownership.counted_nested_chain", "Ownership/CountedNested.lean"),
    "counted_nested_chain_edges": ("Ownership.counted_nested_chain_edges", "Ownership/CountedNested.lean"),
    "counted_nested_chain_two_levels": ("Ownership.counted_nested_chain_two_levels", "Ownership/CountedNested.lean"),
    "counted_restore": ("Ownership.counted_restore", "Ownership/CountedNested.lean"),
    "counted_takeOut": ("Ownership.counted_takeOut", "Ownership/CountedNested.lean"),
    "counted_nested_chain_restoration": ("Ownership.counted_nested_chain_restoration", "Ownership/CountedNested.lean"),
    "NestedAgrees": ("OwnershipLcnf.NestedAgrees", "OwnershipLcnf/NestedSemantics.lean"),
    "Runtime.RHeap": ("OwnershipLcnf.Runtime.RHeap", "OwnershipLcnf/RuntimeModel.lean"),
    "dec": ("Ownership.Ctx.dec", "Ownership/Code.lean",
            "the context update; `Ownership.Code.dec` is the constructor of the same name"),
    "decOne": ("Ownership.Accounted.decOne", "Ownership/CompleteAccounting.lean",
               "the accounting lemma; `Ownership.Supported.decOne` is the constructor of the same name"),
    "decTwo_rejected": ("Ownership.decTwo_rejected", "Ownership/CompleteAccounting.lean"),
    "dupSupport_witness": ("Ownership.dupSupport_witness", "Ownership/CompleteAccounting.lean"),
    "execAST_recognized": ("OwnershipLcnf.execAST_recognized", "OwnershipLcnf/Semantics.lean"),
    "execCountedAST": ("OwnershipLcnf.execCountedAST", "OwnershipLcnf/CountedTrace.lean"),
    "execCounted_full_fragment": ("OwnershipLcnf.execCounted_full_fragment", "OwnershipLcnf/CountedTrace.lean"),
    "execCounted_protocol_boundary": ("OwnershipLcnf.execCounted_protocol_boundary", "OwnershipLcnf/CountedTrace.lean"),
    "execNested": ("OwnershipLcnf.execNested", "OwnershipLcnf/NestedSemantics.lean"),
    "execSet": ("Ownership.Runner.execSet", "Ownership/Runner.lean"),
    "fragment_decomp": ("OwnershipLcnf.fragment_decomp", "OwnershipLcnf/CountedTrace.lean"),
    "inc": ("Ownership.Ctx.inc", "Ownership/Code.lean",
            "the context update; `Ownership.Code.inc` is the constructor of the same name"),
    "incPairComponents_eq": ("Ownership.CountedPair.incPairComponents_eq", "Ownership/CountedPair.lean"),
    "index_path_simulates_model": ("OwnershipLcnf.index_path_simulates_model", "OwnershipLcnf/PathRecursion.lean"),
    "initCtx": ("Ownership.Runner.initCtx", "Ownership/Runner.lean",
                "the initializer; `Ownership.Accounted.initCtx` is a different declaration of the same name"),
    "initCtx_accounted": ("Ownership.initCtx_accounted", "Ownership/Accounting.lean"),
    "move": ("Ownership.Ctx.move", "Ownership/Code.lean",
             "the context update the judgment paragraph lists with `setUs` and `bindOwned`"),
    "mult": ("Ownership.Ctx.mult", "Ownership/Code.lean",
             "field of `Ownership.Ctx`; `Ownership.RefCount` is a different count"),
    "mult_eq": ("Ownership.Accounted.mult_eq", "Ownership/CompleteAccounting.lean"),
    "mutate": ("Ownership.PutBack.mutate", "Ownership/PutBack.lean",
               "branch constructor of `Ownership.PutBack.Disposition`"),
    "no_free_components_not_exclusive": ("Ownership.CountedPair.no_free_components_not_exclusive", "Ownership/CountedPair.lean"),
    "nonPersistent": ("Ownership.Inv.nonPersistent", "Ownership/Code.lean",
                      "field of `Ownership.Inv`"),
    "omittedOwner_witness": ("Ownership.omittedOwner_witness", "Ownership/CompleteAccounting.lean"),
    "owned": ("Ownership.Inv.owned", "Ownership/Code.lean",
              "field of `Ownership.Inv`; `Ownership.U.owned` is the usage tag of the same name"),
    "pairPhase_refused": ("OwnershipTest.CountedNested.pairPhase_refused", "OwnershipTest/CountedNested.lean"),
    "pair_traffic_neutral": ("Ownership.CountedPair.pair_traffic_neutral", "Ownership/CountedPair.lean"),
    "principal_accounted": ("OwnershipLcnf.principal_accounted", "OwnershipLcnf/Principal.lean"),
    "principal_counted_fragment": ("OwnershipLcnf.principal_counted_fragment", "OwnershipLcnf/Principal.lean"),
    "principal_supported_path": ("OwnershipLcnf.principal_supported_path", "OwnershipLcnf/Principal.lean"),
    "projectNested": ("OwnershipLcnf.projectNested", "OwnershipLcnf/NestedProjection.lean"),
    "projectPair": ("OwnershipLcnf.projectPair", "OwnershipLcnf/PairProjection.lean"),
    "projectPrefix": ("OwnershipLcnf.projectPrefix", "OwnershipLcnf/Projection.lean"),
    "project_sound": ("OwnershipLcnf.project_sound", "OwnershipLcnf/Semantics.lean"),
    "putBack_exclusive_of_wellFormed": ("Ownership.PutBack.putBack_exclusive_of_wellFormed", "Ownership/PutBack.lean"),
    "rc_eq": ("Ownership.Inv.rc_eq", "Ownership/Code.lean",
              "field of `Ownership.Inv`"),
    "recognized_write_in_place": ("OwnershipLcnf.recognized_write_in_place", "OwnershipLcnf/Semantics.lean"),
    "replaceVar": ("Ownership.replaceVar", "Ownership/CompleteAccounting.lean"),
    "ret": ("Ownership.Code.ret", "Ownership/Code.lean",
            "constructor of `Ownership.Code`; the checker's `.ret` rule is `Ownership.check`'s case for it"),
    "run": ("Ownership.run", "Ownership/Code.lean"),
    "runN": ("Ownership.Nested.runN", "Ownership/Nested.lean"),
    "scalar": ("Ownership.Inv.scalar", "Ownership/Code.lean",
               "field of `Ownership.Inv`; `Ownership.U.scalar` and `Ownership.Val.scalar` are different declarations of the same name"),
    "set": ("Ownership.Heap.set", "Ownership/Heap.lean",
            "the heap update; `Ownership.Env.set` and `OwnershipLcnf.Runtime.Corr.set` carry the same local name"),
    "setArr": ("Ownership.Code.setArr", "Ownership/Code.lean",
               "constructor of `Ownership.Code`; the paper drops its leading dot here"),
    "setAt": ("OwnershipLcnf.Runtime.setAt", "OwnershipLcnf/RuntimeModel.lean",
              "the runtime model's write; the paper names it inside `Runtime.setAt_inPlace_of_entryInv`"),
    "setUs": ("Ownership.Ctx.setUs", "Ownership/Code.lean"),
    "storeSlots_init": ("Ownership.storeSlots_init", "Ownership/Preservation.lean"),
    "support_nodup": ("Ownership.Accounted.support_nodup", "Ownership/CompleteAccounting.lean",
                      "field of `Ownership.Accounted`, not a free-standing declaration"),
    "supported_check": ("Ownership.supported_check", "Ownership/Preservation.lean"),
    "supported_run": ("Ownership.supported_run", "Ownership/Preservation.lean"),
    "supported_store_exclusive": ("Ownership.supported_store_exclusive", "Ownership/Preservation.lean"),
    "unboundRoot_witness": ("Ownership.unboundRoot_witness", "Ownership/CompleteAccounting.lean"),
}

# --------------------------------------------------------------------------
# Modules: token -> repository path of the module the paper names. The path must
# exist; the paper names modules both with their file path and with their root
# name.
# --------------------------------------------------------------------------
MODULES = {
    "Ownership": "Ownership.lean",
    "OwnershipLcnf": "OwnershipLcnf.lean",
    "OwnershipTest": "OwnershipTest.lean",
    "OwnershipLcnf/Principal.lean": "OwnershipLcnf/Principal.lean",
}

# --------------------------------------------------------------------------
# The explicit allowlist. Every row whose kind is not `declaration` must have its
# token here, and the value carries the reason the map repeats: the boundary it
# names, or why it is not a declaration in this development. Adding a
# concept/expression/runtime-primitive row without an entry here fails the check.
# --------------------------------------------------------------------------
ALLOWLIST = {
    # -- runtime primitives --------------------------------------------------
    "lean_is_exclusive": (
        "runtime-primitive", "lean_is_exclusive", "OwnershipLcnf/RuntimeModel.lean",
        "Lean 4's runtime test of whether a heap object's reference count is one; a C "
        "primitive of the Lean runtime, not a declaration of this development. "
        "`OwnershipLcnf.Runtime.RHeap.isExclusive` is the model written from its documented meaning."),
    "lean_array_fget": (
        "runtime-primitive", "lean_array_fget", "docs/notes/artifacts/backend-binding.txt",
        "Lean runtime C primitive that reads an array element into the unboxed exchange; it "
        "appears in the pinned backend artifact and has no Lean declaration in this repository."),
    "lean_array_fset": (
        "runtime-primitive", "lean_array_fset", "docs/notes/artifacts/backend-binding.txt",
        "Lean runtime C primitive that writes an array element in the unboxed exchange; it "
        "appears in the pinned backend artifact and has no Lean declaration in this repository."),
    "LEAN_ABORT_ON_NONLINEAR": (
        "runtime-primitive", "LEAN_ABORT_ON_NONLINEAR", "—",
        "Lean runtime option that aborts execution on a nonlinear use of a linearly marked "
        "array; a runtime flag of Lean itself, not a declaration of this development."),
    # -- concepts ------------------------------------------------------------
    "Layout5.setAt": (
        "concept", "Layout5.setAt", "—",
        "declaration of the pinned sibling compiler-input package, not of this repository; the "
        "paper names it as the source of the running example."),
    "Path.index": (
        "concept", "Path.index", "—",
        "the `.index` constructor arm of the sibling `Path` type that `Layout5.setAt` matches; "
        "declared in the pinned sibling repository, and the local `Ownership.Path` module has no "
        "`index` constructor."),
    "\\#guard": (
        "concept", "\\#guard", "—",
        "Lean command syntax (an elaboration-time test) written with a LaTeX-escaped `#`; a "
        "command, not a declaration."),
    # -- expressions ---------------------------------------------------------
    ".dec x 1": (
        "expression", "Ownership.Code.dec", "Ownership/Code.lean",
        "displayed program fragment: the `dec` constructor at count one; the checker's form of "
        "the same step is `Ownership.Supported.decOne`."),
    ".inPlace H' root": (
        "expression", "OwnershipLcnf.Runtime.SetOutcome.inPlace", "OwnershipLcnf/RuntimeModel.lean",
        "displayed result pattern of the runtime model's in-place branch."),
    ".ref 1": (
        "expression", "Ownership.Val.ref", "Ownership/Heap.lean",
        "displayed heap value: the `ref` constructor of `Ownership.Val` at reference 1."),
    ".scalar 0": (
        "expression", "Ownership.Val.scalar", "Ownership/Heap.lean",
        "displayed heap value: the `scalar` constructor of `Ownership.Val` holding 0."),
    ".scalar 7": (
        "expression", "Ownership.Val.scalar", "Ownership/Heap.lean",
        "displayed heap value: the `scalar` constructor of `Ownership.Val` holding 7."),
    "1 < c.mult r": (
        "expression", "Ownership.Supported.decOne", "Ownership/CompleteAccounting.lean",
        "displayed premise of the `decOne` constructor: the checker's `n < c.mult r` at n = 1, "
        "with `c.mult` being `Ownership.Ctx.mult`."),
    "Accounted (resultSupport s support) H' env' c'": (
        "expression", "Ownership.Accounted", "Ownership/CompleteAccounting.lean",
        "applied conclusion of the preservation theorem; `Ownership.resultSupport` supplies the "
        "extended support."),
    "Accounted support H env c": (
        "expression", "Ownership.Accounted", "Ownership/CompleteAccounting.lean",
        "applied form of the relation, not a second declaration."),
    "Accounted support H mEnv c": (
        "expression", "Ownership.Accounted", "Ownership/CompleteAccounting.lean",
        "applied form of the relation at the model environment."),
    "AccountedAlong H env c support s": (
        "expression", "Ownership.AccountedAlong", "Ownership/Preservation.lean",
        "applied form of the along-the-run relation."),
    "Agrees assign p s env H root i v": (
        "expression", "OwnershipLcnf.Agrees", "OwnershipLcnf/Semantics.lean",
        "applied form at the machine and model arguments; `Ownership.Nested.Agrees` is a "
        "same-named predicate with a different signature."),
    "Corr H R": (
        "expression", "OwnershipLcnf.Runtime.Corr", "OwnershipLcnf/RuntimeModel.lean",
        "applied form of the runtime correspondence relation."),
    "CountFree b": (
        "expression", "Ownership.Nested.CountFree", "Ownership/Nested.lean",
        "applied form of the body predicate used as a checker premise."),
    "EntryInv H env (Runner.initCtx root) root client": (
        "expression", "Ownership.Entry.EntryInv", "Ownership/Entry.lean",
        "applied form of the entry invariant at the initializer's context."),
    "Exclusive H r": (
        "expression", "Ownership.Heap.Exclusive", "Ownership/Heap.lean",
        "applied form; `Ownership.Heap.Exclusive` is the predicate it spells."),
    "HeapCompat Hc Ha": (
        "expression", "Ownership.HeapCompat", "Ownership/CountedNested.lean",
        "applied form of the compatibility relation."),
    "Inv H env c": (
        "expression", "Ownership.Inv", "Ownership/Code.lean",
        "applied form of the raw invariant."),
    "Layout assign p": (
        "expression", "OwnershipLcnf.Layout", "OwnershipLcnf/Semantics.lean",
        "applied form of the layout premise."),
    "Path.build path value body (l :: rest)": (
        "expression", "Ownership.Path.build", "Ownership/Path.lean",
        "applied form at a cons list of levels."),
    "StoreSlots H env s": (
        "expression", "Ownership.StoreSlots", "Ownership/Preservation.lean",
        "applied form of the supplied slot premise."),
    "Supported c s": (
        "expression", "Ownership.Supported", "Ownership/CompleteAccounting.lean",
        "applied form of the fragment predicate."),
    "WellFormedEntry H p c i": (
        "expression", "Ownership.CountedPair.WellFormedEntry", "Ownership/CountedPair.lean",
        "applied form of the pair-protocol entry predicate at its parameters."),
    "check : Ctx → Code → Option Ctx": (
        "expression", "Ownership.check", "Ownership/Code.lean",
        "the checker's type ascription, written in the paper's notation."),
    "check c s = some c'": (
        "expression", "Ownership.check", "Ownership/Code.lean",
        "the judgment's definition as an equation on the checker; there is no separate "
        "derivability relation to name."),
    "checkNF : Ctx → List Frame → NCode → Option Ctx": (
        "expression", "Ownership.Nested.checkNF", "Ownership/Nested.lean",
        "the nested checker's type ascription, written in the paper's notation."),
    "checkAlias x": (
        "expression", "Ownership.LetF.checkAlias", "Ownership/Code.lean",
        "displayed right-hand side: the `checkAlias` constructor of `Ownership.LetF`."),
    "callAt state path x result b": (
        "expression", "Ownership.Nested.NCode.callAt", "Ownership/Nested.lean",
        "displayed constructor pattern of the nested language."),
    "dec x 1": (
        "expression", "Ownership.Code.dec", "Ownership/Code.lean",
        "displayed constructor pattern; the count-one form the fragment admits."),
    "inPlaceOutcome root i v o H": (
        "expression", "OwnershipLcnf.inPlaceOutcome", "OwnershipLcnf/Semantics.lean",
        "applied form of the outcome the executed prefix and the model run must both equal."),
    "isShared x": (
        "expression", "Ownership.LetF.isShared", "Ownership/Code.lean",
        "displayed right-hand side: the `isShared` constructor of `Ownership.LetF`."),
    "let y (checkAlias x)": (
        "expression", "Ownership.Code.let", "Ownership/Code.lean",
        "displayed program fragment; its right-hand side is `Ownership.LetF.checkAlias` and the "
        "checker rule for it is `Ownership.Supported.bindAlias`."),
    "lit n": (
        "expression", "Ownership.LetF.lit", "Ownership/Code.lean",
        "displayed right-hand side: the `lit` constructor of `Ownership.LetF`."),
    "projectPrefix code = some p": (
        "expression", "OwnershipLcnf.projectPrefix", "OwnershipLcnf/Projection.lean",
        "the recogniser's success equation, not a declaration."),
    "run s env H = .done H' env' v ws": (
        "expression", "Ownership.run", "Ownership/Code.lean",
        "the interpreter's completed-run equation."),
    "setArr x i v": (
        "expression", "Ownership.Code.setArr", "Ownership/Code.lean",
        "displayed constructor pattern of the flat language."),
    "size a": (
        "expression", "Ownership.LetF.size", "Ownership/Code.lean",
        "displayed right-hand side: the `size` constructor of `Ownership.LetF`."),
    "takeOut a i fst snd e": (
        "expression", "Ownership.Nested.NCode.takeOut", "Ownership/Nested.lean",
        "displayed constructor pattern of the nested language."),
    # -- bound variables in displayed rules ---------------------------------
    # A short name that the paper displays inside a statement is a binder, not a
    # declaration; the qualified column names the declaration whose binder it is
    # and the reason records the reading.
    "a": (
        "expression", "Ownership.Nested.NCode.takeOut", "Ownership/Nested.lean",
        "program variable: the array in the `takeOut` rule; a binder, not a declaration."),
    "c": (
        "expression", "Ownership.Supported", "Ownership/CompleteAccounting.lean",
        "program variable: the pre-state context `Supported` is indexed at; a binder, not a declaration."),
    "e": (
        "expression", "Ownership.Nested.NCode.takeOut", "Ownership/Nested.lean",
        "program variable: the fresh reference in the `takeOut` rule; a binder, not a declaration."),
    "fst": (
        "expression", "Ownership.Nested.NCode.takeOut", "Ownership/Nested.lean",
        "program variable: the parent binder of the take-out; a binder, not a declaration."),
    "i": (
        "expression", "Ownership.Code.setArr", "Ownership/Code.lean",
        "program variable: the index in the `setArr` and `takeOut` rules; a binder, not a declaration."),
    "path": (
        "expression", "Ownership.Nested.NCode.callAt", "Ownership/Nested.lean",
        "program variable: the path argument of the call rule; a binder, not a declaration."),
    "r": (
        "expression", "Ownership.Heap.Exclusive", "Ownership/Heap.lean",
        "program variable: the reference `Exclusive` is stated at; a binder, not a declaration."),
    "result": (
        "expression", "Ownership.Nested.NCode.callAt", "Ownership/Nested.lean",
        "program variable: the result binder of the call rule; a binder, not a declaration."),
    "snd": (
        "expression", "Ownership.Nested.NCode.takeOut", "Ownership/Nested.lean",
        "program variable: the child binder of the take-out; a binder, not a declaration."),
    "state": (
        "expression", "Ownership.Nested.NCode.callAt", "Ownership/Nested.lean",
        "program variable: the state argument of the call rule; a binder, not a declaration."),
    "v": (
        "expression", "Ownership.Code.setArr", "Ownership/Code.lean",
        "program variable: the stored value in the `setArr` rule; a binder, not a declaration."),
    "x": (
        "expression", "Ownership.Supported.bindAlias", "Ownership/CompleteAccounting.lean",
        "program variable: the owned source handle of the alias rule, reused across the other "
        "rules of the table; a binder, not a declaration."),
    "y": (
        "expression", "Ownership.Supported.bindAlias", "Ownership/CompleteAccounting.lean",
        "program variable: the alias target of the alias rule; a binder, not a declaration."),
}


# --------------------------------------------------------------------------
# Paper extraction
# --------------------------------------------------------------------------
HEADING = re.compile(r"^\s*\\(section|subsection|subsubsection|paragraph)\*?\{([^}]*)\}")


def blank_comments(text):
    """Blank LaTeX comments, preserving every offset and line break.

    A `\\lean{...}` inside a comment is not displayed, so it is not a token:
    the paper's macro definition paragraph uses `\\lean{...}` as an example.
    """
    buf = list(text)
    i = 0
    n = len(text)
    while i < n:
        if text[i] == "%" and (i == 0 or text[i - 1] != "\\"):
            j = text.find("\n", i)
            j = n if j < 0 else j
            for k in range(i, j):
                buf[k] = " "
            i = j
        else:
            i += 1
    return "".join(buf)


def heading_offsets(text):
    """(offset, title) for every heading, in order."""
    out = []
    pos = 0
    for line in text.split("\n"):
        m = HEADING.match(line)
        if m:
            out.append((pos, re.sub(r"\\[a-zA-Z]+\s*", "", m.group(2)).strip()))
        pos += len(line) + 1
    return out


def unescape(raw):
    s = raw.replace("\\allowbreak", "")
    s = s.replace("\\_", "_")
    # A line continuation inside a span, and any other run of whitespace, is one
    # space in the displayed name.
    return " ".join(s.split())


def paper_tokens(text):
    """Ordered token -> sections, from the spans that survive comment blanking."""
    text = blank_comments(text)
    heads = heading_offsets(text)
    tokens = {}
    pos = 0
    for m in re.finditer(r"\\lean\{", text):
        if m.start() < pos:
            continue
        start = m.end()
        depth = 1
        j = start
        while j < len(text) and depth > 0:
            if text[j] == "{":
                depth += 1
            elif text[j] == "}":
                depth -= 1
            j += 1
        if depth != 0:
            raise SystemExit(f"claim census: unterminated \\lean{{ at offset {m.start()}")
        tok = unescape(text[start:j - 1])
        pos = j
        if "\n" in tok or "|" in tok:
            raise SystemExit(f"claim census: token unusable in a table cell: {tok!r}")
        section = "(front matter)"
        for off, title in heads:
            if off <= m.start():
                section = title
            else:
                break
        sections = tokens.setdefault(tok, [])
        if section not in sections:
            sections.append(section)
    return tokens


# --------------------------------------------------------------------------
# Map generation and parsing
# --------------------------------------------------------------------------
def classification():
    table = {}
    for tok, value in DECLARATIONS.items():
        qual, mod = value[0], value[1]
        reason = value[2] if len(value) > 2 else ""
        table[tok] = ("declaration", qual, mod, reason)
    for tok, path in MODULES.items():
        if tok in table:
            raise SystemExit(f"claim census: {tok} classified twice")
        table[tok] = ("module", path, path, "")
    for tok, (kind, qual, mod, reason) in ALLOWLIST.items():
        if tok in table:
            raise SystemExit(f"claim census: {tok} classified twice")
        if kind == "declaration":
            raise SystemExit(f"claim census: {tok} is in the declaration table, not the allowlist")
        if kind not in KINDS:
            raise SystemExit(f"claim census: {tok} has unknown kind {kind}")
        if not reason.strip():
            raise SystemExit(f"claim census: allowlisted {tok} has no reason")
        table[tok] = (kind, qual, mod, reason)
    for tok, (kind, qual, mod, reason) in table.items():
        for field in (tok, kind, qual, mod, reason):
            if "|" in field:
                raise SystemExit(f"claim census: {tok} has a field containing '|'")
    return table


def render(table, sections):
    lines = [
        "# Claim census",
        "",
        "Every Lean name the manuscript displays in a `\\lean{...}` span, mapped to what it",
        "denotes in this repository. The table is generated: `scripts/check_claims.sh --generate`",
        "rewrites exactly this file, and the checker fails when the checked-in table differs from",
        "that output. Edit the classification in the script, not here.",
        "",
        "Kinds: `declaration` rows are checked with `#check` under the pinned toolchain; `module`",
        "rows must name an existing path; `runtime-primitive`, `concept` and `expression` rows are",
        "allowlisted in the script and must carry the reason the last column records.",
        "",
        "| token | kind | qualified | module | section | reason |",
        "| --- | --- | --- | --- | --- | --- |",
    ]
    for tok in sorted(table):
        kind, qual, mod, reason = table[tok]
        cells = [
            f"`{tok}`",
            kind,
            f"`{qual}`" if qual and qual != "—" else "—",
            f"`{mod}`" if mod and mod != "—" else "—",
            "; ".join(sections.get(tok, [])) or "—",
            reason if reason else "—",
        ]
        lines.append("| " + " | ".join(cells) + " |")
    return "\n".join(lines) + "\n"


def parse_map(text):
    rows = []
    seen_header = False
    for lineno, line in enumerate(text.split("\n"), 1):
        stripped = line.strip()
        if not stripped.startswith("|"):
            continue
        cells = [c.strip() for c in stripped.strip("|").split("|")]
        if len(cells) != 6:
            raise ValueError(f"line {lineno}: expected 6 columns, found {len(cells)}")
        if cells[0] == "token":
            seen_header = True
            continue
        if all(set(c) <= set("-: ") for c in cells):
            continue
        tok = cells[0]
        if not (tok.startswith("`") and tok.endswith("`")):
            raise ValueError(f"line {lineno}: token cell is not a code span: {tok}")
        tok = tok[1:-1]

        def value(cell):
            return "" if cell == "—" else cell.strip("`")

        rows.append({
            "token": tok,
            "kind": cells[1],
            "qualified": value(cells[2]),
            "module": value(cells[3]),
            "section": cells[4],
            "reason": "" if cells[5] == "—" else cells[5],
            "line": lineno,
        })
    if not rows:
        raise ValueError("no rows found")
    if not seen_header:
        raise ValueError("no table header found")
    return rows


# --------------------------------------------------------------------------
# The check
# --------------------------------------------------------------------------
LEAN_TMP = os.path.join(tempfile.gettempdir(), "ownership-claim-check")
LEAN_FILE = os.path.join(LEAN_TMP, "ClaimCheck.lean")


def module_path_ok(mod):
    """A declaration row's module is a repository path, or Lean's core `Init`.

    `Nat`, `Array.markLinear` and `Array.getElem?_setIfInBounds_self_of_lt` are
    core declarations the paper displays; their module is the core library, which
    has no path in this repository.
    """
    return mod == "Init" or os.path.exists(os.path.join(ROOT, mod))


def lean_check(decls):
    """`#check` every declaration row; return the problems and the command run."""
    imports = sorted({r["module"][:-len(".lean")].replace("/", ".") for r in decls
                      if r["module"].endswith(".lean")})
    os.makedirs(LEAN_TMP, exist_ok=True)
    with open(LEAN_FILE, "w", encoding="utf-8") as fh:
        for mod in imports:
            fh.write(f"import {mod}\n")
        fh.write("\n")
        for r in sorted(decls, key=lambda r: r["token"]):
            fh.write(f"#check {r['qualified']}\n")
    cmd = ["nix", "develop", "-c", "lake", "env", "lean", LEAN_FILE]
    try:
        proc = subprocess.run(cmd, cwd=ROOT, capture_output=True, text=True)
    except FileNotFoundError:
        return ([f"declaration check failed: '{cmd[0]}' not found; run this script under "
                 f"'nix develop -c bash scripts/check_claims.sh'"], " ".join(cmd))
    out = (proc.stdout or "") + (proc.stderr or "")
    problems = []
    for line in out.split("\n"):
        low = line.lower()
        if "error" in low or "unknownidentifier" in low or "unknown constant" in low:
            problems.append(f"declaration check failed: {line.strip()}")
    if proc.returncode != 0:
        lines = [l.strip() for l in out.split("\n")
                 if l.strip() and "warning:" not in l and not l.strip().startswith("scidonia-lean:")]
        tail = " / ".join(lines[-2:]) if lines else "(no diagnostic)"
        problems.append(f"declaration check failed: lean exited {proc.returncode}: {tail}")
    return problems, " ".join(cmd)


def check(paper_text, map_text, run_lean=True):
    problems = []
    tokens = paper_tokens(paper_text)
    try:
        rows = parse_map(map_text)
    except ValueError as exc:
        return [f"claim map unreadable: {exc}"], None, None

    by_token = {}
    for r in rows:
        if r["token"] in by_token:
            problems.append(f"paper token mapped by more than one row: {r['token']}")
        else:
            by_token[r["token"]] = r
    for tok in tokens:
        if tok not in by_token:
            problems.append(f"paper token with no map row: {tok}")
    for tok in by_token:
        if tok not in tokens:
            problems.append(f"map row not cited by any paper token: {tok}")

    for r in rows:
        tok = r["token"]
        if r["kind"] not in KINDS:
            problems.append(f"row {tok} has unknown kind: {r['kind']}")
            continue
        if r["kind"] == "declaration":
            if not r["qualified"]:
                problems.append(f"declaration row without a qualified name: {tok}")
            if not r["module"]:
                problems.append(f"declaration row without a module: {tok}")
            if not module_path_ok(r["module"]):
                problems.append(f"declaration row module missing: {r['module']} ({tok})")
        elif r["kind"] == "module":
            if not os.path.exists(os.path.join(ROOT, r["module"])):
                problems.append(f"module row path missing: {r['module']} ({tok})")
        else:
            allow = ALLOWLIST.get(tok)
            if allow is None:
                problems.append(f"non-declaration row not allowlisted: {tok}")
            elif allow[0] != r["kind"]:
                problems.append(f"row {tok} kind {r['kind']} disagrees with the allowlist ({allow[0]})")
            if not r["reason"].strip():
                problems.append(f"allowlisted row without a reason: {tok}")

    generated = render(classification(), tokens)
    for tok in classification():
        if tok not in tokens:
            problems.append(f"classification token absent from the paper: {tok}")
    if map_text != generated:
        problems.append("claim map differs from --generate output: regenerate it with "
                        "'bash scripts/check_claims.sh --generate'")

    cmd = None
    if run_lean:
        decls = [r for r in rows if r["kind"] == "declaration" and r["qualified"] and r["module"]]
        if decls:
            lean_problems, cmd = lean_check(decls)
            problems.extend(lean_problems)
    return problems, tokens, cmd


def read(path):
    with open(path, encoding="utf-8") as fh:
        return fh.read()


def counts(rows):
    out = {k: 0 for k in KINDS}
    for r in rows:
        out[r["kind"]] = out.get(r["kind"], 0) + 1
    return ", ".join(f"{k} {out[k]}" for k in KINDS)


def report(problems):
    for p in problems:
        print(f"claim census: FAIL: {p}")
    return 1


def generate():
    text = render(classification(), paper_tokens(read(PAPER)))
    with open(MAP, "w", encoding="utf-8") as fh:
        fh.write(text)
    print(f"claim census: wrote {os.path.relpath(MAP, ROOT)} ({text.count(chr(10) + '| `')} rows)",
          file=sys.stderr)


def self_test():
    """Three negative controls plus the unmodified inputs.

    Each mutant must fail with its own diagnostic; the unmodified inputs must
    pass. The diagnostics are printed so the run reports what it observed.
    """
    paper = read(PAPER)
    map_text = read(MAP)
    failures = []

    base_problems, _, base_cmd = check(paper, map_text)
    if base_problems:
        failures.extend(["unmodified inputs did not pass"] + base_problems)

    token_mutant = paper.replace(
        "\\end{document}",
        "\\lean{orphanTokenForSelfTest}\n\\end{document}",
        1,
    )
    if token_mutant == paper:
        failures.append("self-test could not place the orphan token")
    problems, _, _ = check(token_mutant, map_text, run_lean=False)
    want = "paper token with no map row: orphanTokenForSelfTest"
    if want not in problems:
        failures.extend([f"missing-token control did not report '{want}'"] + problems)
    else:
        print(f"self-test (a) observed: {want}")

    ghost = ("| `ghostTokenForSelfTest` | concept | — | — | Introduction | "
             "a row no paper token cites |")
    ghost_map = map_text.replace("| --- | --- | --- | --- | --- | --- |\n",
                                 "| --- | --- | --- | --- | --- | --- |\n" + ghost + "\n", 1)
    if ghost_map == map_text:
        failures.append("self-test could not insert the ghost row")
    problems, _, _ = check(paper, ghost_map, run_lean=False)
    want = "map row not cited by any paper token: ghostTokenForSelfTest"
    if want not in problems:
        failures.extend([f"uncited-row control did not report '{want}'"] + problems)
    else:
        print(f"self-test (b) observed: {want}")

    broken = []
    for line in map_text.split("\n"):
        if line.startswith("| `Accounted` | declaration |"):
            broken.append(line.replace("`Ownership.Accounted`",
                                       "`Ownership.thisDeclarationDoesNotExist`", 1))
        else:
            broken.append(line)
    broken_map = "\n".join(broken)
    if broken_map == map_text:
        failures.append("self-test could not corrupt the declaration row")
    problems, _, _ = check(paper, broken_map)
    want = "declaration check failed: "
    hit = [p for p in problems if p.startswith(want) and "thisDeclarationDoesNotExist" in p]
    if not hit:
        failures.extend([f"nonexistent-declaration control did not report '{want}'"] + problems)
    else:
        print(f"self-test (c) observed: {hit[0]}")

    if failures:
        print("claim census: SELF-TEST FAILED")
        return report(failures)
    print("claim census: self-test OK: (a) orphan paper token, (b) uncited map row, "
          "(c) unknown declaration each failed with the diagnostic above; the "
          "unmodified inputs pass")
    print(f"claim census: declaration command: {base_cmd}")
    return 0


def main():
    if not ARGV:
        problems, tokens, cmd = check(read(PAPER), read(MAP))
        if problems:
            return report(problems)
        rows = parse_map(read(MAP))
        print(f"claim census: OK: {len(tokens)} distinct tokens, {len(rows)} rows "
              f"({counts(rows)})")
        if cmd:
            print(f"claim census: declaration command: {cmd}")
        return 0
    if ARGV == ["--generate"]:
        generate()
        return 0
    if ARGV == ["--self-test"]:
        return self_test()
    print("usage: bash scripts/check_claims.sh [--generate|--self-test]", file=sys.stderr)
    return 2


sys.exit(main())
PY
