# Claim census

Every Lean name the manuscript displays in a `\lean{...}` span, mapped to what it
denotes in this repository. The table is generated: `scripts/check_claims.sh --generate`
rewrites exactly this file, and the checker fails when the checked-in table differs from
that output. Edit the classification in the script, not here.

Kinds: `declaration` rows are checked with `#check` under the pinned toolchain; `module`
rows must name an existing path; `runtime-primitive`, `concept` and `expression` rows are
allowlisted in the script and must carry the reason the last column records.

| token | kind | qualified | module | section | reason |
| --- | --- | --- | --- | --- | --- |
| `.dec` | declaration | `Ownership.Code.dec` | `Ownership/Code.lean` | The supported fragment | constructor of `Ownership.Code`, displayed with its leading dot |
| `.dec x 1` | expression | `Ownership.Code.dec` | `Ownership/Code.lean` | The supported fragment; Scope, conclusion and disclosure | displayed program fragment: the `dec` constructor at count one; the checker's form of the same step is `Ownership.Supported.decOne`. |
| `.inPlace H' root` | expression | `OwnershipLcnf.Runtime.SetOutcome.inPlace` | `OwnershipLcnf/RuntimeModel.lean` | Recognition, and the flat guarantee | displayed result pattern of the runtime model's in-place branch. |
| `.inc` | declaration | `Ownership.Code.inc` | `Ownership/Code.lean` | The supported fragment; Scope, conclusion and disclosure | constructor of `Ownership.Code`, displayed with its leading dot |
| `.let` | declaration | `Ownership.Code.let` | `Ownership/Code.lean` | The supported fragment | constructor of `Ownership.Code`, displayed with its leading dot |
| `.mutate` | declaration | `Ownership.PutBack.mutate` | `Ownership/PutBack.lean` | The counted call and restoration; A worked instance | constructor of `Ownership.PutBack.Disposition`, displayed with its leading dot |
| `.ref 1` | expression | `Ownership.Val.ref` | `Ownership/Heap.lean` | A worked instance | displayed heap value: the `ref` constructor of `Ownership.Val` at reference 1. |
| `.scalar 0` | expression | `Ownership.Val.scalar` | `Ownership/Heap.lean` | A worked instance | displayed heap value: the `scalar` constructor of `Ownership.Val` holding 0. |
| `.scalar 7` | expression | `Ownership.Val.scalar` | `Ownership/Heap.lean` | A worked instance | displayed heap value: the `scalar` constructor of `Ownership.Val` holding 7. |
| `1 < c.mult r` | expression | `Ownership.Supported.decOne` | `Ownership/CompleteAccounting.lean` | The supported fragment | displayed premise of the `decOne` constructor: the checker's `n < c.mult r` at n = 1, with `c.mult` being `Ownership.Ctx.mult`. |
| `Accounted` | declaration | `Ownership.Accounted` | `Ownership/CompleteAccounting.lean` | The pair and its boundary; Compatibility and the boundary argument; Proof sketch.; Recognition, and the flat guarantee; Related work | — |
| `Accounted (resultSupport s support) H' env' c'` | expression | `Ownership.Accounted` | `Ownership/CompleteAccounting.lean` | Preservation | applied conclusion of the preservation theorem; `Ownership.resultSupport` supplies the extended support. |
| `Accounted support H env c` | expression | `Ownership.Accounted` | `Ownership/CompleteAccounting.lean` | Complete ownership accounting; Preservation | applied form of the relation, not a second declaration. |
| `Accounted support H mEnv c` | expression | `Ownership.Accounted` | `Ownership/CompleteAccounting.lean` | The finite path and the counted fragment | applied form of the relation at the model environment. |
| `Accounted.decOne` | declaration | `Ownership.Accounted.decOne` | `Ownership/CompleteAccounting.lean` | Proof sketch. | — |
| `Accounted.move` | declaration | `Ownership.Accounted.move` | `Ownership/CompleteAccounting.lean` | Proof sketch. | — |
| `Accounted.setArrInPlace` | declaration | `Ownership.Accounted.setArrInPlace` | `Ownership/CompleteAccounting.lean` | Proof sketch. | — |
| `Accounted.setScalar` | declaration | `Ownership.Accounted.setScalar` | `Ownership/CompleteAccounting.lean` | Proof sketch. | — |
| `AccountedAlong` | declaration | `Ownership.AccountedAlong` | `Ownership/Preservation.lean` | Preservation | — |
| `AccountedAlong H env c support s` | expression | `Ownership.AccountedAlong` | `Ownership/Preservation.lean` | Preservation | applied form of the along-the-run relation. |
| `Agrees assign p s env H root i v` | expression | `OwnershipLcnf.Agrees` | `OwnershipLcnf/Semantics.lean` | Recognition, and the flat guarantee | applied form at the machine and model arguments; `Ownership.Nested.Agrees` is a same-named predicate with a different signature. |
| `AnnotationsIn` | declaration | `Ownership.Entry.AnnotationsIn` | `Ownership/Entry.lean` | Compatibility and the boundary argument | — |
| `Array.getElem?_setIfInBounds_self_of_lt` | declaration | `Array.getElem?_setIfInBounds_self_of_lt` | `Init` | A worked instance | — |
| `Array.markLinear` | declaration | `Array.markLinear` | `Init` | Related work | — |
| `ChildCall.separated` | declaration | `Ownership.PutBack.ChildCall.separated` | `Ownership/PutBack.lean` | Compatibility and the boundary argument | — |
| `ChildContract` | declaration | `OwnershipLcnf.ChildContract` | `OwnershipLcnf/NestedSemantics.lean` | The counted call and restoration; The finite path and the counted fragment | — |
| `Code` | declaration | `Ownership.Code` | `Ownership/Code.lean` | Two languages, one accounted subset | — |
| `Corr` | declaration | `OwnershipLcnf.Runtime.Corr` | `OwnershipLcnf/RuntimeModel.lean` | Recognition, and the flat guarantee | the runtime correspondence relation inside `OwnershipLcnf.Runtime`; the model-side `OwnershipLcnf.Agrees` is a different relation |
| `Corr H R` | expression | `OwnershipLcnf.Runtime.Corr` | `OwnershipLcnf/RuntimeModel.lean` | Recognition, and the flat guarantee | applied form of the runtime correspondence relation. |
| `CountFidelity` | declaration | `Ownership.CountFidelity` | `Ownership/Accounting.lean` | Complete ownership accounting; Recognition, and the flat guarantee | — |
| `CountFree b` | expression | `Ownership.Nested.CountFree` | `Ownership/Nested.lean` | The judgement. | applied form of the body predicate used as a checker premise. |
| `CountedChildCall` | declaration | `Ownership.CountedChildCall` | `Ownership/CountedNested.lean` | The pair and its boundary; The counted call and restoration; A worked instance; Scope, conclusion and disclosure | — |
| `EntryInv H env (Runner.initCtx root) root client` | expression | `Ownership.Entry.EntryInv` | `Ownership/Entry.lean` | Recognition, and the flat guarantee | applied form of the entry invariant at the initializer's context. |
| `EnvOwnerCount` | declaration | `Ownership.EnvOwnerCount` | `Ownership/Accounting.lean` | Proof sketch.; The pair and its boundary | — |
| `Exclusive H r` | expression | `Ownership.Heap.Exclusive` | `Ownership/Heap.lean` | Complete ownership accounting | applied form; `Ownership.Heap.Exclusive` is the predicate it spells. |
| `Heap` | declaration | `Ownership.Heap` | `Ownership/Heap.lean` | Two languages, one accounted subset | — |
| `Heap.Exclusive` | declaration | `Ownership.Heap.Exclusive` | `Ownership/Heap.lean` | The pair and its boundary; The counted call and restoration | — |
| `HeapCompat` | declaration | `Ownership.HeapCompat` | `Ownership/CountedNested.lean` | The counted call and restoration; Proof sketch.; The finite path and the counted fragment; A worked instance; What the mechanisation taught | — |
| `HeapCompat Hc Ha` | expression | `Ownership.HeapCompat` | `Ownership/CountedNested.lean` | Compatibility and the boundary argument | applied form of the compatibility relation. |
| `HeapCompat.eq_of_cursor_eq` | declaration | `Ownership.HeapCompat.eq_of_cursor_eq` | `Ownership/CountedNested.lean` | Compatibility and the boundary argument | — |
| `IncomingCount` | declaration | `Ownership.IncomingCount` | `Ownership/Accounting.lean` | Proof sketch.; The pair and its boundary | — |
| `IncomingCount_baseHeap` | declaration | `OwnershipTest.CountedFamily.IncomingCount_baseHeap` | `OwnershipTest/CountedFamily.lean` | A worked instance | — |
| `IncomingCount_set_fill` | declaration | `Ownership.IncomingCount_set_fill` | `Ownership/CompleteAccounting.lean` | A worked instance | — |
| `IncomingCount_set_fill_ne` | declaration | `Ownership.IncomingCount_set_fill_ne` | `Ownership/CompleteAccounting.lean` | A worked instance | — |
| `Inv` | declaration | `Ownership.Inv` | `Ownership/Code.lean` | Complete ownership accounting; Compatibility and the boundary argument; Scope, conclusion and disclosure | — |
| `Inv H env c` | expression | `Ownership.Inv` | `Ownership/Code.lean` | Complete ownership accounting | applied form of the raw invariant. |
| `Inv.owned` | declaration | `Ownership.Inv.owned` | `Ownership/Code.lean` | Complete ownership accounting | — |
| `Inv.rc_eq` | declaration | `Ownership.Inv.rc_eq` | `Ownership/Code.lean` | Complete ownership accounting | — |
| `LEAN_ABORT_ON_NONLINEAR` | runtime-primitive | `LEAN_ABORT_ON_NONLINEAR` | — | Related work | Lean runtime option that aborts execution on a nonlinear use of a linearly marked array; a runtime flag of Lean itself, not a declaration of this development. |
| `Layout assign p` | expression | `OwnershipLcnf.Layout` | `OwnershipLcnf/Semantics.lean` | Recognition, and the flat guarantee | applied form of the layout premise. |
| `Layout5.setAt` | concept | `Layout5.setAt` | — | The update and its ownership traffic | declaration of the pinned sibling compiler-input package, not of this repository; the paper names it as the source of the running example. |
| `LetF` | declaration | `Ownership.LetF` | `Ownership/Code.lean` | Two languages, one accounted subset | — |
| `NCode` | declaration | `Ownership.Nested.NCode` | `Ownership/Nested.lean` | Two languages, one accounted subset | the nested language lives in `Ownership.Nested`; `Ownership.Code` is the flat one |
| `Nat` | declaration | `Nat` | `Init` | Two languages, one accounted subset | — |
| `NestedAgrees` | declaration | `OwnershipLcnf.NestedAgrees` | `OwnershipLcnf/NestedSemantics.lean` | The finite path and the counted fragment | — |
| `NestedOutcome` | declaration | `OwnershipLcnf.NestedOutcome` | `OwnershipLcnf/NestedSemantics.lean` | The finite path and the counted fragment | — |
| `NestedOutcome.Compat` | declaration | `OwnershipLcnf.NestedOutcome.Compat` | `OwnershipLcnf/CountedTrace.lean` | The finite path and the counted fragment; Proof sketch. | — |
| `OwnersAccounted` | declaration | `Ownership.OwnersAccounted` | `Ownership/Accounting.lean` | Complete ownership accounting; Recognition, and the flat guarantee; Scope, conclusion and disclosure | — |
| `Ownership` | module | `Ownership.lean` | `Ownership.lean` | Evidence and artifact; Scope, conclusion and disclosure | — |
| `Ownership.Pair.runP` | declaration | `Ownership.Pair.runP` | `Ownership/Pair.lean` | Scope, conclusion and disclosure | — |
| `Ownership/CompleteAccounting.lean` | module | `Ownership/CompleteAccounting.lean` | `Ownership/CompleteAccounting.lean` | Evidence and artifact | — |
| `Ownership/CountedNested.lean` | module | `Ownership/CountedNested.lean` | `Ownership/CountedNested.lean` | Evidence and artifact | — |
| `Ownership/Preservation.lean` | module | `Ownership/Preservation.lean` | `Ownership/Preservation.lean` | Evidence and artifact | — |
| `OwnershipLcnf` | module | `OwnershipLcnf.lean` | `OwnershipLcnf.lean` | Evidence and artifact; Scope, conclusion and disclosure | — |
| `OwnershipLcnf/CountedTrace.lean` | module | `OwnershipLcnf/CountedTrace.lean` | `OwnershipLcnf/CountedTrace.lean` | Evidence and artifact | — |
| `OwnershipLcnf/Principal.lean` | module | `OwnershipLcnf/Principal.lean` | `OwnershipLcnf/Principal.lean` | The finite path and the counted fragment; Evidence and artifact | — |
| `OwnershipTest` | module | `OwnershipTest.lean` | `OwnershipTest.lean` | Evidence and artifact | — |
| `Path.build` | declaration | `Ownership.Path.build` | `Ownership/Path.lean` | The finite path and the counted fragment | — |
| `Path.build path value body (l :: rest)` | expression | `Ownership.Path.build` | `Ownership/Path.lean` | The finite path and the counted fragment | applied form at a cons list of levels. |
| `Path.index` | concept | `Path.index` | — | Recognition, and the flat guarantee | the `.index` constructor arm of the sibling `Path` type that `Layout5.setAt` matches; declared in the pinned sibling repository, and the local `Ownership.Path` module has no `index` constructor. |
| `Prefix.toModel` | declaration | `OwnershipLcnf.Prefix.toModel` | `OwnershipLcnf/Projection.lean` | Two languages, one accounted subset | — |
| `Prefix.toModel_supported` | declaration | `OwnershipLcnf.Prefix.toModel_supported` | `OwnershipLcnf/Principal.lean` | Recognition, and the flat guarantee | — |
| `Runtime.setAt_inPlace_of_entryInv` | declaration | `OwnershipLcnf.Runtime.setAt_inPlace_of_entryInv` | `OwnershipLcnf/RuntimeModel.lean` | Recognition, and the flat guarantee | — |
| `StoreSlots` | declaration | `Ownership.StoreSlots` | `Ownership/Preservation.lean` | The supported fragment; Recognition, and the flat guarantee; Scope, conclusion and disclosure | — |
| `StoreSlots H env s` | expression | `Ownership.StoreSlots` | `Ownership/Preservation.lean` | The supported fragment; Preservation | applied form of the supplied slot premise. |
| `Supported` | declaration | `Ownership.Supported` | `Ownership/CompleteAccounting.lean` | Two languages, one accounted subset; Scope, conclusion and disclosure | — |
| `Supported c s` | expression | `Ownership.Supported` | `Ownership/CompleteAccounting.lean` | The supported fragment; Preservation; Proof sketch. | applied form of the fragment predicate. |
| `TakeOutsOK` | declaration | `Ownership.Nested.TakeOutsOK` | `Ownership/Nested.lean` | Compatibility and the boundary argument | — |
| `Val` | declaration | `Ownership.Val` | `Ownership/Heap.lean` | Two languages, one accounted subset | — |
| `WellFormedEntry H p c i` | expression | `Ownership.CountedPair.WellFormedEntry` | `Ownership/CountedPair.lean` | The pair and its boundary | applied form of the pair-protocol entry predicate at its parameters. |
| `Write` | declaration | `Ownership.Write` | `Ownership/Code.lean` | Scope, conclusion and disclosure | — |
| `\#guard` | concept | `\#guard` | — | Scope, conclusion and disclosure | Lean command syntax (an elaboration-time test) written with a LaTeX-escaped `#`; a command, not a declaration. |
| `\#print axioms` | concept | `\#print axioms` | — | A worked instance | Lean command that prints a declaration's axiom footprint; a command, not a declaration. |
| `a` | expression | `Ownership.Nested.NCode.takeOut` | `Ownership/Nested.lean` | The judgement. | program variable: the array in the `takeOut` rule; a binder, not a declaration. |
| `accounted` | declaration | `Ownership.CountedChildCall.accounted` | `Ownership/CountedNested.lean` | The counted call and restoration; Scope, conclusion and disclosure | the field, not a free-standing declaration; `Ownership.CountedChildCall.call` is its sibling |
| `alias_not_accounted` | declaration | `Ownership.alias_not_accounted` | `Ownership/Accounting.lean` | Introduction; Complete ownership accounting; What the mechanisation taught | — |
| `at_most_one_owner` | declaration | `Ownership.Accounted.at_most_one_owner` | `Ownership/CompleteAccounting.lean` | Complete ownership accounting | — |
| `bindAlias` | declaration | `Ownership.Supported.bindAlias` | `Ownership/CompleteAccounting.lean` | Proof sketch. | constructor of `Ownership.Supported`, not `Ownership.Ctx.bindOwned` |
| `bindLit` | declaration | `Ownership.Supported.bindLit` | `Ownership/CompleteAccounting.lean` | Proof sketch. | constructor of `Ownership.Supported` |
| `bindOwned` | declaration | `Ownership.Ctx.bindOwned` | `Ownership/Code.lean` | Complete ownership accounting; The judgement. | context update; the paper lists it with `setUs`, `move`, `inc` and `dec` |
| `bindShared` | declaration | `Ownership.Supported.bindShared` | `Ownership/CompleteAccounting.lean` | Proof sketch. | constructor of `Ownership.Supported` |
| `bindSize` | declaration | `Ownership.Supported.bindSize` | `Ownership/CompleteAccounting.lean` | Proof sketch. | constructor of `Ownership.Supported` |
| `borrow` | declaration | `Ownership.Inv.borrow` | `Ownership/Code.lean` | Complete ownership accounting | field of `Ownership.Inv`; `Ownership.U.borrow` is the usage tag of the same name |
| `boundary_accounted` | declaration | `OwnershipTest.CountedFamily.boundary_accounted` | `OwnershipTest/CountedFamily.lean` | A worked instance | — |
| `boundary_cells` | declaration | `OwnershipTest.CountedFamily.boundary_cells` | `OwnershipTest/CountedFamily.lean` | A worked instance | — |
| `c` | expression | `Ownership.Supported` | `Ownership/CompleteAccounting.lean` | The supported fragment | program variable: the pre-state context `Supported` is indexed at; a binder, not a declaration. |
| `call` | declaration | `Ownership.CountedChildCall.call` | `Ownership/CountedNested.lean` | The counted call and restoration | the field, not `Ownership.PutBack.ChildCall` |
| `callAt state path x result b` | expression | `Ownership.Nested.NCode.callAt` | `Ownership/Nested.lean` | The judgement. | displayed constructor pattern of the nested language. |
| `callAt_frame_confined` | declaration | `Ownership.Entry.callAt_frame_confined` | `Ownership/Entry.lean` | Compatibility and the boundary argument | — |
| `calledAccounted` | declaration | `OwnershipTest.calledAccounted` | `OwnershipTest/Principal.lean` | The counted call and restoration; A worked instance | the closed principal instance's discharge; `OwnershipTest.CountedFamily.calledAccounted` and `OwnershipTest.CountedNested.calledAccounted` are same-named siblings for other instances |
| `check` | declaration | `Ownership.check` | `Ownership/Code.lean` | Two languages, one accounted subset | — |
| `check : Ctx → Code → Option Ctx` | expression | `Ownership.check` | `Ownership/Code.lean` | The judgement, once | the checker's type ascription, written in the paper's notation. |
| `check c s = some c'` | expression | `Ownership.check` | `Ownership/Code.lean` | Two languages, one accounted subset; The judgement.; Preservation | the judgment's definition as an equation on the checker; there is no separate derivability relation to name. |
| `checkAlias x` | expression | `Ownership.LetF.checkAlias` | `Ownership/Code.lean` | Two languages, one accounted subset | displayed right-hand side: the `checkAlias` constructor of `Ownership.LetF`. |
| `checkN` | declaration | `Ownership.Nested.checkN` | `Ownership/Nested.lean` | Two languages, one accounted subset | — |
| `checkNF` | declaration | `Ownership.Nested.checkNF` | `Ownership/Nested.lean` | The counted call and restoration | — |
| `checkNF : Ctx → List Frame → NCode → Option Ctx` | expression | `Ownership.Nested.checkNF` | `Ownership/Nested.lean` | The judgement, once | the nested checker's type ascription, written in the paper's notation. |
| `checkN_extraction_exclusive_of_entryInv` | declaration | `Ownership.Entry.checkN_extraction_exclusive_of_entryInv` | `Ownership/Entry.lean` | Scope, conclusion and disclosure | — |
| `childContracts_of_path` | declaration | `OwnershipLcnf.childContracts_of_path` | `OwnershipLcnf/PathRecursion.lean` | The counted call and restoration; The finite path and the counted fragment | — |
| `count_one_dichotomy` | declaration | `Ownership.Accounted.count_one_dichotomy` | `Ownership/CompleteAccounting.lean` | Complete ownership accounting | — |
| `countedBoundaryCall` | declaration | `OwnershipTest.CountedFamily.countedBoundaryCall` | `OwnershipTest/CountedFamily.lean` | A worked instance | — |
| `countedPrefix` | declaration | `OwnershipLcnf.countedPrefix` | `OwnershipLcnf/CountedTrace.lean` | Proof sketch. | — |
| `countedSuffix` | declaration | `OwnershipLcnf.countedSuffix` | `OwnershipLcnf/CountedTrace.lean` | Proof sketch. | — |
| `counted_fragment_instance` | declaration | `OwnershipTest.counted_fragment_instance` | `OwnershipTest/PrincipalCounted.lean` | A worked instance | — |
| `counted_nested_chain` | declaration | `Ownership.counted_nested_chain` | `Ownership/CountedNested.lean` | Three contributions.; The counted call and restoration; Proof sketch.; A worked instance | — |
| `counted_nested_chain_restoration` | declaration | `Ownership.counted_nested_chain_restoration` | `Ownership/CountedNested.lean` | The counted call and restoration | — |
| `counted_restore` | declaration | `Ownership.counted_restore` | `Ownership/CountedNested.lean` | The counted call and restoration | — |
| `counted_takeOut` | declaration | `Ownership.counted_takeOut` | `Ownership/CountedNested.lean` | The counted call and restoration | — |
| `dec` | declaration | `Ownership.Ctx.dec` | `Ownership/Code.lean` | The judgement. | the context update; `Ownership.Code.dec` is the constructor of the same name |
| `dec x 1` | expression | `Ownership.Code.dec` | `Ownership/Code.lean` | The judgement. | displayed constructor pattern; the count-one form the fragment admits. |
| `decOne` | declaration | `Ownership.Accounted.decOne` | `Ownership/CompleteAccounting.lean` | Proof sketch. | the accounting lemma; `Ownership.Supported.decOne` is the constructor of the same name |
| `decTwo_rejected` | declaration | `Ownership.decTwo_rejected` | `Ownership/CompleteAccounting.lean` | Proof sketch. | — |
| `dupSupport_witness` | declaration | `Ownership.dupSupport_witness` | `Ownership/CompleteAccounting.lean` | Complete ownership accounting; A worked instance | — |
| `e` | expression | `Ownership.Nested.NCode.takeOut` | `Ownership/Nested.lean` | The judgement. | program variable: the fresh reference in the `takeOut` rule; a binder, not a declaration. |
| `entryAccounted` | declaration | `OwnershipTest.CountedFamily.entryAccounted` | `OwnershipTest/CountedFamily.lean` | A worked instance | — |
| `execAST` | declaration | `OwnershipLcnf.execAST` | `OwnershipLcnf/Semantics.lean` | Two languages, one accounted subset | — |
| `execAST_recognized` | declaration | `OwnershipLcnf.execAST_recognized` | `OwnershipLcnf/Semantics.lean` | Recognition, and the flat guarantee | — |
| `execCountedAST` | declaration | `OwnershipLcnf.execCountedAST` | `OwnershipLcnf/CountedTrace.lean` | The finite path and the counted fragment; Proof sketch. | — |
| `execCounted_full_fragment` | declaration | `OwnershipLcnf.execCounted_full_fragment` | `OwnershipLcnf/CountedTrace.lean` | Proof sketch. | — |
| `execCounted_protocol_boundary` | declaration | `OwnershipLcnf.execCounted_protocol_boundary` | `OwnershipLcnf/CountedTrace.lean` | The finite path and the counted fragment; Proof sketch. | — |
| `execNested` | declaration | `OwnershipLcnf.execNested` | `OwnershipLcnf/NestedSemantics.lean` | The finite path and the counted fragment; Proof sketch. | — |
| `execNestedAST` | declaration | `OwnershipLcnf.execNestedAST` | `OwnershipLcnf/NestedSemantics.lean` | Two languages, one accounted subset | — |
| `execSet` | declaration | `Ownership.Runner.execSet` | `Ownership/Runner.lean` | Recognition, and the flat guarantee | — |
| `family_chain` | declaration | `OwnershipTest.CountedFamily.family_chain` | `OwnershipTest/CountedFamily.lean` | A worked instance | — |
| `family_chain_two` | declaration | `OwnershipTest.CountedFamily.family_chain_two` | `OwnershipTest/CountedFamily.lean` | A worked instance | — |
| `fragment_decomp` | declaration | `OwnershipLcnf.fragment_decomp` | `OwnershipLcnf/CountedTrace.lean` | Proof sketch. | — |
| `fst` | expression | `Ownership.Nested.NCode.takeOut` | `Ownership/Nested.lean` | The judgement. | program variable: the parent binder of the take-out; a binder, not a declaration. |
| `i` | expression | `Ownership.Code.setArr` | `Ownership/Code.lean` | The judgement. | program variable: the index in the `setArr` and `takeOut` rules; a binder, not a declaration. |
| `inPlaceOutcome root i v o H` | expression | `OwnershipLcnf.inPlaceOutcome` | `OwnershipLcnf/Semantics.lean` | Recognition, and the flat guarantee | applied form of the outcome the executed prefix and the model run must both equal. |
| `inc` | declaration | `Ownership.Ctx.inc` | `Ownership/Code.lean` | The judgement. | the context update; `Ownership.Code.inc` is the constructor of the same name |
| `incPairComponents_eq` | declaration | `Ownership.CountedPair.incPairComponents_eq` | `Ownership/CountedPair.lean` | The pair and its boundary; Compatibility and the boundary argument | — |
| `indexModelTerm` | declaration | `OwnershipLcnf.indexModelTerm` | `OwnershipLcnf/NestedSemantics.lean` | Two languages, one accounted subset | — |
| `index_path_simulates_model` | declaration | `OwnershipLcnf.index_path_simulates_model` | `OwnershipLcnf/PathRecursion.lean` | The finite path and the counted fragment | — |
| `initCtx` | declaration | `Ownership.Runner.initCtx` | `Ownership/Runner.lean` | Complete ownership accounting | the initializer; `Ownership.Accounted.initCtx` is a different declaration of the same name |
| `initCtx_accounted` | declaration | `Ownership.initCtx_accounted` | `Ownership/Accounting.lean` | Complete ownership accounting | — |
| `isShared x` | expression | `Ownership.LetF.isShared` | `Ownership/Code.lean` | Two languages, one accounted subset | displayed right-hand side: the `isShared` constructor of `Ownership.LetF`. |
| `lean_array_fget` | runtime-primitive | `lean_array_fget` | `docs/notes/artifacts/backend-binding.txt` | The update and its ownership traffic | Lean runtime C primitive that reads an array element into the unboxed exchange; it appears in the pinned backend artifact and has no Lean declaration in this repository. |
| `lean_array_fset` | runtime-primitive | `lean_array_fset` | `docs/notes/artifacts/backend-binding.txt` | The update and its ownership traffic | Lean runtime C primitive that writes an array element in the unboxed exchange; it appears in the pinned backend artifact and has no Lean declaration in this repository. |
| `lean_is_exclusive` | runtime-primitive | `lean_is_exclusive` | `OwnershipLcnf/RuntimeModel.lean` | Introduction; The running example and the semantic setting; The update and its ownership traffic; Evidence and artifact | Lean 4's runtime test of whether a heap object's reference count is one; a C primitive of the Lean runtime, not a declaration of this development. `OwnershipLcnf.Runtime.RHeap.isExclusive` is the model written from its documented meaning. |
| `let y (checkAlias x)` | expression | `Ownership.Code.let` | `Ownership/Code.lean` | The judgement. | displayed program fragment; its right-hand side is `Ownership.LetF.checkAlias` and the checker rule for it is `Ownership.Supported.bindAlias`. |
| `lit n` | expression | `Ownership.LetF.lit` | `Ownership/Code.lean` | Two languages, one accounted subset | displayed right-hand side: the `lit` constructor of `Ownership.LetF`. |
| `move` | declaration | `Ownership.Ctx.move` | `Ownership/Code.lean` | The judgement. | the context update the judgment paragraph lists with `setUs` and `bindOwned` |
| `mult` | declaration | `Ownership.Ctx.mult` | `Ownership/Code.lean` | Complete ownership accounting | field of `Ownership.Ctx`; `Ownership.RefCount` is a different count |
| `mult_eq` | declaration | `Ownership.Accounted.mult_eq` | `Ownership/CompleteAccounting.lean` | Complete ownership accounting | — |
| `mutate` | declaration | `Ownership.PutBack.mutate` | `Ownership/PutBack.lean` | The finite path and the counted fragment | branch constructor of `Ownership.PutBack.Disposition` |
| `no_free_components_not_exclusive` | declaration | `Ownership.CountedPair.no_free_components_not_exclusive` | `Ownership/CountedPair.lean` | The pair and its boundary; A worked instance | — |
| `nonPersistent` | declaration | `Ownership.Inv.nonPersistent` | `Ownership/Code.lean` | Complete ownership accounting | field of `Ownership.Inv` |
| `omittedOwner_witness` | declaration | `Ownership.omittedOwner_witness` | `Ownership/CompleteAccounting.lean` | Complete ownership accounting; A worked instance | — |
| `oproj[1]` | expression | — | `docs/notes/artifacts/execP.lcnf.txt` | The finite path and the counted fragment | emitted-LCNF projection syntax for a pair's second component, not a Lean name; it occurs in the captured artifact and is named in `Ownership.CountedPair`'s documentation. |
| `owned` | declaration | `Ownership.Inv.owned` | `Ownership/Code.lean` | Complete ownership accounting | field of `Ownership.Inv`; `Ownership.U.owned` is the usage tag of the same name |
| `pairPhase_refused` | declaration | `OwnershipTest.CountedNested.pairPhase_refused` | `OwnershipTest/CountedNested.lean` | The update and its ownership traffic; Compatibility and the boundary argument; A worked instance | — |
| `pair_traffic_neutral` | declaration | `Ownership.CountedPair.pair_traffic_neutral` | `Ownership/CountedPair.lean` | The pair and its boundary; Compatibility and the boundary argument | — |
| `path` | expression | `Ownership.Nested.NCode.callAt` | `Ownership/Nested.lean` | The judgement. | program variable: the path argument of the call rule; a binder, not a declaration. |
| `persistent_check` | declaration | `OwnershipTest.Runtime.persistent_check` | `OwnershipTest/RuntimeModel.lean` | A worked instance | — |
| `persistent_setAt` | declaration | `OwnershipTest.Runtime.persistent_setAt` | `OwnershipTest/RuntimeModel.lean` | A worked instance | — |
| `principal_accounted` | declaration | `OwnershipLcnf.principal_accounted` | `OwnershipLcnf/Principal.lean` | Recognition, and the flat guarantee | — |
| `principal_counted_fragment` | declaration | `OwnershipLcnf.principal_counted_fragment` | `OwnershipLcnf/Principal.lean` | Introduction; The finite path and the counted fragment; A worked instance; Scope, conclusion and disclosure | — |
| `principal_instance` | declaration | `OwnershipTest.principal_instance` | `OwnershipTest/Principal.lean` | A worked instance | — |
| `principal_supported_path` | declaration | `OwnershipLcnf.principal_supported_path` | `OwnershipLcnf/Principal.lean` | Introduction; A worked instance; Scope, conclusion and disclosure | — |
| `principal_write` | declaration | `OwnershipLcnf.principal_write` | `OwnershipLcnf/Principal.lean` | Scope, conclusion and disclosure | — |
| `projectNested` | declaration | `OwnershipLcnf.projectNested` | `OwnershipLcnf/NestedProjection.lean` | Two languages, one accounted subset; Recognition, and the flat guarantee; The finite path and the counted fragment | — |
| `projectPair` | declaration | `OwnershipLcnf.projectPair` | `OwnershipLcnf/PairProjection.lean` | Recognition, and the flat guarantee | — |
| `projectPrefix` | declaration | `OwnershipLcnf.projectPrefix` | `OwnershipLcnf/Projection.lean` | Two languages, one accounted subset; Recognition, and the flat guarantee | — |
| `projectPrefix code = some p` | expression | `OwnershipLcnf.projectPrefix` | `OwnershipLcnf/Projection.lean` | Recognition, and the flat guarantee | the recogniser's success equation, not a declaration. |
| `project_sound` | declaration | `OwnershipLcnf.project_sound` | `OwnershipLcnf/Semantics.lean` | Recognition, and the flat guarantee | — |
| `putBack_exclusive_of_wellFormed` | declaration | `Ownership.PutBack.putBack_exclusive_of_wellFormed` | `Ownership/PutBack.lean` | The pair and its boundary; The counted call and restoration | — |
| `r` | expression | `Ownership.Heap.Exclusive` | `Ownership/Heap.lean` | Complete ownership accounting | program variable: the reference `Exclusive` is stated at; a binder, not a declaration. |
| `rc_eq` | declaration | `Ownership.Inv.rc_eq` | `Ownership/Code.lean` | Complete ownership accounting | field of `Ownership.Inv` |
| `recognized_write_in_place` | declaration | `OwnershipLcnf.recognized_write_in_place` | `OwnershipLcnf/Semantics.lean` | Recognition, and the flat guarantee | — |
| `replaceVar` | declaration | `Ownership.replaceVar` | `Ownership/CompleteAccounting.lean` | Proof sketch. | — |
| `result` | expression | `Ownership.Nested.NCode.callAt` | `Ownership/Nested.lean` | The judgement. | program variable: the result binder of the call rule; a binder, not a declaration. |
| `ret` | declaration | `Ownership.Code.ret` | `Ownership/Code.lean` | The judgement. | constructor of `Ownership.Code`; the checker's `.ret` rule is `Ownership.check`'s case for it |
| `retained_parent_copies` | declaration | `OwnershipTest.retained_parent_copies` | `OwnershipTest/Principal.lean` | A worked instance | the control the worked instance reports; `Ownership.PutBack.retained_parent_copies` is the underlying lemma of the same name |
| `retained_parent_not_mutate` | declaration | `OwnershipTest.retained_parent_not_mutate` | `OwnershipTest/Principal.lean` | A worked instance | — |
| `run` | declaration | `Ownership.run` | `Ownership/Code.lean` | Two languages, one accounted subset; Proof sketch. | — |
| `run s env H = .done H' env' v ws` | expression | `Ownership.run` | `Ownership/Code.lean` | Preservation | the interpreter's completed-run equation. |
| `runN` | declaration | `Ownership.Nested.runN` | `Ownership/Nested.lean` | Two languages, one accounted subset; The counted call and restoration | — |
| `scalar` | declaration | `Ownership.Inv.scalar` | `Ownership/Code.lean` | Complete ownership accounting | field of `Ownership.Inv`; `Ownership.U.scalar` and `Ownership.Val.scalar` are different declarations of the same name |
| `set` | declaration | `Ownership.Heap.set` | `Ownership/Heap.lean` | A worked instance | the heap update; `Ownership.Env.set` and `OwnershipLcnf.Runtime.Corr.set` carry the same local name |
| `setArr` | declaration | `Ownership.Code.setArr` | `Ownership/Code.lean` | Proof sketch. | constructor of `Ownership.Code`; the paper drops its leading dot here |
| `setArr x i v` | expression | `Ownership.Code.setArr` | `Ownership/Code.lean` | The judgement. | displayed constructor pattern of the flat language. |
| `setAt` | declaration | `OwnershipLcnf.Runtime.setAt` | `OwnershipLcnf/RuntimeModel.lean` | Recognition, and the flat guarantee | the runtime model's write; the paper names it inside `Runtime.setAt_inPlace_of_entryInv` |
| `setUs` | declaration | `Ownership.Ctx.setUs` | `Ownership/Code.lean` | The judgement. | — |
| `size a` | expression | `Ownership.LetF.size` | `Ownership/Code.lean` | Two languages, one accounted subset | displayed right-hand side: the `size` constructor of `Ownership.LetF`. |
| `snd` | expression | `Ownership.Nested.NCode.takeOut` | `Ownership/Nested.lean` | The judgement. | program variable: the child binder of the take-out; a binder, not a declaration. |
| `state` | expression | `Ownership.Nested.NCode.callAt` | `Ownership/Nested.lean` | The judgement. | program variable: the state argument of the call rule; a binder, not a declaration. |
| `storeSlots_init` | declaration | `Ownership.storeSlots_init` | `Ownership/Preservation.lean` | The supported fragment; Recognition, and the flat guarantee; Scope, conclusion and disclosure | — |
| `support_nodup` | declaration | `Ownership.Accounted.support_nodup` | `Ownership/CompleteAccounting.lean` | Proof sketch. | field of `Ownership.Accounted`, not a free-standing declaration |
| `supported_check` | declaration | `Ownership.supported_check` | `Ownership/Preservation.lean` | The supported fragment | — |
| `supported_run` | declaration | `Ownership.supported_run` | `Ownership/Preservation.lean` | Three contributions.; Recognition, and the flat guarantee | — |
| `supported_store_exclusive` | declaration | `Ownership.supported_store_exclusive` | `Ownership/Preservation.lean` | Preservation | — |
| `takeOut a i fst snd e` | expression | `Ownership.Nested.NCode.takeOut` | `Ownership/Nested.lean` | The judgement. | displayed constructor pattern of the nested language. |
| `unboundRoot_witness` | declaration | `Ownership.unboundRoot_witness` | `Ownership/CompleteAccounting.lean` | Complete ownership accounting; A worked instance | — |
| `v` | expression | `Ownership.Code.setArr` | `Ownership/Code.lean` | The judgement. | program variable: the stored value in the `setArr` rule; a binder, not a declaration. |
| `x` | expression | `Ownership.Supported.bindAlias` | `Ownership/CompleteAccounting.lean` | The judgement.; Proof sketch. | program variable: the owned source handle of the alias rule, reused across the other rules of the table; a binder, not a declaration. |
| `y` | expression | `Ownership.Supported.bindAlias` | `Ownership/CompleteAccounting.lean` | The judgement. | program variable: the alias target of the alias rule; a binder, not a declaration. |
