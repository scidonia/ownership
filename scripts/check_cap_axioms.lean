/-
The axiom audit for the borrow lifecycle.

Every declaration the combined invariant relies on is printed with the axioms it
depends on, so an unproved assumption shows up as `sorryAx` or as an axiom
outside Lean's standard set (`propext`, `Classical.choice`, `Quot.sound`).
-/
import Cap.FullInv
import Cap.IProg
import Cap.Discipline
import Cap.Sealed
import Cap.Certify
import Cap.UFReuse
import Cap.UFReuseRunner
import Cap.Reconstruction
import Cap.Integrated
import Cap.UFIntegrated
import Cap.AddressMap

open Cap

/-! ### World preservation and the combined invariant -/

#print axioms World.checkWorld_fullInv
#print axioms Cap.checkWorld_wf
#print axioms Cap.checkWorld_rel
#print axioms Cap.checkWorld_top
#print axioms Cap.checkWorld_topInv
#print axioms World.checkWorld_beginBorrow
#print axioms World.checkWorld_endBorrow
#print axioms World.fullInv_beginBorrowChecked
#print axioms World.fullInv_endBorrowChecked
#print axioms World.fullInv_commandInv
#print axioms World.commandInv_iff
#print axioms World.uWorld_borrowOK
#print axioms World.emptyWorld_fullInv

/-! ### Delegation preservation -/

#print axioms World.delegationChains_ok
#print axioms World.borrowOK_beginBorrow
#print axioms World.borrowOK_endBorrow
#print axioms World.borrowOK_loansReady
#print axioms World.freeChecked_wf

/-! ### The nested delegation chain -/

#print axioms Delegation.Chain.holder_begin
#print axioms Delegation.Chain.holder_end
#print axioms Delegation.Chain.beginCheck_sound
#print axioms Delegation.Chain.holder_not_lender
#print axioms Delegation.Chain.begin_OK
#print axioms Delegation.Chain.begin?_OK
#print axioms Delegation.Chain.end_OK
#print axioms Delegation.Chain.end?_OK
#print axioms Delegation.Chain.delegate_conserved
#print axioms Delegation.Chain.retract_restores

/-! ### The discipline carrier -/

#print axioms Discipline.initialState_OK
#print axioms Discipline.State.write_OK
#print axioms Discipline.State.beginBorrow_OK
#print axioms Discipline.State.endBorrow_OK

/-! ### Indexed programs -/

#print axioms Cap.evalIProg_post
#print axioms Cap.runIProg_no_refusal

/-! ### The delegation lifecycles -/

#print axioms Cap.iDelegationLifecycle_ok
#print axioms Cap.iDelegationLifecycle_ctx
#print axioms Cap.iDelegationLifecycle_owner
#print axioms Cap.iDelegationLifecycle_returned
#print axioms Cap.iDelegationLifecycle_snapshot
#print axioms Cap.iClosedDelegation_ok
#print axioms Cap.iClosedDelegation_ctx
#print axioms Cap.iClosedDelegation_closed
#print axioms Cap.iClosedDelegation_owner
#print axioms Cap.iClosedDelegation_snapshot

/-! ### The closed delegation certificates -/

#print axioms Cap.closedDelegation_ok
#print axioms Cap.closedDelegation_snapshot
#print axioms Cap.closedDelegation_wf
#print axioms Cap.closedDelegation_fullInv
#print axioms Cap.closedDelegationProg_snapshot

/-! ### The reusable two-find union-find client -/

#print axioms Cap.reuseStart_ranked
#print axioms Cap.reuseFirst_eq
#print axioms Cap.reuseFirst_ranked
#print axioms Cap.reuseFirst_accepts_second
#print axioms Cap.reuseFirst_same_iff
#print axioms Cap.reuseSecond_eq
#print axioms Cap.reuseSecond_ranked
#print axioms Cap.reuseSecond_same_iff
#print axioms Cap.reuseTwoFinds_eq
#print axioms Cap.reuseTwoFinds_same_iff

/-! ### The state-threaded reusable union-find runner -/

#print axioms Cap.replay_append
#print axioms Cap.compressAll_length
#print axioms Cap.findRootF_rank_le
#print axioms Cap.rootPath_rank_lt
#print axioms Cap.ranked_compress
#print axioms Cap.ranked_compressAll
#print axioms Cap.compressAll_chase_ranked
#print axioms Cap.compressAll_chase_same_iff
#print axioms Cap.PathRunner.find_ranked
#print axioms Cap.PathRunner.find_same_iff
#print axioms Cap.reuseRunnerFirst_root
#print axioms Cap.reuseRunnerFirst_parent
#print axioms Cap.reuseRunnerFirst_parent_eq
#print axioms Cap.reuseRunnerFirst_trace
#print axioms Cap.reuseRunnerSecond_root
#print axioms Cap.reuseRunnerSecond_parent
#print axioms Cap.reuseRunnerSecond_parent_eq
#print axioms Cap.reuseRunnerSecond_trace
#print axioms Cap.reuseRunnerFreshFour_parent
#print axioms Cap.reuseRunnerFreshFour_trace
#print axioms Cap.reuseRunnerSecond_consumes
#print axioms Cap.reuseRunnerSecond_same_iff
#print axioms Cap.reuseRunnerSecond_acyclic

/-! ### Borrowed subdivision and reconstruction obligations -/

#print axioms Cap.Reconstruction.Forest.budget_eq_toTree
#print axioms Cap.Reconstruction.Forest.spatial_split_budget
#print axioms Cap.Reconstruction.Forest.fractional_split_budget
#print axioms Cap.Reconstruction.Forest.spatial_join_budget
#print axioms Cap.Reconstruction.Forest.fractional_join_budget
#print axioms Cap.Reconstruction.Forest.budget_modifyLeafAt
#print axioms Cap.Reconstruction.Forest.valid_modifyLeafAt
#print axioms Cap.Reconstruction.Forest.splitSpatialAt_budget
#print axioms Cap.Reconstruction.Forest.splitSpatialAt_valid
#print axioms Cap.Reconstruction.Forest.splitFractionAt_budget
#print axioms Cap.Reconstruction.Forest.splitFractionAt_valid
#print axioms Cap.Reconstruction.Forest.reconstructHere_budget
#print axioms Cap.Reconstruction.Forest.reconstructHere_valid
#print axioms Cap.Reconstruction.Forest.reconstructAt_budget
#print axioms Cap.Reconstruction.Forest.reconstructAt_valid
#print axioms Cap.Reconstruction.Forest.retagLeaf_budget
#print axioms Cap.Reconstruction.Forest.retagLeaf_valid
#print axioms Cap.Reconstruction.State.initial_inv
#print axioms Cap.Reconstruction.State.splitSpatial_inv
#print axioms Cap.Reconstruction.State.splitFraction_inv
#print axioms Cap.Reconstruction.State.splitSpatial_frames_restores
#print axioms Cap.Reconstruction.State.splitFraction_frames_restores
#print axioms Cap.Reconstruction.State.reconstruct_inv
#print axioms Cap.Reconstruction.State.borrow_inv
#print axioms Cap.Reconstruction.State.return_inv
#print axioms Cap.Reconstruction.State.return_none_of_no_leaf
#print axioms Cap.Reconstruction.State.splitSpatial_none_of_issued
#print axioms Cap.Reconstruction.State.splitFraction_none_of_retired
#print axioms Cap.Reconstruction.State.write_inv
#print axioms Cap.Reconstruction.State.Storage.of_heap
#print axioms Cap.Reconstruction.State.initial_storage
#print axioms Cap.Reconstruction.State.write_storage
#print axioms Cap.Reconstruction.State.borrow_storage
#print axioms Cap.Reconstruction.State.splitSpatial_storage
#print axioms Cap.Reconstruction.State.splitFraction_storage
#print axioms Cap.Reconstruction.State.reconstruct_storage
#print axioms Cap.Reconstruction.State.return_storage
#print axioms Cap.Reconstruction.Forest.ids_mem_nodes_or_ruleIds
#print axioms Cap.Reconstruction.Forest.splitSpatialAt_children_ne
#print axioms Cap.Reconstruction.Forest.splitFractionAt_children_ne
#print axioms Cap.Reconstruction.Forest.retagLeaf_nodes_cases
#print axioms Cap.Reconstruction.Forest.retagLeaf_nodes_old_mem
#print axioms Cap.Reconstruction.Forest.findLeaf?_mem_leaves
#print axioms Cap.Reconstruction.Forest.eq_of_mem_of_map_nodup
#print axioms Cap.Reconstruction.State.Accounts.dormant_not_current
#print axioms Cap.Reconstruction.State.Accounts.retired_not_current
#print axioms Cap.Reconstruction.State.Accounts.cons_restore_not_accounts
#print axioms Cap.Reconstruction.Forest.split_budget_of_children
#print axioms Cap.Reconstruction.Forest.suspended_frontier_realizes
#print axioms Cap.Reconstruction.Restore.SameResource.trans
#print axioms Cap.Reconstruction.State.Accounts.restoreReaches_idx_lt
#print axioms Cap.Reconstruction.State.Accounts.dependency_wellFounded
#print axioms Cap.Reconstruction.State.Accounts.restoreReaches_sameResource
#print axioms Cap.Reconstruction.State.Accounts.restore_reaches_terminal
#print axioms Cap.Reconstruction.State.Accounts.restore_terminal_agrees
#print axioms Cap.Reconstruction.World.splitAtChecked_refuses_with_loan

/-! ### The sealed integrated boundary -/

#print axioms Cap.Sealed.invariant
#print axioms Cap.Sealed.run
#print axioms Cap.Integrated.Sealed.run_invariant
#print axioms Cap.Integrated.lifecycle64_snapshot_of_ok

/-! ### The integrated multi-allocation semantics -/

#print axioms Cap.Integrated.wholeActiveB_iff
#print axioms Cap.Integrated.State.initial_inv
#print axioms Cap.Integrated.updateState_alloc_mem
#print axioms Cap.Integrated.updateState_inv
#print axioms Cap.Integrated.State.update_inv
#print axioms Cap.Integrated.State.alloc_inv
#print axioms Cap.Integrated.State.free_inv
#print axioms Cap.Integrated.State.free_histories_intact
#print axioms Cap.Integrated.State.alloc_refuses_issued_allocation
#print axioms Cap.Integrated.State.alloc_refuses_issued_capability
#print axioms Cap.Integrated.State.alloc_fresh_some
#print axioms Cap.Integrated.State.reallocate_after_free_refused
#print axioms Cap.Integrated.State.realloc_initial64_refused
#print axioms Cap.Integrated.State.alloc_fresh_after_free_some
#print axioms Cap.Integrated.State.alloc_reusing_old_capability_refused
#print axioms Cap.Integrated.State.free_guard
#print axioms Cap.Integrated.State.exec_inv
#print axioms Cap.Integrated.State.run_inv
#print axioms Cap.Integrated.State.exec_frames_other
#print axioms Cap.Integrated.State.checkRun_sound
#print axioms Cap.Integrated.Prog.never_refuses
#print axioms Cap.Integrated.Prog.finish_inv
#print axioms Cap.Integrated.Sealed.invariant
#print axioms Cap.Integrated.Sealed.run
#print axioms Cap.Integrated.Sealed.run_invariant
#print axioms Cap.Integrated.lifecycle64_ok
#print axioms Cap.Integrated.lifecycle64_snapshot
#print axioms Cap.Integrated.lifecycle64_authority
#print axioms Cap.Integrated.lifecycle64_retired
#print axioms Cap.Integrated.lifecycle64_restores
#print axioms Cap.Integrated.reuse64_ok
#print axioms Cap.Integrated.reuse64_snapshot
#print axioms Cap.Integrated.reuse64_authority
#print axioms Cap.Integrated.reuse64_retired
#print axioms Cap.Integrated.lifecycleThenAlloc_ok
#print axioms Cap.Integrated.lifecycleThenAlloc_snapshot
#print axioms Cap.Integrated.lifecycleThenAlloc_authority
#print axioms Cap.Integrated.lifecycle64Prog_no_refusal
#print axioms Cap.Integrated.lifecycle64Prog_finish_inv

/-! ### The general sealed union-find -/

#print axioms Cap.state_read?_snapshot
#print axioms Cap.heap_write_lookup
#print axioms Cap.heap_write_lookup_ne
#print axioms Cap.heap_lookupList?_updateList_ne
#print axioms Cap.Reconstruction.Forest.findLeaf?_leaf
#print axioms Cap.Reconstruction.State.write_component
#print axioms Cap.Integrated.findState?_updateState_self
#print axioms Cap.Integrated.findState?_updateState_some
#print axioms Cap.Integrated.updateState_none_of_find_none
#print axioms Cap.Integrated.updateState_exists
#print axioms Cap.Integrated.updateState_allocIds
#print axioms Cap.Integrated.State.update_find_self
#print axioms Cap.Integrated.Sealed.write_exists_of_exec
#print axioms Cap.sealed_write_component
#print axioms Cap.sealed_write_snapshot_self
#print axioms Cap.WriteFrame.refl
#print axioms Cap.WriteFrame.trans
#print axioms Cap.WriteFrame.snapshot_other
#print axioms Cap.WriteFrame.component_other
#print axioms Cap.WriteFrame.storage_other
#print axioms Cap.sealed_write_frames
#print axioms Cap.WriteFrame.rel_write
#print axioms Cap.UFGeneric.Rep.fits
#print axioms Cap.UFGeneric.eq_map_ofNat_of_map_toNat
#print axioms Cap.UFGeneric.Rep.snapshot_eq
#print axioms Cap.UFGeneric.Rep.read
#print axioms Cap.UFGeneric.chase?_eq_of_stops
#print axioms Cap.UFGeneric.chase?_some_spec
#print axioms Cap.UFGeneric.chase?_none_iff
#print axioms Cap.UFGeneric.chase?_eq_ranked
#print axioms Cap.UFGeneric.Writable.component
#print axioms Cap.UFGeneric.Writable.write_exists
#print axioms Cap.UFGeneric.Writable.write_preserved
#print axioms Cap.UFGeneric.Writable.frames
#print axioms Cap.UFGeneric.decode_set
#print axioms Cap.UFGeneric.compressPath_spec
#print axioms Cap.UFGeneric.sealedFind_some
#print axioms Cap.UFGeneric.sealedFind_ok_stops
#print axioms Cap.UFGeneric.sealedFind_error_of_no_stops
#print axioms Cap.UFGeneric.sealedFind_spec
#print axioms Cap.UFGeneric.findRanked_eq
#print axioms Cap.UFGeneric.findRanked_spec
#print axioms Cap.UFGeneric.findRanked_twice

/-! ### The two-call union-find instance -/

#print axioms Cap.UFIntegrated.setup_ok
#print axioms Cap.UFIntegrated.ufStart_snapshot
#print axioms Cap.UFIntegrated.ufStart_rep
#print axioms Cap.UFIntegrated.ufStart_ranked
#print axioms Cap.UFIntegrated.ufStart_writable
#print axioms Cap.UFIntegrated.ufStart_precondition
#print axioms Cap.UFIntegrated.ufFirst_chase
#print axioms Cap.UFIntegrated.ufFirst_spec
#print axioms Cap.UFIntegrated.ufFirst_general
#print axioms Cap.UFIntegrated.ufFirst_root
#print axioms Cap.UFIntegrated.ufFirst_snapshot
#print axioms Cap.UFIntegrated.ufFirst_rep
#print axioms Cap.UFIntegrated.ufFirst_precondition
#print axioms Cap.UFIntegrated.ufFirst_frame
#print axioms Cap.UFIntegrated.ufFirst_root_spec
#print axioms Cap.UFIntegrated.ufFirst_matches_runner
#print axioms Cap.UFIntegrated.ufFirstState_snapshot
#print axioms Cap.UFIntegrated.ufSecond_chase
#print axioms Cap.UFIntegrated.ufSecond_general
#print axioms Cap.UFIntegrated.ufSecond_run
#print axioms Cap.UFIntegrated.ufSecond_root
#print axioms Cap.UFIntegrated.ufSecond_snapshot
#print axioms Cap.UFIntegrated.ufSecond_root_spec
#print axioms Cap.UFIntegrated.ufSecond_rep
#print axioms Cap.UFIntegrated.ufSecond_matches_runner
#print axioms Cap.UFIntegrated.ufSecond_invariant
#print axioms Cap.UFIntegrated.ufFreshFour_snapshot_option
#print axioms Cap.UFIntegrated.ufSecond_consumes
#print axioms Cap.UFIntegrated.ufSecondOther_frames
#print axioms Cap.UFIntegrated.ufSecondOther_authority
#print axioms Cap.UFIntegrated.ufSecondOther_retired
#print axioms Cap.UFIntegrated.ufSecondOther_restores
#print axioms Cap.UFIntegrated.ufSecondOwnershipFrames_of_ok
#print axioms Cap.UFIntegrated.ufSecondOther_invariant
#print axioms Cap.UFIntegrated.ufStartWithOther_snapshot0
#print axioms Cap.UFIntegrated.ufStartWithOther_snapshot1
#print axioms Cap.UFIntegrated.selfWrite_snapshot_option
#print axioms Cap.UFIntegrated.selfWrite_frames

/-! ### The finite address map -/

#print axioms Cap.AddressMap.Map.alloc_wellFormed
#print axioms Cap.AddressMap.Map.free_wellFormed
#print axioms Cap.AddressMap.Map.addr?_lt
#print axioms Cap.AddressMap.Rel.alloc
#print axioms Cap.AddressMap.Rel.free
#print axioms Cap.AddressMap.Rel.write
#print axioms Cap.AddressMap.twoAlloc_rel
#print axioms Cap.AddressMap.example_write_other
#print axioms Cap.AddressMap.example_window_addr
#print axioms Cap.AddressMap.Map.alloc_refuses_overlap
#print axioms Cap.AddressMap.Map.alloc_refuses_unbounded
#print axioms Cap.AddressMap.overlapping_alloc_refused
#print axioms Cap.AddressMap.missing_window_addr_none
#print axioms Cap.AddressMap.out_of_window_addr_none
