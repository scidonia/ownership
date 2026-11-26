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
import Cap.Reconstruction
import Cap.ReconstructionSealed

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

/-! ### The sealed and closed delegation certificates -/

#print axioms Cap.sealedDelegation_ok
#print axioms Cap.sealedDelegation_snapshot
#print axioms Cap.sealedDelegation_run
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
#print axioms Cap.Reconstruction.World.splitAtChecked_refuses_with_loan

/-! ### The sealed reconstruction path -/

#print axioms Cap.Reconstruction.Sealed.invariant
#print axioms Cap.Reconstruction.Sealed.initial
#print axioms Cap.Reconstruction.Sealed.lifecycle
#print axioms Cap.Reconstruction.lifecycle_ok
#print axioms Cap.Reconstruction.lifecycle_snapshot
#print axioms Cap.Reconstruction.lifecycle_authority
#print axioms Cap.Reconstruction.lifecycle_retired
#print axioms Cap.Reconstruction.lifecycle_restores
#print axioms Cap.Reconstruction.lifecycle_snapshot_of_ok
#print axioms Cap.Reconstruction.lifecycle_authority_of_ok
#print axioms Cap.Reconstruction.lifecycle_retired_of_ok
#print axioms Cap.Reconstruction.lifecycle_restores_of_ok
#print axioms Cap.Reconstruction.lifecycle_inv_of_ok
#print axioms Cap.Reconstruction.reuse_ok
#print axioms Cap.Reconstruction.reuse_snapshot
#print axioms Cap.Reconstruction.reuse_authority
#print axioms Cap.Reconstruction.reuse_retired
#print axioms Cap.Reconstruction.reuse_snapshot_of_ok
#print axioms Cap.Reconstruction.reuse_authority_of_ok
#print axioms Cap.Reconstruction.reuse_inv_of_ok
