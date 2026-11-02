import Ownership.Soundness
import Ownership.Entry
import Ownership.CountedPair
import Ownership.PutBack
import Ownership.Accounting
import OwnershipLcnf.Semantics
import OwnershipLcnf.PathRecursion
import OwnershipLcnf.RuntimeModel
import OwnershipLcnf.NoAbort
import OwnershipLcnf.Principal
import Ownership.CompleteAccounting

#print axioms Ownership.check_sound
#print axioms Ownership.Entry.checkN_sound_of_entryInv
#print axioms OwnershipLcnf.project_sound
#print axioms OwnershipLcnf.recognized_write_in_place
#print axioms OwnershipLcnf.index_path_simulates_model
#print axioms Ownership.CountedPair.pair_accounting
#print axioms Ownership.PutBack.putBack_exclusive_of_wellFormed
#print axioms OwnershipLcnf.Runtime.checkExclusive_no_abort
#print axioms OwnershipLcnf.Runtime.setAt_inPlace_of_entryInv
#print axioms OwnershipLcnf.prefix_abort_impossible
#print axioms OwnershipLcnf.principal_write
#print axioms Ownership.initCtx_accounted
#print axioms Ownership.alias_not_accounted
#print axioms Ownership.Nested.checkN_extraction_exclusive
#print axioms Ownership.Entry.checkN_extraction_exclusive_of_entryInv
#print axioms Ownership.RefCount
#print axioms Ownership.EdgeAt
#print axioms Ownership.IncomingCount_eq_edges
#print axioms Ownership.sum_range_congr
#print axioms Ownership.sum_range_update
#print axioms Ownership.sum_range_split
#print axioms Ownership.filter_set_length_eq
#print axioms Ownership.filter_set_length_remove
#print axioms Ownership.filter_set_length_add
#print axioms Ownership.RefCount_set_scalar_scalar
#print axioms Ownership.RefCount_set_ref_scalar_of_eq
#print axioms Ownership.RefCount_set_ref_scalar_of_ne
#print axioms Ownership.RefCount_set_scalar_ref_of_eq
#print axioms Ownership.RefCount_set_scalar_ref_of_ne
#print axioms Ownership.RefCount_setIfInBounds_ref_scalar_of_eq
#print axioms Ownership.RefCount_setIfInBounds_ref_scalar_of_ne
#print axioms Ownership.IncomingCount_set
#print axioms Ownership.IncomingCount_inc
#print axioms Ownership.IncomingCount_dec
#print axioms Ownership.IncomingCount_set_scalar_of_scalar
#print axioms Ownership.IncomingCount_set_of_ref
#print axioms Ownership.IncomingCount_set_of_ref_ne
#print axioms Ownership.IncomingCount_set_fill
#print axioms Ownership.IncomingCount_set_fill_ne
#print axioms Ownership.Heap_set_next
#print axioms Ownership.Heap_inc_next
#print axioms Ownership.Heap_dec_next
#print axioms Ownership.replaceVar
#print axioms Ownership.replaceVar_length
#print axioms Ownership.replaceVar_mem
#print axioms Ownership.replaceVar_cons
#print axioms Ownership.replaceVar_nodup
#print axioms Ownership.filter_erase_length_eq
#print axioms Ownership.filter_erase_length_add
#print axioms Ownership.EnvOwnerCount_setUs
#print axioms Ownership.EnvOwnerCount_move
#print axioms Ownership.EnvOwnerCount_erase
#print axioms Ownership.EnvOwnerCount_bindOwned
#print axioms Ownership.EnvOwnerCount_dec
#print axioms Ownership.nodup_filter
#print axioms Ownership.two_le_length_of_nodup_mem
#print axioms Ownership.length_eq_of_nodup_mem_iff
#print axioms Ownership.Accounted
#print axioms Ownership.Accounted.mult_eq
#print axioms Ownership.Accounted.count_one_dichotomy
#print axioms Ownership.Accounted.at_most_one_owner
#print axioms Ownership.Accounted.incoming_le_one
#print axioms Ownership.Accounted.ownersAccounted
#print axioms Ownership.Accounted.countFidelity
#print axioms Ownership.Accounted.noOwnerOfSingleEdge
#print axioms Ownership.Accounted.RefCount_initFields
#print axioms Ownership.Accounted.IncomingCount_initHeap
#print axioms Ownership.Accounted.EnvOwnerCount_initCtx
#print axioms Ownership.Accounted.initCtx
#print axioms Ownership.Accounted.setDead
#print axioms Ownership.Accounted.setScalar
#print axioms Ownership.Accounted.move
#print axioms Ownership.Accounted.decOne
#print axioms Ownership.Accounted.setFieldsScalar
#print axioms Ownership.Accounted.setArrInPlace
#print axioms Ownership.Accounted.takeOut
#print axioms Ownership.Accounted.putBack
#print axioms Ownership.EnvOwnerCount_eq_of_sound_complete
#print axioms Ownership.nodup_length_le_one
#print axioms Ownership.aliasHeap
#print axioms Ownership.aliasEnv
#print axioms Ownership.aliasCtx
#print axioms Ownership.alias_rejected
#print axioms Ownership.inc_rejected
#print axioms Ownership.decTwo_rejected
#print axioms Ownership.outOfRangeHeap
#print axioms Ownership.inRangeHeap
#print axioms Ownership.witnessEnv
#print axioms Ownership.witnessCtx
#print axioms Ownership.inv_witness
#print axioms Ownership.inv_outOfRange
#print axioms Ownership.outOfRange_rejected
#print axioms Ownership.outOfRange_accepted
#print axioms Ownership.dupSupport_witness
#print axioms Ownership.omittedOwner_witness
#print axioms Ownership.unboundRoot_witness
#print axioms Ownership.bindAloneHeap
#print axioms Ownership.bindAloneEnv
#print axioms Ownership.bindAloneCtx
#print axioms Ownership.bindAlone_rejected
#print axioms Ownership.scalarOverwrite_rejected
#print axioms Ownership.Supported
#print axioms OwnershipLcnf.Prefix.toModel_supported
#print axioms OwnershipLcnf.principal_accounted
