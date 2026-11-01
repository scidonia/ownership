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
#print axioms Ownership.alias_not_accounted
