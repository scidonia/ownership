/-
The axiom footprint of the bridge, printed for the build log.  The same
footprints are pinned in `LlvmBridge/Store8.lean` with `#guard_msgs`, so a
change to any of them fails the build rather than this audit.
-/
import LlvmBridge.Store8

#print axioms LlvmBridge.runFuel_store8IR_succ
#print axioms LlvmBridge.Beh_store8IR_iff
#print axioms LlvmBridge.store8IR_refines_model
#print axioms LlvmBridge.store8IR_completes
#print axioms LlvmBridge.store8IR_frame
#print axioms LlvmBridge.store8Model_replay_read
#print axioms LlvmBridge.Beh_store8Ref_iff
#print axioms LlvmBridge.store8IR_refines_store8Ref
