/-
The axiom footprint of the bridge, printed for the build log.  The same
footprints are pinned in `LlvmBridge/Store8.lean` and
`LlvmBridge/Ownership.lean` with `#guard_msgs`, so a change to any of them fails
the build rather than this audit.
-/
import LlvmBridge.Store8
import LlvmBridge.Ownership
import LlvmBridge.MultiAlloc

#print axioms LlvmBridge.runFuel_store8IR_succ
#print axioms LlvmBridge.Beh_store8IR_iff
#print axioms LlvmBridge.store8IR_refines_model
#print axioms LlvmBridge.store8IR_completes
#print axioms LlvmBridge.store8IR_frame
#print axioms LlvmBridge.store8Model_replay_read
#print axioms LlvmBridge.Beh_store8Ref_iff
#print axioms LlvmBridge.store8IR_refines_store8Ref
#print axioms LlvmBridge.store8_exec_write_comp
#print axioms LlvmBridge.sealed_store8_write_comp
#print axioms LlvmBridge.write_authority
#print axioms LlvmBridge.component_write_parts
#print axioms LlvmBridge.exec_write_parts
#print axioms LlvmBridge.runFuel_store8_at_mem
#print axioms LlvmBridge.store8IR_refines_model_at_mem
#print axioms LlvmBridge.MemRepMap.write
#print axioms LlvmBridge.MemRepMap.write_len
#print axioms LlvmBridge.sealed_store8_write_comp_map
#print axioms LlvmBridge.memRepMap_twoAlloc
#print axioms LlvmBridge.example_write_model
#print axioms LlvmBridge.example_out_of_window_refused
#print axioms LlvmBridge.overlapping_window_refused
