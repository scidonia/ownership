/-
The multi-owner context.

A context is a list of owners plus the budget denominator and a fresh-allocation
counter. `Realizes` requires every owner's bytes to be fully covered and the
allocation identifiers to be distinct. Allocation appends a fully covered owner at
a fresh identifier; disposal removes the owner for an allocation.

Capability-identifier freshness across owners, disposal entitlements recorded per
owner, loans and the dispatch of the owner-level transitions over the list are the
next slice; the single-owner `Cap.Session` exercises the transitions meanwhile.
-/
import Cap.Ledger

namespace Cap

structure Ctx where
  owners : List Owner
  D : Nat
  nextAlloc : Nat

def Ctx.Realizes (C : Ctx) : Prop :=
  (∀ o ∈ C.owners, o.Covered C.D) ∧ (C.owners.map (·.alloc)).Nodup

def Ctx.alloc (C : Ctx) (a : AllocId) (n : Nat) (pos : 0 < C.D) (disposal : CapId)
    (hfresh : a ∉ C.owners.map (·.alloc)) : Ctx :=
  { owners := Owner.init a n C.D pos disposal :: C.owners,
    D := C.D,
    nextAlloc := C.nextAlloc + 1 }

theorem Ctx.alloc_realizes {C : Ctx} {a : AllocId} {n : Nat} {pos : 0 < C.D}
    {disposal : CapId} {hfresh : a ∉ C.owners.map (·.alloc)}
    (hr : C.Realizes) : (C.alloc a n pos disposal hfresh).Realizes := by
  refine ⟨?_, ?_⟩
  · intro o ho
    simp [Ctx.alloc] at ho
    rcases ho with rfl | ho
    · exact Owner.init_covered a n C.D pos disposal
    · exact hr.1 o ho
  · dsimp [Ctx.alloc]
    have hmap : (Owner.init a n C.D pos disposal :: C.owners).map (·.alloc)
        = a :: C.owners.map (·.alloc) := by
      simp [Owner.init]
    rw [hmap]
    exact List.nodup_cons.mpr ⟨hfresh, hr.2⟩

def Ctx.free (C : Ctx) (a : AllocId) : Ctx :=
  { C with owners := C.owners.filter (fun o => o.alloc ≠ a) }

theorem Ctx.free_realizes {C : Ctx} {a : AllocId} (hr : C.Realizes) :
    (C.free a).Realizes := by
  refine ⟨?_, ?_⟩
  · intro o ho
    exact hr.1 o (List.mem_filter.mp ho).1
  · dsimp [Ctx.free]
    have hmap : (C.owners.filter (fun o => o.alloc ≠ a)).map (·.alloc)
        = List.filter (fun x => x ≠ a) (C.owners.map (·.alloc)) := by
      rw [List.filter_map]
      rfl
    rw [hmap]
    exact List.Nodup.sublist List.filter_sublist hr.2

end Cap
