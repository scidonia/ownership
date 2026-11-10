import Alias

/-
Known gaps in the experimental checker: each of these violates the intended
discipline, and each is currently *accepted*. They are recorded as negative
regressions for an ordered ownership-state analysis, not as passing properties.

1. the old array is read after the consuming write;
2. the condition consumes the array, and the branches then use it;
3. two binders from the same element read, each later written.
-/

-- 1
#alias_check (fun (a : Array Nat) =>
  (let b : Array Nat := a.set! 0 1
   (b, a.getD 0 0)))

-- 2
#alias_check (fun (a : Array Nat) =>
  (if (a.set! 0 1).getD 0 0 = 1 then a else a.set! 1 2))

-- 3
#alias_check (fun (outer : Array (Array Nat)) =>
  (let a : Array Nat := outer.getD 0 #[]
   let b : Array Nat := outer.getD 0 #[]
   (a.set! 0 1, b)))
