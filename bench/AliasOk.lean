import Alias

-- one owner, transferred: `a` is consumed by the first update, `b` by the second
#alias_check (fun (a : Array Nat) =>
  (let b : Array Nat := a.set! 0 1; (b.set! 1 2 : Array Nat)))

-- a loop uses the owner once; a duplicate inside the body would still be caught
#alias_check (fun (a : Array Nat) =>
  (List.foldl (fun (acc : Array Nat) i => acc.set! i 0) a (List.range 10) : Array Nat))
