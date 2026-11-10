import Alias

-- duplication: `a` is used to build `b` and then used again
#alias_check (fun (a : Array Nat) =>
  (let b : Array Nat := a; ((a.set! 0 1).size + b.size : Nat)))
