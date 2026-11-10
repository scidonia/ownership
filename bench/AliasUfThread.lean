import Alias

/-
Union-find's threading pattern: borrow the array to read, move it into an update,
return it. With the borrow/move rule and path sensitivity this is accepted: two
borrowed reads, one move on each branch.
-/
#alias_check (fun (parent : Array Nat) (x : Nat) =>
  (let px := parent.getD x 0
   if px = x then (x, parent)
   else
     let gx := parent.getD px 0
     ((x, parent.set! x gx) : Nat × Array Nat)))
