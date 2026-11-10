import Alias

-- a retained alias: `snapshot` and the update both own the array at the write
#alias_check (fun (a : Array Nat) =>
  (let snapshot : Array Nat := a
   let b : Array Nat := a.set! 0 1
   (snapshot.size + b.size : Nat)))
