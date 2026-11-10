import Alias

-- capture: the array is closed over and also used directly
#alias_check (fun (a : Array Nat) =>
  (((fun (_ : Unit) => a) ()).size + a.size : Nat))
