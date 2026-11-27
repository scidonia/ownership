import CapRuntime.Bytes

namespace CapRuntime

/-- Runtime commands. Handles and lengths are runtime data; no ghost proof or
forest/restoration state occurs here. -/
inductive Cmd where
  | alloc (n : Nat)
  | write (h : Handle) (v : UInt8)
  | free (h : Handle)
  deriving Repr

/-- A runtime program: runtime commands only, no certificate. -/
abbrev Program := List Cmd

/-- Execute one runtime command. -/
def exec (s : State) : Cmd → Except String State
  | .alloc n => .ok (s.alloc n).1
  | .write h v => s.write? h v
  | .free h => s.free? h

/-- Run a runtime command list, stopping at the first refusal. -/
def run (s : State) : List Cmd → Except String State
  | [] => .ok s
  | c :: cs =>
      match exec s c with
      | .ok s' => run s' cs
      | .error e => .error e

end CapRuntime
