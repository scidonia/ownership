import CapCore.Context

namespace CapCore

/-- Checked commands over one allocation context. -/
inductive Cmd where
  | read (id : Nat)
  | write (id off : Nat)
  | splitSpatial (id c1 c2 mid : Nat)
  | splitFraction (id c1 c2 q1 q2 : Nat) (h1 : 0 < q1) (h2 : 0 < q2)
  | borrow (lender borrower : Nat)
  | restore (borrower lender : Nat)
  | free (id : Nat)

/-- Execute one command, returning `none` when the current context refuses it. -/
def step (c : Ctx) : Cmd → Option Ctx
  | .read id =>
      if c.readAllowed id then some c else none
  | .write id off =>
      if c.writeAllowed id off then some c else none
  | .splitSpatial id c1 c2 mid =>
      c.splitSpatial? id c1 c2 mid
  | .splitFraction id c1 c2 q1 q2 h1 h2 =>
      c.splitFraction? id c1 c2 q1 q2 h1 h2
  | .borrow lender borrower =>
      c.borrow? lender borrower
  | .restore borrower lender =>
      c.return? borrower lender
  | .free id =>
      c.free? id

/-- Run a command sequence from a context. -/
def run (c : Ctx) : List Cmd → Option Ctx
  | [] => some c
  | cmd :: rest =>
      match step c cmd with
      | none => none
      | some c' => run c' rest

/-- A program certificate: the checker accepted the whole sequence. -/
structure Prog where
  pre : Ctx
  cmds : List Cmd
  accepted : (run pre cmds).isSome = true

namespace Prog

def execute (p : Prog) : Option Ctx :=
  run p.pre p.cmds

theorem execute_some (p : Prog) : p.execute.isSome = true :=
  p.accepted

end Prog

end CapCore
