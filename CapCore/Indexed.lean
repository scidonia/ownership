import CapCore.Program

namespace CapCore

/-- An indexed, proof-carrying command: the constructor's premise is exactly the
acceptance condition of the corresponding Boolean checker. -/
inductive Step : Ctx → Cmd → Ctx → Prop
  | read {c : Ctx} {id : Nat} (h : c.readAllowed id = true) :
      Step c (.read id) c
  | write {c : Ctx} {id off : Nat} (h : c.writeAllowed id off = true) :
      Step c (.write id off) c
  | splitSpatial {c c' : Ctx} {id c1 c2 mid : Nat}
      (h : c.splitSpatial? id c1 c2 mid = some c') :
      Step c (.splitSpatial id c1 c2 mid) c'
  | splitFraction {c c' : Ctx} {id c1 c2 q1 q2 : Nat}
      (h1 : 0 < q1) (h2 : 0 < q2)
      (h : c.splitFraction? id c1 c2 q1 q2 h1 h2 = some c') :
      Step c (.splitFraction id c1 c2 q1 q2 h1 h2) c'
  | reconstruct {c c' : Ctx} {id1 id2 newId : Nat}
      (h : c.reconstruct? id1 id2 newId = some c') :
      Step c (.reconstruct id1 id2 newId) c'
  | borrow {c c' : Ctx} {lender borrower : Nat}
      (h : c.borrow? lender borrower = some c') :
      Step c (.borrow lender borrower) c'
  | restore {c c' : Ctx} {borrower lender : Nat}
      (h : c.return? borrower lender = some c') :
      Step c (.restore borrower lender) c'
  | free {c c' : Ctx} {id : Nat}
      (h : c.free? id = some c') :
      Step c (.free id) c'

theorem Step.sound {c c' : Ctx} {cmd : Cmd} (h : Step c cmd c') :
    step c cmd = some c' := by
  cases h <;> simp [step, *]

/-- A proof-carrying accepted sequence, indexed by its command list. -/
inductive Program : Ctx → List Cmd → Ctx → Prop
  | nil (c : Ctx) : Program c [] c
  | cons {c c' c'' : Ctx} {cmd : Cmd} {rest : List Cmd}
      (h : Step c cmd c') (p : Program c' rest c'') :
      Program c (cmd :: rest) c''

theorem Program.run_some {c c' : Ctx} {cmds : List Cmd}
    (p : Program c cmds c') : run c cmds = some c' := by
  induction p with
  | nil c => rfl
  | cons h p ih => simp [run, Step.sound h, ih]

end CapCore
