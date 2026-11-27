import Cap.Share

namespace CapCore

/-- A byte region in one allocation. -/
structure Region where
  alloc : Nat
  lo : Nat
  hi : Nat
  deriving DecidableEq, Repr

/-- One capability in the current context. -/
structure Cap where
  id : Nat
  region : Region
  q : Nat
  pos : 0 < q
  deriving Repr

/-- A sequential context for one allocation. `D` is the whole share. -/
structure Ctx where
  D : Nat
  len : Nat
  caps : List Cap
  deriving Repr

namespace Ctx

def find? (c : Ctx) (id : Nat) : Option Cap :=
  c.caps.find? (fun cap => cap.id = id)

def remove (c : Ctx) (id : Nat) : Ctx :=
  { c with caps := c.caps.filter (fun cap => cap.id ≠ id) }

def add (c : Ctx) (cap : Cap) : Ctx :=
  { c with caps := cap :: c.caps }

def has (c : Ctx) (id : Nat) : Bool :=
  (c.find? id).isSome

/-- Fresh allocation with one whole-share capability over `[0,len)`. -/
def new (D len root : Nat) (hD : 0 < D) : Ctx :=
  { D, len, caps := [{ id := root, region := ⟨0, 0, len⟩, q := D, pos := hD }] }

/-- A read is allowed only from a capability present in the current context. -/
def readAllowed (c : Ctx) (id : Nat) : Bool :=
  (c.find? id).isSome

/-- A write requires current-context membership, the whole share, and an offset
inside the capability's region. -/
def writeAllowed (c : Ctx) (id : Nat) (off : Nat) : Bool :=
  match c.find? id with
  | none => false
  | some cap =>
      cap.q = c.D && cap.region.lo ≤ off && off < cap.region.hi

/-- Spatially split a current capability at `mid`. The parent capability is
removed; the two children are added with the same share over disjoint ranges. -/
def splitSpatial? (c : Ctx) (id c1 c2 mid : Nat) : Option Ctx :=
  match c.find? id with
  | none => none
  | some cap =>
      if cap.region.lo < mid ∧ mid < cap.region.hi ∧
          c1 ≠ c2 ∧ c.has c1 = false ∧ c.has c2 = false then
        let left : Cap := { cap with id := c1, region := { cap.region with hi := mid } }
        let right : Cap := { cap with id := c2, region := { cap.region with lo := mid } }
        some ((c.remove id).add left |>.add right)
      else none

/-- Fractionally split a current capability using the existing share algebra. -/
def splitFraction? (c : Ctx) (id c1 c2 q1 q2 : Nat)
    (h1 : 0 < q1) (h2 : 0 < q2) : Option Ctx :=
  match c.find? id with
  | none => none
  | some cap =>
      if q1 + q2 = cap.q then
        if c1 ≠ c2 ∧ c.has c1 = false ∧ c.has c2 = false then
          let left : Cap := { cap with id := c1, q := q1, pos := h1 }
          let right : Cap := { cap with id := c2, q := q2, pos := h2 }
          some ((c.remove id).add left |>.add right)
        else none
      else none

/-- Borrow is a rename of the current holder; the lender name is no longer a
current capability. -/
def borrow? (c : Ctx) (lender borrower : Nat) : Option Ctx :=
  match c.find? lender with
  | none => none
  | some cap =>
      if borrower ≠ lender ∧ c.has borrower = false then
        some ((c.remove lender).add { cap with id := borrower })
      else none

/-- Return is the inverse rename. -/
def return? (c : Ctx) (borrower lender : Nat) : Option Ctx :=
  match c.find? borrower with
  | none => none
  | some cap =>
      if lender ≠ borrower ∧ c.has lender = false then
        some ((c.remove borrower).add { cap with id := lender })
      else none

/-- Free/remove a current capability. A later operation through its id is
rejected because the id is no longer in the context. -/
def free? (c : Ctx) (id : Nat) : Option Ctx :=
  if c.has id then some (c.remove id) else none

end Ctx

end CapCore
