import Cap.Share
import CapRuntime.View

namespace CapCertified

/-- A compile-time fractional token. The proof is the gate; it is erased from the
runtime `View`. -/
structure ShareToken (D q : Nat) : Type where
  wf : Cap.ShareWf D q

def ShareToken.whole {D : Nat} (h : 0 < D) : ShareToken D D :=
  ⟨⟨h, Nat.le_refl D⟩⟩

/-- Split a fractional token using the existing `Cap.Share` algebra. -/
def ShareToken.split {D q q1 q2 : Nat} (t : ShareToken D q)
    (h : Cap.Splits q q1 q2) (h1 : 0 < q1) (h2 : 0 < q2) :
    ShareToken D q1 × ShareToken D q2 :=
  (⟨⟨h1, by have hsum : q1 + q2 = q := h; have := t.wf.2; omega⟩⟩,
   ⟨⟨h2, by have hsum : q1 + q2 = q := h; have := t.wf.2; omega⟩⟩)

/-- A runtime view with a compile-time fractional token. The token is proof-only;
runtime code reads `view` only. -/
structure Owned (D q : Nat) where
  view : CapRuntime.View
  token : ShareToken D q

/-- Construct a whole-share owned view over an allocation. -/
def Owned.new (s : CapRuntime.State) (alloc len : Nat) (h : 0 < len) :
    Option (Owned len len) :=
  match s.view? alloc 0 len with
  | none => none
  | some view => some ⟨view, ShareToken.whole h⟩

/-- A write requires whole-share evidence. A half share cannot satisfy this
argument, so the rejected write is a type error at the call site. -/
def Owned.fill (s : CapRuntime.State) (o : Owned D q)
    (_hw : Cap.Writable D q) (v : UInt8) : Except String CapRuntime.State :=
  o.view.fill? s v

/-- Split the runtime view and the fractional token together. -/
def Owned.split (o : Owned D q) (mid : Nat) (h : Cap.Splits q q1 q2)
    (h1 : 0 < q1) (h2 : 0 < q2) : Option (Owned D q1 × Owned D q2) :=
  match o.view.split mid with
  | none => none
  | some (l, r) =>
      let (t1, t2) := o.token.split h h1 h2
      some (⟨l, t1⟩, ⟨r, t2⟩)

/-- Runtime erasure: only the view is exposed. -/
def Owned.erase (o : Owned D q) : CapRuntime.View := o.view

end CapCertified
