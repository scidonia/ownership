import Cap.Marshal

open Cap

/-!
Executable controls for the marshalling interface. The product encoding is the
pair `(UInt8, UInt8)`, so the bytes `[7, 99]` decode to `(7, 99)`.
-/

private def pairCode : Code := .prod .uint8 .uint8

private def pairMarshal : Marshal pairCode := ⟨codec pairCode⟩

private def alloc0 : AllocId := ⟨0⟩

private def wholeLeaf : Leaf :=
  { id := ⟨1⟩, alloc := alloc0, lo := 0, hi := 2, ordered := by decide,
    q := 64, pos := by decide, ceiling := .readWrite, state := .active }

private def wholeOwner : Owner :=
  { alloc := alloc0, len := 2, root := .leaf wholeLeaf, disposal := ⟨2⟩ }

private def wholeCtx : Ctx :=
  { owners := [wholeOwner], D := 64, nextAlloc := 1, issued := [⟨1⟩, ⟨2⟩],
    loans := .rootOnly }

private def wholeWorld : World :=
  { ctx := wholeCtx, heaps := fun x => if x = alloc0 then some (Backend.ofBytes [7, 99]) else none }

private def leftLeaf : Leaf :=
  { id := ⟨1⟩, alloc := alloc0, lo := 0, hi := 1, ordered := by decide,
    q := 64, pos := by decide, ceiling := .readWrite, state := .active }

private def rightLeaf : Leaf :=
  { id := ⟨2⟩, alloc := alloc0, lo := 1, hi := 2, ordered := by decide,
    q := 64, pos := by decide, ceiling := .readWrite, state := .active }

private def splitTree : Tree :=
  .spatial ⟨3⟩ (.leaf leftLeaf) (.leaf rightLeaf)

private def splitOwner : Owner :=
  { alloc := alloc0, len := 2, root := splitTree, disposal := ⟨4⟩ }

private def splitCtx : Ctx :=
  { owners := [splitOwner], D := 64, nextAlloc := 1,
    issued := [⟨1⟩, ⟨2⟩, ⟨3⟩, ⟨4⟩], loans := .rootOnly }

private theorem wholeCanRead (j : Nat) (hj : j < 2) :
    Ctx.CanRead wholeCtx alloc0 ⟨1⟩ j := by
  refine ⟨wholeOwner, ?_, ?_⟩
  · simp [wholeCtx, Ctx.findOwner?, wholeOwner]
  · refine ⟨wholeLeaf, ?_, rfl, by decide, ?_, ?_⟩
    · simp [wholeOwner, Tree.find?, wholeLeaf]
    · simp [wholeLeaf]
    · exact hj

/-- The whole-share capability decodes the whole product. -/
example : pairMarshal.readC wholeWorld alloc0 ⟨1⟩ (Backend.ofBytes [7, 99])
    (by simp [wholeWorld, alloc0])
    (by
      intro j _hj0 hj2
      exact wholeCanRead j (by simpa [Backend.ofBytes] using hj2)) = some (7, 99) := by
  apply Marshal.readC_rep
  simp [Marshal.Rep, pairMarshal, pairCode, Cap.codec, Cap.decodeCode,
    Cap.decodePrefix, Cap.Backend.ofBytes]

private theorem splitFindLeft : splitTree.find? ⟨1⟩ = some leftLeaf := by
  simp [splitTree, Tree.find?, leftLeaf]

/-- A left-only spatial capability cannot authorize the whole two-byte read. -/
example : ¬ Cap.Marshal.Ctx.CanReadRange splitCtx alloc0 ⟨1⟩ 0 2 := by
  intro h
  have hc := h 1 (by decide) (by decide)
  obtain ⟨o, ho, c, hread, _hactive, _hq, _hlo, hhi⟩ := hc
  simp [Ctx.findOwner?, splitCtx, splitOwner] at ho
  subst o
  have hc' : c = leftLeaf := by
    simpa [splitOwner] using (Option.some.inj (hread.symm.trans splitFindLeft))
  subst c
  exact Nat.not_lt.mpr (by decide : leftLeaf.hi ≤ 1) hhi

private theorem wholeCanWrite (j : Nat) (hj : j < 2) :
    Ctx.CanWrite wholeCtx alloc0 ⟨1⟩ j := by
  refine ⟨wholeOwner, ?_, ?_⟩
  · simp [wholeCtx, Ctx.findOwner?, wholeOwner]
  · simp [Owner.writableB, wholeOwner, Tree.find?, wholeLeaf, wholeCtx]
    omega

private def replacementWorld : World :=
  pairMarshal.writeC wholeWorld alloc0 ⟨1⟩ (8, 100) (Backend.ofBytes [7, 99]) rfl
    (by simp [wholeWorld, alloc0])
    (by
      intro j hj0 hj2
      exact wholeCanWrite j (by simpa [Backend.ofBytes] using hj2))

/-- Same-length replacement re-establishes the representation. -/
example : Marshal.Rep pairMarshal (8, 100) (Backend.ofBytes [8, 100]).buf := by
  simp [Marshal.Rep, pairMarshal, pairCode, Cap.codec, Cap.decodeCode,
    Cap.decodePrefix, Cap.Backend.ofBytes]

/-- The replacement really installs the new encoded buffer. -/
example : replacementWorld.heaps alloc0 = some (Backend.ofBytes [8, 100]) := by
  simp [replacementWorld, Marshal.writeC, wholeWorld, alloc0, pairMarshal,
    pairCode, Cap.codec, Cap.encodeCode]

/-- The write interface preserves the encoding size it requires. -/
example : (pairMarshal.codec.encode (8, 100)).length =
    (pairMarshal.codec.encode (7, 99)).length := rfl

/-- A shorter unary-natural encoding cannot satisfy a longer operation's
    same-length premise. -/
example : ((Cap.codec Code.nat).encode 0).length ≠
    ((Cap.codec Code.nat).encode 1).length := by
  simp [Cap.codec, Cap.encodeCode, Cap.encodeNat]

private def unitMarshal : Marshal .unit := ⟨codec .unit⟩

private def emptyOwner : Owner := Owner.init alloc0 0 64 (by decide) ⟨1⟩ ⟨2⟩

private def emptyCtx : Ctx :=
  { owners := [emptyOwner], D := 64, nextAlloc := 1, issued := [⟨1⟩, ⟨2⟩],
    loans := .rootOnly }

private def emptyWorld : World :=
  { ctx := emptyCtx, heaps := fun x => if x = alloc0 then some (Backend.ofBytes []) else none }

/-- Empty encoding policy: the empty range is vacuously authorized, but the read
    still consumes an existing empty backend; it does not fabricate an object. -/
example : unitMarshal.readC emptyWorld alloc0 ⟨1⟩ (Backend.ofBytes [])
    (by simp [emptyWorld, alloc0])
    (by intro j _hj0 hj1; simp [Backend.ofBytes] at hj1) = some () := by
  apply Marshal.readC_rep
  simp [Marshal.Rep, unitMarshal, Cap.codec, Cap.decodeCode, Cap.decodePrefix,
    Cap.Backend.ofBytes]
