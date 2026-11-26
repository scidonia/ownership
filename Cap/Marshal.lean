import Cap.Code
import Cap.Unified
import Cap.Borrow
import Cap.UFCertified

namespace Cap

/-- Unary length-prefixed encoding of a natural: `n` one-bytes then a zero. -/
def encodeNat (n : Nat) : List UInt8 := List.replicate n 1 ++ [0]

/-- Parse a unary natural prefix. -/
def decodeNatPrefix : List UInt8 → Option (Nat × List UInt8)
  | [] => none
  | 0 :: rest => some (0, rest)
  | 1 :: rest => (decodeNatPrefix rest).map (fun p => (p.1 + 1, p.2))
  | _ :: _ => none

theorem decodeNatPrefix_encode (n : Nat) :
    decodeNatPrefix (encodeNat n) = some (n, []) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [encodeNat, List.replicate_succ]
    change (decodeNatPrefix (List.replicate n 1 ++ [0])).map
      (fun p => (p.1 + 1, p.2)) = some (n + 1, [])
    rw [show List.replicate n 1 ++ [0] = encodeNat n from rfl, ih]
    rfl

theorem decodeNatPrefix_append (n : Nat) (rest : List UInt8) :
    decodeNatPrefix (encodeNat n ++ rest) = some (n, rest) := by
  induction n generalizing rest with
  | zero => rfl
  | succ n ih =>
    simp only [encodeNat, List.replicate_succ, List.cons_append]
    change (decodeNatPrefix (List.replicate n 1 ++ [0] ++ rest)).map
      (fun p => (p.1 + 1, p.2)) = some (n + 1, rest)
    rw [show List.replicate n 1 ++ [0] ++ rest = encodeNat n ++ rest from rfl, ih]
    rfl

mutual
/-- Encode one value of a code. -/
def encodeCode : (c : Code) → El c → List UInt8
  | .unit, () => []
  | .bool, false => [0]
  | .bool, true => [1]
  | .uint8, b => [b]
  | .nat, n => encodeNat n
  | .prod a b, (x, y) => encodeCode a x ++ encodeCode b y
  | .sum a b, Sum.inl x => 0 :: encodeCode a x
  | .sum a b, Sum.inr y => 1 :: encodeCode b y
  | .list a, xs => encodeNat xs.length ++ xs.flatMap (encodeCode a)

/-- Parse a value and leave the remaining bytes. -/
def decodePrefix : (c : Code) → List UInt8 → Option (El c × List UInt8)
  | .unit, rest => some ((), rest)
  | .bool, 0 :: rest => some (false, rest)
  | .bool, 1 :: rest => some (true, rest)
  | .bool, _ => none
  | .uint8, b :: rest => some (b, rest)
  | .uint8, [] => none
  | .nat, bs => decodeNatPrefix bs
  | .prod a b, bs =>
      match decodePrefix a bs with
      | some (x, r1) =>
          match decodePrefix b r1 with
          | some (y, r2) => some ((x, y), r2)
          | none => none
      | none => none
  | .sum a b, 0 :: rest =>
      match decodePrefix a rest with
      | some (x, r) => some (Sum.inl x, r)
      | none => none
  | .sum a b, 1 :: rest =>
      match decodePrefix b rest with
      | some (y, r) => some (Sum.inr y, r)
      | none => none
  | .sum _ _, _ => none
  | .list a, bs =>
      match decodeNatPrefix bs with
      | some (n, r1) =>
          match decodeN a n r1 with
          | some (xs, r2) => some (xs, r2)
          | none => none
      | none => none

/-- Parse exactly `n` encoded elements. -/
def decodeN (c : Code) : Nat → List UInt8 → Option (List (El c) × List UInt8)
  | 0, rest => some ([], rest)
  | n + 1, rest =>
      match decodePrefix c rest with
      | some (x, r1) =>
          match decodeN c n r1 with
          | some (xs, r2) => some (x :: xs, r2)
          | none => none
      | none => none
end

mutual
theorem decodePrefix_encode_append :
    ∀ (c : Code) (v : El c) (rest : List UInt8),
      decodePrefix c (encodeCode c v ++ rest) = some (v, rest)
  | .unit, (), rest => by
    simp [encodeCode, decodePrefix]
  | .bool, false, rest => by
    simp [encodeCode, decodePrefix]
  | .bool, true, rest => by
    simp [encodeCode, decodePrefix]
  | .uint8, b, rest => by
    simp [encodeCode, decodePrefix]
  | .nat, n, rest => by
    simp only [encodeCode, decodePrefix]
    exact decodeNatPrefix_append n rest
  | .prod a b, (x, y), rest => by
    simp only [encodeCode, List.append_assoc, decodePrefix, El]
    rw [decodePrefix_encode_append a x (encodeCode b y ++ rest)]
    simp only
    rw [decodePrefix_encode_append b y rest]
  | .sum a b, Sum.inl x, rest => by
    simp only [encodeCode]
    simp [decodePrefix]
    rw [decodePrefix_encode_append a x rest]
  | .sum a b, Sum.inr y, rest => by
    simp only [encodeCode]
    simp [decodePrefix]
    rw [decodePrefix_encode_append b y rest]
  | .list a, xs, rest => by
    simp only [encodeCode, List.append_assoc, decodePrefix, El]
    rw [decodeNatPrefix_append xs.length]
    simp only
    rw [decodeN_encode_append a xs rest]

theorem decodeN_encode_append (c : Code) :
    ∀ (xs : List (El c)) (rest : List UInt8),
      decodeN c xs.length (xs.flatMap (encodeCode c) ++ rest) = some (xs, rest)
  | [], rest => by
    simp [decodeN]
  | x :: xs, rest => by
    simp only [List.length_cons, List.flatMap_cons, List.append_assoc, decodeN]
    rw [decodePrefix_encode_append c x (xs.flatMap (encodeCode c) ++ rest)]
    simp only
    rw [decodeN_encode_append c xs rest]

end

/-- Exact decoding: the whole input must be consumed. -/
def decodeCode (c : Code) (bs : List UInt8) : Option (El c) :=
  match decodePrefix c bs with
  | some (v, []) => some v
  | _ => none

theorem decodeCode_encode (c : Code) (v : El c) :
    decodeCode c (encodeCode c v) = some v := by
  unfold decodeCode
  have h : decodePrefix c (encodeCode c v) = some (v, []) := by
    simpa using decodePrefix_encode_append c v []
  rw [h]

/-- A verified codec for one closed code. -/
structure Codec (c : Code) where
  encode : El c → List UInt8
  decode : List UInt8 → Option (El c)
  decode_encode : ∀ v, decode (encode v) = some v

/-- The canonical codec for every code. -/
def codec (c : Code) : Codec c :=
  { encode := encodeCode c
    decode := decodeCode c
    decode_encode := decodeCode_encode c }

/-- A backend initialised from a byte list. -/
def Backend.ofBytes (bytes : List UInt8) : Backend :=
  { buf := bytes, len := bytes.length, hlen := rfl }

/-- Allocate a fresh owner whose backend is the given bytes. -/
def World.allocWithChecked (w : World) (bytes : List UInt8)
    (rootId disposal : CapId) (pos : 0 < w.ctx.D) : Except String World :=
  if hf : (⟨w.ctx.nextAlloc⟩ : AllocId) ∉ w.ctx.owners.map (·.alloc) then
    if hfresh : rootId ∉ w.ctx.ids ∧ disposal ∉ w.ctx.ids ∧ rootId ≠ disposal
                ∧ rootId ∉ w.ctx.issued ∧ disposal ∉ w.ctx.issued then
      .ok { w with
            ctx := w.ctx.alloc ⟨w.ctx.nextAlloc⟩ bytes.length pos rootId disposal hf,
            heaps := fun x => if x = (⟨w.ctx.nextAlloc⟩ : AllocId) then
              some (Backend.ofBytes bytes) else w.heaps x }
    else .error "allocWith: capability identifiers are not fresh"
  else .error "allocWith: stale allocation identifier"

/-- Byte-initialised allocation succeeds when its freshness checks hold. -/
theorem World.allocWithChecked_succeeds {w : World} {bytes : List UInt8}
    {rootId disposal : CapId} {pos : 0 < w.ctx.D}
    (hf : (⟨w.ctx.nextAlloc⟩ : AllocId) ∉ w.ctx.owners.map (·.alloc))
    (hfresh : rootId ∉ w.ctx.ids ∧ disposal ∉ w.ctx.ids ∧ rootId ≠ disposal
              ∧ rootId ∉ w.ctx.issued ∧ disposal ∉ w.ctx.issued) :
    ∃ w', w.allocWithChecked bytes rootId disposal pos = .ok w' := by
  unfold World.allocWithChecked
  rw [dif_pos hf, dif_pos hfresh]
  exact ⟨_, rfl⟩

/-- A successful byte-initialised allocation preserves the world invariant. -/
theorem World.allocWithChecked_wf {w w' : World} {bytes : List UInt8}
    {rootId disposal : CapId} {pos : 0 < w.ctx.D}
    (h : w.allocWithChecked bytes rootId disposal pos = .ok w')
    (hwf : w.WellFormed) : w'.WellFormed := by
  unfold World.allocWithChecked at h
  split at h
  · rename_i hf
    split at h
    · rename_i hfresh
      cases h
      refine ⟨Ctx.alloc_wellFormed (hfresh := hf) hwf.1 hfresh.1 hfresh.2.1 hfresh.2.2.1, ?_, ?_⟩
      · apply Ctx.functional_of_nodup
        simp only [Ctx.alloc, List.map_cons, List.nodup_cons]
        exact ⟨hf, hwf.1.1.2⟩
      · intro a' o' hfind
        unfold Ctx.findOwner? Ctx.alloc at hfind
        simp only [List.find?_cons] at hfind
        by_cases hx : (Owner.init ⟨w.ctx.nextAlloc⟩ bytes.length w.ctx.D pos rootId disposal).alloc = a'
        · simp [hx] at hfind
          cases hfind
          refine ⟨Backend.ofBytes bytes, ?_, ?_⟩
          · rw [← hx]
            exact if_pos rfl
          · simp [Backend.ofBytes, Owner.init]
        · simp [hx] at hfind
          have hmem : o' ∈ w.ctx.owners := List.mem_of_find?_eq_some hfind
          have hoalloc : o'.alloc = a' := by
            have h := List.find?_some (p := fun x : Owner => decide (x.alloc = a')) hfind
            simpa using h
          have hne : a' ≠ (⟨w.ctx.nextAlloc⟩ : AllocId) := by
            intro hcontra
            rw [hcontra] at hoalloc
            have : (Owner.init ⟨w.ctx.nextAlloc⟩ bytes.length w.ctx.D pos rootId disposal).alloc = ⟨w.ctx.nextAlloc⟩ := rfl
            exact hx (this.trans hcontra.symm)
          have hfind_old : w.ctx.findOwner? a' = some o' := by
            have holdfun : w.ctx.Functional := Ctx.functional_of_nodup hwf.1.1.2
            have := Ctx.findOwner?_eq_some_of_mem_of_functional holdfun hmem
            rwa [hoalloc] at this
          obtain ⟨b, hb, hlen⟩ := hwf.2.2 a' o' hfind_old
          exact ⟨b, by simp [hne, hb], hlen⟩
    · simp at h
  · simp at h

/-- Byte-initialised allocation preserves the issuance history. -/
theorem World.historyOK_allocWithChecked {w w' : World} {bytes : List UInt8}
    {rootId disposal : CapId} {po : 0 < w.ctx.D}
    (hw : w.allocWithChecked bytes rootId disposal po = .ok w')
    (hh : Ctx.HistoryOK w.ctx) : Ctx.HistoryOK w'.ctx := by
  unfold World.allocWithChecked at hw
  split at hw
  · rename_i hf
    split at hw
    · rename_i hfresh
      simp only [Except.ok.injEq] at hw
      cases hw
      exact Ctx.historyOK_alloc (hf := hf) hh hfresh.2.2.2.1 hfresh.2.2.2.2 hfresh.2.2.1
    · simp at hw
  · simp at hw

/-- Byte-initialised allocation preserves the delegation invariant. -/
theorem World.borrowOK_allocWithChecked {w w' : World} {bytes : List UInt8}
    {rootId disposal : CapId} {po : 0 < w.ctx.D}
    (hw : w.allocWithChecked bytes rootId disposal po = .ok w')
    (h : w.BorrowOK) : w'.BorrowOK := by
  unfold World.allocWithChecked at hw
  split at hw
  · rename_i hf
    split at hw
    · rename_i hfresh
      simp only [Except.ok.injEq] at hw
      cases hw
      have hwA : w.allocChecked bytes.length rootId disposal po = .ok
          { w with
            ctx := w.ctx.alloc ⟨w.ctx.nextAlloc⟩ bytes.length po rootId disposal hf,
            heaps := fun x => if x = (⟨w.ctx.nextAlloc⟩ : AllocId) then
              some (Backend.empty bytes.length) else w.heaps x } := by
        unfold World.allocChecked
        rw [dif_pos hf, dif_pos hfresh]
      have hb := World.borrowOK_allocChecked hwA h
      simpa [World.BorrowOK, World.LoansDistinctOK, World.LoansNonAliasOK,
        World.LoansIssuedOK, World.LifetimesBoundedOK, World.LoansAllocOK,
        World.LoansDetachedOK, World.LoansBaseOK, World.LoansTerminalOK,
        World.LoansAgreeOK, World.LoansOrderOK, World.BorrowAcyclic] using hb
    · simp at hw
  · simp at hw

/-- Byte-initialised allocation preserves the combined invariant. -/
theorem World.allocWithChecked_fullInv {w w' : World} {bytes : List UInt8}
    {rootId disposal : CapId} {po : 0 < w.ctx.D}
    (hw : w.allocWithChecked bytes rootId disposal po = .ok w')
    (hinv : w.FullInv) : w'.FullInv :=
  ⟨⟨World.allocWithChecked_wf hw hinv.1.1,
    World.historyOK_allocWithChecked hw hinv.1.2⟩,
    World.borrowOK_allocWithChecked hw hinv.2⟩

/-- A marshalled representation of a closed code. -/
structure Marshal (c : Code) where
  codec : Codec c

namespace Marshal

/-- The representation relation: the buffer decodes to the ghost value. -/
def Rep {c : Code} (m : Marshal c) (v : El c) (buf : List UInt8) : Prop :=
  m.codec.decode buf = some v

/-- Allocate a buffer holding the encoding of `v`. -/
def alloc {c : Code} (m : Marshal c) (w : World) (v : El c)
    (rootId disposal : CapId) (pos : 0 < w.ctx.D) : Except String World :=
  w.allocWithChecked (m.codec.encode v) rootId disposal pos

/-- The allocated backend represents `v`. -/
theorem alloc_rep {c : Code} (m : Marshal c) {w w' : World} {v : El c}
    {rootId disposal : CapId} {pos : 0 < w.ctx.D}
    (h : m.alloc w v rootId disposal pos = .ok w') :
    ∃ b, w'.heaps ⟨w.ctx.nextAlloc⟩ = some b ∧ Rep m v b.buf := by
  unfold alloc World.allocWithChecked at h
  split at h
  · rename_i hf
    split at h
    · rename_i hfresh
      cases h
      refine ⟨Backend.ofBytes (m.codec.encode v), ?_, ?_⟩
      · simp
      · simpa [Rep, Backend.ofBytes] using m.codec.decode_encode v
    · simp at h
  · simp at h

/-- Decode the buffer at an allocation back to its ghost value. -/
def read {c : Code} (m : Marshal c) (w : World) (a : AllocId) : Option (El c) :=
  match w.heaps a with
  | some b => m.codec.decode b.buf
  | none => none

/-- A represented backend decodes to its value. -/
theorem read_rep {c : Code} (m : Marshal c) {w : World} {a : AllocId}
    {b : Backend} {v : El c} (hb : w.heaps a = some b) (hrep : Rep m v b.buf) :
    read m w a = some v := by
  unfold read
  rw [hb]
  exact hrep

/-- Read authority over every byte of a half-open range. -/
def Ctx.CanReadRange (Γ : Ctx) (a : AllocId) (id : CapId)
    (lo hi : Nat) : Prop :=
  ∀ j, lo ≤ j → j < hi → Ctx.CanRead Γ a id j

/-- Every byte of an authorized range is readable. -/
theorem Ctx.CanReadRange.at {Γ : Ctx} {a : AllocId} {id : CapId} {lo hi j : Nat}
    (h : Ctx.CanReadRange Γ a id lo hi) (hl : lo ≤ j) (hh : j < hi) :
    Ctx.CanRead Γ a id j :=
  h j hl hh

/-- A range-authorized read. The premise covers every byte the decoder may
inspect (the backend's length), rather than an arbitrary single index. -/
def readC {c : Code} (m : Marshal c) (w : World) (a : AllocId) (id : CapId)
    (b : Backend) (hb : w.heaps a = some b)
    (h : Ctx.CanReadRange w.ctx a id 0 b.buf.length) : Option (El c) :=
  read m w a

/-- A represented backend with whole-range read authority decodes to its
value. -/
theorem readC_rep {c : Code} (m : Marshal c) {w : World} {a : AllocId}
    {id : CapId} {b : Backend} {v : El c}
    (hb : w.heaps a = some b)
    (hcan : Ctx.CanReadRange w.ctx a id 0 b.buf.length)
    (hrep : Rep m v b.buf) : readC m w a id b hb hcan = some v :=
  read_rep m hb hrep

/-- Write authority over every byte of a half-open range. -/
def Ctx.CanWriteRange (Γ : Ctx) (a : AllocId) (id : CapId)
    (lo hi : Nat) : Prop :=
  ∀ j, lo ≤ j → j < hi → Ctx.CanWrite Γ a id j

/-- Replace a marshalled buffer by the encoding of `v`, provided the new
encoding has exactly the backend's length and the caller has write authority
over the whole range. -/
def writeC {c : Code} (m : Marshal c) (w : World) (a : AllocId) (id : CapId)
    (v : El c) (b : Backend) (hlen : (m.codec.encode v).length = b.buf.length)
    (hb : w.heaps a = some b)
    (hcan : Ctx.CanWriteRange w.ctx a id 0 b.buf.length) : World :=
  { w with heaps := fun x =>
      if x = a then some (Backend.ofBytes (m.codec.encode v)) else w.heaps x }

/-- The range-authorized, same-length write re-establishes the representation. -/
theorem writeC_rep {c : Code} (m : Marshal c) {w : World} {a : AllocId}
    {id : CapId} {v : El c} {b : Backend}
    (hlen : (m.codec.encode v).length = b.buf.length)
    (hb : w.heaps a = some b)
    (hcan : Ctx.CanWriteRange w.ctx a id 0 b.buf.length) :
    ∃ b', (writeC m w a id v b hlen hb hcan).heaps a = some b' ∧
      Rep m v b'.buf := by
  refine ⟨Backend.ofBytes (m.codec.encode v), ?_, ?_⟩
  · simp [writeC]
  · simpa [Rep, Backend.ofBytes] using m.codec.decode_encode v

/-- A successful marshalled allocation preserves the combined invariant. -/
theorem alloc_fullInv {c : Code} (m : Marshal c) {w w' : World} {v : El c}
    {rootId disposal : CapId} {pos : 0 < w.ctx.D}
    (h : m.alloc w v rootId disposal pos = .ok w') (hinv : w.FullInv) :
    w'.FullInv :=
  World.allocWithChecked_fullInv (by simpa [alloc] using h) hinv

/-- The range-authorized, same-length write preserves the combined invariant. -/
theorem writeC_fullInv {c : Code} (m : Marshal c) {w : World} {a : AllocId}
    {id : CapId} {v : El c} {b : Backend}
    (hlen : (m.codec.encode v).length = b.buf.length)
    (hb : w.heaps a = some b)
    (hcan : Ctx.CanWriteRange w.ctx a id 0 b.buf.length)
    (hinv : w.FullInv) : (writeC m w a id v b hlen hb hcan).FullInv := by
  let w' := writeC m w a id v b hlen hb hcan
  have hwf : w'.WellFormed := by
    refine ⟨hinv.1.1.1, hinv.1.1.2.1, ?_⟩
    intro a' o' hfind
    by_cases hx : a' = a
    · cases hx
      unfold w' writeC at hfind ⊢
      simp only [if_pos] at hfind ⊢
      have hb0 : w.heaps a = some b := hb
      have hlen0 : b.buf.length = o'.len := by
        obtain ⟨b0, hb0', hlen0⟩ := hinv.1.1.2.2 a o' hfind
        exact (Option.some.inj (hb0'.symm.trans hb0)) ▸ hlen0
      refine ⟨Backend.ofBytes (m.codec.encode v), rfl, ?_⟩
      simp [Backend.ofBytes, hlen, hlen0]
    · unfold w' writeC at hfind ⊢
      simp only [if_neg hx] at hfind ⊢
      exact hinv.1.1.2.2 a' o' hfind
  refine ⟨⟨hwf, ?_⟩, ?_⟩
  · change Ctx.HistoryOK w.ctx
    exact hinv.1.2
  · change w.BorrowOK
    exact hinv.2

/-- Checked deallocation preserves the combined invariant. -/
theorem World.freeChecked_fullInv {w w' : World} {a : AllocId} {d : CapId}
    (h : w.freeChecked a d = .ok w') (hinv : w.FullInv) : w'.FullInv := by
  apply World.checkWorld_fullInv w w' [UCmd.free a d] _ hinv
  cases hw : w.freeChecked a d with
  | error e => simp [hw] at h
  | ok w'' =>
    simp [checkWorld, hw]
    simpa [hw] using h

/-- A byte-wise write trace for a buffer encoding. -/
def writeCmds (a : AllocId) (id : CapId) (start : Nat) : List UInt8 → List UCmd
  | [] => []
  | v :: vs => UCmd.write a id start v :: writeCmds a id (start + 1) vs

/-- A byte-wise write trace whose indices stay inside an authorized range is
accepted by the checker. -/
theorem checkWorld_writeCmds_ok {w : World} {a : AllocId} {id : CapId}
    {start n : Nat} {bytes : List UInt8}
    (hle : start + bytes.length ≤ n)
    (hcan : Ctx.CanWriteRange w.ctx a id 0 n)
    (hwf : w.WellFormed) :
    (checkWorld w (writeCmds a id start bytes)).isOk = true := by
  induction bytes generalizing start w with
  | nil => rfl
  | cons v vs ih =>
    have hle' : start + (vs.length + 1) ≤ n := by
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hle
    have hstart : start < n := by omega
    have hc : Ctx.CanWrite w.ctx a id start := hcan start (Nat.zero_le _) hstart
    obtain ⟨w', hw'⟩ := World.write_succeeds (w := w) hc rfl hwf
    have hwf' : w'.WellFormed := World.writeChecked_wf hw' hwf
    obtain ⟨o, b, b', hfind, hguard, hb, hbw, hctx', hheaps⟩ :=
      World.writeChecked_sound hw'
    rw [writeCmds, checkWorld, hw']
    apply ih (w := w') (start := start + 1) (by omega)
      (by simpa [hctx'] using hcan) hwf'

/-- The range-authorized, same-length write is accepted by a checker trace. -/
theorem writeC_trace_ok {c : Code} (m : Marshal c) {w : World} {a : AllocId}
    {id : CapId} {v : El c} {b : Backend}
    (hlen : (m.codec.encode v).length = b.buf.length)
    (hb : w.heaps a = some b)
    (hcan : Ctx.CanWriteRange w.ctx a id 0 b.buf.length)
    (hinv : w.FullInv) :
    (checkWorld w (writeCmds a id 0 (m.codec.encode v))).isOk = true :=
  checkWorld_writeCmds_ok (n := b.buf.length) (by omega) hcan hinv.1.1

/-- Deallocate a marshalled buffer through the checked disposal route. -/
def free (w : World) (a : AllocId) (d : CapId) : Except String World :=
  w.freeChecked a d

/-- A successful marshalled deallocation preserves the world invariant. -/
theorem free_wf {w w' : World} {a : AllocId} {d : CapId}
    (h : free w a d = .ok w') (hwf : w.WellFormed) : w'.WellFormed :=
  World.freeChecked_wf h hwf

/-- A successful marshalled deallocation preserves the combined invariant. -/
theorem free_fullInv {w w' : World} {a : AllocId} {d : CapId}
    (h : free w a d = .ok w') (hinv : w.FullInv) : w'.FullInv :=
  World.freeChecked_fullInv h hinv

/-- Write a byte list from `start`, threading the backend write state. -/
def writeBackend (b : Backend) (start : Nat) : List UInt8 → Option Backend
  | [] => some b
  | v :: vs => (b.write start v).bind (fun b' => writeBackend b' (start + 1) vs)

/-- The byte-wise backend writes replace the range and preserve the prefix and suffix. -/
theorem writeBackend_buf {b : Backend} {start : Nat} {bytes : List UInt8}
    (h : start + bytes.length ≤ b.buf.length) :
    ∃ b', writeBackend b start bytes = some b' ∧
      b'.buf = b.buf.take start ++ bytes ++ b.buf.drop (start + bytes.length) := by
  induction bytes generalizing b start with
  | nil =>
    refine ⟨b, rfl, ?_⟩
    simp [List.take_append_drop]
  | cons v vs ih =>
    have hlt : start < b.buf.length := by
      have h' : start + (vs.length + 1) ≤ b.buf.length := by simpa using h
      omega
    obtain ⟨b1, hb1⟩ : ∃ b1, b.write start v = some b1 := by
      unfold Backend.write
      rw [if_pos hlt]
      exact ⟨_, rfl⟩
    have hbuf1 : b1.buf = b.buf.set start v := Backend.write_buf hb1
    have hlen1 : b1.buf.length = b.buf.length := by rw [hbuf1, List.length_set]
    have hbound1 : start + 1 + vs.length ≤ b1.buf.length := by
      rw [hlen1]
      have h' : start + vs.length + 1 ≤ b.buf.length := by
        simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using h
      omega
    obtain ⟨b2, hb2, hbuf2⟩ := ih (b := b1) (start := start + 1) hbound1
    refine ⟨b2, ?_, ?_⟩
    · simp [writeBackend, hb1, hb2]
    · rw [hbuf2]
      rw [hbuf1]
      rw [List.take_set]
      have htake : start < (b.buf.take (start + 1)).length := by
        rw [List.length_take]
        omega
      rw [List.set_eq_take_append_cons_drop]
      rw [if_pos htake]
      rw [List.drop_set_of_lt (by omega)]
      simp [List.take_take, Nat.add_assoc, List.append_assoc]
      omega



/-- The byte-wise checker trace reaches the backend `writeBackend` computes, with the
    same context and only the target allocation changed. -/
theorem checkWorld_writeCmds_eq {w : World} {a : AllocId} {id : CapId}
    {start n : Nat} {bytes : List UInt8} {b : Backend}
    (hbn : b.buf.length ≤ n)
    (hle : start + bytes.length ≤ b.buf.length)
    (hb : w.heaps a = some b)
    (hcan : Ctx.CanWriteRange w.ctx a id 0 n)
    (hwf : w.WellFormed) :
    ∃ w' b', checkWorld w (writeCmds a id start bytes) = .ok w' ∧
      w'.ctx = w.ctx ∧
      w'.heaps = (fun x => if x = a then some b' else w.heaps x) ∧
      writeBackend b start bytes = some b' := by
  induction bytes generalizing start w b with
  | nil =>
    refine ⟨w, b, rfl, rfl, ?_, rfl⟩
    funext x
    by_cases hx : x = a <;> simp [hx, hb]
  | cons v vs ih =>
    have hstart : start < n := by
      have h' : start + (vs.length + 1) ≤ n := by
        have hb' : start + (vs.length + 1) ≤ b.buf.length := by simpa using hle
        omega
      omega
    have hc : Ctx.CanWrite w.ctx a id start := hcan start (Nat.zero_le _) hstart
    obtain ⟨w1, hw1⟩ := World.write_succeeds (w := w) hc rfl hwf
    have hwf1 : w1.WellFormed := World.writeChecked_wf hw1 hwf
    obtain ⟨o, b0, b1, hfind, hguard, hb0, hbw, hctx1, hheaps1⟩ :=
      World.writeChecked_sound hw1
    have hb_eq : b = b0 := Option.some.inj (hb.symm.trans hb0)
    subst b0
    have hlen1 : b1.buf.length = b.buf.length := by
      rw [Backend.write_buf hbw]
      exact List.length_set (as := b.buf) (i := start) (a := v)
    have hle1 : start + 1 + vs.length ≤ b1.buf.length := by
      rw [hlen1]
      have h' : start + (vs.length + 1) ≤ b.buf.length := by simpa using hle
      omega
    have hheaps1a : w1.heaps a = some b1 := by
      rw [hheaps1]
      simp
    obtain ⟨w2, b2, hw2, hctx2, hheaps2, hb2⟩ :=
      ih (b := b1) (start := start + 1) (by omega) hle1 hheaps1a
        (by simpa [hctx1] using hcan) hwf1
    refine ⟨w2, b2, ?_, hctx2.trans hctx1, ?_, ?_⟩
    · unfold writeCmds checkWorld
      rw [hw1]
      exact hw2
    · rw [hheaps2, hheaps1]
      funext x
      by_cases hx : x = a <;> simp [hx]
    · simp [writeBackend, hbw, hb2]



/-- Writing a full buffer from zero yields exactly `Backend.ofBytes`. -/
theorem writeBackend_full {b : Backend} {bytes : List UInt8}
    (hlen : bytes.length = b.buf.length) :
    writeBackend b 0 bytes = some (Backend.ofBytes bytes) := by
  obtain ⟨b', hb', hbuf⟩ :=
    writeBackend_buf (b := b) (start := 0) (bytes := bytes) (by omega)
  have hbuf_eq : b'.buf = bytes := by
    rw [hbuf]
    simp [hlen]
  have hb_eq : b' = Backend.ofBytes bytes := by
    cases b' with
    | mk buf len hlen' =>
      simp only [Backend.ofBytes]
      have hbuf_eq' : buf = bytes := by simpa using hbuf_eq
      have hlen_eq : len = bytes.length := by
        rw [← hlen', hbuf_eq']
      simp [hbuf_eq', hlen_eq]
  rw [hb', hb_eq]



/-- The accepted byte-wise trace reaches exactly `writeC`. -/
theorem writeC_trace_eq {c : Code} (m : Marshal c) {w : World} {a : AllocId}
    {id : CapId} {v : El c} {b : Backend}
    (hlen : (m.codec.encode v).length = b.buf.length)
    (hb : w.heaps a = some b)
    (hcan : Ctx.CanWriteRange w.ctx a id 0 b.buf.length)
    (hinv : w.FullInv) :
    checkWorld w (writeCmds a id 0 (m.codec.encode v)) = .ok (writeC m w a id v b hlen hb hcan) := by
  have hle : 0 + (m.codec.encode v).length ≤ b.buf.length := by omega
  obtain ⟨w', b', hcheck, hctx, hheaps, hb'⟩ :=
    checkWorld_writeCmds_eq (n := b.buf.length) (Nat.le_refl b.buf.length) hle hb hcan hinv.1.1
  have hfull : writeBackend b 0 (m.codec.encode v) = some (Backend.ofBytes (m.codec.encode v)) :=
    writeBackend_full hlen
  have hb_eq : b' = Backend.ofBytes (m.codec.encode v) :=
    Option.some.inj (hb'.symm.trans hfull)
  subst b'
  have hw_eq : w' = writeC m w a id v b hlen hb hcan := by
    cases w' with
    | mk ctx heaps =>
      simp only [writeC]
      have hctx' : ctx = w.ctx := hctx
      have hheaps' : heaps = (fun x => if x = a then some (Backend.ofBytes (m.codec.encode v)) else w.heaps x) := hheaps
      simp [hctx', hheaps']
  rw [hcheck, hw_eq]

end Marshal

/-- The canonical codec round-trips a product. -/
example : (codec (.prod .nat .bool)).decode
    ((codec (.prod .nat .bool)).encode (3, true)) = some (3, true) :=
  (codec (.prod .nat .bool)).decode_encode (3, true)

/-- End-to-end marshalling on the concrete 64-byte world: allocate a
`(Nat × Bool)` buffer, and observe that its backend represents the value. -/
theorem marshal_example : ∃ w' b,
    Marshal.alloc ⟨codec (.prod .nat .bool)⟩ uWorld (3, true) ⟨7⟩ ⟨8⟩ (by decide) = .ok w' ∧
      w'.heaps ⟨uWorld.ctx.nextAlloc⟩ = some b ∧
      Marshal.Rep ⟨codec (.prod .nat .bool)⟩ (3, true) b.buf ∧
      Marshal.read ⟨codec (.prod .nat .bool)⟩ w' ⟨uWorld.ctx.nextAlloc⟩ = some (3, true) := by
  obtain ⟨w', hw'⟩ := World.allocWithChecked_succeeds (w := uWorld)
    (bytes := (codec (.prod .nat .bool)).encode (3, true))
    (rootId := ⟨7⟩) (disposal := ⟨8⟩) (pos := by decide) (by decide) (by decide)
  have hw'' : Marshal.alloc ⟨codec (.prod .nat .bool)⟩ uWorld (3, true) ⟨7⟩ ⟨8⟩
      (by decide) = .ok w' := by
    simpa [Marshal.alloc] using hw'
  obtain ⟨b, hb, hrep⟩ := Marshal.alloc_rep (m := ⟨codec (.prod .nat .bool)⟩)
    (w := uWorld) (v := (3, true)) (rootId := ⟨7⟩) (disposal := ⟨8⟩)
    (pos := by decide) hw''
  exact ⟨w', b, hw'', hb, hrep,
    Marshal.read_rep ⟨codec (.prod .nat .bool)⟩ hb hrep⟩

/-- The canonical codec round-trips a list of bytes. -/
example : (codec (.list .uint8)).decode
    ((codec (.list .uint8)).encode [1, 2]) = some [1, 2] :=
  (codec (.list .uint8)).decode_encode [1, 2]


end Cap
