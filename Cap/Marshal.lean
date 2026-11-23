import Cap.Code
import Cap.Unified
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

/-- Deallocate a marshalled buffer through the checked disposal route. -/
def free (w : World) (a : AllocId) (d : CapId) : Except String World :=
  w.freeChecked a d

/-- A successful marshalled deallocation preserves the world invariant. -/
theorem free_wf {w w' : World} {a : AllocId} {d : CapId}
    (h : free w a d = .ok w') (hwf : w.WellFormed) : w'.WellFormed :=
  World.freeChecked_wf h hwf

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
