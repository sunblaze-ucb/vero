-- !benchmark @start imports
-- !benchmark @end imports

/-!
# VerifiedBitmasks.Impl.BitmaskFixedChunks

Fixed-chunk bitmask implementation. The representation type `BFC_T` is
`List (List Bool)`: a list of 64-bit chunks, each a 64-element `List Bool`.
The interpretation function `BFC_I` flattens the chunks into a single
`List Bool` matching the canonical `BitmaskSpec.T`.

Translated from `src/BitMask/BitmaskFixedChunks.i.dfy`.

DO NOT MODIFY types or signatures — these are the fixed vocabulary.
Implement only the function bodies (inside the `!benchmark code` markers).
-/

-- ── Type (no markers — fixed vocabulary) ─────────────────────────────────────

/-- The fixed-chunk bitmask type: a list of 64-element chunks. -/
abbrev BFC_T := List (List Bool)

-- ── Spec helpers (frozen vocabulary) ─────────────────────────────────────────

/-- Size of each chunk in bits (64). -/
def BFC_CHUNK_SIZE : Nat := 64

/-- Index of the chunk containing bit i. -/
def BFC_GetChunk (i : Nat) : Nat := i / BFC_CHUNK_SIZE

/-- Bit offset within the chunk containing bit i. -/
def BFC_GetChunkOffset (i : Nat) : Nat := i % BFC_CHUNK_SIZE

/-- Flatten a list of chunks into a single boolean list. -/
def BFC_Flatten : BFC_T → List Bool := List.flatten

/-- Interpretation function: flatten chunk representation to a flat List Bool. -/
def BFC_I (A : BFC_T) : List Bool := BFC_Flatten A

/-- Invariant: every chunk has exactly CHUNK_SIZE bits. -/
def BFC_Inv (A : BFC_T) : Prop := ∀ chunk ∈ A, chunk.length = BFC_CHUNK_SIZE

/-- A size n is valid iff it is a multiple of CHUNK_SIZE. -/
def BFC_ValidSize (n : Nat) : Prop := n % BFC_CHUNK_SIZE = 0

/-- BFC_Flatten and BFC_I agree on valid bitmasks (they are identical by definition). -/
theorem lemma_BFC_FlattenIsI (A : BFC_T) (_ : BFC_Inv A) : BFC_Flatten A = BFC_I A := by rfl

/-- The i-th bit of I(A) equals the offset bit in the chunk containing i. -/
axiom lemma_BFC_IResult (A : BFC_T) (i : Nat) (_ : BFC_Inv A)
    (_ : i < A.length * BFC_CHUNK_SIZE) :
    (BFC_I A).getD i false = (A.getD (BFC_GetChunk i) []).getD (BFC_GetChunkOffset i) false

/-- I(A) = A[0] ++ I(A[1..]) for non-empty A. -/
axiom lemma_BFC_IStep (A : BFC_T) (_ : BFC_Inv A) (_ : A ≠ []) :
    BFC_I A = A.head! ++ BFC_I A.tail

/-- Two valid chunk bitmasks are equal iff their interpretations are equal. -/
axiom lemma_BFC_IEqual (A B : BFC_T) (_ : BFC_Inv A) (_ : BFC_Inv B) :
    A = B ↔ BFC_I A = BFC_I B

/-- Count set bits in a single chunk. -/
def bFC_popcntChunk (chunk : List Bool) : Nat := chunk.countP id

/-- Boolean equality of two chunk bitmasks. -/
def bFC_eq (A B : BFC_T) : Bool := A == B

/-- True iff all bits in all chunks are false. -/
def bFC_isZeros (A : BFC_T) : Bool := A.all (·.all (· == false))

/-- True iff all bits in all chunks are true. -/
def bFC_isOnes (A : BFC_T) : Bool := A.all (·.all (· == true))

-- ── API signatures (no markers — fixed vocabulary) ────────────────────────────

namespace VerifiedBitmasks

/-- Signature for `bFC_newZeros`: create an all-zeros chunk bitmask of M bits. -/
abbrev BFCNewZerosSig := Nat → BFC_T

/-- Signature for `bFC_newOnes`: create an all-ones chunk bitmask of M bits. -/
abbrev BFCNewOnesSig := Nat → BFC_T

/-- Signature for `bFC_nbits`: number of bits (length × 64). -/
abbrev BFCNbitsSig := BFC_T → Nat

/-- Signature for `bFC_popcnt`: count of set bits across all chunks. -/
abbrev BFCPopcntSig := BFC_T → Nat

/-- Signature for `bFC_getBit`: get the value of bit i. -/
abbrev BFCGetBitSig := BFC_T → Nat → Bool

/-- Signature for `bFC_setBit`: set bit i to true. -/
abbrev BFCSetBitSig := BFC_T → Nat → BFC_T

/-- Signature for `bFC_clearBit`: set bit i to false. -/
abbrev BFCClearBitSig := BFC_T → Nat → BFC_T

/-- Signature for `bFC_toggleBit`: toggle bit i. -/
abbrev BFCToggleBitSig := BFC_T → Nat → BFC_T

/-- Signature for `bFC_and`: pointwise AND of two chunk bitmasks. -/
abbrev BFCAndSig := BFC_T → BFC_T → BFC_T

/-- Signature for `bFC_or`: pointwise OR of two chunk bitmasks. -/
abbrev BFCOrSig := BFC_T → BFC_T → BFC_T

/-- Signature for `bFC_xor`: pointwise XOR of two chunk bitmasks. -/
abbrev BFCXorSig := BFC_T → BFC_T → BFC_T

/-- Signature for `bFC_not`: pointwise NOT of a chunk bitmask. -/
abbrev BFCNotSig := BFC_T → BFC_T

end VerifiedBitmasks

-- !benchmark @start global_aux
-- !benchmark @end global_aux

-- ── Implementation stubs (LLM task) ───────────────────────────────────────────

-- !benchmark @start code_aux def=bFC_newZeros
-- !benchmark @end code_aux def=bFC_newZeros

def bFC_newZeros : VerifiedBitmasks.BFCNewZerosSig :=
-- !benchmark @start code def=bFC_newZeros
  fun M =>
    let nchunks := M / BFC_CHUNK_SIZE
    List.replicate nchunks (List.replicate BFC_CHUNK_SIZE false)
-- !benchmark @end code def=bFC_newZeros

-- !benchmark @start code_aux def=bFC_newOnes
-- !benchmark @end code_aux def=bFC_newOnes

def bFC_newOnes : VerifiedBitmasks.BFCNewOnesSig :=
-- !benchmark @start code def=bFC_newOnes
  fun M =>
    let nchunks := M / BFC_CHUNK_SIZE
    List.replicate nchunks (List.replicate BFC_CHUNK_SIZE true)
-- !benchmark @end code def=bFC_newOnes

-- !benchmark @start code_aux def=bFC_nbits
-- !benchmark @end code_aux def=bFC_nbits

def bFC_nbits : VerifiedBitmasks.BFCNbitsSig :=
-- !benchmark @start code def=bFC_nbits
  fun A => A.length * BFC_CHUNK_SIZE
-- !benchmark @end code def=bFC_nbits

-- !benchmark @start code_aux def=bFC_popcnt
-- !benchmark @end code_aux def=bFC_popcnt

def bFC_popcnt : VerifiedBitmasks.BFCPopcntSig :=
-- !benchmark @start code def=bFC_popcnt
  fun A => A.foldl (fun acc chunk => acc + bFC_popcntChunk chunk) 0
-- !benchmark @end code def=bFC_popcnt

-- !benchmark @start code_aux def=bFC_getBit
-- !benchmark @end code_aux def=bFC_getBit

def bFC_getBit : VerifiedBitmasks.BFCGetBitSig :=
-- !benchmark @start code def=bFC_getBit
  fun A i =>
    let c := BFC_GetChunk i
    let o := BFC_GetChunkOffset i
    (A.getD c []).getD o false
-- !benchmark @end code def=bFC_getBit

-- !benchmark @start code_aux def=bFC_setBit
-- !benchmark @end code_aux def=bFC_setBit

def bFC_setBit : VerifiedBitmasks.BFCSetBitSig :=
-- !benchmark @start code def=bFC_setBit
  fun A i =>
    let c := BFC_GetChunk i
    let o := BFC_GetChunkOffset i
    A.set c ((A.getD c []).set o true)
-- !benchmark @end code def=bFC_setBit

-- !benchmark @start code_aux def=bFC_clearBit
-- !benchmark @end code_aux def=bFC_clearBit

def bFC_clearBit : VerifiedBitmasks.BFCClearBitSig :=
-- !benchmark @start code def=bFC_clearBit
  fun A i =>
    let c := BFC_GetChunk i
    let o := BFC_GetChunkOffset i
    A.set c ((A.getD c []).set o false)
-- !benchmark @end code def=bFC_clearBit

-- !benchmark @start code_aux def=bFC_toggleBit
-- !benchmark @end code_aux def=bFC_toggleBit

def bFC_toggleBit : VerifiedBitmasks.BFCToggleBitSig :=
-- !benchmark @start code def=bFC_toggleBit
  fun A i =>
    let c := BFC_GetChunk i
    let o := BFC_GetChunkOffset i
    let chunk := A.getD c []
    A.set c (chunk.set o (!chunk.getD o false))
-- !benchmark @end code def=bFC_toggleBit

-- !benchmark @start code_aux def=bFC_and
-- !benchmark @end code_aux def=bFC_and

def bFC_and : VerifiedBitmasks.BFCAndSig :=
-- !benchmark @start code def=bFC_and
  fun A B => List.zipWith (fun ca cb => List.zipWith (· && ·) ca cb) A B
-- !benchmark @end code def=bFC_and

-- !benchmark @start code_aux def=bFC_or
-- !benchmark @end code_aux def=bFC_or

def bFC_or : VerifiedBitmasks.BFCOrSig :=
-- !benchmark @start code def=bFC_or
  fun A B => List.zipWith (fun ca cb => List.zipWith (· || ·) ca cb) A B
-- !benchmark @end code def=bFC_or

-- !benchmark @start code_aux def=bFC_xor
-- !benchmark @end code_aux def=bFC_xor

def bFC_xor : VerifiedBitmasks.BFCXorSig :=
-- !benchmark @start code def=bFC_xor
  fun A B => List.zipWith (fun ca cb => List.zipWith (· != ·) ca cb) A B
-- !benchmark @end code def=bFC_xor

-- !benchmark @start code_aux def=bFC_not
-- !benchmark @end code_aux def=bFC_not

def bFC_not : VerifiedBitmasks.BFCNotSig :=
-- !benchmark @start code def=bFC_not
  fun A => A.map (·.map (!·))
-- !benchmark @end code def=bFC_not
