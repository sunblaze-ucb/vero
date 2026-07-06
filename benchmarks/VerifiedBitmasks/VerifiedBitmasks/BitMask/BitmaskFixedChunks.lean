import VerifiedBitmasks.BitMask.BitmaskImplIF

-- !benchmark @start imports
-- !benchmark @end imports

/-!
# VerifiedBitmasks.BitMask.BitmaskFixedChunks

Fixed-chunk bitmask implementation.  The representation type `T` is
`List (List Bool)`: a list of 64-bit chunks, each a 64-element `List Bool`.
The interpretation function `I` flattens the chunks into a single
`List Bool` matching `BitmaskSpec.T`.

DO NOT MODIFY types or signatures — these are the fixed vocabulary.
Implement only the function bodies (inside the `!benchmark code` markers).
-/

-- !benchmark @start global_aux
-- !benchmark @end global_aux

-- ── Types / spec helpers (no markers — fixed vocabulary) ───────────────────

namespace BitmaskFixedChunks

/-- The fixed-chunk bitmask type: a list of 64-element chunks (LSB first). -/
abbrev T := List (List Bool)

/-- The fixed chunk size (64 bits per chunk). -/
def CHUNK_SIZE : Nat := 64

/-- Chunk index for bit position `i`. -/
def GetChunk (i : Nat) : Nat := i / CHUNK_SIZE

/-- Intra-chunk offset for bit position `i`. -/
def GetChunkOffset (i : Nat) : Nat := i % CHUNK_SIZE

/-- Interpretation: flatten all chunks into a single `List Bool`. -/
def I (A : T) : BitmaskSpec.T :=
  A.foldl (· ++ ·) []

/-- Flatten a chunk list (same as `I` but named for spec helpers). -/
def Flatten (A : T) : List Bool :=
  A.foldl (· ++ ·) []

/-- Per-chunk population count helper. -/
def bitmask_popcnt_chunk (chunk : List Bool) : Nat := chunk.countP id

/-- Validity: every chunk has exactly `CHUNK_SIZE` bits. -/
def Inv (A : T) : Prop := ∀ chunk ∈ A, chunk.length = CHUNK_SIZE

/-- A size `n` is valid iff it is a multiple of `CHUNK_SIZE`. -/
def ValidSize (n : Nat) : Prop := n % CHUNK_SIZE = 0

/-- Extensional equality. -/
def bitmask_eq (A B : T) : Bool := A == B

/-- True iff all bits in all chunks are `false`. -/
def bitmask_is_zeros (A : T) : Bool := A.all (·.all (!·))

/-- True iff all bits in all chunks are `true`. -/
def bitmask_is_ones (A : T) : Bool := A.all (·.all id)

/-- Number of bits: chunks × CHUNK_SIZE. -/
def bitmask_nbits (A : T) : Nat := A.length * CHUNK_SIZE

/-- Population count: sum of per-chunk population counts. -/
def bitmask_popcnt (A : T) : Nat := A.foldl (fun acc c => acc + bitmask_popcnt_chunk c) 0

/-- Get the bit at position `i` (false if out of range). -/
def bitmask_get_bit (A : T) (i : Nat) : Bool :=
  let c := GetChunk i
  let o := GetChunkOffset i
  (A.getD c []).getD o false

/-- Set the bit at position `i`. -/
def bitmask_set_bit (A : T) (i : Nat) : T :=
  let c := GetChunk i
  let o := GetChunkOffset i
  A.mapIdx (fun j chunk => if j == c then chunk.mapIdx (fun k b => if k == o then true else b) else chunk)

/-- Clear the bit at position `i`. -/
def bitmask_clear_bit (A : T) (i : Nat) : T :=
  let c := GetChunk i
  let o := GetChunkOffset i
  A.mapIdx (fun j chunk => if j == c then chunk.mapIdx (fun k b => if k == o then false else b) else chunk)

/-- Toggle the bit at position `i`. -/
def bitmask_toggle_bit (A : T) (i : Nat) : T :=
  let c := GetChunk i
  let o := GetChunkOffset i
  A.mapIdx (fun j chunk => if j == c then chunk.mapIdx (fun k b => if k == o then !b else b) else chunk)

/-- Pointwise AND across corresponding chunks. -/
def bitmask_and (A B : T) : T :=
  List.zipWith (fun ca cb => List.zipWith (· && ·) ca cb) A B

/-- Pointwise OR across corresponding chunks. -/
def bitmask_or (A B : T) : T :=
  List.zipWith (fun ca cb => List.zipWith (· || ·) ca cb) A B

/-- Pointwise XOR across corresponding chunks. -/
def bitmask_xor (A B : T) : T :=
  List.zipWith (fun ca cb => List.zipWith (· != ·) ca cb) A B

/-- Pointwise NOT within each chunk. -/
def bitmask_not (A : T) : T :=
  A.map (·.map (!·))

end BitmaskFixedChunks

-- ── API signatures (no markers — fixed vocabulary) ─────────────────────────

namespace Bank

abbrev BitmaskFCNewZerosSig := Nat → BitmaskFixedChunks.T
abbrev BitmaskFCNewOnesSig  := Nat → BitmaskFixedChunks.T
abbrev BitmaskFCGetBitSig   := BitmaskFixedChunks.T → Nat → Bool

end Bank

-- ── Implementation stubs (LLM task) ────────────────────────────────────────

-- !benchmark @start code_aux def=bFC_newZeros
-- !benchmark @end code_aux def=bFC_newZeros

def Bank.bFC_newZeros : Bank.BitmaskFCNewZerosSig :=
-- !benchmark @start code def=bFC_newZeros
  fun m =>
    let nchunks := m / BitmaskFixedChunks.CHUNK_SIZE
    List.replicate nchunks (List.replicate BitmaskFixedChunks.CHUNK_SIZE false)
-- !benchmark @end code def=bFC_newZeros

-- !benchmark @start code_aux def=bFC_newOnes
-- !benchmark @end code_aux def=bFC_newOnes

def Bank.bFC_newOnes : Bank.BitmaskFCNewOnesSig :=
-- !benchmark @start code def=bFC_newOnes
  fun m =>
    let nchunks := m / BitmaskFixedChunks.CHUNK_SIZE
    List.replicate nchunks (List.replicate BitmaskFixedChunks.CHUNK_SIZE true)
-- !benchmark @end code def=bFC_newOnes

-- !benchmark @start code_aux def=bFC_getBit
-- !benchmark @end code_aux def=bFC_getBit

def Bank.bFC_getBit : Bank.BitmaskFCGetBitSig :=
-- !benchmark @start code def=bFC_getBit
  fun a i => BitmaskFixedChunks.bitmask_get_bit a i
-- !benchmark @end code def=bFC_getBit
