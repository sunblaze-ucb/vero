import Compression.Harness

/-!
# Compression.Spec.CoordinateCompression

Specifications for coordinate compression.  Each `spec_*` is a property
over an arbitrary `impl : RepoImpl`.

DO NOT MODIFY — this file is frozen curator-given content.
-/

/-- First index of an integer in a coordinate-compressor list. -/
def spec_coord_helper_firstIndexOfInt (v : Int) : List Int → Option Nat
  | [] => none
  | x :: xs =>
      if x == v then some 0
      else (spec_coord_helper_firstIndexOfInt v xs).map (· + 1)

/-- Compressing any value against an empty corpus returns none. -/
def spec_coord_compress_empty (impl : RepoImpl) : Prop :=
  ∀ v : Int, impl.compression.coordCompress (α := Int) [] v = none

/-- Decompressing any rank against an empty corpus returns none. -/
def spec_coord_decompress_empty (impl : RepoImpl) : Prop :=
  ∀ i : Nat, impl.compression.coordDecompress (α := Int) [] i = none

/-- Compressing a present value returns its first index in the corpus. -/
def spec_coord_compress_present (impl : RepoImpl) : Prop :=
  ∀ (xs : List Int) (v : Int) (i : Nat),
    xs[i]? = some v →
    v ∉ xs.take i →
    impl.compression.coordCompress (α := Int) xs v = some i

/-- Compressing a value absent from the corpus returns none. -/
def spec_coord_compress_absent (impl : RepoImpl) : Prop :=
  ∀ (xs : List Int) (v : Int),
    v ∉ xs →
    impl.compression.coordCompress (α := Int) xs v = none

/-- Decompressing an in-range rank returns the value at that index. -/
def spec_coord_decompress_in_range (impl : RepoImpl) : Prop :=
  ∀ (xs : List Nat) (i v : Nat),
    xs[i]? = some v →
    impl.compression.coordDecompress (α := Nat) xs i = some v

/-- Decompressing an out-of-range rank returns none. -/
def spec_coord_decompress_out_of_range (impl : RepoImpl) : Prop :=
  ∀ (xs : List Nat) (i : Nat),
    xs[i]? = none →
    impl.compression.coordDecompress (α := Nat) xs i = none

/-- If compress xs v = some i, then decompress xs i = some v (round-trip). -/
def spec_coord_roundtrip_present (impl : RepoImpl) : Prop :=
  ∀ (xs : List Int) (v : Int) (i : Nat),
    impl.compression.coordCompress (α := Int) xs v = some i →
    impl.compression.coordDecompress (α := Int) xs i = some v

/-- Compress returns exactly the first matching index in the compressor list. -/
def spec_coord_compress_exact_first_index (impl : RepoImpl) : Prop :=
  ∀ (xs : List Int) (v : Int),
    impl.compression.coordCompress (α := Int) xs v =
      spec_coord_helper_firstIndexOfInt v xs

/-- Decompress is exactly safe indexing into the compressor list. -/
def spec_coord_decompress_exact_index (impl : RepoImpl) : Prop :=
  ∀ (xs : List Int) (i : Nat),
    impl.compression.coordDecompress (α := Int) xs i = xs[i]?
