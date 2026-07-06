import Compression.Harness

/-!
# Compression.Spec.Lz77

Specifications for LZ77 sliding-window compression.  Each `spec_*` is a
property over an arbitrary `impl : RepoImpl`.

DO NOT MODIFY — this file is frozen curator-given content.
-/

/-- Compressing the empty string returns the empty token list. -/
def spec_lz77_compress_empty (impl : RepoImpl) : Prop :=
  ∀ cfg : LZ77Compressor,
    impl.compression.lz77Compress cfg "" = []

/-- Decompressing the empty token list returns the empty string. -/
def spec_lz77_decompress_empty (impl : RepoImpl) : Prop :=
  ∀ cfg : LZ77Compressor,
    impl.compression.lz77Decompress cfg [] = ""

/-- Compressing a singleton string produces one literal token for that character. -/
def spec_lz77_compress_singleton (impl : RepoImpl) : Prop :=
  ∀ (cfg : LZ77Compressor) (c : Char),
    impl.compression.lz77Compress cfg (String.singleton c) = [⟨0, 0, c⟩]

/-- Concrete round-trip on "abc" with config ⟨10, 4⟩: decompress(compress("abc")) = "abc". -/
def spec_lz77_roundtrip_simple (impl : RepoImpl) : Prop :=
  let cfg : LZ77Compressor := ⟨10, 4⟩
  impl.compression.lz77Decompress cfg (impl.compression.lz77Compress cfg "abc") = "abc"

/-- General round-trip: decompressing the compressor output recovers the original string. -/
def spec_lz77_roundtrip (impl : RepoImpl) : Prop :=
  ∀ (cfg : LZ77Compressor) (s : String),
    impl.compression.lz77Decompress cfg (impl.compression.lz77Compress cfg s) = s

/-- Decompressing the canonical doctest token sequence yields "cabracadabrarrarrad". -/
def spec_lz77_decompress_canonical (impl : RepoImpl) : Prop :=
  impl.compression.lz77Decompress ⟨13, 6⟩
      [⟨0, 0, 'c'⟩, ⟨0, 0, 'a'⟩, ⟨0, 0, 'b'⟩, ⟨0, 0, 'r'⟩,
       ⟨3, 1, 'c'⟩, ⟨2, 1, 'd'⟩, ⟨7, 4, 'r'⟩, ⟨3, 5, 'd'⟩] =
    "cabracadabrarrarrad"
