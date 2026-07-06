import Compression.Impl.Huffman
import Compression.Impl.BurrowsWheeler
import Compression.Impl.Lz77
import Compression.Impl.RunLengthEncoding
import Compression.Impl.CoordinateCompression
import Compression.Bundle
import Compression.Harness

/-!
# Compression.Test

`#guard` conformance tests.  Every guard runs against
`canonical.compression.<api>` so the same tests exercise both the
reference implementation (during curation) and any LLM-supplied
`RepoImpl` (during evaluation).

The Python source has no doctests for most of these algorithms;
where the original module ships an example (LZ77 token list,
`^BANANA|` BWT) we reuse it verbatim, otherwise we author minimal
sanity checks plus encode∘decode round-trips.

DO NOT MODIFY — infrastructure.
-/

-- ── Huffman ──────────────────────────────────────────────────────────────────

-- A single-leaf tree returns the one pair with empty prefix
#guard canonical.compression.traverse_tree (.leaf "a" 1) "" == [("a", "")]

-- Two-leaf tree: left gets "0", right gets "1"
#guard canonical.compression.traverse_tree
    (.node 3 (.leaf "a" 1) (.leaf "b" 2)) ""
  == [("a", "0"), ("b", "1")]

-- Three-leaf balanced tree: left subtree -> "0?", right leaf -> "1"
#guard canonical.compression.traverse_tree
    (.node 6 (.node 3 (.leaf "a" 1) (.leaf "b" 2)) (.leaf "c" 3)) ""
  == [("a", "00"), ("b", "01"), ("c", "1")]

-- traverse_tree honours a non-empty starting prefix
#guard canonical.compression.traverse_tree
    (.node 3 (.leaf "x" 1) (.leaf "y" 2)) "1"
  == [("x", "10"), ("y", "11")]

-- build_tree of one letter returns some tree
#guard (canonical.compression.build_tree [⟨"a", 5⟩]).isSome

-- build_tree of two letters returns some tree
#guard (canonical.compression.build_tree [⟨"a", 3⟩, ⟨"b", 7⟩]).isSome

-- build_tree of empty list returns none
-- (Option HuffmanTree has no BEq since HuffmanTree has no BEq, so use isNone)
#guard (canonical.compression.build_tree []).isNone

-- build_tree on three letters: traversing the result yields all three letters
-- (regardless of tree shape, every leaf must appear exactly once).
#guard
  match canonical.compression.build_tree [⟨"a", 1⟩, ⟨"b", 2⟩, ⟨"c", 3⟩] with
  | none => false
  | some t =>
    let pairs := canonical.compression.traverse_tree t ""
    pairs.length == 3
      && pairs.any (fun p => p.1 == "a")
      && pairs.any (fun p => p.1 == "b")
      && pairs.any (fun p => p.1 == "c")

-- ── Burrows-Wheeler ───────────────────────────────────────────────────────────

-- all_rotations of a 3-char string produces 3 rotations
#guard (canonical.compression.all_rotations "abc").length == 3

-- all_rotations of "abc" enumerates every cyclic shift
#guard canonical.compression.all_rotations "abc" == ["abc", "bca", "cab"]

-- all_rotations of empty string is the empty list
#guard canonical.compression.all_rotations "" == []

-- all_rotations of a single character is just that string
#guard canonical.compression.all_rotations "x" == ["x"]

-- bwt_transform of "^BANANA|" is the canonical example from Wikipedia
#guard (canonical.compression.bwt_transform "^BANANA|").bwt_string == "BNN^AA|A"

-- bwt_transform of empty string returns the documented sentinel
#guard
  let r := canonical.compression.bwt_transform ""
  r.bwt_string == "" && r.idx_original_string == 0

-- bwt_transform of a single character is that character itself, idx 0
#guard
  let r := canonical.compression.bwt_transform "a"
  r.bwt_string == "a" && r.idx_original_string == 0

-- round-trip: reverse_bwt ∘ bwt_transform returns the original string
#guard
  let r := canonical.compression.bwt_transform "^BANANA|"
  canonical.compression.reverse_bwt r.bwt_string r.idx_original_string == "^BANANA|"

-- round-trip on a different non-trivial string
#guard
  let r := canonical.compression.bwt_transform "mississippi"
  canonical.compression.reverse_bwt r.bwt_string r.idx_original_string == "mississippi"

-- reverse_bwt on empty input returns empty string
#guard canonical.compression.reverse_bwt "" 0 == ""

-- ── LZ77 ─────────────────────────────────────────────────────────────────────

-- decompress of empty token list gives ""
#guard canonical.compression.lz77Decompress ⟨13, 6⟩ [] == ""

-- decompress of a known token list reproduces "cabracadabrarrarrad"
-- (example taken directly from the Python source doctest)
#guard canonical.compression.lz77Decompress ⟨13, 6⟩
    [⟨0,0,'c'⟩, ⟨0,0,'a'⟩, ⟨0,0,'b'⟩, ⟨0,0,'r'⟩,
     ⟨3,1,'c'⟩, ⟨2,1,'d'⟩, ⟨7,4,'r'⟩, ⟨3,5,'d'⟩]
  == "cabracadabrarrarrad"

-- decompress of all-literal tokens is just the indicator characters
#guard canonical.compression.lz77Decompress ⟨13, 6⟩
    [⟨0,0,'h'⟩, ⟨0,0,'i'⟩] == "hi"

-- compress of empty input yields empty token list
#guard canonical.compression.lz77Compress ⟨13, 6⟩ "" == []

-- compress of a single character yields one literal token
#guard canonical.compression.lz77Compress ⟨13, 6⟩ "x" == [⟨0, 0, 'x'⟩]

-- compress then decompress round-trips a short string with no repeated chars
-- (avoids the known end-of-match indicator edge case in the simplified algorithm)
#guard
  let cfg : LZ77Compressor := ⟨10, 4⟩
  canonical.compression.lz77Decompress cfg
    (canonical.compression.lz77Compress cfg "abc") == "abc"

-- ── Run-Length Encoding ───────────────────────────────────────────────────────

-- basic encode
#guard canonical.compression.run_length_encode "AAABBC" == "3A2B1C"

-- encode empty string
#guard canonical.compression.run_length_encode "" == ""

-- single char
#guard canonical.compression.run_length_encode "Z" == "1Z"

-- decode round-trips encode on a typical alphabetic string
#guard canonical.compression.run_length_decode
    (canonical.compression.run_length_encode "AAABBC") == "AAABBC"

-- decode of empty string is empty
#guard canonical.compression.run_length_decode "" == ""

-- decode parses multi-digit run counts
#guard canonical.compression.run_length_decode "10A" == "AAAAAAAAAA"

-- decode round-trips encode on a longer mixed-run string
#guard canonical.compression.run_length_decode
    (canonical.compression.run_length_encode "WWWWWWWWWWWWBWWWWWWWWWWWWBBB")
  == "WWWWWWWWWWWWBWWWWWWWWWWWWBBB"

-- ── Coordinate Compression ───────────────────────────────────────────────────

-- compress: element present at rank 0
#guard canonical.compression.coordCompress (α := Int) [1, 3, 5] 1 == some 0

-- compress: element present at rank 2
#guard canonical.compression.coordCompress (α := Int) [1, 3, 5] 5 == some 2

-- compress: element absent → none
#guard canonical.compression.coordCompress (α := Int) [1, 3, 5] 2 == none

-- decompress: rank 0 → first value
#guard canonical.compression.coordDecompress (α := Nat) [1, 3, 5] 0 == some 1

-- decompress: rank 1 → middle value
#guard canonical.compression.coordDecompress (α := Nat) [1, 3, 5] 1 == some 3

-- decompress: out-of-range → none
#guard canonical.compression.coordDecompress (α := Nat) [1, 3, 5] 9 == none
