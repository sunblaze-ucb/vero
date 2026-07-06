import Compression.Impl.Huffman
import Compression.Impl.BurrowsWheeler
import Compression.Impl.Lz77
import Compression.Impl.RunLengthEncoding
import Compression.Impl.CoordinateCompression
import Compression.Bundle
import Compression.Harness
import Compression.Spec.Huffman
import Compression.Spec.BurrowsWheeler
import Compression.Spec.Lz77
import Compression.Spec.RunLengthEncoding
import Compression.Spec.CoordinateCompression
import Compression.Test

/-!
# Compression

Root import hub for the Compression benchmark. Covers five classical
compression / encoding algorithms translated from
TheAlgorithms/Python: Huffman coding, Burrows-Wheeler transform, LZ77,
run-length encoding, and coordinate compression.
-/
