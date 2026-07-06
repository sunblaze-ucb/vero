-- !benchmark @start imports
-- !benchmark @end imports

/-!
# Compression.Impl.Huffman

Types and implementations for Huffman coding.  Builds a
frequency-weighted binary tree from a character-frequency list (`Letter`),
then traverses it to produce `(character, bit-string)` encoding pairs.

`parse_file` and the `huffman` I/O driver are omitted — they depend on
file I/O which cannot be modelled in a pure benchmark.
`traverse_tree` returns `List (String × String)` pairs (character, bit-code)
rather than a mutated `Letter` list, since Lean is purely functional.

DO NOT MODIFY types or signatures — these are the fixed vocabulary.
Implement only the function bodies.
-/

-- ── Core data types (DO NOT MODIFY) ──────────────────────────

/-- A character with its frequency count, used as a Huffman leaf. -/
structure Letter where
  letter : String
  freq   : Nat
  deriving Repr, BEq

/-- The Huffman tree: a `leaf` wraps a (letter, frequency) pair;
    a `node` stores the combined frequency and its two subtrees. -/
inductive HuffmanTree where
  | leaf (letter : String) (freq : Nat) : HuffmanTree
  | node (freq : Nat) (left right : HuffmanTree) : HuffmanTree
  deriving Repr

/-- `TreeNode` is the internal-node form of `HuffmanTree`.
    In the Python source it is a separate class; in Lean the inductive
    subsumes both leaf and node cases. -/
abbrev TreeNode := HuffmanTree

namespace Compression

-- ── API signatures (DO NOT MODIFY) ───────────────────────────
abbrev TraverseTreeSig := HuffmanTree → String → List (String × String)
abbrev BuildTreeSig    := List Letter → Option HuffmanTree

end Compression

-- ── Shared helpers (fixed vocabulary, no markers) ────────────

/-- Extract the frequency from a `HuffmanTree` node. -/
def huffmanFreq : HuffmanTree → Nat
  | .leaf _ f   => f
  | .node f _ _ => f

-- !benchmark @start global_aux
/-- Insert `t` into a frequency-sorted list (ascending), maintaining order. -/
private def insertByFreq (t : HuffmanTree) : List HuffmanTree → List HuffmanTree
  | []       => [t]
  | h :: rest =>
    if huffmanFreq t ≤ huffmanFreq h then t :: h :: rest
    else h :: insertByFreq t rest

/-- Sort a `List HuffmanTree` by frequency ascending (insertion sort). -/
private def sortByFreq (ts : List HuffmanTree) : List HuffmanTree :=
  ts.foldl (fun acc t => insertByFreq t acc) []
-- !benchmark @end global_aux

-- ── Implementation stubs (LLM task) ──────────────────────────

-- !benchmark @start code_aux def=traverse_tree
-- !benchmark @end code_aux def=traverse_tree

-- @review human: `prefix` is a Lean 4 keyword; the lambda uses `pfx` as the binder name
partial def Compression.traverse_tree : Compression.TraverseTreeSig :=
-- !benchmark @start code def=traverse_tree
  fun root pfx =>
    match root with
    | .leaf letter _ => [(letter, pfx)]
    | .node _ left right =>
      Compression.traverse_tree left  (pfx ++ "0") ++
      Compression.traverse_tree right (pfx ++ "1")
-- !benchmark @end code def=traverse_tree

-- !benchmark @start code_aux def=build_tree
-- Merges the two lowest-frequency trees into one node per iteration.
-- @review human: termination via list-length decrease (take 2, insert 1 → net -1)
private partial def buildTreeGo : List HuffmanTree → Option HuffmanTree
  | []            => none
  | [t]           => some t
  | t1 :: t2 :: rest =>
    let merged := HuffmanTree.node (huffmanFreq t1 + huffmanFreq t2) t1 t2
    buildTreeGo (insertByFreq merged rest)
-- !benchmark @end code_aux def=build_tree

-- @review human: parse_file / huffman (I/O) omitted — not representable in benchmark
partial def Compression.build_tree : Compression.BuildTreeSig :=
-- !benchmark @start code def=build_tree
  fun letters =>
    let initial := sortByFreq (letters.map (fun l => HuffmanTree.leaf l.letter l.freq))
    buildTreeGo initial
-- !benchmark @end code def=build_tree
