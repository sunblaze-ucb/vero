import Compression.Harness

/-!
# Compression.Spec.Huffman

Specifications for Huffman coding.  Each `spec_*` is a property over an
arbitrary `impl : RepoImpl`.

DO NOT MODIFY — this file is frozen curator-given content.
-/

/-- Total frequency stored in a Huffman tree. -/
def spec_huffman_helper_treeFreq : HuffmanTree → Nat
  | .leaf _ f => f
  | .node f _ _ => f

/-- Total frequency of the input letters. -/
def spec_huffman_helper_letterFreqSum (letters : List Letter) : Nat :=
  letters.foldl (fun acc l => acc + l.freq) 0

/-- No generated code is a prefix of another generated code for a different letter. -/
def spec_huffman_helper_prefixFree (codes : List (String × String)) : Prop :=
  ∀ (a ca b cb : String),
    (a, ca) ∈ codes →
    (b, cb) ∈ codes →
    a ≠ b →
      List.isPrefixOf ca.toList cb.toList = false ∧
      List.isPrefixOf cb.toList ca.toList = false

/-- Traversing a single-leaf tree with any prefix returns [(letter, prefix)]. -/
def spec_huffman_traverse_leaf (impl : RepoImpl) : Prop :=
  ∀ (l : String) (f : Nat) (pfx : String),
    impl.compression.traverse_tree (.leaf l f) pfx = [(l, pfx)]

/-- Traversing a two-leaf node assigns left and right codes below the prefix. -/
def spec_huffman_traverse_node (impl : RepoImpl) : Prop :=
  ∀ (l1 l2 pfx : String) (f1 f2 total : Nat),
    impl.compression.traverse_tree (.node total (.leaf l1 f1) (.leaf l2 f2)) pfx =
      [(l1, pfx ++ "0"), (l2, pfx ++ "1")]

/-- Starting traversal with any prefix prepends it to all emitted child codes. -/
def spec_huffman_traverse_with_prefix (impl : RepoImpl) : Prop :=
  ∀ (l1 l2 pfx : String) (f1 f2 total : Nat),
    impl.compression.traverse_tree (.node total (.leaf l1 f1) (.leaf l2 f2)) pfx =
      [(l1, pfx ++ "0"), (l2, pfx ++ "1")]

/-- Building a Huffman tree from an empty letter list returns none. -/
def spec_huffman_build_empty (impl : RepoImpl) : Prop :=
  (impl.compression.build_tree []).isNone

/-- Building a Huffman tree from one letter returns some tree. -/
def spec_huffman_build_nonempty (impl : RepoImpl) : Prop :=
  ∀ (l : String) (f : Nat),
    (impl.compression.build_tree [⟨l, f⟩]).isSome

/-- Building a tree from any non-empty letter list yields exactly one code per input letter. -/
def spec_huffman_build_traverse_count (impl : RepoImpl) : Prop :=
  ∀ letters : List Letter,
    letters ≠ [] →
    match impl.compression.build_tree letters with
    | none => False
    | some t => (impl.compression.traverse_tree t "").length = letters.length

/-- A built tree exposes exactly the input letters when traversed from the root. -/
def spec_huffman_build_preserves_letters (impl : RepoImpl) : Prop :=
  ∀ (letters : List Letter) (t : HuffmanTree),
    impl.compression.build_tree letters = some t →
      ∀ l : String,
        l ∈ (impl.compression.traverse_tree t "").map Prod.fst ↔
        l ∈ letters.map Letter.letter

/-- A built tree's root frequency is the sum of all input frequencies. -/
def spec_huffman_build_frequency_sum (impl : RepoImpl) : Prop :=
  ∀ (letters : List Letter) (t : HuffmanTree),
    impl.compression.build_tree letters = some t →
      spec_huffman_helper_treeFreq t = spec_huffman_helper_letterFreqSum letters

/-- Codes emitted by a built Huffman tree are prefix-free. -/
def spec_huffman_build_prefix_free (impl : RepoImpl) : Prop :=
  ∀ (letters : List Letter) (t : HuffmanTree),
    impl.compression.build_tree letters = some t →
      spec_huffman_helper_prefixFree (impl.compression.traverse_tree t "")
