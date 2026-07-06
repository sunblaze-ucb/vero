-- !benchmark @start imports
-- !benchmark @end imports

/-!
# SuffixTree.Impl.SuffixTreeNode

Core node type for the suffix tree. Each node holds a character-keyed
child map, an end-of-string flag, and optional start/end indices into
the original text marking where a suffix ends.

The Python source (`suffix_tree_node.py`) also defines a `suffix_link`
field, used in Ukkonen's algorithm. It is unused in any API in this
benchmark (the build algorithm is the naive O(n²) variant), so it is
omitted here.
--   never assigned or read by build_suffix_tree / _add_suffix / search; omit for
--   clean Lean translation. Re-add if a future spec needs it.

Types and signatures are fixed vocabulary (DO NOT MODIFY). Function
bodies are the curator's reference implementations; the pipeline
replaces them with `sorry` inside the `code` markers before presenting
the benchmark to the LLM.
-/

-- !benchmark @start global_aux
-- !benchmark @end global_aux

-- ── Core data types (DO NOT MODIFY) ──────────────────────────────────

/-- A node in the suffix tree trie.

Each node stores:
- `children`: association list mapping the next character to the child node
- `isEndOfString`: true when this node is the end of some inserted suffix
- `start`: starting index in the original text of the suffix that ends here
- `end_`: ending index in the original text of the suffix that ends here

Note: `children` uses `List (Char × SuffixTreeNode)` (insertion-order
association list) to preserve determinism. The Python source uses `dict`
(insertion-ordered since Python 3.7).
-/
inductive SuffixTreeNode : Type where
  | mk (children : List (Char × SuffixTreeNode))
       (isEndOfString : Bool)
       (start : Option Nat)
       (end_ : Option Nat) : SuffixTreeNode
