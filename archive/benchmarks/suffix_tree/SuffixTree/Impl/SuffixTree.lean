import SuffixTree.Impl.SuffixTreeNode

-- !benchmark @start imports
-- !benchmark @end imports

/-!
# SuffixTree.Impl.SuffixTree

Suffix tree data structure built over `SuffixTreeNode`. The tree
stores every suffix of a given text as a trie path. The four public
APIs correspond to the Python `SuffixTree` class:

- `mk` — create an empty tree for a text (Python `__init__`, no build)
- `buildSuffixTree` — insert every suffix of `text` into the trie
- `addSuffix` — insert a single suffix at a given start index
- `search` — test whether a pattern appears anywhere in the text

Python source: `data_structures/suffix_tree/suffix_tree.py`

Translation notes:
- Python `__init__` calls `build_suffix_tree` automatically; the
  benchmark separates construction (`mk`) from building
  (`buildSuffixTree`) to allow `addSuffix` test cases.
- The mutable trie traversal (`_add_suffix`) becomes the functional
  `insertChars` helper; each call rebuilds the path from root to leaf.
- `SuffixTreeImpl` is the internal structure name; `SuffixTree` is a
  transparent `abbrev` so that `SuffixTree.mk` (the API) can be defined
  without clashing with `SuffixTreeImpl.mk` (the struct constructor).

DO NOT MODIFY types or signatures — these are the fixed vocabulary.
Implement only the function bodies.
-/

-- ── Core data types (DO NOT MODIFY) ──────────────────────────────────

/-- Internal representation: a suffix tree holds the original text and
    the root node of the trie. -/
structure SuffixTreeImpl where
  text : String
  root : SuffixTreeNode

/-- A suffix tree: transparent alias so `SuffixTree.mk` can be defined
    as an API function without conflicting with `SuffixTreeImpl.mk`. -/
abbrev SuffixTree := SuffixTreeImpl

-- ── API signatures (DO NOT MODIFY) ───────────────────────────────────

abbrev SuffixTree.MkSig              := String → SuffixTree
abbrev SuffixTree.BuildSuffixTreeSig := SuffixTree → SuffixTree
abbrev SuffixTree.AddSuffixSig       := SuffixTree → String → Nat → SuffixTree
abbrev SuffixTree.SearchSig          := SuffixTree → String → Bool

-- ── Curator-provided helpers (api_helpers — no markers) ──────────────
-- These helpers support the functional (immutable) translation of the
-- Python trie mutation. The LLM may use or ignore them when filling
-- the `code` slots.

/-- Replace the value for key `k` in an association list, or append
    a new `(k, v)` pair if `k` is not present. -/
private def updateAssoc (k : Char) (v : SuffixTreeNode)
    : List (Char × SuffixTreeNode) → List (Char × SuffixTreeNode)
  | [] => [(k, v)]
  | (k', v') :: rest =>
    if k' == k then (k, v) :: rest
    else (k', v') :: updateAssoc k v rest

/-- Functionally insert a list of characters into the trie rooted at
    `node`. When the character list is exhausted the reached node is
    marked as end-of-string with the supplied `idx` (start) and
    `suffLen` (length of the suffix being inserted). -/
private def insertChars (idx : Nat) (suffLen : Nat)
    : List Char → SuffixTreeNode → SuffixTreeNode
  | [], .mk children _ _ _ =>
    let endIdx := if suffLen > 0 then idx + suffLen - 1 else idx
    .mk children true (some idx) (some endIdx)
  | c :: rest, .mk children isEnd startIdx endIdx =>
    let child := match children.lookup c with
      | some ch => ch
      | none    => .mk [] false none none
    let newChild := insertChars idx suffLen rest child
    .mk (updateAssoc c newChild children) isEnd startIdx endIdx

/-- Walk the trie following each character of `chars`; return `true`
    iff every character is matched. Empty pattern always returns `true`. -/
private def searchNode : List Char → SuffixTreeNode → Bool
  | [],         _                    => true
  | c :: rest, .mk children _ _ _ =>
    match children.lookup c with
    | none       => false
    | some child => searchNode rest child

-- !benchmark @start global_aux
-- !benchmark @end global_aux

-- ── Implementations (LLM task) ────────────────────────────────────────

-- !benchmark @start code_aux def=mk
-- !benchmark @end code_aux def=mk

--   Python __init__ auto-builds; benchmark separates mk from buildSuffixTree.
def SuffixTree.mk : SuffixTree.MkSig :=
-- !benchmark @start code def=mk
  fun text => SuffixTreeImpl.mk text (.mk [] false none none)
-- !benchmark @end code def=mk

-- !benchmark @start code_aux def=addSuffix
-- !benchmark @end code_aux def=addSuffix

--   Translates Python _add_suffix. Functional: returns new tree with updated trie.
def SuffixTree.addSuffix : SuffixTree.AddSuffixSig :=
-- !benchmark @start code def=addSuffix
  fun t suffix index =>
    let chars   := suffix.toList
    let newRoot := insertChars index chars.length chars t.root
    SuffixTreeImpl.mk t.text newRoot
-- !benchmark @end code def=addSuffix

-- !benchmark @start code_aux def=buildSuffixTree
-- !benchmark @end code_aux def=buildSuffixTree

--   Translates Python build_suffix_tree. Adds suffix text[i:] at position i for
--   every i in [0, n). Uses List.range + foldl over the existing tree.
def SuffixTree.buildSuffixTree : SuffixTree.BuildSuffixTreeSig :=
-- !benchmark @start code def=buildSuffixTree
  fun t =>
    let chars := t.text.toList
    let n     := chars.length
    (List.range n).foldl
      (fun acc i => SuffixTree.addSuffix acc (String.ofList (chars.drop i)) i)
      t
-- !benchmark @end code def=buildSuffixTree

-- !benchmark @start code_aux def=search
-- !benchmark @end code_aux def=search

def SuffixTree.search : SuffixTree.SearchSig :=
-- !benchmark @start code def=search
  fun t pattern =>
    searchNode pattern.toList t.root
-- !benchmark @end code def=search
