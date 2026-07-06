import SuffixTree.Harness

/-!
# SuffixTree.Spec.SuffixTree

Specifications for `SuffixTree` APIs (`mk`, `buildSuffixTree`,
`addSuffix`, `search`). Each `spec_*` is a property over an
arbitrary `impl : RepoImpl`, accessing API functions via
`impl.suffixTree.<fn>`.

DO NOT MODIFY — frozen curator-given content.
-/

/-- Ground-truth infix predicate: `true` iff `pat` is a contiguous
    infix of `text`. The empty pattern is a substring of every text. -/
def spec_helper_isSubstring (pat text : List Char) : Bool :=
  match pat, text with
  | [], _ => true
  | _ :: _, [] => false
  | p :: ps, t :: ts =>
    if List.isPrefixOf (p :: ps) (t :: ts) then true
    else spec_helper_isSubstring (p :: ps) ts
termination_by text.length

/-- Character-membership oracle used by negative search specs. -/
def spec_helper_containsChar (text : String) (c : Char) : Bool :=
  text.toList.contains c

/-- `mk s` stores the input text `s` unchanged in the `.text` field.
    No transformation (e.g. lower-casing or trimming) is permitted. -/
def spec_mk_text_preserved (impl : RepoImpl) : Prop :=
  ∀ s : String, (impl.suffixTree.mk s).text = s

/-- A freshly constructed tree has no inserted trie paths, so no
    non-empty pattern is searchable before `addSuffix` or
    `buildSuffixTree` is called. -/
def spec_mk_has_no_nonempty_matches (impl : RepoImpl) : Prop :=
  ∀ text pattern : String,
    pattern ≠ "" →
      impl.suffixTree.search (impl.suffixTree.mk text) pattern = false

/-- The empty pattern `""` is found in every tree, including trees that
    have not been built. -/
def spec_search_empty_pattern_always_true (impl : RepoImpl) : Prop :=
  ∀ t : SuffixTree, impl.suffixTree.search t "" = true

/-- `buildSuffixTree` inserts all suffix paths but must leave the
    `.text` field unchanged from what `mk` stored. -/
def spec_buildSuffixTree_preserves_text (impl : RepoImpl) : Prop :=
  ∀ s : String,
    (impl.suffixTree.buildSuffixTree (impl.suffixTree.mk s)).text = s

/-- `addSuffix` inserts one suffix path but must not modify the
    `.text` field set by `mk`. -/
def spec_addSuffix_preserves_text (impl : RepoImpl) : Prop :=
  ∀ (s u : String) (i : Nat),
    (impl.suffixTree.addSuffix (impl.suffixTree.mk s) u i).text = s

/-- Building a tree reaches a fixed point: rebuilding an already-built
    tree leaves the tree structurally unchanged. -/
def spec_buildSuffixTree_idempotent (impl : RepoImpl) : Prop :=
  ∀ t : SuffixTree,
    impl.suffixTree.buildSuffixTree (impl.suffixTree.buildSuffixTree t) =
      impl.suffixTree.buildSuffixTree t

/-- Adding a suffix to any tree makes that exact suffix searchable. -/
def spec_addSuffix_makes_searchable (impl : RepoImpl) : Prop :=
  ∀ (t : SuffixTree) (suffix : String) (i : Nat),
    impl.suffixTree.search (impl.suffixTree.addSuffix t suffix i) suffix = true

/-- Adding a suffix makes every prefix of that suffix searchable along the inserted path. -/
def spec_addSuffix_makes_prefixes_searchable (impl : RepoImpl) : Prop :=
  ∀ (t : SuffixTree) (suffix pattern : String) (i : Nat),
    List.isPrefixOf pattern.toList suffix.toList = true →
      impl.suffixTree.search (impl.suffixTree.addSuffix t suffix i) pattern = true

/-- Adding a suffix is monotone with respect to successful searches:
    it must not delete patterns that were already searchable. -/
def spec_addSuffix_preserves_existing_searches (impl : RepoImpl) : Prop :=
  ∀ (t : SuffixTree) (suffix pattern : String) (i : Nat),
    impl.suffixTree.search t pattern = true →
      impl.suffixTree.search (impl.suffixTree.addSuffix t suffix i) pattern = true

/-- Search on a built tree is exactly substring membership in the
    original text, covering positive and negative cases uniformly. -/
def spec_search_matches_substring (impl : RepoImpl) : Prop :=
  ∀ text pattern : String,
    impl.suffixTree.search
      (impl.suffixTree.buildSuffixTree (impl.suffixTree.mk text))
      pattern =
        spec_helper_isSubstring pattern.toList text.toList

/-- If a character does not occur in the source text, then the
    corresponding one-character pattern is absent from the built tree. -/
def spec_absent_character_not_found (impl : RepoImpl) : Prop :=
  ∀ (text : String) (c : Char),
    spec_helper_containsChar text c = false →
      impl.suffixTree.search
        (impl.suffixTree.buildSuffixTree (impl.suffixTree.mk text))
        (String.singleton c) = false
