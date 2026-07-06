import SuffixTree.Impl.SuffixTreeNode
import SuffixTree.Impl.SuffixTree
import SuffixTree.Harness

/-!
# SuffixTree.Test

Executable conformance tests. `#guard` assertions run against the
curator's reference implementations exposed via `canonical.suffixTree.*`,
the `RepoImpl` instance that wires the `Impl/SuffixTree.lean` reference
defs into the bundle. Before the LLM sees the benchmark, the pipeline
replaces marker contents with `sorry` — these guards catch regressions
in the reference impls themselves.

Coverage: every API has at least three `#guard` assertions reaching it
through `canonical.suffixTree`. For APIs whose externally observable
state is only reachable via another API (e.g. `mk` and `buildSuffixTree`
expose their effect through `search`), tests compose the APIs so each
is on the critical path of at least three guards.

DO NOT MODIFY — infrastructure.
-/

-- ── canonical.suffixTree.mk ──────────────────────────────────────────
-- mk stores the original text and creates an empty root (no suffixes
-- are inserted until buildSuffixTree runs).
#guard (canonical.suffixTree.mk "abc").text == "abc"
#guard canonical.suffixTree.search (canonical.suffixTree.mk "banana") "" == true
#guard canonical.suffixTree.search (canonical.suffixTree.mk "banana") "b" == false

-- ── canonical.suffixTree.buildSuffixTree ─────────────────────────────
-- After build, every suffix of the text is present; non-suffix
-- substrings of the text are also reachable along trie paths.
#guard canonical.suffixTree.search
    (canonical.suffixTree.buildSuffixTree (canonical.suffixTree.mk "banana")) "ban" == true
#guard canonical.suffixTree.search
    (canonical.suffixTree.buildSuffixTree (canonical.suffixTree.mk "banana")) "nana" == true
#guard canonical.suffixTree.search
    (canonical.suffixTree.buildSuffixTree (canonical.suffixTree.mk "")) "" == true

-- ── canonical.suffixTree.addSuffix ───────────────────────────────────
-- Manually inserting a suffix makes it searchable; suffixes added to
-- a fresh `mk` tree are reachable, and previously-added paths persist.
#guard canonical.suffixTree.search
    (canonical.suffixTree.addSuffix (canonical.suffixTree.mk "abc") "abc" 0) "abc" == true
#guard canonical.suffixTree.search
    (canonical.suffixTree.addSuffix (canonical.suffixTree.buildSuffixTree (canonical.suffixTree.mk "ban")) "ana" 1)
    "ana" == true
#guard canonical.suffixTree.search
    (canonical.suffixTree.addSuffix (canonical.suffixTree.mk "xyz") "z" 2) "z" == true

-- ── canonical.suffixTree.search ──────────────────────────────────────
-- Positive and negative pattern queries on a built tree.
#guard canonical.suffixTree.search
    (canonical.suffixTree.buildSuffixTree (canonical.suffixTree.mk "mississippi")) "issi" == true
#guard canonical.suffixTree.search
    (canonical.suffixTree.buildSuffixTree (canonical.suffixTree.mk "mississippi")) "sip" == true
#guard canonical.suffixTree.search
    (canonical.suffixTree.buildSuffixTree (canonical.suffixTree.mk "mississippi")) "pipi" == false
#guard canonical.suffixTree.search
    (canonical.suffixTree.buildSuffixTree (canonical.suffixTree.mk "ban")) "ana" == false
