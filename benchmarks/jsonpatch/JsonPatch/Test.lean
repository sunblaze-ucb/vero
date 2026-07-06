import JsonPatch.Impl.Pointer
import JsonPatch.Impl.Patch

/-!
# JsonPatch.Test

Executable conformance tests. Each `#guard` runs the curator's reference
implementation (`Impl/Pointer.lean`, `Impl/Patch.lean`) and is checked against
the upstream libraries `jsonpointer` 3.0.0 (`resolve_pointer`, `escape`,
`unescape`) and `jsonpatch` 1.33 (`apply_patch`) — every expected value below
was captured from those libraries on the corresponding input.

JSON is modelled by the inductive `Json` (integer `num`, association-list
`obj`); pointers are reference-token lists (already-unescaped parts). A patch
operation carries its path(s) as token lists, so `applyOp`/`apply` are pure
structural functions returning `Option Json` (`none` = conflict / test failure,
matching `JsonPatchConflict` / `JsonPatchTestFailed`).

DO NOT MODIFY — infrastructure.
-/

open JsonPatch

private def n (i : Int) : Json := .num i
private def doc1 : Json := .obj [("foo", .obj [("bar", .arr [n 10, n 20, n 30])]), ("x", n 1)]

-- ── escape (RFC 6901 token escape: ~ ↦ ~0 then / ↦ ~1) ───────────
#guard escape "~/a/b" == "~0~1a~1b"
#guard escape "~" == "~0"
#guard escape "/~" == "~1~0"
#guard escape "a/b~c" == "a~1b~0c"
#guard escape "plain" == "plain"

-- ── unescape (~1 ↦ / then ~0 ↦ ~ — the asymmetric order) ─────────
#guard unescape "~1" == "/"
#guard unescape "~0" == "~"
#guard unescape "~01" == "~1"          -- trap: ~0 expands first here, leaving 1
#guard unescape "~10" == "/0"          -- trap: ~1 expands first here, leaving 0
#guard unescape "~0~1" == "~/"
-- round-trip on tricky strings
#guard unescape (escape "~/a~1b/c") == "~/a~1b/c"
#guard unescape (escape "~01~10") == "~01~10"

-- ── resolve (reference-token walk; none on miss/oob) ─────────────
#guard resolve doc1 [] == some doc1
#guard resolve doc1 ["foo", "bar", "1"] == some (n 20)
#guard resolve doc1 ["x"] == some (n 1)
#guard resolve doc1 ["foo", "bar", "9"] == none          -- index out of bounds
#guard resolve doc1 ["nope"] == none                     -- missing member
#guard resolve doc1 ["foo", "bar", "-"] == none          -- end-of-list not resolvable

-- ── applyOp: add (insert-or-overwrite / array insert / append) ───
#guard applyOp (.add ["b"] (n 2)) (.obj [("a", n 1)]) == some (.obj [("a", n 1), ("b", n 2)])
#guard applyOp (.add ["a"] (n 9)) (.obj [("a", n 1)]) == some (.obj [("a", n 9)])          -- overwrite in place
#guard applyOp (.add ["1"] (n 99)) (.arr [n 0, n 1, n 2]) == some (.arr [n 0, n 99, n 1, n 2])
#guard applyOp (.add ["-"] (n 9)) (.arr [n 0, n 1]) == some (.arr [n 0, n 1, n 9])          -- append
#guard applyOp (.add ["5"] (n 9)) (.arr [n 0, n 1]) == none                                 -- out of range
#guard applyOp (.add ["foo", "b"] (n 2)) (.obj [("foo", .obj [("a", n 1)])])
        == some (.obj [("foo", .obj [("a", n 1), ("b", n 2)])])                             -- nested

-- ── applyOp: remove (delete existing, conflict on absent) ────────
#guard applyOp (.remove ["a"]) (.obj [("a", n 1), ("b", n 2)]) == some (.obj [("b", n 2)])
#guard applyOp (.remove ["z"]) (.obj [("a", n 1)]) == none                                   -- absent
#guard applyOp (.remove ["1"]) (.arr [n 0, n 1, n 2]) == some (.arr [n 0, n 2])

-- ── applyOp: replace (overwrite existing, conflict on absent, root) ──
#guard applyOp (.replace ["a"] (n 5)) (.obj [("a", n 1)]) == some (.obj [("a", n 5)])
#guard applyOp (.replace ["z"] (n 5)) (.obj [("a", n 1)]) == none                            -- absent
#guard applyOp (.replace [] (.obj [("x", n 2)])) (.obj [("a", n 1)]) == some (.obj [("x", n 2)]) -- root

-- ── applyOp: move (= remove-then-add; no-op when from = path) ─────
#guard applyOp (.move ["a"] ["b"]) (.obj [("a", n 1)]) == some (.obj [("b", n 1)])
#guard applyOp (.move ["a"] ["a"]) (.obj [("a", n 1)]) == some (.obj [("a", n 1)])           -- no-op
#guard applyOp (.move ["a"] ["d"]) (.obj [("a", n 1), ("b", n 2), ("c", n 3)])
        == some (.obj [("b", n 2), ("c", n 3), ("d", n 1)])                                  -- removed then appended

-- ── applyOp: copy (add source value, keep source) ───────────────
#guard applyOp (.copy ["a"] ["b"]) (.obj [("a", n 1)]) == some (.obj [("a", n 1), ("b", n 1)])
#guard applyOp (.copy ["a"] ["a"]) (.obj [("a", n 1)]) == some (.obj [("a", n 1)])
#guard applyOp (.copy ["z"] ["b"]) (.obj [("a", n 1)]) == none                               -- missing source

-- ── applyOp: test (identity when value matches, else conflict) ───
#guard applyOp (.test ["a"] (n 1)) (.obj [("a", n 1)]) == some (.obj [("a", n 1)])
#guard applyOp (.test ["a"] (n 2)) (.obj [("a", n 1)]) == none                               -- mismatch
#guard applyOp (.test ["foo", "bar"] (.arr [n 10, n 20, n 30])) doc1 == some doc1            -- deep equality

-- ── root (empty pointer) semantics ──────────────────────────────
#guard applyOp (.replace [] (.obj [("x", n 2)])) (.obj [("a", n 1)]) == some (.obj [("x", n 2)]) -- replace root
#guard applyOp (.add [] (.obj [("x", n 2)])) (.obj [("a", n 1)]) == some (.obj [("x", n 2)])     -- add root (obj → replace)
#guard applyOp (.add [] (n 9)) (.arr [n 0]) == none                                              -- add root on array conflicts
#guard applyOp (.remove []) (.obj [("a", n 1)]) == none                                          -- remove root conflicts
#guard applyOp (.move [] ["b"]) (.obj [("a", n 1)]) == none                                      -- move from root conflicts
#guard applyOp (.copy [] ["b"]) (.obj [("a", n 1)]) == none                                      -- copy from root conflicts
#guard applyOp (.move ["a"] []) (.obj [("a", .obj [("b", n 1)])]) == some (.obj [("b", n 1)])    -- move to root
#guard applyOp (.move [] []) (.obj [("a", n 1)]) == none                                         -- root→root conflicts (source read fails)

-- ── apply: op-list fold (identity, composition, short-circuit) ───
#guard apply [] doc1 == some doc1                                                            -- identity
#guard apply [.add ["b"] (n 2), .add ["c"] (n 3)] (.obj [("a", n 1)])
        == some (.obj [("a", n 1), ("b", n 2), ("c", n 3)])                                  -- composition
#guard apply [.remove ["z"], .add ["b"] (n 2)] (.obj [("a", n 1)]) == none                   -- head conflict aborts
-- composition = sequential apply
#guard (apply [.add ["b"] (n 2)] (.obj [("a", n 1)]) >>= apply [.add ["c"] (n 3)])
        == apply ([.add ["b"] (n 2)] ++ [.add ["c"] (n 3)]) (.obj [("a", n 1)])
