import Cachetools.Impl.Lru

/-!
# Cachetools.Test

Executable conformance tests. `#guard` assertions run against the
curator's reference implementations inside the `code` markers in
`Impl/Lru.lean`.

DO NOT MODIFY — infrastructure.
-/

open Cachetools

-- ── empty / contains / put ─────────────────────────────────────
#guard (empty 3).order == []
#guard contains (empty 3) 1 == false
#guard contains (put (empty 3) 1) 1 == true
#guard (put (empty 3) 1).order == [1]

-- ── put: MRU is the head; updates move to front ────────────────
#guard (put (put (empty 3) 1) 2).order == [2, 1]
#guard (put (put (put (empty 3) 1) 2) 1).order == [1, 2]   -- touch 1 again → MRU

-- ── get: hit moves to front, miss is a no-op ───────────────────
#guard (get (put (put (empty 3) 1) 2) 1).order == [1, 2]   -- hit: 1 to front
#guard (get (put (empty 3) 1) 9) == (put (empty 3) 1)      -- miss: unchanged
#guard (get (empty 3) 5).order == []                       -- miss on empty

-- ── eviction: full cache drops the LRU (last) key ──────────────
-- capacity 2, insert 1 then 2 → order [2,1]; inserting 3 evicts LRU 1.
#guard (put (put (put (empty 2) 1) 2) 3).order == [3, 2]
#guard contains (put (put (put (empty 2) 1) 2) 3) 1 == false   -- 1 was the LRU
#guard contains (put (put (put (empty 2) 1) 2) 3) 2 == true    -- 2 preserved
-- touching 1 before the insert makes 2 the LRU instead.
#guard (put (get (put (put (empty 2) 1) 2) 1) 3).order == [3, 1]
#guard contains (put (get (put (put (empty 2) 1) 2) 1) 3) 2 == false  -- now 2 is LRU

-- ── lruKey: the eviction victim is the last element ────────────
#guard lruKey (empty 3) == none
#guard lruKey (put (put (empty 3) 1) 2) == some 1          -- 1 is LRU
#guard lruKey (put (empty 3) 7) == some 7
