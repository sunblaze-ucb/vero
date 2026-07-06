import Pygtrie.Impl.Trie

/-!
# Pygtrie.Test

Executable conformance tests. `#guard` assertions run against the
curator's reference implementations inside the `code` markers in
`Impl/Trie.lean`.

DO NOT MODIFY — infrastructure.
-/

open Pygtrie

-- ── set / get / hasKey ─────────────────────────────────────────
#guard get [1, 2] (set [1, 2] 9 []) == some 9
#guard get [1, 2] (set [1, 3] 9 []) == none
#guard get [1] (set [1] 5 (set [1] 4 [])) == some 5      -- overwrite
#guard hasKey [1, 2] (set [1, 2] 9 []) == true
#guard hasKey [7] [] == false

-- ── prefixes ───────────────────────────────────────────────────
-- stored keys [1], [1,2] are both prefixes of [1,2,3]; [4] is not.
#guard prefixes [1, 2, 3] (set [4] 0 (set [1, 2] 0 (set [1] 0 []))) == [[1, 2], [1]]
#guard prefixes [9] (set [1] 0 []) == []
#guard prefixes [] (set [1] 0 []) == []                  -- empty query: no nonempty prefix
#guard ([] : Key).isPrefixOf [5, 6] == true              -- empty key prefixes anything

-- ── longestPrefix: returns the LONGEST stored prefix ───────────
-- both [1] and [1,2] match [1,2,3]; the longer one wins.
#guard longestPrefix [1, 2, 3] (set [1, 2] 0 (set [1] 0 [])) == some [1, 2]
#guard longestPrefix [1, 2, 3] (set [1] 0 (set [1, 2] 0 [])) == some [1, 2]  -- order-independent
#guard longestPrefix [9, 9] (set [1] 0 []) == none       -- no stored key is a prefix
#guard longestPrefix [5] [] == none                      -- empty trie
#guard longestPrefix [1] (set [] 0 (set [1] 0 [])) == some [1]  -- [] and [1] match; [1] longer
