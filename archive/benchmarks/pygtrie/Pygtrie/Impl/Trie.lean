-- !benchmark @start imports
-- !benchmark @end imports

/-!
# Pygtrie.Impl.Trie

Prefix-tree (trie) operations. The headline operation is
`longestPrefix`: given a query key, return the longest stored key that
is a prefix of the query.

Keys are sequences (`List Nat`). The trie is modelled as an association
list of `(key, value)` entries; observable behaviour is pinned by the
specs.

Types and signatures are fixed vocabulary (DO NOT MODIFY). Function
bodies inside the `code` markers are what the benchmark asks you to
write.
-/

-- ── Core data types (DO NOT MODIFY) ──────────────────────────

/-- A trie key is a sequence of symbols. -/
abbrev Key := List Nat

/-- The trie, modelled as an association list of `(key, value)` entries. -/
abbrev Trie := List (Key × Nat)

namespace Pygtrie

-- ── API signatures (DO NOT MODIFY) ───────────────────────────

/-- `set k v t`: associate value `v` with key `k` (overwriting any
    existing binding for `k`). -/
abbrev SetSig            := Key → Nat → Trie → Trie

/-- `get k t`: the value bound to `k`, or `none` if `k` is not stored. -/
abbrev GetSig            := Key → Trie → Option Nat

/-- `hasKey k t`: whether key `k` has a stored value. -/
abbrev HasKeySig         := Key → Trie → Bool

/-- `longestPrefix q t`: the longest stored key that is a prefix of the
    query `q`, or `none` if no stored key is a prefix of `q`. -/
abbrev LongestPrefixSig  := Key → Trie → Option Key

/-- `prefixes q t`: every stored key that is a prefix of the query `q`. -/
abbrev PrefixesSig       := Key → Trie → List Key

end Pygtrie

-- !benchmark @start global_aux
-- !benchmark @end global_aux

-- !benchmark @start code_aux def=set
-- !benchmark @end code_aux def=set

def Pygtrie.set : Pygtrie.SetSig :=
-- !benchmark @start code def=set
  fun k v t => (k, v) :: t.filter (fun p => !(p.1 == k))
-- !benchmark @end code def=set

-- !benchmark @start code_aux def=get
-- !benchmark @end code_aux def=get

def Pygtrie.get : Pygtrie.GetSig :=
-- !benchmark @start code def=get
  fun k t => (t.find? (fun p => p.1 == k)).map Prod.snd
-- !benchmark @end code def=get

-- !benchmark @start code_aux def=hasKey
-- !benchmark @end code_aux def=hasKey

def Pygtrie.hasKey : Pygtrie.HasKeySig :=
-- !benchmark @start code def=hasKey
  fun k t => t.any (fun p => p.1 == k)
-- !benchmark @end code def=hasKey

-- !benchmark @start code_aux def=longestPrefix
-- !benchmark @end code_aux def=longestPrefix

def Pygtrie.longestPrefix : Pygtrie.LongestPrefixSig :=
-- !benchmark @start code def=longestPrefix
  fun q t =>
    ((t.map Prod.fst).filter (fun k => k.isPrefixOf q)).foldl
      (fun acc k =>
        match acc with
        | none => some k
        | some best => if best.length < k.length then some k else some best)
      none
-- !benchmark @end code def=longestPrefix

-- !benchmark @start code_aux def=prefixes
-- !benchmark @end code_aux def=prefixes

def Pygtrie.prefixes : Pygtrie.PrefixesSig :=
-- !benchmark @start code def=prefixes
  fun q t => (t.map Prod.fst).filter (fun k => k.isPrefixOf q)
-- !benchmark @end code def=prefixes
