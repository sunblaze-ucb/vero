import Pygtrie.Harness

/-!
# Pygtrie.Spec.Trie

Specifications for the trie operations. Each `spec_*` is a property
over an arbitrary `impl : RepoImpl`; the API is always reached through
`impl.pygtrie.<fn>`.

The longest-prefix-match specs use the witness ∧ maximality ∧
completeness pattern, anchored on the frozen `List.isPrefixOf`.

DO NOT MODIFY.
-/

-- ── set / get observer laws ────────────────────────────────────

/-- Read-after-write: getting a key just set returns the set value. -/
def spec_get_set_eq (impl : RepoImpl) : Prop :=
  ∀ (k : Key) (v : Nat) (t : Trie),
    impl.pygtrie.get k (impl.pygtrie.set k v t) = some v

/-- Frame: setting one key does not affect lookups of other keys. -/
def spec_get_set_ne (impl : RepoImpl) : Prop :=
  ∀ (k k' : Key) (v : Nat) (t : Trie),
    k ≠ k' →
    impl.pygtrie.get k' (impl.pygtrie.set k v t) = impl.pygtrie.get k' t

/-- `hasKey` agrees with `get`: a key is present iff its lookup succeeds. -/
def spec_hasKey_iff_get (impl : RepoImpl) : Prop :=
  ∀ (k : Key) (t : Trie),
    impl.pygtrie.hasKey k t = true ↔ (impl.pygtrie.get k t).isSome = true

-- ── prefixes: canonical set characterization ───────────────────

/-- `prefixes q t` contains exactly the stored keys that are prefixes
    of the query. Both directions, so the output set is pinned. -/
def spec_prefixes_canonical (impl : RepoImpl) : Prop :=
  ∀ (q : Key) (t : Trie) (k : Key),
    k ∈ impl.pygtrie.prefixes q t ↔
      (k ∈ (t.map Prod.fst) ∧ k.isPrefixOf q = true)

-- ── longestPrefix: witness ∧ maximality ∧ completeness ─────────

/-- Witness (full bidirectional characterization). `longestPrefix q t`
    returns `k` *iff* `k` is a stored key, a prefix of `q`, and one that
    every stored prefix of `q` is itself a prefix of. Stated as an `↔`, so
    it is the operation's defining property: any implementation returning a
    different key — or `none` when such a key exists — is wrong. -/
def spec_longestPrefix_witness (impl : RepoImpl) : Prop :=
  ∀ (q : Key) (t : Trie) (k : Key),
    impl.pygtrie.longestPrefix q t = some k ↔
      (k ∈ (t.map Prod.fst) ∧ k.isPrefixOf q = true ∧
        ∀ (k' : Key), k' ∈ (t.map Prod.fst) → k'.isPrefixOf q = true →
          k'.isPrefixOf k = true)

/-- Maximality: the returned prefix is at least as long as every stored
    key that is a prefix of the query. -/
def spec_longestPrefix_maximal (impl : RepoImpl) : Prop :=
  ∀ (q : Key) (t : Trie) (k : Key),
    impl.pygtrie.longestPrefix q t = some k →
      ∀ (k' : Key), k' ∈ (t.map Prod.fst) → k'.isPrefixOf q = true →
        k'.length ≤ k.length

/-- Completeness (both directions): `longestPrefix q t` is `none`
    *exactly* when no stored key is a prefix of the query. The forward
    direction rules out a spurious `none`; the backward direction rules
    out a spurious match when the query has no stored prefix. -/
def spec_longestPrefix_complete (impl : RepoImpl) : Prop :=
  ∀ (q : Key) (t : Trie),
    impl.pygtrie.longestPrefix q t = none ↔
      ∀ (k : Key), k ∈ (t.map Prod.fst) → k.isPrefixOf q = false

-- ── empty-trie defining equations ──────────────────────────────

/-- `get` on the empty trie always misses. -/
def spec_get_empty (impl : RepoImpl) : Prop :=
  ∀ (k : Key), impl.pygtrie.get k [] = none

/-- `hasKey` on the empty trie is always `false`. -/
def spec_hasKey_empty (impl : RepoImpl) : Prop :=
  ∀ (k : Key), impl.pygtrie.hasKey k [] = false

/-- No key is a prefix-match in the empty trie. -/
def spec_prefixes_empty_trie (impl : RepoImpl) : Prop :=
  ∀ (q : Key), impl.pygtrie.prefixes q [] = []

/-- `longestPrefix` on the empty trie is always `none`. -/
def spec_longestPrefix_empty_trie (impl : RepoImpl) : Prop :=
  ∀ (q : Key), impl.pygtrie.longestPrefix q [] = none

-- ── empty-query boundary ───────────────────────────────────────

/-- With the empty query, the only stored key that is a prefix is the
    empty key itself: `k ∈ prefixes [] t ↔ k` is stored and `k = []`. -/
def spec_prefixes_empty_query (impl : RepoImpl) : Prop :=
  ∀ (t : Trie) (k : Key),
    k ∈ impl.pygtrie.prefixes [] t ↔ (k ∈ (t.map Prod.fst) ∧ k = [])

-- ── set / get / hasKey algebra ─────────────────────────────────

/-- Last write wins (structural): `set k v (set k w t)` and `set k v t`
    are the *same trie*, not merely indistinguishable under `get k`. The
    intermediate value `w` leaves no trace. -/
def spec_set_overwrite (impl : RepoImpl) : Prop :=
  ∀ (k : Key) (v w : Nat) (t : Trie),
    impl.pygtrie.set k v (impl.pygtrie.set k w t) = impl.pygtrie.set k v t

/-- After setting `k`, the key is present. -/
def spec_hasKey_set_eq (impl : RepoImpl) : Prop :=
  ∀ (k : Key) (v : Nat) (t : Trie),
    impl.pygtrie.hasKey k (impl.pygtrie.set k v t) = true

/-- Frame for `hasKey`: setting one key does not change membership of a
    different key. -/
def spec_hasKey_set_ne (impl : RepoImpl) : Prop :=
  ∀ (k k' : Key) (v : Nat) (t : Trie),
    k ≠ k' →
    impl.pygtrie.hasKey k' (impl.pygtrie.set k v t) = impl.pygtrie.hasKey k' t

-- ── prefixes structural invariants ─────────────────────────────

/-- Soundness invariant: every element returned by `prefixes` is a
    stored key and a genuine prefix of the query. -/
def spec_prefixes_sound (impl : RepoImpl) : Prop :=
  ∀ (q : Key) (t : Trie),
    ∀ k ∈ impl.pygtrie.prefixes q t,
      k ∈ (t.map Prod.fst) ∧ k.isPrefixOf q = true

/-- `prefixes` never returns more entries than the trie has. -/
def spec_prefixes_length_le (impl : RepoImpl) : Prop :=
  ∀ (q : Key) (t : Trie),
    (impl.pygtrie.prefixes q t).length ≤ t.length

-- ── prefixes ↔ longestPrefix relationship ──────────────────────

/-- `longestPrefix` fails exactly when `prefixes` is empty. -/
def spec_longestPrefix_none_iff_prefixes_nil (impl : RepoImpl) : Prop :=
  ∀ (q : Key) (t : Trie),
    impl.pygtrie.longestPrefix q t = none ↔ impl.pygtrie.prefixes q t = []

/-- A returned longest prefix is one of the `prefixes` entries. -/
def spec_longestPrefix_mem_prefixes (impl : RepoImpl) : Prop :=
  ∀ (q : Key) (t : Trie) (k : Key),
    impl.pygtrie.longestPrefix q t = some k →
      k ∈ impl.pygtrie.prefixes q t

/-- The longest prefix dominates the whole `prefixes` list: it is at
    least as long as every prefix-match. -/
def spec_longestPrefix_dominates_prefixes (impl : RepoImpl) : Prop :=
  ∀ (q : Key) (t : Trie) (k : Key),
    impl.pygtrie.longestPrefix q t = some k →
      ∀ k' ∈ impl.pygtrie.prefixes q t, k'.length ≤ k.length

-- ── frozen vocabulary for the argmax / composition specs ───────

/-- `lpStep acc k`: a longest-wins fold step over candidate keys. A new
    candidate `k` replaces the running best only when it is *strictly*
    longer, so on a length tie the *earlier* key is retained. Frozen
    helper — references only `Key`, never `impl`. -/
def lpStep (acc : Option Key) (k : Key) : Option Key :=
  match acc with
  | none => some k
  | some best => if best.length < k.length then some k else some best

/-- `setManyWith f entries t`: fold the per-step function `f` over a list
    of `(key, value)` pairs (a bulk insertion). Frozen helper — `f` is
    supplied by the spec via `impl`, so `setManyWith` never mentions
    `impl` directly. -/
def setManyWith (f : Key → Nat → Trie → Trie)
    (entries : List (Key × Nat)) (t : Trie) : Trie :=
  entries.foldl (fun acc kv => f kv.1 kv.2 acc) t

/-- `IsFirstMaximal ks k`: `k` is the *first longest* element of `ks` —
    a split `ks = pre ++ k :: suf` with every element of `pre` strictly
    shorter than `k` and every element of `suf` no longer. Pins both
    maximality of `k` and the left-to-right tie-break; exactly one such
    `k` exists for a given `ks`. Frozen helper. -/
def IsFirstMaximal (ks : List Key) (k : Key) : Prop :=
  ∃ pre suf, ks = pre ++ k :: suf ∧
    (∀ z ∈ pre, z.length < k.length) ∧
    (∀ z ∈ suf, z.length ≤ k.length)

-- ── frozen vocabulary for the batch-insertion specs ────────────

/-- `lastValue k entries`: the value of the *last* `(k, _)` pair in
    `entries`, scanning left-to-right (so a later binding shadows an
    earlier one), or `none` if `k` never appears. Frozen helper —
    references only the entry list, never `impl`. -/
def lastValue (k : Key) : List (Key × Nat) → Option Nat
  | [] => none
  | (k', v') :: rest =>
    match lastValue k rest with
    | some v => some v
    | none => if k' = k then some v' else none

-- ── batch insertion (`setMany`): the op-sequence laws ──────────
-- `entries.foldl (fun acc kv => impl.pygtrie.set kv.1 kv.2 acc) t`
-- threads `set` over a list of `(key, value)` pairs. These specs pin the
-- *cumulative* behaviour of a sequence of writes, including how a later
-- write shadows an earlier one.

/-- Last-write-wins over a batch: after folding `set` across `entries`
    (starting from `t`), `get k` returns the value of the *last*
    `(k, _)` pair in `entries` (captured by the frozen `lastValue`),
    falling back to the prior value in `t` when `k` is absent. -/
def spec_get_setMany (impl : RepoImpl) : Prop :=
  ∀ (k : Key) (entries : List (Key × Nat)) (t : Trie),
    impl.pygtrie.get k
        (entries.foldl (fun acc kv => impl.pygtrie.set kv.1 kv.2 acc) t)
      = (match lastValue k entries with
         | some v => some v
         | none => impl.pygtrie.get k t)

/-- Batch-built `prefixes`: building a trie from `entries` (over the
    empty trie) and querying `prefixes q` yields exactly the entry keys
    that are prefixes of `q`. Membership is pinned in both directions. -/
def spec_prefixes_setMany_canonical (impl : RepoImpl) : Prop :=
  ∀ (q : Key) (entries : List (Key × Nat)) (k : Key),
    k ∈ impl.pygtrie.prefixes q
          (entries.foldl (fun acc kv => impl.pygtrie.set kv.1 kv.2 acc) [])
      ↔ (k ∈ (entries.map Prod.fst) ∧ k.isPrefixOf q = true)

/-- Batch-built `longestPrefix` (witness ∧ maximality, **both directions**):
    for a trie built from `entries`, the longest prefix of `q` is `k`
    *exactly when* `k` is one of the entry keys, is a prefix of `q`, and is at
    least as long as every entry key that is a prefix of `q`. Stated as an
    `↔`, so it is the defining property over the bulk-load; any implementation
    returning a different match — or `none` when a maximal entry-key prefix
    exists — is wrong. -/
def spec_longestPrefix_setMany_witness (impl : RepoImpl) : Prop :=
  ∀ (q : Key) (entries : List (Key × Nat)) (k : Key),
    impl.pygtrie.longestPrefix q
        (entries.foldl (fun acc kv => impl.pygtrie.set kv.1 kv.2 acc) []) = some k ↔
      ((k ∈ (entries.map Prod.fst) ∧ k.isPrefixOf q = true) ∧
       (∀ k', k' ∈ (entries.map Prod.fst) → k'.isPrefixOf q = true →
        k'.length ≤ k.length))

/-- Batch-built `longestPrefix` (completeness): the query has no match
    in a trie built from `entries` only when no entry key is a prefix of
    `q`. -/
def spec_longestPrefix_setMany_complete (impl : RepoImpl) : Prop :=
  ∀ (q : Key) (entries : List (Key × Nat)),
    impl.pygtrie.longestPrefix q
        (entries.foldl (fun acc kv => impl.pygtrie.set kv.1 kv.2 acc) []) = none →
      ∀ k, k ∈ (entries.map Prod.fst) → k.isPrefixOf q = false

-- ── monotonicity of the longest-prefix match under insertion ───

/-- Inserting a key can only *extend* the longest-prefix match along the
    prefix chain: if `longestPrefix q t = some a`, then
    `longestPrefix q (set k v t) = some b` for some `b` with `a` a *prefix*
    of `b`. Strictly stronger than a length bound — the two answers lie on a
    single prefix chain. -/
def spec_longestPrefix_monotone (impl : RepoImpl) : Prop :=
  ∀ (q : Key) (k : Key) (v : Nat) (t : Trie) (a : Key),
    impl.pygtrie.longestPrefix q t = some a →
      ∃ b, impl.pygtrie.longestPrefix q (impl.pygtrie.set k v t) = some b ∧
        a.isPrefixOf b = true

-- ── idempotent re-set: observationally a no-op ─────────────────

/-- Re-setting a key to the same value is observationally idempotent:
    `set k v (set k v t)` and `set k v t` agree on *every* observation
    (`get`, `hasKey`, `prefixes`, `longestPrefix`) for *every* query.
    Stated extensionally over all four observers and all queries. -/
def spec_set_idempotent_obs (impl : RepoImpl) : Prop :=
  ∀ (k : Key) (v : Nat) (t : Trie),
    (∀ q, impl.pygtrie.get q (impl.pygtrie.set k v (impl.pygtrie.set k v t))
            = impl.pygtrie.get q (impl.pygtrie.set k v t)) ∧
    (∀ q, impl.pygtrie.hasKey q (impl.pygtrie.set k v (impl.pygtrie.set k v t))
            = impl.pygtrie.hasKey q (impl.pygtrie.set k v t)) ∧
    (∀ q, impl.pygtrie.prefixes q (impl.pygtrie.set k v (impl.pygtrie.set k v t))
            = impl.pygtrie.prefixes q (impl.pygtrie.set k v t)) ∧
    (∀ q, impl.pygtrie.longestPrefix q (impl.pygtrie.set k v (impl.pygtrie.set k v t))
            = impl.pygtrie.longestPrefix q (impl.pygtrie.set k v t))

-- ── prefix-match length is bounded by the query ────────────────

/-- Every prefix-match is no longer than the query itself: each key
    returned by `prefixes q t` has length ≤ `q.length`, since a prefix
    cannot exceed the sequence it prefixes. -/
def spec_prefixes_length_le_query (impl : RepoImpl) : Prop :=
  ∀ (q : Key) (t : Trie),
    ∀ k ∈ impl.pygtrie.prefixes q t, k.length ≤ q.length

-- ════════════════════════════════════════════════════════════════
-- Deeper laws — argmax / permutation / counting invariants of the
-- longest-prefix match and the prefix-match list.
-- ════════════════════════════════════════════════════════════════

-- ── longestPrefix as a global argmax with canonical tie-break ──────

/-- **Global argmax characterization (full iff, with tie-break).**
    `longestPrefix q t` returns `k` *iff* `k` is the `IsFirstMaximal`
    element of the prefix-match list `prefixes q t` — the first-longest
    stored prefix of `q`. Pins not just *which length* the answer has, but
    *which key* is returned on a tie (the earliest in trie order). The
    bidirectional `↔` leaves no other key able to satisfy it. -/
def spec_longestPrefix_global_argmax_iff (impl : RepoImpl) : Prop :=
  ∀ (q : Key) (t : Trie) (k : Key),
    impl.pygtrie.longestPrefix q t = some k ↔
      IsFirstMaximal (impl.pygtrie.prefixes q t) k

/-- **Permutation invariance of `longestPrefix`.** Reordering the trie's
    entries never changes the longest-prefix match: if `t₂` is a
    permutation of `t₁` then `longestPrefix q t₁ = longestPrefix q t₂`
    for every query. The answer depends on *which* keys are stored, not on
    insertion order. -/
def spec_longestPrefix_perm_invariant (impl : RepoImpl) : Prop :=
  ∀ (q : Key) (t₁ t₂ : Trie),
    t₁.Perm t₂ →
    impl.pygtrie.longestPrefix q t₁ = impl.pygtrie.longestPrefix q t₂

/-- **Uniqueness of equal-length prefix-matches.** Any two prefix-matches
    of the query that have the same length are the *same key*. Two distinct
    stored keys can never tie for the same prefix length of a query. -/
def spec_prefixes_unique_maximal (impl : RepoImpl) : Prop :=
  ∀ (q : Key) (t : Trie) (k₁ k₂ : Key),
    k₁ ∈ impl.pygtrie.prefixes q t → k₂ ∈ impl.pygtrie.prefixes q t →
    k₁.length = k₂.length → k₁ = k₂

/-- **`longestPrefix` is the argmax of `prefixes` (two-API composition).**
    The longest-prefix match equals folding the frozen step `lpStep` over
    the entire `prefixes q t` list — the two public APIs compute a
    *consistent* maximum. -/
def spec_longestPrefix_eq_prefixes_argmax (impl : RepoImpl) : Prop :=
  ∀ (q : Key) (t : Trie),
    impl.pygtrie.longestPrefix q t = (impl.pygtrie.prefixes q t).foldl lpStep none

-- ── batch insertion: order / last-write characterization ───────────

/-- **Last write wins under append (order-dependence of `setMany`).**
    Folding `set` across `entries ++ [(k, v)]` — ending the batch with a
    write of `k` — always leaves `k` bound to `v`. Only the *last* binding
    per key survives. -/
def spec_get_setMany_append_last (impl : RepoImpl) : Prop :=
  ∀ (k : Key) (v : Nat) (entries : List (Key × Nat)) (t : Trie),
    impl.pygtrie.get k
        (setManyWith impl.pygtrie.set (entries ++ [(k, v)]) t) = some v

-- ── disjoint-key set commutation: full observational equivalence ───

/-- **Disjoint `set`s commute, observed by *every* API on *every* query.**
    For distinct keys `k₁ ≠ k₂`, the two orders
    `set k₁ v₁ (set k₂ v₂ t)` and `set k₂ v₂ (set k₁ v₁ t)` are
    observationally identical under `get`, `hasKey`, `prefixes` *and*
    `longestPrefix`, for all queries. -/
def spec_set_commute_disjoint_obs (impl : RepoImpl) : Prop :=
  ∀ (k₁ k₂ : Key) (v₁ v₂ : Nat) (t : Trie),
    k₁ ≠ k₂ →
    (∀ q, impl.pygtrie.get q (impl.pygtrie.set k₁ v₁ (impl.pygtrie.set k₂ v₂ t))
            = impl.pygtrie.get q (impl.pygtrie.set k₂ v₂ (impl.pygtrie.set k₁ v₁ t))) ∧
    (∀ q, impl.pygtrie.hasKey q (impl.pygtrie.set k₁ v₁ (impl.pygtrie.set k₂ v₂ t))
            = impl.pygtrie.hasKey q (impl.pygtrie.set k₂ v₂ (impl.pygtrie.set k₁ v₁ t))) ∧
    (∀ q, impl.pygtrie.prefixes q (impl.pygtrie.set k₁ v₁ (impl.pygtrie.set k₂ v₂ t))
            |>.Perm (impl.pygtrie.prefixes q (impl.pygtrie.set k₂ v₂ (impl.pygtrie.set k₁ v₁ t)))) ∧
    (∀ q, impl.pygtrie.longestPrefix q (impl.pygtrie.set k₁ v₁ (impl.pygtrie.set k₂ v₂ t))
            = impl.pygtrie.longestPrefix q (impl.pygtrie.set k₂ v₂ (impl.pygtrie.set k₁ v₁ t)))

-- ── prefixes: counting invariant under distinct keys ───────────────

/-- **Distinct-key count bound on `prefixes` (a counting invariant).**
    When the stored keys are pairwise distinct (`(t.map Prod.fst).Nodup`),
    the number of prefix-matches of `q` is at most `q.length + 1`. The
    bound is tight (a chain `[], [a], [a,b], …` realises it). A wrong
    implementation returning spurious or duplicated matches would breach
    it. -/
def spec_prefixes_count_distinct_bound (impl : RepoImpl) : Prop :=
  ∀ (q : Key) (t : Trie),
    (t.map Prod.fst).Nodup →
    (impl.pygtrie.prefixes q t).length ≤ q.length + 1

/-- **Permutation invariance of `prefixes`.** Reordering the trie's
    entries permutes the prefix-match list:
    `t₁.Perm t₂ → (prefixes q t₁).Perm (prefixes q t₂)`. -/
def spec_prefixes_perm_invariant (impl : RepoImpl) : Prop :=
  ∀ (q : Key) (t₁ t₂ : Trie),
    t₁.Perm t₂ →
    (impl.pygtrie.prefixes q t₁).Perm (impl.pygtrie.prefixes q t₂)

-- ════════════════════════════════════════════════════════════════
-- Full-correctness and cross-structure laws — nested quantifier
-- alternation, observational determinism, and laws relating two tries
-- at once (concatenation, get-oracle equivalence).
-- ════════════════════════════════════════════════════════════════

/-- `lpCombine a b`: the option-level "longest wins, first-on-tie"
    combiner for two longest-prefix results. `none` is the identity (an
    empty half contributes nothing); when both halves match, the
    *strictly longer* one wins and a tie keeps the first (`a`). Frozen
    helper — references only `Key`/`Option Key`, never `impl`. -/
def lpCombine (a b : Option Key) : Option Key :=
  match a, b with
  | none, _ => b
  | _, none => a
  | some x, some y => if x.length < y.length then some y else some x

-- ── longestPrefix: the full correctness disjunction ────────────────

/-- **Full functional correctness of `longestPrefix` as one
    quantifier-alternating disjunction.** For every query and trie,
    *either* the match is `none` and no stored key is a prefix of `q`,
    *or* it is `some k` where `k` is a stored key, a prefix of `q`, and
    at least as long as every stored prefix of `q`. The top-level `∨`
    covers both regimes at once, so no implementation can satisfy it by
    handling only one. -/
def spec_longestPrefix_fully_correct (impl : RepoImpl) : Prop :=
  ∀ (q : Key) (t : Trie),
    (impl.pygtrie.longestPrefix q t = none ∧
      ∀ k ∈ (t.map Prod.fst), k.isPrefixOf q = false)
    ∨
    (∃ k, impl.pygtrie.longestPrefix q t = some k ∧
      k ∈ (t.map Prod.fst) ∧ k.isPrefixOf q = true ∧
      ∀ k' ∈ (t.map Prod.fst), k'.isPrefixOf q = true → k'.length ≤ k.length)

-- ── longestPrefix from a get-oracle: observational determinism ─────

/-- **`longestPrefix` is a function of the `get` behaviour alone.** If
    two tries agree on `get` for *every* key, they agree on
    `longestPrefix` for *every* query — observational determinism from a
    one-API oracle. Note `get`-agreement fixes only the keyset as a set,
    not the entry order or multiplicity. -/
def spec_longestPrefix_get_oracle_ext (impl : RepoImpl) : Prop :=
  ∀ (t₁ t₂ : Trie),
    (∀ k, impl.pygtrie.get k t₁ = impl.pygtrie.get k t₂) →
    ∀ q, impl.pygtrie.longestPrefix q t₁ = impl.pygtrie.longestPrefix q t₂

-- ── prefixes: the prefix-chain structural invariant ────────────────

/-- **Prefix-matches of a common query form a chain.** When the stored
    keys are pairwise distinct (`Nodup`), any two entries of
    `prefixes q t` are *comparable*: one is a prefix of the other. -/
def spec_prefixes_chain_nodup (impl : RepoImpl) : Prop :=
  ∀ (q : Key) (t : Trie),
    (t.map Prod.fst).Nodup →
    ∀ k₁ ∈ impl.pygtrie.prefixes q t, ∀ k₂ ∈ impl.pygtrie.prefixes q t,
      k₁.isPrefixOf k₂ = true ∨ k₂.isPrefixOf k₁ = true

-- ── batch insertion ∘ permutation ∘ argmax: a three-way composition ─

/-- **Permutation invariance of the batch-built longest prefix.**
    Building a trie by folding `set` across `entries` and querying
    `longestPrefix q` gives the same answer for any *reordering* of
    `entries`. The load order is not observable. -/
def spec_longestPrefix_setMany_perm_invariant (impl : RepoImpl) : Prop :=
  ∀ (q : Key) (entries₁ entries₂ : List (Key × Nat)),
    entries₁.Perm entries₂ →
    impl.pygtrie.longestPrefix q
        (entries₁.foldl (fun acc kv => impl.pygtrie.set kv.1 kv.2 acc) [])
      = impl.pygtrie.longestPrefix q
          (entries₂.foldl (fun acc kv => impl.pygtrie.set kv.1 kv.2 acc) [])

-- ── two-trie simultaneous law: longestPrefix over a concatenation ──

/-- **`longestPrefix` distributes over trie concatenation via
    `lpCombine`.** The longest prefix of `q` in `t₁ ++ t₂` is the
    `lpCombine` of the longest prefixes in `t₁` and `t₂` separately —
    longest wins, with the *first* trie's match kept on a length tie. -/
def spec_longestPrefix_append_combine (impl : RepoImpl) : Prop :=
  ∀ (q : Key) (t₁ t₂ : Trie),
    impl.pygtrie.longestPrefix q (t₁ ++ t₂)
      = lpCombine (impl.pygtrie.longestPrefix q t₁)
                  (impl.pygtrie.longestPrefix q t₂)

-- ════════════════════════════════════════════════════════════════
-- PREFIX-CHAIN specs — the longest-prefix match is the *prefix-greatest*
-- stored prefix of the query, not merely the *length*-greatest. Each
-- states a clean end-fact about how the match, the enumerated prefixes,
-- and the query relate under the prefix order.
-- ════════════════════════════════════════════════════════════════

/-- **The longest prefix prefix-dominates every stored match.** If
    `longestPrefix q t = some k`, then every stored key that is a prefix of
    `q` is itself a *prefix of `k`*. Strictly stronger than length-maximality:
    the returned key sits at the *top of a prefix chain*, with every other
    matching key lying *along* that chain, not merely being shorter. -/
def spec_longestPrefix_dominates_prefix (impl : RepoImpl) : Prop :=
  ∀ (q : Key) (t : Trie) (k : Key),
    impl.pygtrie.longestPrefix q t = some k →
      ∀ k', k' ∈ (t.map Prod.fst) → k'.isPrefixOf q = true → k'.isPrefixOf k = true

/-- **Every enumerated prefix-match is a prefix of the longest one.** The
    `prefixes`-level twin of the domination law: if `longestPrefix q t =
    some k`, every entry of `prefixes q t` is a prefix of `k`. Pins that
    `prefixes` and `longestPrefix` are not just length-consistent but
    *chain-consistent* — the whole match list nests inside the headline
    answer. -/
def spec_longestPrefix_prefixes_chain (impl : RepoImpl) : Prop :=
  ∀ (q : Key) (t : Trie) (k : Key),
    impl.pygtrie.longestPrefix q t = some k →
      ∀ k' ∈ impl.pygtrie.prefixes q t, k'.isPrefixOf k = true

/-- **The longest prefix is its own longest prefix (self-stability).** If
    `longestPrefix q t = some k`, then querying the trie with `k` itself
    returns `k`: `longestPrefix k t = some k`. The match is a *fixed point*
    of the operation — a clean idempotence-on-the-answer law. -/
def spec_longestPrefix_self_stable (impl : RepoImpl) : Prop :=
  ∀ (q : Key) (t : Trie) (k : Key),
    impl.pygtrie.longestPrefix q t = some k →
      impl.pygtrie.longestPrefix k t = some k

/-- **Querying the answer reproduces the whole result.** If
    `longestPrefix q t = some k`, then `longestPrefix q t = longestPrefix k t`
    — collapsing the query to the matched key leaves the longest-prefix
    answer unchanged. A strictly stronger equality than self-stability (it
    equates the two *calls*, not just their values via `some k`). -/
def spec_longestPrefix_self_query_eq (impl : RepoImpl) : Prop :=
  ∀ (q : Key) (t : Trie) (k : Key),
    impl.pygtrie.longestPrefix q t = some k →
      impl.pygtrie.longestPrefix q t = impl.pygtrie.longestPrefix k t

/-- **Extending the query only adds matches (order-preserving).** If `q₁`
    is a prefix of `q₂`, the prefix-match list of `q₁` is a *sublist* of
    the prefix-match list of `q₂` — every match of `q₁` survives, in the
    same relative order and with multiplicity preserved. Strictly stronger
    than set inclusion: the two lists share a common skeleton, ruling out
    any reordering or duplication. -/
def spec_prefixes_query_monotone (impl : RepoImpl) : Prop :=
  ∀ (q₁ q₂ : Key) (t : Trie),
    q₁.isPrefixOf q₂ = true →
      (impl.pygtrie.prefixes q₁ t).Sublist (impl.pygtrie.prefixes q₂ t)

/-- **The matched key is genuinely stored (value bridge).** If
    `longestPrefix q t = some k`, then `get k t` succeeds
    (`(get k t).isSome`). Bridges the prefix API to the lookup API: the key
    that the longest-prefix search hands back is always a live binding, so
    its associated value can be read. -/
def spec_longestPrefix_value_some (impl : RepoImpl) : Prop :=
  ∀ (q : Key) (t : Trie) (k : Key),
    impl.pygtrie.longestPrefix q t = some k →
      (impl.pygtrie.get k t).isSome = true

/-- **The empty key matches every query when stored.** Membership of the
    empty key in `prefixes q t` is independent of the query: `[] ∈
    prefixes q t ↔ [] ∈ keys`. The empty sequence prefixes everything, so
    its presence among the matches is decided solely by whether it is
    stored. -/
def spec_prefixes_contains_empty_iff (impl : RepoImpl) : Prop :=
  ∀ (q : Key) (t : Trie),
    ([] ∈ impl.pygtrie.prefixes q t) ↔ ([] ∈ (t.map Prod.fst))

/-- **Inserting a non-matching key is a frame for `prefixes`.** If the
    inserted key `k` is *not* a prefix of `q`, then `set k v t` and `t`
    expose the *identical* prefix-match list of `q` — equal as literal
    lists, so order and multiplicity are pinned too. Only insertions whose
    key is itself a prefix of the query can perturb a `prefixes q`. -/
def spec_prefixes_set_irrelevant (impl : RepoImpl) : Prop :=
  ∀ (q k : Key) (v : Nat) (t : Trie),
    k.isPrefixOf q = false →
      impl.pygtrie.prefixes q (impl.pygtrie.set k v t)
        = impl.pygtrie.prefixes q t

/-- **A single insertion adds at most one prefix-match.** Inserting any
    `(k, v)` increases the number of prefix-matches of `q` by at most one:
    `#prefixes q (set k v t) ≤ #prefixes q t + 1`. A bound on how much one
    write can disturb a longest-prefix query — independent of whether `k`
    overwrites an existing binding. -/
def spec_prefixes_set_count_incr (impl : RepoImpl) : Prop :=
  ∀ (q k : Key) (v : Nat) (t : Trie),
    (impl.pygtrie.prefixes q (impl.pygtrie.set k v t)).length
      ≤ (impl.pygtrie.prefixes q t).length + 1

/-- **`prefixes` distributes over trie concatenation.** The prefix-matches
    of `q` in `t₁ ++ t₂` are exactly those of `t₁` followed by those of `t₂`:
    `prefixes q (t₁ ++ t₂) = prefixes q t₁ ++ prefixes q t₂`. A literal-list
    decomposition (not merely set/permutation), so it also pins the relative
    order of the two halves' matches. -/
def spec_prefixes_append (impl : RepoImpl) : Prop :=
  ∀ (q : Key) (t₁ t₂ : Trie),
    impl.pygtrie.prefixes q (t₁ ++ t₂)
      = impl.pygtrie.prefixes q t₁ ++ impl.pygtrie.prefixes q t₂

/-- **First-trie-wins lookup over concatenation.** A lookup in `t₁ ++ t₂`
    consults `t₁` first and falls back to `t₂` only on a miss:
    `get k (t₁ ++ t₂) = (get k t₁).orElse (fun _ => get k t₂)`. Pins the
    earliest-entry-wins shadowing semantics across a concatenation. -/
def spec_get_append (impl : RepoImpl) : Prop :=
  ∀ (k : Key) (t₁ t₂ : Trie),
    impl.pygtrie.get k (t₁ ++ t₂)
      = (impl.pygtrie.get k t₁).orElse (fun _ => impl.pygtrie.get k t₂)

/-- **`hasKey` distributes over concatenation.** A key is present in
    `t₁ ++ t₂` iff it is present in either half:
    `hasKey k (t₁ ++ t₂) = hasKey k t₁ || hasKey k t₂`. -/
def spec_hasKey_append (impl : RepoImpl) : Prop :=
  ∀ (k : Key) (t₁ t₂ : Trie),
    impl.pygtrie.hasKey k (t₁ ++ t₂)
      = (impl.pygtrie.hasKey k t₁ || impl.pygtrie.hasKey k t₂)

-- ════════════════════════════════════════════════════════════════
-- PREFIX-CHAIN, part II — each spec states a clean end-fact about how the
-- longest-prefix match, the enumerated prefixes, and the query relate
-- under the prefix order.
-- ════════════════════════════════════════════════════════════════

/-- **The prefix-match list is a comparability chain.** Any earlier/later
    pair in `prefixes q t` is *comparable* under the prefix order: one is a
    prefix of the other. Stated as a `List.Pairwise` over the match list, so
    it pins the whole list at once, with no `Nodup` hypothesis. -/
def spec_prefixes_pairwise_chain (impl : RepoImpl) : Prop :=
  ∀ (q : Key) (t : Trie),
    List.Pairwise (fun a b => a.isPrefixOf b = true ∨ b.isPrefixOf a = true)
      (impl.pygtrie.prefixes q t)

/-- **The match is stable on every query lying between it and the original.**
    If `longestPrefix q t = some k`, then for *any* `q'` sandwiched between the
    match and the query (`k` is a prefix of `q'` and `q'` is a prefix of `q`),
    querying `q'` reproduces the same match: `longestPrefix q' t = some k`.
    Pins the answer across a whole *interval* of queries at once, not just the
    endpoints. -/
def spec_longestPrefix_between_stable (impl : RepoImpl) : Prop :=
  ∀ (q : Key) (t : Trie) (k : Key),
    impl.pygtrie.longestPrefix q t = some k →
      ∀ (q' : Key), k.isPrefixOf q' = true → q'.isPrefixOf q = true →
        impl.pygtrie.longestPrefix q' t = some k

/-- **The prefix-match lengths are pairwise distinct.** When the stored keys
    are pairwise distinct (`Nodup`), mapping `prefixes q t` through `List.length`
    yields a `Nodup` list: no two matches of a query share a length. The winner
    of the longest-prefix search is therefore unambiguous. -/
def spec_prefixes_lengths_nodup (impl : RepoImpl) : Prop :=
  ∀ (q : Key) (t : Trie),
    (t.map Prod.fst).Nodup →
    ((impl.pygtrie.prefixes q t).map List.length).Nodup

/-- **The query's match list equals the answer key's match list.** If
    `longestPrefix q t = some k`, then `prefixes q t = prefixes k t` — as
    *literal lists*, order and multiplicity included. Collapsing the query
    down to the matched key leaves the entire enumerated match family
    unchanged. A strictly stronger fixed-point law than the value-level
    self-stability: it equates the whole match *lists*, not just the headline
    answers. -/
def spec_prefixes_eq_at_answer (impl : RepoImpl) : Prop :=
  ∀ (q : Key) (t : Trie) (k : Key),
    impl.pygtrie.longestPrefix q t = some k →
      impl.pygtrie.prefixes q t = impl.pygtrie.prefixes k t

/-- **Query refinement recovers the shorter query's matches by re-filtering.**
    If `q₁` is a prefix of `q₂`, then re-filtering the longer query's match
    list by "is a prefix of `q₁`" recovers *exactly* the shorter query's match
    list: `(prefixes q₂ t).filter (·.isPrefixOf q₁) = prefixes q₁ t`, as literal
    lists — no reordering, no loss, no duplication. Strictly stronger than the
    sublist monotonicity: it pins which entries of the longer list constitute
    the shorter one. -/
def spec_prefixes_query_refine (impl : RepoImpl) : Prop :=
  ∀ (q₁ q₂ : Key) (t : Trie),
    q₁.isPrefixOf q₂ = true →
      (impl.pygtrie.prefixes q₂ t).filter (fun z => z.isPrefixOf q₁)
        = impl.pygtrie.prefixes q₁ t

-- ════════════════════════════════════════════════════════════════
-- POSITIONAL / COUNTING / WHOLE-STATE-FRAME laws — the enumerated
-- prefix list, the longest-prefix answer, and the post-`set` state
-- pinned by their trie-order position, their derived count, and the
-- full residual state, not merely by membership or length.
-- ════════════════════════════════════════════════════════════════

/-- **`prefixes` is an order-preserving, exact-count enumeration.** The
    match list is a `Sublist` of the stored keys (so it preserves trie
    order and multiplicity), every entry is a prefix of `q`, and its length
    equals the filtered-key count. Anchored on `List.Sublist`, `List.map`,
    `List.filter`, `List.length`. -/
def spec_prefixes_order_embedding_count (impl : RepoImpl) : Prop :=
  ∀ (q : Key) (t : Trie),
    (impl.pygtrie.prefixes q t).Sublist (t.map Prod.fst) ∧
    (∀ k ∈ impl.pygtrie.prefixes q t, k.isPrefixOf q = true) ∧
    (impl.pygtrie.prefixes q t).length =
      ((t.map Prod.fst).filter (fun k => k.isPrefixOf q)).length

/-- **A match's index equals the count of earlier matching keys.** For a
    key `k` in `prefixes q t`, its first index in the match list equals the
    number of prefix-matching stored keys occurring before `k`'s first key
    occurrence in trie order. Anchored on `List.idxOf`, `List.take`,
    `List.filter`, `List.length`. -/
def spec_prefixes_first_occurrence_index (impl : RepoImpl) : Prop :=
  ∀ (q : Key) (t : Trie) (k : Key),
    k ∈ impl.pygtrie.prefixes q t →
      List.idxOf k (impl.pygtrie.prefixes q t) =
        (((t.map Prod.fst).take (List.idxOf k (t.map Prod.fst))).filter
          (fun z => z.isPrefixOf q)).length

/-- **`set` rewrites the whole `prefixes` list.** After `set k v t`, the
    match list of `q` is the old match list with every copy of `k` removed,
    prepended with `k` exactly when `k` is a prefix of `q`. A literal-list
    frame. Anchored on `set`, `prefixes`, `List.filter`, `List.isPrefixOf`. -/
def spec_prefixes_set_exact_frame (impl : RepoImpl) : Prop :=
  ∀ (q k : Key) (v : Nat) (t : Trie),
    impl.pygtrie.prefixes q (impl.pygtrie.set k v t) =
      if k.isPrefixOf q then
        k :: (impl.pygtrie.prefixes q t).filter (fun z => !(z == k))
      else
        (impl.pygtrie.prefixes q t).filter (fun z => !(z == k))

/-- **The longest-prefix answer sits at its first-maximal position.** If
    `longestPrefix q t = some k`, then in `prefixes q t` every entry before
    `k`'s first index is strictly shorter than `k` and every entry from the
    next index on is no longer. Anchored on `longestPrefix`, `prefixes`,
    `List.findIdx`, `List.take`, `List.drop`. -/
def spec_longestPrefix_index_first_maximal (impl : RepoImpl) : Prop :=
  ∀ (q : Key) (t : Trie) (k : Key),
    impl.pygtrie.longestPrefix q t = some k →
      let ps := impl.pygtrie.prefixes q t
      k ∈ ps ∧
      (∀ z ∈ ps.take (ps.findIdx (fun z => z == k)), z.length < k.length) ∧
      (∀ z ∈ ps.drop (ps.findIdx (fun z => z == k) + 1), z.length ≤ k.length)

/-- **Splitting the match list at any point and recombining is stable.**
    For every split index `n`, `longestPrefix q t` equals `lpCombine` of the
    `lpStep`-fold over the first `n` matches and the `lpStep`-fold over the
    rest. Anchored on `lpStep`, `lpCombine`, `List.foldl`, `List.take`,
    `List.drop`. -/
def spec_longestPrefix_prefixes_split_combine (impl : RepoImpl) : Prop :=
  ∀ (q : Key) (t : Trie) (n : Nat),
    impl.pygtrie.longestPrefix q t =
      lpCombine (((impl.pygtrie.prefixes q t).take n).foldl lpStep none)
        (((impl.pygtrie.prefixes q t).drop n).foldl lpStep none)

/-- **`set k` leaves every other key's entry bucket untouched.** For
    `k' ≠ k`, filtering `set k v t` for entries keyed by `k'` yields the same
    literal list as filtering `t`. A whole-bucket frame. Anchored on `set`
    and `List.filter`. -/
def spec_set_other_key_bucket_frame (impl : RepoImpl) : Prop :=
  ∀ (k k' : Key) (v : Nat) (t : Trie),
    k' ≠ k →
      (impl.pygtrie.set k v t).filter (fun p => p.1 == k') =
        t.filter (fun p => p.1 == k')

/-- **A successful `get` is the first stored occurrence.** If
    `get k t = some v`, then `(k, v)` is stored and no entry before its first
    occurrence is keyed by `k`. Anchored on `get`, `List.idxOf`,
    `List.take`. -/
def spec_get_some_first_occurrence (impl : RepoImpl) : Prop :=
  ∀ (k : Key) (t : Trie) (v : Nat),
    impl.pygtrie.get k t = some v →
      (k, v) ∈ t ∧
      ∀ p ∈ t.take (List.idxOf (k, v) t), p.1 ≠ k

/-- **The head of `prefixes` is the first matching stored entry.**
    `prefixes q t = k :: rest` iff `t` splits as `before ++ (k, v) :: after`
    with no key in `before` a prefix of `q`, `k` a prefix of `q`, and `rest`
    the filtered keys of `after`. Anchored on `prefixes`, `List.filter`,
    `List.map`. -/
def spec_prefixes_cons_first_match (impl : RepoImpl) : Prop :=
  ∀ (q : Key) (t : Trie) (k : Key) (rest : List Key),
    impl.pygtrie.prefixes q t = k :: rest ↔
      ∃ (before after : Trie) (v : Nat),
        t = before ++ (k, v) :: after ∧
        k.isPrefixOf q = true ∧
        (∀ p ∈ before, p.1.isPrefixOf q = false) ∧
        (after.map Prod.fst).filter (fun z => z.isPrefixOf q) = rest

/-- **The answer's rank equals the earlier-match count.** If
    `longestPrefix q t = some k`, the index of `k` in `prefixes q t` equals
    the number of prefix-matching stored keys before `k`'s first key
    occurrence. Anchored on `longestPrefix`, `prefixes`, `List.findIdx`,
    `List.take`, `List.filter`. -/
def spec_longestPrefix_rank_in_keys (impl : RepoImpl) : Prop :=
  ∀ (q : Key) (t : Trie) (k : Key),
    impl.pygtrie.longestPrefix q t = some k →
      let ps := impl.pygtrie.prefixes q t
      let keys := t.map Prod.fst
      ps.findIdx (fun z => z == k) =
        ((keys.take (keys.findIdx (fun z => z == k))).filter
          (fun z => z.isPrefixOf q)).length

/-- **The `lpStep` fold reaches the answer and then holds it.** If
    `longestPrefix q t = some k` and `i` is `k`'s first index in
    `prefixes q t`, then folding `lpStep` over the first `i+1` matches gives
    `some k`, and folding the remaining matches from `some k` keeps `some k`.
    Anchored on `lpStep`, `List.findIdx`, `List.take`, `List.drop`,
    `List.foldl`. -/
def spec_longestPrefix_foldl_split_at_answer (impl : RepoImpl) : Prop :=
  ∀ (q : Key) (t : Trie) (k : Key),
    impl.pygtrie.longestPrefix q t = some k →
      let ps := impl.pygtrie.prefixes q t
      (ps.take (ps.findIdx (fun z => z == k) + 1)).foldl lpStep none = some k ∧
      (ps.drop (ps.findIdx (fun z => z == k) + 1)).foldl lpStep (some k) = some k

/-- **`set` fully determines `get` on every key.** After `set k v t`,
    `get q` returns `some v` when `q = k` and the old `get q t` otherwise, for
    every query. A total post-state `get` frame. Anchored on `get` and
    `set`. -/
def spec_get_set_extensional_frame (impl : RepoImpl) : Prop :=
  ∀ (k : Key) (v : Nat) (t : Trie),
    ∀ q, impl.pygtrie.get q (impl.pygtrie.set k v t) =
      if q = k then some v else impl.pygtrie.get q t

/-- **Every `prefixes` split lifts to a stored-key split.** Whenever
    `prefixes q t = pre ++ k :: suf`, the stored-key list splits as
    `before ++ k :: after` with `before` filtering to `pre`, `k` a prefix of
    `q`, and `after` filtering to `suf`. Anchored on `List.map`,
    `List.filter`. -/
def spec_prefixes_occurrence_lift_to_keys (impl : RepoImpl) : Prop :=
  ∀ (q : Key) (t : Trie) (pre : List Key) (k : Key) (suf : List Key),
    impl.pygtrie.prefixes q t = pre ++ k :: suf →
      ∃ (before after : List Key),
        t.map Prod.fst = before ++ k :: after ∧
        before.filter (fun z => z.isPrefixOf q) = pre ∧
        k.isPrefixOf q = true ∧
        after.filter (fun z => z.isPrefixOf q) = suf
