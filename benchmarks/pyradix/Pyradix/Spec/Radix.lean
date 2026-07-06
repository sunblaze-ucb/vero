import Pyradix.Harness

/-!
# Pyradix.Spec.Radix

Specifications for the CIDR longest-prefix-match operations. Each `spec_*`
is a property over an arbitrary `impl : RepoImpl`, reached through
`impl.pyradix.<fn>`.

`coversBits net plen q` is the spec's own notion of coverage — whether the
prefix `(net, plen)` contains the address `q` — and `sameBlock` / `bitsAbove`
are its supporting vocabulary. These are defined here (independent of `impl`)
so the specs pin behaviour against a fixed meaning of coverage.
-/

-- ── Frozen ground-truth coverage machinery (DO NOT MODIFY) ──────

/-- The frozen address bit width used by the specification's coverage
    notion. Matches the implementation's `Pyradix.W`, but is stated here
    independently so the specs do not depend on any implementation
    constant. -/
def specW : Nat := 32

/-- `bitsAbove p x`: the top `p` bits of `x`, read as a number. Two
    addresses agree on their leading `p` bits exactly when their
    `bitsAbove p` values are equal. The specification's own ground truth,
    independent of any implementation. -/
def bitsAbove (p x : Nat) : Nat := x / 2 ^ (specW - p)

/-- `coversBits net plen q`: does the CIDR prefix `(net, plen)` cover the
    address `q`? True when `net` and `q` share their top `plen` bits.
    This is the frozen bit-prefix containment predicate; it never
    mentions `impl`. -/
def coversBits (net plen q : Nat) : Bool := bitsAbove plen net == bitsAbove plen q

/-- `sameBlock net₁ plen₁ net₂ plen₂`: do two entries denote the same
    CIDR block — identical prefix length and identical masked network?
    Frozen helper. -/
def sameBlock (net₁ plen₁ net₂ plen₂ : Nat) : Bool :=
  plen₁ == plen₂ && bitsAbove plen₁ net₁ == bitsAbove plen₂ net₂

/-- `IsFirstBest entries p`: `p` is the *first longest* entry of the list
    `entries`. Captured by a split `entries = pre ++ p :: suf` in which
    every earlier entry (`pre`) is *strictly* shorter than `p` and every
    later entry (`suf`) is no longer than `p`. This pins both the
    maximality of `p` *and* the canonical left-to-right tie-break — there
    is exactly one such `p` for a given `entries`. Frozen helper —
    references only the entry list, never `impl`. -/
def IsFirstBest (entries : List Pyradix.Prefix) (p : Pyradix.Prefix) : Prop :=
  ∃ pre suf, entries = pre ++ p :: suf ∧
    (∀ z ∈ pre, z.plen < p.plen) ∧
    (∀ z ∈ suf, z.plen ≤ p.plen)

-- ── searchBest: the most-specific covering prefix ──────────────────

/-- Witness: if `searchBest t q = some p`, then `p` is stored and covers `q`. -/
def spec_searchBest_covers (impl : RepoImpl) : Prop :=
  ∀ (t : Table) (q : Nat) (p : Pyradix.Prefix),
    impl.pyradix.searchBest t q = some p →
      p ∈ t ∧ coversBits p.net p.plen q = true

/-- Maximality: the returned prefix is at least as specific (long) as every
    stored entry covering the query — if `searchBest t q = some p` then every
    stored `p'` covering `q` has `p'.plen ≤ p.plen`. -/
def spec_searchBest_maximal (impl : RepoImpl) : Prop :=
  ∀ (t : Table) (q : Nat) (p : Pyradix.Prefix),
    impl.pyradix.searchBest t q = some p →
      ∀ (p' : Pyradix.Prefix), p' ∈ t → coversBits p'.net p'.plen q = true →
        p'.plen ≤ p.plen

/-- **Completeness (both directions).** `searchBest t q` is `none`
    *exactly* when no stored entry covers `q`. The forward direction rules
    out a spurious `none` (an impl that gives up while a covering prefix
    exists); the backward direction rules out a spurious match (returning
    a prefix when nothing covers the address). -/
def spec_searchBest_complete (impl : RepoImpl) : Prop :=
  ∀ (t : Table) (q : Nat),
    impl.pyradix.searchBest t q = none ↔
      ∀ (p : Pyradix.Prefix), p ∈ t → coversBits p.net p.plen q = false

/-- Full witness characterization (`↔`): `searchBest t q = some p` iff `p`
    is the first-longest entry of the covering sublist — the unique
    `IsFirstBest` element of `t.filter (covers · q)`. Pins both the returned
    length (maximal) and which record is returned on a length tie (the
    earliest in table order). -/
def spec_searchBest_witness_iff (impl : RepoImpl) : Prop :=
  ∀ (t : Table) (q : Nat) (p : Pyradix.Prefix),
    impl.pyradix.searchBest t q = some p ↔
      IsFirstBest (t.filter (fun e => coversBits e.net e.plen q)) p

-- ════════════════════════════════════════════════════════════════
-- searchWorst: the dual — shortest (least specific) covering prefix.
-- ════════════════════════════════════════════════════════════════

/-- **Witness for `searchWorst`.** A returned least-specific prefix is
    stored and covers the query. -/
def spec_searchWorst_covers (impl : RepoImpl) : Prop :=
  ∀ (t : Table) (q : Nat) (p : Pyradix.Prefix),
    impl.pyradix.searchWorst t q = some p →
      p ∈ t ∧ coversBits p.net p.plen q = true

/-- Minimality (dual of maximality): the returned prefix is no longer than
    every stored entry covering the query — if `searchWorst t q = some p`
    then every stored `p'` covering `q` has `p.plen ≤ p'.plen`. -/
def spec_searchWorst_minimal (impl : RepoImpl) : Prop :=
  ∀ (t : Table) (q : Nat) (p : Pyradix.Prefix),
    impl.pyradix.searchWorst t q = some p →
      ∀ (p' : Pyradix.Prefix), p' ∈ t → coversBits p'.net p'.plen q = true →
        p.plen ≤ p'.plen

/-- **Completeness of `searchWorst`.** `searchWorst t q` is `none`
    exactly when no stored entry covers `q` — the same coverage condition
    as `searchBest`, so the two queries agree on existence. -/
def spec_searchWorst_complete (impl : RepoImpl) : Prop :=
  ∀ (t : Table) (q : Nat),
    impl.pyradix.searchWorst t q = none ↔
      ∀ (p : Pyradix.Prefix), p ∈ t → coversBits p.net p.plen q = false

/-- `IsFirstWorst entries p`: `p` is the *first shortest* entry of
    `entries` — the dual of `IsFirstBest`. A split `entries = pre ++ p ::
    suf` in which every earlier entry (`pre`) is strictly longer than `p`
    and every later entry (`suf`) is no shorter than `p`. Pins both the
    minimality of `p` and the left-to-right tie-break (the earliest entry
    of minimal `plen`); exactly one `p` satisfies it. Frozen helper —
    references only the entry list, never `impl`. -/
def IsFirstWorst (entries : List Pyradix.Prefix) (p : Pyradix.Prefix) : Prop :=
  ∃ pre suf, entries = pre ++ p :: suf ∧
    (∀ z ∈ pre, p.plen < z.plen) ∧
    (∀ z ∈ suf, p.plen ≤ z.plen)

/-- Full witness characterization of `searchWorst` (`↔`): `searchWorst t q
    = some p` iff `p` is the first-shortest entry of the covering sublist —
    the unique `IsFirstWorst` element of `t.filter (covers · q)`. The dual
    of `spec_searchBest_witness_iff`: pins both the returned length (minimal)
    and which record is returned on a length tie (the earliest in table
    order). Stronger than `spec_searchWorst_minimal`, which fixes only the
    length. -/
def spec_searchWorst_witness_iff (impl : RepoImpl) : Prop :=
  ∀ (t : Table) (q : Nat) (p : Pyradix.Prefix),
    impl.pyradix.searchWorst t q = some p ↔
      IsFirstWorst (t.filter (fun e => coversBits e.net e.plen q)) p

/-- Best dominates worst: when both succeed on the same query, the
    most-specific match is at least as long as the least-specific one —
    `best.plen ≥ worst.plen`. -/
def spec_best_ge_worst (impl : RepoImpl) : Prop :=
  ∀ (t : Table) (q : Nat) (b w : Pyradix.Prefix),
    impl.pyradix.searchBest t q = some b →
    impl.pyradix.searchWorst t q = some w →
      w.plen ≤ b.plen

/-- **Best and worst agree on existence.** `searchBest` succeeds exactly
    when `searchWorst` does — both are `some` iff some stored entry covers
    `q`. Pins the two public queries to share one coverage criterion. -/
def spec_best_some_iff_worst_some (impl : RepoImpl) : Prop :=
  ∀ (t : Table) (q : Nat),
    impl.pyradix.searchBest t q ≠ none ↔ impl.pyradix.searchWorst t q ≠ none

-- ════════════════════════════════════════════════════════════════
-- searchExact: exact-block lookup, membership and determinism.
-- ════════════════════════════════════════════════════════════════

/-- **Exact lookup is backed by a real, matching entry.** If
    `searchExact t net plen = some p` then `p` is stored and denotes the
    queried block (`sameBlock`). Pins the returned entry to a genuine
    stored prefix with the requested network and length. -/
def spec_searchExact_mem (impl : RepoImpl) : Prop :=
  ∀ (t : Table) (net plen : Nat) (p : Pyradix.Prefix),
    impl.pyradix.searchExact t net plen = some p →
      p ∈ t ∧ sameBlock p.net p.plen net plen = true

/-- **Exact-lookup completeness.** `searchExact t net plen = none`
    exactly when no stored entry denotes that block. The bidirectional
    failure characterization. -/
def spec_searchExact_none_iff_absent (impl : RepoImpl) : Prop :=
  ∀ (t : Table) (net plen : Nat),
    impl.pyradix.searchExact t net plen = none ↔
      ∀ (p : Pyradix.Prefix), p ∈ t → sameBlock p.net p.plen net plen = false

-- ════════════════════════════════════════════════════════════════
-- add / delete interaction laws and search/update bridges.
-- ════════════════════════════════════════════════════════════════

/-- **Read-after-add (exact).** Adding a prefix `p` makes its own block
    exactly findable: `searchExact (add t p) p.net p.plen = some p`. The
    inserted entry sits at the front, so it is the first exact match. -/
def spec_add_searchExact_eq (impl : RepoImpl) : Prop :=
  ∀ (t : Table) (p : Pyradix.Prefix),
    impl.pyradix.searchExact (impl.pyradix.add t p) p.net p.plen = some p

/-- **Add overwrites the same block (structural).** Adding `p` after a
    prior `q` for the *same* block completely erases `q`: `add (add t q) p`
    equals `add t p` whenever `q` and `p` denote the same block. The stale
    entry leaves no trace. -/
def spec_add_overwrite (impl : RepoImpl) : Prop :=
  ∀ (t : Table) (p q : Pyradix.Prefix),
    sameBlock q.net q.plen p.net p.plen = true →
      impl.pyradix.add (impl.pyradix.add t q) p = impl.pyradix.add t p

/-- **Delete then exact misses.** After deleting the block `(net, plen)`,
    an exact lookup for it fails: `searchExact (delete t net plen) net plen
    = none`. The block is gone. -/
def spec_delete_searchExact_none (impl : RepoImpl) : Prop :=
  ∀ (t : Table) (net plen : Nat),
    impl.pyradix.searchExact (impl.pyradix.delete t net plen) net plen = none

/-- **Delete is a frame on other blocks (exact).** Deleting one block does
    not change an exact lookup of a *different* block: if `(net', plen')`
    is not the same block as `(net, plen)`, then `searchExact` agrees on
    `(net', plen')` before and after the delete. -/
def spec_delete_searchExact_ne (impl : RepoImpl) : Prop :=
  ∀ (t : Table) (net plen net' plen' : Nat),
    sameBlock net' plen' net plen = false →
      impl.pyradix.searchExact (impl.pyradix.delete t net plen) net' plen'
        = impl.pyradix.searchExact t net' plen'

/-- Delete is a membership filter (`↔`): an entry `p` is in `delete t net
    plen` exactly when it was already stored and does not denote the deleted
    block `(net, plen)`. Characterizes the entire returned table's
    membership — the deleted block's entries are absent and every other
    stored entry is preserved. Stronger than the `searchExact`-framed delete
    laws, which observe only one block at a time. -/
def spec_delete_mem_iff (impl : RepoImpl) : Prop :=
  ∀ (t : Table) (net plen : Nat) (p : Pyradix.Prefix),
    p ∈ impl.pyradix.delete t net plen ↔
      (p ∈ t ∧ sameBlock p.net p.plen net plen = false)

/-- **Adding a covering prefix lower-bounds the best match.** After
    inserting `p` whose prefix covers `q`, the longest-prefix match for
    `q` exists and is at least as specific as `p`: `searchBest (add t p) q
    = some b` with `p.plen ≤ b.plen`. So inserting a route that covers the
    address can only sharpen (never coarsen, never lose) the match. -/
def spec_add_searchBest_lower_bound (impl : RepoImpl) : Prop :=
  ∀ (t : Table) (q : Nat) (p : Pyradix.Prefix),
    coversBits p.net p.plen q = true →
      ∃ b, impl.pyradix.searchBest (impl.pyradix.add t p) q = some b ∧ p.plen ≤ b.plen

-- ════════════════════════════════════════════════════════════════
-- covered: canonical subset of entries contained in a query prefix.
-- ════════════════════════════════════════════════════════════════

/-- **`covered` is the canonical contained-subset (`↔`).** A stored entry
    `p` is reported by `covered t net plen` *iff* it is stored, at least
    as specific as `(net, plen)` (`plen ≤ p.plen`), and its network is
    covered by `(net, plen)`. Pinned in both directions, so the output set
    is exactly the prefixes lying inside the query block. -/
def spec_covered_canonical (impl : RepoImpl) : Prop :=
  ∀ (t : Table) (net plen : Nat) (p : Pyradix.Prefix),
    p ∈ impl.pyradix.covered t net plen ↔
      (p ∈ t ∧ plen ≤ p.plen ∧ coversBits net plen p.net = true)

/-- **`covered` is sound.** Every entry it returns is stored, no less
    specific than the query, and covered by the query block. The forward
    half of the canonical characterization, stated standalone. -/
def spec_covered_sound (impl : RepoImpl) : Prop :=
  ∀ (t : Table) (net plen : Nat),
    ∀ p ∈ impl.pyradix.covered t net plen,
      p ∈ t ∧ plen ≤ p.plen ∧ coversBits net plen p.net = true

/-- **`covered` never invents entries.** It returns no more entries than
    the table holds. -/
def spec_covered_length_le (impl : RepoImpl) : Prop :=
  ∀ (t : Table) (net plen : Nat),
    (impl.pyradix.covered t net plen).length ≤ t.length

/-- **`covered` distributes over table concatenation.** The entries of
    `t₁ ++ t₂` contained in the query block are exactly those of `t₁`
    followed by those of `t₂`: a literal-list decomposition, so it also
    pins the relative order of the two halves. -/
def spec_covered_append (impl : RepoImpl) : Prop :=
  ∀ (t₁ t₂ : Table) (net plen : Nat),
    impl.pyradix.covered (t₁ ++ t₂) net plen
      = impl.pyradix.covered t₁ net plen ++ impl.pyradix.covered t₂ net plen

-- ════════════════════════════════════════════════════════════════
-- Deep global laws of the longest-prefix match: empty/self-stability,
-- prefix-chain nesting, append-combine, and existence bridges.
-- ════════════════════════════════════════════════════════════════

/-- **Empty table never matches.** `searchBest [] q = none` for every
    query — the base case anchoring completeness. -/
def spec_searchBest_empty (impl : RepoImpl) : Prop :=
  ∀ (q : Nat), impl.pyradix.searchBest [] q = none

/-- **A covering entry forces a match (existence).** If some stored entry
    covers `q`, then `searchBest t q` succeeds. The contrapositive of the
    forward completeness direction, stated as a positive existence law:
    no covered address may be reported unmatched. -/
def spec_searchBest_some_of_cover (impl : RepoImpl) : Prop :=
  ∀ (t : Table) (q : Nat) (p : Pyradix.Prefix),
    p ∈ t → coversBits p.net p.plen q = true →
      impl.pyradix.searchBest t q ≠ none

/-- **An exact entry covering the query lower-bounds the best match.** If
    a block `(net, plen)` is stored (`searchExact t net plen = some p`) and
    its prefix covers `q`, then `searchBest t q` succeeds and is at least
    as specific as `p`: `some b` with `p.plen ≤ b.plen`. Bridges the exact
    and longest-prefix queries — a present covering route can never be
    beaten down to a coarser answer. -/
def spec_searchExact_best_lower_bound (impl : RepoImpl) : Prop :=
  ∀ (t : Table) (q net plen : Nat) (p : Pyradix.Prefix),
    impl.pyradix.searchExact t net plen = some p →
    coversBits p.net p.plen q = true →
      ∃ b, impl.pyradix.searchBest t q = some b ∧ p.plen ≤ b.plen

/-- **Entries contained in a query block share the block prefix
    (common-ancestor nesting).** Any two entries reported by `covered t net
    plen` agree with each other on the query block's top `plen` bits:
    `coversBits p₁.net plen p₂.net = true`. Every prefix a radix table
    reports as lying inside a query block descends from that block, so the
    enumerated subtree is genuinely rooted at `(net, plen)` rather than
    splaying into incomparable blocks. Anchored on the `covered` output. -/
def spec_covered_chain (impl : RepoImpl) : Prop :=
  ∀ (t : Table) (net plen : Nat) (p₁ p₂ : Pyradix.Prefix),
    p₁ ∈ impl.pyradix.covered t net plen →
    p₂ ∈ impl.pyradix.covered t net plen →
      coversBits p₁.net plen p₂.net = true

/-- **The best match dominates every covering entry in the chain.** If
    `searchBest t q = some p`, then every stored entry `p'` covering `q`
    has its network covered by `p`'s prefix at `p'`'s own (shorter-or-equal)
    length — i.e. `p'` lies *along* the chain ending at `p`. Strictly
    stronger than the length-maximality already pinned: it places the
    winner at the bottom (most specific) of the covering chain. -/
def spec_searchBest_dominates_chain (impl : RepoImpl) : Prop :=
  ∀ (t : Table) (q : Nat) (p : Pyradix.Prefix),
    impl.pyradix.searchBest t q = some p →
      ∀ (p' : Pyradix.Prefix), p' ∈ t → coversBits p'.net p'.plen q = true →
        coversBits p'.net p'.plen p.net = true

/-- **`searchBest` distributes over table concatenation via longest-wins.**
    The best match over `t₁ ++ t₂` is the longer of the two halves' best
    matches, keeping the *first* table's match on a length tie. Lets a
    routing table be sharded and queried piecewise: the whole-table answer
    is recovered by combining per-shard answers with the same tie-break a
    single table would use. -/
def spec_searchBest_append_combine (impl : RepoImpl) : Prop :=
  ∀ (t₁ t₂ : Table) (q : Nat),
    impl.pyradix.searchBest (t₁ ++ t₂) q
      = (match impl.pyradix.searchBest t₁ q, impl.pyradix.searchBest t₂ q with
         | none, b => b
         | a, none => a
         | some a, some b => if a.plen < b.plen then some b else some a)

/-- **Inserting a non-covering prefix is a frame for `searchBest`.** If
    the inserted prefix does *not* cover the query `q`, the longest-prefix
    match is unchanged: `searchBest (add t p) q = searchBest t q`. Isolates
    which insertions can perturb a query — only routes that actually cover
    the address. -/
def spec_add_irrelevant (impl : RepoImpl) : Prop :=
  ∀ (t : Table) (q : Nat) (p : Pyradix.Prefix),
    coversBits p.net p.plen q = false →
      impl.pyradix.searchBest (impl.pyradix.add t p) q = impl.pyradix.searchBest t q

-- ════════════════════════════════════════════════════════════════
-- Chain-nesting and cross-query laws: the extremal matches sit at the
-- ends of the covering chain, re-querying a winner's own address is
-- stable, a strictly-dominant insert pins the exact winner, and the
-- `covered` subtree is monotone under block refinement.
-- ════════════════════════════════════════════════════════════════

/-- The worst match roots the covering chain (dual dominance): if
    `searchWorst t q = some w`, then every stored entry `p'` covering `q`
    has its network covered by `w`'s prefix at `w`'s own length —
    `coversBits w.net w.plen p'.net = true`. The least-specific match sits
    at the top of the containment chain (every covering route descends from
    it), just as `searchBest` sits at the bottom. Stronger than
    length-minimality: it places the winner as the common ancestor of the
    covering set. -/
def spec_searchWorst_dominates_chain (impl : RepoImpl) : Prop :=
  ∀ (t : Table) (q : Nat) (w : Pyradix.Prefix),
    impl.pyradix.searchWorst t q = some w →
      ∀ (p' : Pyradix.Prefix), p' ∈ t → coversBits p'.net p'.plen q = true →
        coversBits w.net w.plen p'.net = true

/-- Worst covers best (the chain endpoints nest): when both queries succeed
    on the same address, the least-specific match's prefix covers the
    most-specific match's network — `searchBest t q = some b` and
    `searchWorst t q = some w` give `coversBits w.net w.plen b.net = true`.
    The shortest match is a genuine ancestor of the longest one. -/
def spec_worst_covers_best (impl : RepoImpl) : Prop :=
  ∀ (t : Table) (q : Nat) (b w : Pyradix.Prefix),
    impl.pyradix.searchBest t q = some b →
    impl.pyradix.searchWorst t q = some w →
      coversBits w.net w.plen b.net = true

/-- Re-querying the winner's own address is stable: if `searchBest t q =
    some p`, then querying `searchBest` again at `p`'s own network address
    `p.net` still succeeds and returns a match at least as specific as `p` —
    `searchBest t p.net = some p'` with `p.plen ≤ p'.plen`. The
    longest-prefix match of an address a stored route already covers can
    never be coarser than that route. -/
def spec_searchBest_requery_own (impl : RepoImpl) : Prop :=
  ∀ (t : Table) (q : Nat) (p : Pyradix.Prefix),
    impl.pyradix.searchBest t q = some p →
      ∃ p', impl.pyradix.searchBest t p.net = some p' ∧ p.plen ≤ p'.plen

/-- A strictly-dominant insert pins the exact winner: insert a prefix `p`
    that covers `q` and is strictly more specific than every entry currently
    covering `q`. Then the longest-prefix match for `q` becomes exactly `p`
    — `searchBest (add t p) q = some p`. Not merely a lower bound on the
    returned length (as `spec_add_searchBest_lower_bound` gives) but the
    identity of the record. -/
def spec_add_searchBest_exact (impl : RepoImpl) : Prop :=
  ∀ (t : Table) (q : Nat) (p : Pyradix.Prefix),
    coversBits p.net p.plen q = true →
    (∀ p' ∈ t, coversBits p'.net p'.plen q = true → p'.plen < p.plen) →
      impl.pyradix.searchBest (impl.pyradix.add t p) q = some p

/-- **`covered` is monotone under block refinement (subtree nesting).** If
    a query block `(net₂, plen₂)` lies *inside* a coarser block `(net₁,
    plen₁)` — the coarser one is no longer (`plen₁ ≤ plen₂`) and covers
    `net₂` — then every entry reported for the finer block is also reported
    for the coarser one: `covered t net₂ plen₂ ⊆ covered t net₁ plen₁`
    (membership). Enumerating a sub-block can never surface a route that the
    enclosing block misses; the `covered` subtrees nest exactly as the CIDR
    blocks do. A genuine radix containment law over the whole table. -/
def spec_covered_nested (impl : RepoImpl) : Prop :=
  ∀ (t : Table) (net₁ plen₁ net₂ plen₂ : Nat) (p : Pyradix.Prefix),
    plen₁ ≤ plen₂ →
    coversBits net₁ plen₁ net₂ = true →
    p ∈ impl.pyradix.covered t net₂ plen₂ →
      p ∈ impl.pyradix.covered t net₁ plen₁

-- ════════════════════════════════════════════════════════════════
-- Duplicate-sensitive counts, positional lookup, key uniqueness, and an
-- alternate mask-based coverage view.
-- ════════════════════════════════════════════════════════════════

/-- Count exact record occurrences without relying on `BEq Prefix`. -/
def prefixEqCount (p : Pyradix.Prefix) (xs : List Pyradix.Prefix) : Nat :=
  xs.countP (fun e => decide (e = p))

/-- The spec-side predicate for an entry lying inside a query block. -/
def insideBlock (net plen : Nat) (p : Pyradix.Prefix) : Bool :=
  decide (plen ≤ p.plen) && coversBits net plen p.net

/-- Stable key for a CIDR block, ignoring the stored value. -/
def blockKey (p : Pyradix.Prefix) : Nat × Nat :=
  (p.plen, bitsAbove p.plen p.net)

/-- Low-bit mask below the prefix boundary. -/
def bitsBelowMask (plen : Nat) : Nat :=
  2 ^ (specW - plen) - 1

/-- Mask containing exactly the top `plen` bits within the spec width. -/
def topBitsMask (plen : Nat) : Nat :=
  (2 ^ specW - 1) - bitsBelowMask plen

/-- Coverage stated with bitwise AND rather than division. -/
def coversAnd (net plen q : Nat) : Bool :=
  (net &&& topBitsMask plen) == (q &&& topBitsMask plen)

/-- `covered` preserves exactly the matching copies of each record. -/
def spec_covered_count_exact (impl : RepoImpl) : Prop :=
  ∀ (t : Table) (net plen : Nat) (p : Pyradix.Prefix),
    prefixEqCount p (impl.pyradix.covered t net plen) =
      if insideBlock net plen p = true then prefixEqCount p t else 0

/-- `delete` removes precisely the copies in the requested block. -/
def spec_delete_count_exact (impl : RepoImpl) : Prop :=
  ∀ (t : Table) (net plen : Nat) (p : Pyradix.Prefix),
    prefixEqCount p (impl.pyradix.delete t net plen) =
      if sameBlock p.net p.plen net plen = true then 0 else prefixEqCount p t

/-- `add` leaves exactly one copy of the inserted record and overwrites its block. -/
def spec_add_count_exact (impl : RepoImpl) : Prop :=
  ∀ (t : Table) (p x : Pyradix.Prefix),
    prefixEqCount x (impl.pyradix.add t p) =
      if x = p then 1
      else if sameBlock x.net x.plen p.net p.plen = true then 0
      else prefixEqCount x t

/-- Exact lookup agrees with the entry at the first matching index, when one exists. -/
def spec_searchExact_findIdx_get (impl : RepoImpl) : Prop :=
  ∀ (t : Table) (net plen : Nat),
    impl.pyradix.searchExact t net plen =
      Option.bind (t.findIdx? (fun e => sameBlock e.net e.plen net plen))
        (fun i => t[i]?)

/-- Adding a record preserves uniqueness of stored block keys. -/
def spec_add_blockKey_nodup (impl : RepoImpl) : Prop :=
  ∀ (t : Table) (p : Pyradix.Prefix),
    (t.map blockKey).Nodup → ((impl.pyradix.add t p).map blockKey).Nodup

/-- The best match is extremal when coverage is observed through the mask view. -/
def spec_searchBest_and_extremal (impl : RepoImpl) : Prop :=
  ∀ (t : Table) (q : Nat) (p : Pyradix.Prefix),
    q < 2 ^ specW →
    (∀ e ∈ t, e.net < 2 ^ specW ∧ e.plen ≤ specW) →
    impl.pyradix.searchBest t q = some p →
      p ∈ t ∧ coversAnd p.net p.plen q = true ∧
        ∀ p' ∈ t, coversAnd p'.net p'.plen q = true → p'.plen ≤ p.plen

-- ════════════════════════════════════════════════════════════════
-- Update-then-query frames, whole-table structural identities, and
-- cross-operation algebra: deleting a block frames unaffected queries,
-- `delete`/`covered` are order-preserving filters, and add/delete
-- interact by their block keys.
-- ════════════════════════════════════════════════════════════════

/-- **Deleting a non-covering block frames both searches.** If the block
    `(net, plen)` does not cover `q`, then removing it changes neither the
    longest- nor the least-specific match for `q`: `searchBest`/`searchWorst`
    over `delete t net plen` agree with those over `t`. Anchored on
    `coversBits`; isolates which deletions can perturb a query. -/
def spec_delete_search_frame_noncover (impl : RepoImpl) : Prop :=
  ∀ (t : Table) (q net plen : Nat),
    coversBits net plen q = false →
      impl.pyradix.searchBest (impl.pyradix.delete t net plen) q =
        impl.pyradix.searchBest t q ∧
      impl.pyradix.searchWorst (impl.pyradix.delete t net plen) q =
        impl.pyradix.searchWorst t q

/-- **Deleting the winning block strictly coarsens (or drops) the match.**
    If `searchBest t q = some b`, then after deleting `b`'s own block the
    longest-prefix match for `q` is `none` or a strictly less specific
    entry: `searchBest (delete t b.net b.plen) q` is `none` or `some b'`
    with `b'.plen < b.plen`. The route that won can never survive the
    deletion of its block. -/
def spec_delete_searchBest_winner_drops (impl : RepoImpl) : Prop :=
  ∀ (t : Table) (q : Nat) (b : Pyradix.Prefix),
    impl.pyradix.searchBest t q = some b →
      match impl.pyradix.searchBest (impl.pyradix.delete t b.net b.plen) q with
      | none => True
      | some b' => b'.plen < b.plen

/-- **`covered` is exactly the in-block filter (whole-list, ordered).**
    `covered t net plen` equals `t.filter (insideBlock net plen)` as a list
    — same entries, same multiplicity, same table order. Stronger than the
    membership/count characterizations: it pins the entire returned list. -/
def spec_covered_filter_eq (impl : RepoImpl) : Prop :=
  ∀ (t : Table) (net plen : Nat),
    impl.pyradix.covered t net plen = t.filter (insideBlock net plen)

/-- **`delete` is exactly the not-same-block filter (whole-list, ordered).**
    `delete t net plen` equals `t.filter (fun p => sameBlock p.net p.plen
    net plen = false)` — the surviving entries in their original order and
    multiplicity. Pins the entire returned table, not one probed block. -/
def spec_delete_eq_filter (impl : RepoImpl) : Prop :=
  ∀ (t : Table) (net plen : Nat),
    impl.pyradix.delete t net plen =
      t.filter (fun p => sameBlock p.net p.plen net plen = false)

/-- **`delete` returns a sublist of the input.** `delete t net plen` is a
    `List.Sublist` of `t`: deletion only drops entries, never reorders or
    invents them. -/
def spec_delete_sublist (impl : RepoImpl) : Prop :=
  ∀ (t : Table) (net plen : Nat),
    List.Sublist (impl.pyradix.delete t net plen) t

/-- **Enumerate-after-delete equals delete-after-enumerate.** The entries
    inside `(cnet, cplen)` after deleting block `(dnet, dplen)` are exactly
    the previously-covered entries with the deleted block removed:
    `covered (delete t dnet dplen) cnet cplen = (covered t cnet cplen).filter
    (fun p => sameBlock p.net p.plen dnet dplen = false)`. A whole-list,
    order-preserving identity linking `covered` and `delete`. -/
def spec_covered_after_delete_filter (impl : RepoImpl) : Prop :=
  ∀ (t : Table) (cnet cplen dnet dplen : Nat),
    impl.pyradix.covered (impl.pyradix.delete t dnet dplen) cnet cplen =
      (impl.pyradix.covered t cnet cplen).filter
        (fun p => sameBlock p.net p.plen dnet dplen = false)

/-- **`covered` size equals the in-block count.** The number of entries
    reported by `covered t net plen` equals `t.countP (insideBlock net
    plen)` — the count of stored entries lying inside the query block,
    duplicates included. -/
def spec_covered_length_countP (impl : RepoImpl) : Prop :=
  ∀ (t : Table) (net plen : Nat),
    (impl.pyradix.covered t net plen).length =
      t.countP (fun p => insideBlock net plen p)

/-- **Add and delete of different blocks commute.** If `p` and `(net,
    plen)` denote different blocks (`sameBlock … = false`), then inserting
    `p` and deleting `(net, plen)` may be done in either order: `delete (add
    t p) net plen = add (delete t net plen) p`. -/
def spec_add_delete_commute_ne (impl : RepoImpl) : Prop :=
  ∀ (t : Table) (p : Pyradix.Prefix) (net plen : Nat),
    sameBlock p.net p.plen net plen = false →
      impl.pyradix.delete (impl.pyradix.add t p) net plen =
        impl.pyradix.add (impl.pyradix.delete t net plen) p

/-- **`delete` is idempotent, and deletes of different blocks commute.**
    Deleting the same block twice equals deleting it once; deleting two
    different blocks (`sameBlock … = false`) gives the same table in either
    order. Whole-table structural identities. -/
def spec_delete_idempotent_and_commute (impl : RepoImpl) : Prop :=
  (∀ (t : Table) (net plen : Nat),
    impl.pyradix.delete (impl.pyradix.delete t net plen) net plen =
      impl.pyradix.delete t net plen) ∧
  (∀ (t : Table) (net₁ plen₁ net₂ plen₂ : Nat),
    sameBlock net₁ plen₁ net₂ plen₂ = false →
      impl.pyradix.delete (impl.pyradix.delete t net₁ plen₁) net₂ plen₂ =
        impl.pyradix.delete (impl.pyradix.delete t net₂ plen₂) net₁ plen₁)

/-- **Add then delete the same block equals delete alone.** Inserting `p`
    and then deleting `p`'s own block yields the table with that block
    removed, as if `p` had never been added: `delete (add t p) p.net p.plen
    = delete t p.net p.plen`. -/
def spec_delete_add_same (impl : RepoImpl) : Prop :=
  ∀ (t : Table) (p : Pyradix.Prefix),
    impl.pyradix.delete (impl.pyradix.add t p) p.net p.plen =
      impl.pyradix.delete t p.net p.plen

/-- **A finer covered subtree is a sublist of the coarser one, with no
    count increase.** If block `(net₂, plen₂)` lies inside `(net₁, plen₁)`
    (`plen₁ ≤ plen₂` and `coversBits net₁ plen₁ net₂ = true`), then
    `covered t net₂ plen₂` is a `List.Sublist` of `covered t net₁ plen₁`,
    and every record occurs no more often in the finer enumeration than the
    coarser. Strengthens the membership-only nesting to order and
    multiplicity. -/
def spec_covered_nested_sublist_count (impl : RepoImpl) : Prop :=
  ∀ (t : Table) (net₁ plen₁ net₂ plen₂ : Nat),
    plen₁ ≤ plen₂ →
    coversBits net₁ plen₁ net₂ = true →
      List.Sublist (impl.pyradix.covered t net₂ plen₂)
        (impl.pyradix.covered t net₁ plen₁) ∧
      ∀ (p : Pyradix.Prefix),
        prefixEqCount p (impl.pyradix.covered t net₂ plen₂) ≤
          prefixEqCount p (impl.pyradix.covered t net₁ plen₁)

/-- **Exact-lookup existence is a positive block count, and a best match
    lies in its own covered subtree.** `searchExact t net plen` succeeds iff
    the table holds at least one entry of that block (`0 < t.countP (fun e
    => sameBlock e.net e.plen net plen)`); and if `searchBest t q = some p`
    then `p ∈ covered t p.net p.plen`. Bridges exact lookup to counting and
    the best match to `covered` self-membership. -/
def spec_searchExact_count_and_best_self_covered (impl : RepoImpl) : Prop :=
  (∀ (t : Table) (net plen : Nat),
    impl.pyradix.searchExact t net plen ≠ none ↔
      0 < t.countP (fun e => sameBlock e.net e.plen net plen)) ∧
  (∀ (t : Table) (q : Nat) (p : Pyradix.Prefix),
    impl.pyradix.searchBest t q = some p →
      p ∈ impl.pyradix.covered t p.net p.plen)
