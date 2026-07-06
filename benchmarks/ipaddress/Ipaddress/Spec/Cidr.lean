import Ipaddress.Harness

/-!
# Ipaddress.Spec.Cidr

Specifications for the IPv4 CIDR algebra. Each `spec_*` is a property over an
arbitrary `impl : RepoImpl`; the API is always reached through
`impl.ipaddress.<fn>`.

The headline specs characterise `collapse` as the canonical set of maximal
blocks: `spec_collapse_coverage` pins the covered address set two-sidedly over
the full `Addr` domain, `spec_collapse_subset` keeps every output block an
input, and `spec_collapse_no_containment` is the minimality conjunct — no output
block is subsumed by a strictly less-specific output block. The supporting
anchors pin `containsAddr` / `networkAddr` / `broadcast` / `supernet` and the
frozen mask arithmetic.

DO NOT MODIFY — frozen curator-given content.
-/

-- ── frozen spec vocabulary (frozen ops only; never references `impl`) ──

/-- A block is *aligned* (a network address in canonical form) iff its stored
    `network` field is already an exact multiple of its block size — flooring it
    to the block boundary is a no-op. Frozen mask arithmetic; references no API.
    Some `collapse` specs (disjointness, partition) require aligned inputs, as
    real CIDR lists are. -/
def isAligned (c : Cidr) : Prop :=
  (c.network / blockSize c.prefixLen) * blockSize c.prefixLen = c.network

/-- Total address count of a list of blocks, counted *with multiplicity* —
    the sum of each block's size `2^(32 - prefixLen)`. Frozen `Nat` fold over
    the frozen `blockSize`; references no API. -/
def sumSizes (xs : List Cidr) : Nat :=
  (xs.map (fun c => blockSize c.prefixLen)).foldr (· + ·) 0

/-- `k`-fold application of a supernet function `f`: `superIter f 0 c = c` and
    `superIter f (k+1) c = f (superIter f k c)`. The function is a parameter so
    specs iterate the *impl's* `supernet` (`superIter impl.ipaddress.supernet k
    c`). Models walking up the CIDR aggregation tree `k` levels. -/
def superIter (f : Cidr → Cidr) : Nat → Cidr → Cidr
  | 0,     c => c
  | k + 1, c => f (superIter f k c)

/-- Frozen redundancy predicate: `coveredByRef c xs` holds iff some block in `xs`
    is *strictly less specific* than `c` (`prefixLen` strictly smaller) and
    contains `c`'s network address. This is the specification's ground-truth
    notion of a redundant block — the fixed vocabulary the `collapse` laws are
    stated against — not the `collapse` algorithm itself. References no API. -/
def coveredByRef (c : Cidr) (xs : List Cidr) : Bool :=
  xs.any (fun d => (d.prefixLen < c.prefixLen) && memNet c.network d)

-- ── frozen-op anchors: network / broadcast / supernet ──────────

/-- `networkAddr` is the *least* address of a block: it lies in the block, and
    every contained address is at least as large — the exact lower endpoint of
    the block's address range, not merely some member. -/
def spec_contains_network (impl : RepoImpl) : Prop :=
  ∀ (c : Cidr),
    impl.ipaddress.containsAddr (impl.ipaddress.networkAddr c) c = true ∧
    (∀ a : Addr, impl.ipaddress.containsAddr a c = true →
      impl.ipaddress.networkAddr c ≤ a)

/-- `broadcast` is the *greatest* address of a block: it lies in the block, and
    no contained address exceeds it — the exact upper endpoint, not merely some
    member. -/
def spec_broadcast_in_block (impl : RepoImpl) : Prop :=
  ∀ (c : Cidr),
    impl.ipaddress.containsAddr (impl.ipaddress.broadcast c) c = true ∧
    (∀ a : Addr, impl.ipaddress.containsAddr a c = true →
      a ≤ impl.ipaddress.broadcast c)

/-- The broadcast address is never below the network address, and the two
    endpoints *coincide* exactly when the block is a single host (`prefixLen`
    saturates at 32). -/
def spec_broadcast_ge_network (impl : RepoImpl) : Prop :=
  ∀ (c : Cidr),
    impl.ipaddress.networkAddr c ≤ impl.ipaddress.broadcast c ∧
    (impl.ipaddress.networkAddr c = impl.ipaddress.broadcast c ↔ 32 ≤ c.prefixLen)

/-- Any address in a block is also in its supernet (parent block), for any
    well-formed prefix — including the `/0` block, whose supernet is itself. -/
def spec_supernet_contains (impl : RepoImpl) : Prop :=
  ∀ (a : Addr) (c : Cidr),
    c.prefixLen ≤ 32 →
    impl.ipaddress.containsAddr a c = true →
    impl.ipaddress.containsAddr a (impl.ipaddress.supernet c) = true

-- ── collapse: canonical maximal-block set ──────────────────────

/-- Coverage (full domain): for every address `a < 2^32` and every list of
    well-formed (`prefixLen ≤ 32`) blocks, `a` is covered by some block of
    `collapse xs` iff it was covered by some block of `xs`. -/
def spec_collapse_coverage (impl : RepoImpl) : Prop :=
  ∀ (xs : List Cidr) (a : Addr),
    a < 2 ^ 32 →
    (∀ c ∈ xs, c.prefixLen ≤ 32) →
    ((∃ c ∈ impl.ipaddress.collapse xs, impl.ipaddress.containsAddr a c = true) ↔
     (∃ c ∈ xs, memNet a c = true))

/-- Soundness of the output: every block returned by `collapse` was one of the
    inputs (it does not invent blocks). -/
def spec_collapse_subset (impl : RepoImpl) : Prop :=
  ∀ (xs : List Cidr) (c : Cidr),
    c ∈ impl.ipaddress.collapse xs → c ∈ xs

/-- Minimality: the output is irredundant — no output block is subsumed by a
    strictly less-specific (coarser) output block. -/
def spec_collapse_no_containment (impl : RepoImpl) : Prop :=
  ∀ (xs : List Cidr) (c1 c2 : Cidr),
    c1 ∈ impl.ipaddress.collapse xs →
    c2 ∈ impl.ipaddress.collapse xs →
    c1 ≠ c2 →
    ¬ (c2.prefixLen < c1.prefixLen ∧ memNet c1.network c2 = true)

/-- The collapsed output has no duplicate blocks (canonical form). -/
def spec_collapse_nodup (impl : RepoImpl) : Prop :=
  ∀ (xs : List Cidr), (impl.ipaddress.collapse xs).Nodup

-- ── networkAddr / broadcast: defining equations + alignment ────

/-- `networkAddr` floors the network field down to its block boundary, so it
    never exceeds the stored network address. -/
def spec_network_addr_le_network (impl : RepoImpl) : Prop :=
  ∀ (c : Cidr), impl.ipaddress.networkAddr c ≤ c.network

/-- Defining equation of `broadcast`: it is exactly the network address plus
    one less than the block size (the last address of the block). Pins the `+`,
    `-` arithmetic relating the two endpoints. -/
def spec_broadcast_eq (impl : RepoImpl) : Prop :=
  ∀ (c : Cidr),
    impl.ipaddress.broadcast c
      = impl.ipaddress.networkAddr c + blockSize c.prefixLen - 1

/-- The network address is block-aligned: it is an exact multiple of the block
    size (its low `32 - prefixLen` bits are zero). -/
def spec_network_addr_aligned (impl : RepoImpl) : Prop :=
  ∀ (c : Cidr), impl.ipaddress.networkAddr c % blockSize c.prefixLen = 0

/-- Block size from the two endpoints: the number of addresses in a block is
    `broadcast - networkAddr + 1`, which equals `2^(32 - prefixLen)`. -/
def spec_block_size_eq (impl : RepoImpl) : Prop :=
  ∀ (c : Cidr),
    impl.ipaddress.broadcast c - impl.ipaddress.networkAddr c + 1
      = blockSize c.prefixLen

-- ── containsAddr: range characterization + boundary cases ──────

/-- Range characterization: an address lies in a block iff it falls within the
    closed interval `[networkAddr c, broadcast c]`, tying membership to the two
    endpoint APIs over the entire `Addr` domain. -/
def spec_contains_iff_range (impl : RepoImpl) : Prop :=
  ∀ (a : Addr) (c : Cidr),
    impl.ipaddress.containsAddr a c = true
      ↔ (impl.ipaddress.networkAddr c ≤ a ∧ a ≤ impl.ipaddress.broadcast c)

/-- A block always contains its own (stored) network field. -/
def spec_contains_self_network (impl : RepoImpl) : Prop :=
  ∀ (c : Cidr), impl.ipaddress.containsAddr c.network c = true

/-- A `/32` host block contains exactly its own network address: membership
    reduces to equality (the block has size one). -/
def spec_slash32_contains_iff (impl : RepoImpl) : Prop :=
  ∀ (a : Addr) (c : Cidr),
    c.prefixLen = 32 →
    (impl.ipaddress.containsAddr a c = true ↔ a = c.network)

/-- The `/0` block covers the whole IPv4 space: every well-formed address is
    contained when both the address and the block's network fit in 32 bits. -/
def spec_full_block_contains_all (impl : RepoImpl) : Prop :=
  ∀ (a : Addr) (c : Cidr),
    a < 2 ^ 32 → c.network < 2 ^ 32 → c.prefixLen = 0 →
    impl.ipaddress.containsAddr a c = true

/-- Sub-block monotonicity (cross-API): if `c1` is no more specific than `c2`
    (smaller-or-equal prefix) and contains `c2`'s network, then everything in
    `c2` is also in `c1` — the nesting law of CIDR blocks. -/
def spec_subblock_in_superblock (impl : RepoImpl) : Prop :=
  ∀ (a : Addr) (c1 c2 : Cidr),
    c1.prefixLen ≤ c2.prefixLen → c2.prefixLen ≤ 32 →
    impl.ipaddress.containsAddr c2.network c1 = true →
    impl.ipaddress.containsAddr a c2 = true →
    impl.ipaddress.containsAddr a c1 = true

-- ── supernet: defining equation + size doubling ────────────────

/-- `supernet` decreases the prefix length by exactly one. -/
def spec_supernet_prefix (impl : RepoImpl) : Prop :=
  ∀ (c : Cidr), (impl.ipaddress.supernet c).prefixLen = c.prefixLen - 1

/-- A supernet is twice the size of its child block (one fewer prefix bit
    doubles the address count), for any non-trivial well-formed prefix. -/
def spec_supernet_block_twice (impl : RepoImpl) : Prop :=
  ∀ (c : Cidr),
    0 < c.prefixLen → c.prefixLen ≤ 32 →
    blockSize (impl.ipaddress.supernet c).prefixLen = 2 * blockSize c.prefixLen

/-- `supernet`'s stored network is the exact canonical aligned parent block —
    not merely *some* coarser block that contains the child. The three conjuncts
    together pin the network field uniquely: the output is itself block-aligned
    (`isAligned`), it never exceeds the child's stored network, and the child's
    network lies strictly within one parent-block-size of it. -/
def spec_supernet_exact_parent (impl : RepoImpl) : Prop :=
  ∀ (c : Cidr),
    isAligned (impl.ipaddress.supernet c) ∧
    (impl.ipaddress.supernet c).network ≤ c.network ∧
    c.network
      < (impl.ipaddress.supernet c).network + blockSize (impl.ipaddress.supernet c).prefixLen

-- ── supernet: iterated-aggregation (superIter) laws ────────────
-- Walking `k` levels up the CIDR aggregation tree via repeated `supernet`.

/-- Iterated-supernet prefix law: walking `k` levels up the aggregation tree
    lowers the prefix length by exactly `k` (saturating at `0`) —
    `(superIter supernet k c).prefixLen = c.prefixLen - k`. -/
def spec_supernet_iter_prefix (impl : RepoImpl) : Prop :=
  ∀ (k : Nat) (c : Cidr),
    (superIter impl.ipaddress.supernet k c).prefixLen = c.prefixLen - k

/-- Iterated-supernet alignment: after at least one aggregation step the result
    is *aligned* — a canonical network address — for every input,
    `0 < k → isAligned (superIter supernet k c)`. -/
def spec_supernet_iter_aligned (impl : RepoImpl) : Prop :=
  ∀ (k : Nat) (c : Cidr),
    0 < k → isAligned (superIter impl.ipaddress.supernet k c)

/-- Iterated-supernet containment (full domain): every address of a well-formed
    block `c` remains contained after walking *any* number of aggregation levels
    up — `containsAddr a c → containsAddr a (superIter supernet k c)` for all
    `k`. -/
def spec_supernet_iter_contains (impl : RepoImpl) : Prop :=
  ∀ (k : Nat) (c : Cidr) (a : Addr),
    c.prefixLen ≤ 32 →
    impl.ipaddress.containsAddr a c = true →
    impl.ipaddress.containsAddr a (superIter impl.ipaddress.supernet k c) = true

-- ── collapse: edge cases, bounds, well-formedness, idempotence ──

/-- `collapse []` is `[]` (no blocks in, no blocks out). -/
def spec_collapse_nil (impl : RepoImpl) : Prop :=
  impl.ipaddress.collapse [] = []

/-- A single block is already canonical: `collapse [c] = [c]`. -/
def spec_collapse_singleton (impl : RepoImpl) : Prop :=
  ∀ (c : Cidr), impl.ipaddress.collapse [c] = [c]

/-- `collapse` never grows the list — its output is no longer than the input
    with its *duplicates already removed*. Strictly tighter than `≤ xs.length`. -/
def spec_collapse_length_le (impl : RepoImpl) : Prop :=
  ∀ (xs : List Cidr), (impl.ipaddress.collapse xs).length ≤ xs.eraseDups.length

/-- Well-formedness is preserved: if every input block has `prefixLen ≤ 32`,
    so does every output block. -/
def spec_collapse_wf (impl : RepoImpl) : Prop :=
  ∀ (xs : List Cidr),
    (∀ c ∈ xs, c.prefixLen ≤ 32) →
    ∀ c ∈ impl.ipaddress.collapse xs, c.prefixLen ≤ 32

/-- Idempotence on coverage: collapsing twice covers the exact same address set
    as collapsing once. -/
def spec_collapse_idempotent_coverage (impl : RepoImpl) : Prop :=
  ∀ (xs : List Cidr) (a : Addr),
    a < 2 ^ 32 →
    (∀ c ∈ xs, c.prefixLen ≤ 32) →
    ((∃ c ∈ impl.ipaddress.collapse (impl.ipaddress.collapse xs),
        impl.ipaddress.containsAddr a c = true) ↔
     (∃ c ∈ impl.ipaddress.collapse xs, impl.ipaddress.containsAddr a c = true))

-- ── collapse: deep list-algorithm invariants ──────────────────

/-- Exact canonical-form fixpoint: `collapse (collapse xs) = collapse xs` as a
    literal *list* equality — a second pass reproduces the output exactly, same
    blocks in the same order. Stronger than the coverage-level idempotence
    above. -/
def spec_collapse_idempotent_exact (impl : RepoImpl) : Prop :=
  ∀ (xs : List Cidr),
    impl.ipaddress.collapse (impl.ipaddress.collapse xs)
      = impl.ipaddress.collapse xs

/-- Structural soundness: the output is a *sublist* of the input — it preserves
    the relative order of the blocks it keeps and never reorders or invents them.
    Stronger than `spec_collapse_subset` and `spec_collapse_nodup`. -/
def spec_collapse_sublist (impl : RepoImpl) : Prop :=
  ∀ (xs : List Cidr), List.Sublist (impl.ipaddress.collapse xs) xs

/-- Removal-completeness (converse of minimality): *every* redundant block is
    dropped. If `coveredBy c xs` (a strictly less-specific block of `xs` subsumes
    `c`), then `c` does not appear in `collapse xs`. -/
def spec_collapse_drops_covered (impl : RepoImpl) : Prop :=
  ∀ (xs : List Cidr) (c : Cidr),
    coveredByRef c xs = true →
    c ∉ impl.ipaddress.collapse xs

/-- Nested-chain canonicalisation (frozen structured input): collapsing the
    chain `nestedChain n` — `n+1` blocks all based at `0` with prefix lengths
    `n, n-1, …, 0` — yields exactly the single coarsest `/0` block `⟨0, 0⟩`. -/
def spec_collapse_chain_coarsest (impl : RepoImpl) : Prop :=
  ∀ (n : Nat), impl.ipaddress.collapse (nestedChain n) = [⟨0, 0⟩]

/-- Order-independence of the survivor *set* (cross-list): `collapse xs` and
    `collapse xs.reverse` contain exactly the same blocks —
    `c ∈ collapse xs ↔ c ∈ collapse xs.reverse` for every block `c`. The output
    *order* genuinely differs under reversal, so this is a set-level law, not a
    list equality. -/
def spec_collapse_reverse_coverage (impl : RepoImpl) : Prop :=
  ∀ (xs : List Cidr) (c : Cidr),
    c ∈ impl.ipaddress.collapse xs ↔ c ∈ impl.ipaddress.collapse xs.reverse

/-- Duplication absorption (cross-list, exact list equality): collapsing
    `xs ++ xs` yields the literally identical canonical list as collapsing `xs` —
    same blocks, same order, no duplicates. -/
def spec_collapse_dup_absorb (impl : RepoImpl) : Prop :=
  ∀ (xs : List Cidr),
    impl.ipaddress.collapse (xs ++ xs) = impl.ipaddress.collapse xs

-- ── collapse: structural list-algorithm invariants ────────────
-- Disjointness, partition, measure conservation, and the closure-operator
-- triple (extensive · monotone · idempotent) of the canonical maximal-block
-- set, plus the negative "no sibling merge" characterisation.

/-- Pairwise disjointness of the canonical output: for *aligned* well-formed
    inputs, any two distinct output blocks are disjoint — neither one's network
    address lies in the other. The alignment premise is essential:
    `collapse [⟨0,24⟩, ⟨5,24⟩]` keeps two overlapping blocks because `⟨5,24⟩` is
    not aligned, as a real un-normalised CIDR list would. -/
def spec_collapse_pairwise_disjoint (impl : RepoImpl) : Prop :=
  ∀ (xs : List Cidr) (c1 c2 : Cidr),
    (∀ c ∈ xs, c.prefixLen ≤ 32) →
    (∀ c ∈ xs, isAligned c) →
    c1 ∈ impl.ipaddress.collapse xs →
    c2 ∈ impl.ipaddress.collapse xs →
    c1 ≠ c2 →
    memNet c2.network c1 = false ∧ memNet c1.network c2 = false

/-- Partition theorem: every IPv4 address covered by `collapse xs` (for aligned
    well-formed inputs) lies in *exactly one* output block — at least one output
    block contains it (existence) and at most one (uniqueness). The canonical
    output is a genuine partition of the union it covers. -/
def spec_collapse_partition (impl : RepoImpl) : Prop :=
  ∀ (xs : List Cidr) (a : Addr),
    a < 2 ^ 32 →
    (∀ c ∈ xs, c.prefixLen ≤ 32) →
    (∀ c ∈ xs, isAligned c) →
    (∃ c ∈ xs, memNet a c = true) →
    (∃ c ∈ impl.ipaddress.collapse xs, impl.ipaddress.containsAddr a c = true) ∧
    (∀ c1 ∈ impl.ipaddress.collapse xs, ∀ c2 ∈ impl.ipaddress.collapse xs,
      impl.ipaddress.containsAddr a c1 = true →
      impl.ipaddress.containsAddr a c2 = true → c1 = c2)

/-- Measure conservation: `collapse` never increases the total block-size sum
    `Σ 2^(32 - prefixLen)`. -/
def spec_collapse_sumSizes_le (impl : RepoImpl) : Prop :=
  ∀ (xs : List Cidr), sumSizes (impl.ipaddress.collapse xs) ≤ sumSizes xs

/-- Closure-operator extensivity (full domain): the output *covers the input* —
    every address contained in any input block is contained in some output block.
    With `spec_collapse_sumSizes_le` and `spec_collapse_idempotent_exact` this
    makes `collapse` a closure operator (extensive · monotone · idempotent). -/
def spec_collapse_extensive (impl : RepoImpl) : Prop :=
  ∀ (xs : List Cidr) (a : Addr) (c : Cidr),
    a < 2 ^ 32 →
    (∀ d ∈ xs, d.prefixLen ≤ 32) →
    c ∈ xs →
    impl.ipaddress.containsAddr a c = true →
    ∃ d ∈ impl.ipaddress.collapse xs, impl.ipaddress.containsAddr a d = true

/-- Closure-operator monotonicity (full domain): enlarging the input can only
    enlarge the coverage — every address covered by `collapse xs` is also covered
    by `collapse (xs ++ ys)`. Completes the closure-operator triple. -/
def spec_collapse_monotone (impl : RepoImpl) : Prop :=
  ∀ (xs ys : List Cidr) (a : Addr),
    a < 2 ^ 32 →
    (∀ c ∈ xs, c.prefixLen ≤ 32) →
    (∀ c ∈ ys, c.prefixLen ≤ 32) →
    (∃ c ∈ impl.ipaddress.collapse xs, impl.ipaddress.containsAddr a c = true) →
    (∃ c ∈ impl.ipaddress.collapse (xs ++ ys), impl.ipaddress.containsAddr a c = true)

/-- Negative characterisation — `collapse` does NOT merge adjacent siblings:
    every output block's `prefixLen` is exactly the `prefixLen` of some input
    block. It only removes blocks that were already present, never synthesises a
    new prefix length. Two adjacent non-nested `/25`s stay two `/25`s; it does not
    coalesce `[⟨0,25⟩, ⟨128,25⟩]` into `[⟨0,24⟩]`. -/
def spec_collapse_no_merge (impl : RepoImpl) : Prop :=
  ∀ (xs : List Cidr) (c : Cidr),
    c ∈ impl.ipaddress.collapse xs →
    ∃ d ∈ xs, d.prefixLen = c.prefixLen

/-- Survival of uncovered blocks: a block `c ∈ xs` that is not `coveredBy` any
    strictly-coarser block of `xs` survives into `collapse xs`. `collapse` keeps
    every maximal block. -/
def spec_collapse_keeps_uncovered (impl : RepoImpl) : Prop :=
  ∀ (xs : List Cidr) (c : Cidr),
    c ∈ xs →
    coveredByRef c xs = false →
    c ∈ impl.ipaddress.collapse xs

-- ── collapse: input-absorption laws ────────────────────────────
-- Clean END equalities between canonical outputs under input transformations:
-- appending or splicing in blocks that are already subsumed (or duplicated),
-- and how a dominating coarse block absorbs the whole list. These are *list*
-- equalities, stronger than the membership characterisation of `collapse`.

/-- Subsumed-block absorption (exact list equality): appending one well-formed
    block `c` that is already subsumed by a strictly less-specific block of `xs`
    (`coveredBy c xs`) leaves the canonical output literally unchanged. -/
def spec_collapse_absorb_subsumed (impl : RepoImpl) : Prop :=
  ∀ (xs : List Cidr) (c : Cidr),
    c.prefixLen ≤ 32 →
    coveredByRef c xs = true →
    impl.ipaddress.collapse (xs ++ [c]) = impl.ipaddress.collapse xs

/-- Bulk subsumed-tail absorption (exact list equality): appending an entire
    list `ys` of well-formed blocks, each already subsumed by some strictly
    less-specific block of `xs`, leaves the canonical output literally unchanged.
    Generalises `spec_collapse_absorb_subsumed` to a whole list. -/
def spec_collapse_absorb_all_subsumed (impl : RepoImpl) : Prop :=
  ∀ (xs ys : List Cidr),
    (∀ c ∈ ys, c.prefixLen ≤ 32) →
    (∀ c ∈ ys, coveredByRef c xs = true) →
    impl.ipaddress.collapse (xs ++ ys) = impl.ipaddress.collapse xs

/-- Duplicate-tail absorption (exact list equality): appending blocks that
    already occur in `xs` leaves the canonical output literally unchanged —
    distinct from the subsumption laws, here the trailing copies are exact
    repeats rather than finer covered blocks. -/
def spec_collapse_absorb_duplicates (impl : RepoImpl) : Prop :=
  ∀ (xs ys : List Cidr),
    (∀ c ∈ ys, c ∈ xs) →
    impl.ipaddress.collapse (xs ++ ys) = impl.ipaddress.collapse xs

/-- Coarse-block absorption (exact list equality): if a single block `d` is
    strictly less specific than *every* block of `xs` and contains each of their
    network addresses, then prepending `d` collapses the whole input to the
    singleton `[d]`. Generalises `spec_collapse_chain_coarsest`. -/
def spec_collapse_dominator_absorbs (impl : RepoImpl) : Prop :=
  ∀ (xs : List Cidr) (d : Cidr),
    (∀ c ∈ xs, d.prefixLen < c.prefixLen ∧ memNet c.network d = true) →
    impl.ipaddress.collapse (d :: xs) = [d]

-- ── collapse: normalisation-commutation laws ───────────────────
-- Exact list/coverage equalities expressing that `collapse` commutes with
-- pre-normalising part of its input: pre-collapsing a prefix or a suffix of an
-- append, pre-pruning subsumed blocks, splicing in a redundant or dominating
-- block at an interior position, and coverage additivity / order-independence
-- over concatenation.

/-- Prefix-collapse idempotence (exact list equality): pre-collapsing the *first*
    segment of an append leaves the canonical output literally unchanged —
    `collapse (collapse xs ++ ys) = collapse (xs ++ ys)`. -/
def spec_collapse_prefix_collapse (impl : RepoImpl) : Prop :=
  ∀ (xs ys : List Cidr),
    (∀ c ∈ xs, c.prefixLen ≤ 32) →
    impl.ipaddress.collapse (impl.ipaddress.collapse xs ++ ys)
      = impl.ipaddress.collapse (xs ++ ys)

/-- Suffix-collapse idempotence (exact list equality): the mirror of the prefix
    law — pre-collapsing the *second* segment of an append leaves the canonical
    output literally unchanged, `collapse (xs ++ collapse ys) =
    collapse (xs ++ ys)`. -/
def spec_collapse_suffix_collapse (impl : RepoImpl) : Prop :=
  ∀ (xs ys : List Cidr),
    (∀ c ∈ ys, c.prefixLen ≤ 32) →
    impl.ipaddress.collapse (xs ++ impl.ipaddress.collapse ys)
      = impl.ipaddress.collapse (xs ++ ys)

/-- Idempotent pre-pruning (exact list equality): removing every subsumed block
    from the input *before* collapsing changes nothing —
    `collapse xs = collapse (xs.filter (¬ coveredBy · xs))`. -/
def spec_collapse_prepruned (impl : RepoImpl) : Prop :=
  ∀ (xs : List Cidr),
    (∀ c ∈ xs, c.prefixLen ≤ 32) →
    impl.ipaddress.collapse xs
      = impl.ipaddress.collapse (xs.filter (fun c => !coveredByRef c xs))

/-- Interior subsumed-block absorption (exact list equality): a well-formed block
    `c` subsumed by the rest of the input can be spliced in at *any* interior
    position without changing the canonical output —
    `collapse (xs ++ c :: ys) = collapse (xs ++ ys)` whenever
    `coveredBy c (xs ++ ys)`. Generalises the trailing-absorption laws to an
    arbitrary slot. -/
def spec_collapse_insert_subsumed (impl : RepoImpl) : Prop :=
  ∀ (xs ys : List Cidr) (c : Cidr),
    c.prefixLen ≤ 32 →
    coveredByRef c (xs ++ ys) = true →
    impl.ipaddress.collapse (xs ++ c :: ys) = impl.ipaddress.collapse (xs ++ ys)

/-- Interior dominator absorption (exact list equality): a single block `d`
    strictly less specific than every *other* block and containing each of their
    networks swallows the whole input to `[d]`, from *any* position —
    `collapse (xs1 ++ d :: xs2) = [d]`. Generalises
    `spec_collapse_dominator_absorbs` to an arbitrary slot. -/
def spec_collapse_dominator_anywhere (impl : RepoImpl) : Prop :=
  ∀ (xs1 xs2 : List Cidr) (d : Cidr),
    (∀ c ∈ xs1 ++ xs2, d.prefixLen < c.prefixLen ∧ memNet c.network d = true) →
    impl.ipaddress.collapse (xs1 ++ d :: xs2) = [d]

/-- Coverage union homomorphism (full domain): `collapse` distributes over list
    concatenation at the level of covered address sets — an address is covered by
    `collapse (xs ++ ys)` iff it is covered by `collapse xs` or by
    `collapse ys`. -/
def spec_collapse_coverage_union (impl : RepoImpl) : Prop :=
  ∀ (xs ys : List Cidr) (a : Addr),
    a < 2 ^ 32 →
    (∀ c ∈ xs, c.prefixLen ≤ 32) →
    (∀ c ∈ ys, c.prefixLen ≤ 32) →
    ((∃ c ∈ impl.ipaddress.collapse (xs ++ ys), impl.ipaddress.containsAddr a c = true) ↔
     ((∃ c ∈ impl.ipaddress.collapse xs, impl.ipaddress.containsAddr a c = true) ∨
      (∃ c ∈ impl.ipaddress.collapse ys, impl.ipaddress.containsAddr a c = true)))

/-- Coverage append-commutativity (full domain): swapping the two halves of an
    append does not change which addresses `collapse` covers —
    `collapse (xs ++ ys)` and `collapse (ys ++ xs)` cover exactly the same IPv4
    space. -/
def spec_collapse_coverage_comm (impl : RepoImpl) : Prop :=
  ∀ (xs ys : List Cidr) (a : Addr),
    a < 2 ^ 32 →
    (∀ c ∈ xs, c.prefixLen ≤ 32) →
    (∀ c ∈ ys, c.prefixLen ≤ 32) →
    ((∃ c ∈ impl.ipaddress.collapse (xs ++ ys), impl.ipaddress.containsAddr a c = true) ↔
     (∃ c ∈ impl.ipaddress.collapse (ys ++ xs), impl.ipaddress.containsAddr a c = true))

/-- Block-set order-independence (set level): the *survivor set* — which exact
    blocks appear — is invariant under swapping the two halves of an append:
    `c ∈ collapse (xs ++ ys) ↔ c ∈ collapse (ys ++ xs)`. Distinct from the
    coverage laws above (which compare covered *addresses*); the output *order*
    genuinely differs between the two arrangements. -/
def spec_collapse_block_set_comm (impl : RepoImpl) : Prop :=
  ∀ (xs ys : List Cidr) (c : Cidr),
    c ∈ impl.ipaddress.collapse (xs ++ ys) ↔ c ∈ impl.ipaddress.collapse (ys ++ xs)

/-- Range disjointness of the canonical output (cross-API): for aligned
    well-formed inputs, any two distinct output blocks occupy *non-overlapping
    address intervals* — one block's `[networkAddr, broadcast]` range lies
    entirely below the other's, `broadcast c1 < networkAddr c2 ∨ broadcast c2 <
    networkAddr c1`. The interval face of the canonical form's disjointness,
    expressed through the endpoint APIs rather than the internal `memNet` test. -/
def spec_collapse_disjoint_ranges (impl : RepoImpl) : Prop :=
  ∀ (xs : List Cidr) (c1 c2 : Cidr),
    (∀ c ∈ xs, c.prefixLen ≤ 32) →
    (∀ c ∈ xs, isAligned c) →
    c1 ∈ impl.ipaddress.collapse xs →
    c2 ∈ impl.ipaddress.collapse xs →
    c1 ≠ c2 →
    impl.ipaddress.broadcast c1 < impl.ipaddress.networkAddr c2 ∨
    impl.ipaddress.broadcast c2 < impl.ipaddress.networkAddr c1

/-- If all earlier blocks are discarded and the next block is retained,
    canonicalisation starts with that retained block. -/
def spec_collapse_head_first_survivor (impl : RepoImpl) : Prop :=
  ∀ (pre post : List Cidr) (c : Cidr),
    (∀ d ∈ pre, coveredByRef d (pre ++ c :: post) = true) →
    coveredByRef c (pre ++ c :: post) = false →
    (impl.ipaddress.collapse (pre ++ c :: post)).head? = some c

/-- A fresh retained block followed only by discarded blocks is the last block
    of the canonical result. -/
def spec_collapse_getLast_last_survivor (impl : RepoImpl) : Prop :=
  ∀ (pre post : List Cidr) (c : Cidr),
    c ∉ pre →
    coveredByRef c (pre ++ c :: post) = false →
    (∀ d ∈ post, coveredByRef d (pre ++ c :: post) = true) →
    (impl.ipaddress.collapse (pre ++ c :: post)).getLast? = some c

/-- A block occurs exactly once in the canonical output iff it is an uncovered
    input block. -/
def spec_collapse_count_survivor_exact (impl : RepoImpl) : Prop :=
  ∀ (xs : List Cidr) (c : Cidr),
    List.count c (impl.ipaddress.collapse xs) =
      if c ∈ xs ∧ coveredByRef c xs = false then 1 else 0

/-- Permuting the input only permutes the canonical output. -/
def spec_collapse_perm_of_input_perm (impl : RepoImpl) : Prop :=
  ∀ (xs ys : List Cidr),
    xs.Perm ys →
    (impl.ipaddress.collapse xs).Perm (impl.ipaddress.collapse ys)

/-- Swapping the two sides of an append only permutes the canonical output. -/
def spec_collapse_append_comm_perm (impl : RepoImpl) : Prop :=
  ∀ (xs ys : List Cidr),
    (impl.ipaddress.collapse (xs ++ ys)).Perm
      (impl.ipaddress.collapse (ys ++ xs))

/-- If a pre-normalised prefix contributes no leading block before a retained
    block, the full canonical result starts with that retained block. -/
def spec_collapse_head_after_precollapsed_prefix (impl : RepoImpl) : Prop :=
  ∀ (xs ys : List Cidr) (c : Cidr),
    (∀ d ∈ xs, d.prefixLen ≤ 32) →
    (∀ d ∈ impl.ipaddress.collapse xs,
      coveredByRef d (impl.ipaddress.collapse xs ++ c :: ys) = true) →
    coveredByRef c (impl.ipaddress.collapse xs ++ c :: ys) = false →
    (impl.ipaddress.collapse (xs ++ c :: ys)).head? = some c

-- ── collapse: positional first-occurrence ordering + counting ──
-- Laws pinning the canonical output as the distinct surviving blocks in
-- their input order, expressed through indices and multiplicities.

/-- Order preservation among survivors: for two distinct uncovered input
    blocks, one precedes the other in the canonical output exactly when it
    occurs earlier in the input — the relative order of surviving blocks is
    the relative order of their first input occurrences. -/
def spec_collapse_order_iff_first_indices (impl : RepoImpl) : Prop :=
  ∀ (xs : List Cidr) (c d : Cidr),
    c ∈ xs →
    d ∈ xs →
    c ≠ d →
    coveredByRef c xs = false →
    coveredByRef d xs = false →
    ((impl.ipaddress.collapse xs).idxOf c < (impl.ipaddress.collapse xs).idxOf d ↔
      xs.idxOf c < xs.idxOf d)

/-- Output index of a survivor: an uncovered input block sits at the position
    in the canonical output equal to the number of output blocks whose first
    input occurrence is earlier than its own. -/
def spec_collapse_idx_eq_prior_output_count (impl : RepoImpl) : Prop :=
  ∀ (xs : List Cidr) (c : Cidr),
    c ∈ xs →
    coveredByRef c xs = false →
    (impl.ipaddress.collapse xs).idxOf c =
      List.countP (fun d => decide (xs.idxOf d < xs.idxOf c))
        (impl.ipaddress.collapse xs)

/-- Output length as a positional count: the canonical output has exactly one
    block per input position that is the first occurrence of an uncovered
    block — the number of such positions is the output length. -/
def spec_collapse_length_first_survivor_positions (impl : RepoImpl) : Prop :=
  ∀ (xs : List Cidr),
    (impl.ipaddress.collapse xs).length =
      List.countP
        (fun i =>
          match (List.drop i xs).head? with
          | some c => (!coveredByRef c xs) && decide (xs.idxOf c = i)
          | none => false)
        (List.range xs.length)

/-- Aggregate transfer: for any Boolean predicate, its count over the canonical
    output equals its count over the distinct input blocks that are uncovered.
    The output realises exactly the uncovered blocks, once each. -/
def spec_collapse_countP_distinct_survivors (impl : RepoImpl) : Prop :=
  ∀ (xs : List Cidr) (p : Cidr → Bool),
    List.countP p (impl.ipaddress.collapse xs) =
      List.countP (fun c => p c && !coveredByRef c xs) xs.eraseDups

/-- Placement after a duplicate-free retained prefix: when every block of a
    duplicate-free prefix survives, a fresh surviving block appearing next lands
    at the output position equal to the prefix length. -/
def spec_collapse_index_after_retained_nodup_prefix (impl : RepoImpl) : Prop :=
  ∀ (pre post : List Cidr) (c : Cidr),
    pre.Nodup →
    c ∉ pre →
    (∀ d ∈ pre, coveredByRef d (pre ++ c :: post) = false) →
    coveredByRef c (pre ++ c :: post) = false →
    (impl.ipaddress.collapse (pre ++ c :: post)).idxOf c = pre.length

/-- Membership characterisation: a block appears in the canonical output
    exactly when it is an input block that no strictly less-specific input
    block subsumes. -/
def spec_collapse_mem_iff_survivor (impl : RepoImpl) : Prop :=
  ∀ (xs : List Cidr) (c : Cidr),
    c ∈ impl.ipaddress.collapse xs ↔ (c ∈ xs ∧ coveredByRef c xs = false)

-- ── supernet: unique aligned parent ────────────────────────────

/-- Uniqueness of the parent block: the only block at prefix length
    `prefixLen - 1` that is aligned and whose address range contains the
    child's stored network is `supernet` itself — the aligned parent is
    unique, not merely one coarser containing block. -/
def spec_supernet_unique_aligned_parent (impl : RepoImpl) : Prop :=
  ∀ (c p : Cidr),
    p.prefixLen = c.prefixLen - 1 →
    isAligned p →
    p.network ≤ c.network →
    c.network < p.network + blockSize p.prefixLen →
    p = impl.ipaddress.supernet c

-- ── containsAddr: key + in-block offset decomposition ──────────

/-- Membership as a key-plus-offset decomposition: an address lies in a block
    exactly when it equals the block's network key times the block size plus
    some in-block offset strictly below the block size — tying `containsAddr`
    to the frozen quotient (`keyAt`) and block-size arithmetic. -/
def spec_contains_key_remainder_decomposition (impl : RepoImpl) : Prop :=
  ∀ (a : Addr) (c : Cidr),
    c.prefixLen ≤ 32 →
    (impl.ipaddress.containsAddr a c = true ↔
      ∃ r : Nat,
        r < blockSize c.prefixLen ∧
        a = keyAt c.network c.prefixLen * blockSize c.prefixLen + r)
