import Netaddr.Harness

/-!
# Netaddr.Spec.Cidr

Specifications for the IPv4 CIDR bit-algebra. Each `spec_*` is a property over
an arbitrary `impl : RepoImpl`; the API is always reached through
`impl.netaddr.<fn>`.

The two headline operations are each pinned to a unique answer by a witness and
an optimality property:

* `spanningCidr` — the single *smallest* aligned block covering the inputs:
  alignment (`spec_spanning_aligned`), coverage (`spec_spanning_covers`,
  full-domain witness), and maximal prefix (`spec_spanning_maximal_prefix` — no
  aligned block of strictly longer prefix covers every input).

* `iprangeToCidrs` — the *minimal* aligned cover of `[lo, hi]`: exact two-sided
  coverage (`spec_iprange_covers_exact`), all-aligned, within-range, and no
  adjacent pair mergeable into one block (`spec_iprange_minimal_no_merge`).

The frozen mask vocabulary (`isAligned`, `coversAll`, `mergeableSpec` below, plus
`blockSize`, `keyAt`, `memNet`, `alignBase` from `Impl/Cidr.lean`) never
references `impl`: it is the specification's own ground truth. Everything is
anchored on `/`, `*`, `%`, `^`, `==`, `≤`, `<`.

DO NOT MODIFY — this file is frozen.
-/

-- ── frozen spec vocabulary (frozen ops only; never references `impl`) ──

/-- A block is *aligned* (its `network` field is already an exact multiple of
    its block size). Anchored purely on the frozen `/`, `*`, `^` mask
    arithmetic, never on any API. -/
def isAligned (c : Cidr) : Prop :=
  alignBase c.network c.prefixLen = c.network

/-- Frozen "covers every block of `xs`" predicate: `c` contains the network
    address and the broadcast address of every block in `xs`. -/
def coversAll (c : Cidr) (xs : List Cidr) : Prop :=
  ∀ d ∈ xs, memNet (alignBase d.network d.prefixLen) c = true ∧
            memNet (alignBase d.network d.prefixLen + blockSize d.prefixLen - 1) c = true

/-- Frozen "mergeable siblings" predicate (spec-side ground truth): two blocks
    of the same positive prefix length, both already aligned, with distinct
    bases but a common parent block at prefix `p-1` — i.e. they tile a single
    `/(p-1)` block and a canonical merge would fuse them. Anchored on `/`, `*`,
    `^`, `==`. -/
def mergeableSpec (c d : Cidr) : Prop :=
  c.prefixLen = d.prefixLen ∧ 0 < c.prefixLen ∧
    alignBase c.network c.prefixLen ≠ alignBase d.network d.prefixLen ∧
    alignBase c.network (c.prefixLen - 1) = alignBase d.network (d.prefixLen - 1)

-- ── frozen-op anchors: containsAddr / networkAddr / broadcast ───

/-- Range characterization (STRONG cross-API): an address lies in a block iff it
    falls within the closed interval `[networkAddr c, broadcast c]`. Ties
    membership to the two endpoint APIs over the entire `Addr` domain — the
    defining semantics of a CIDR block as a contiguous IP range. Any membership
    test off by one at an endpoint is rejected. -/
def spec_contains_iff_range (impl : RepoImpl) : Prop :=
  ∀ (a : Addr) (c : Cidr),
    impl.netaddr.containsAddr a c = true
      ↔ (impl.netaddr.networkAddr c ≤ a ∧ a ≤ impl.netaddr.broadcast c)

/-- `networkAddr` is the *least* address of a block: it lies in the block, and
    every contained address is at least as large. Pins `networkAddr` as the
    exact lower endpoint (extremal), not merely as some member. -/
def spec_network_addr_least (impl : RepoImpl) : Prop :=
  ∀ (c : Cidr),
    impl.netaddr.containsAddr (impl.netaddr.networkAddr c) c = true ∧
    (∀ a : Addr, impl.netaddr.containsAddr a c = true →
      impl.netaddr.networkAddr c ≤ a)

/-- `broadcast` is the *greatest* address of a block: it lies in the block, and
    no contained address exceeds it. Pins `broadcast` as the exact upper endpoint
    (extremal). -/
def spec_broadcast_greatest (impl : RepoImpl) : Prop :=
  ∀ (c : Cidr),
    impl.netaddr.containsAddr (impl.netaddr.broadcast c) c = true ∧
    (∀ a : Addr, impl.netaddr.containsAddr a c = true →
      a ≤ impl.netaddr.broadcast c)

/-- The network address is block-aligned: it is an exact multiple of the block
    size (its low `32 - prefixLen` bits are zero). -/
def spec_network_addr_aligned (impl : RepoImpl) : Prop :=
  ∀ (c : Cidr), impl.netaddr.networkAddr c % blockSize c.prefixLen = 0

/-- Defining equation of `broadcast`: it is exactly the network address plus one
    less than the block size (the last address of the block). Pins the `+`, `-`
    arithmetic relating the two endpoints. -/
def spec_broadcast_eq (impl : RepoImpl) : Prop :=
  ∀ (c : Cidr),
    impl.netaddr.broadcast c
      = impl.netaddr.networkAddr c + blockSize c.prefixLen - 1

-- ── spanningCidr: smallest aligned block spanning the inputs ────

/-- Empty input boundary: `spanningCidr [] = ⟨0, 0⟩`. -/
def spec_spanning_empty (impl : RepoImpl) : Prop :=
  impl.netaddr.spanningCidr [] = ⟨0, 0⟩

/-- Alignment (canonical form): the spanning block's network field is
    block-aligned. The output is always a genuine CIDR network address. -/
def spec_spanning_aligned (impl : RepoImpl) : Prop :=
  ∀ (xs : List Cidr), isAligned (impl.netaddr.spanningCidr xs)

/-- Coverage (full domain): every address in any input block lies in the
    spanning block. Quantifies over the whole `∀ a < 2^32` space; the
    well-formedness premise is the IPv4 convention (`prefixLen ≤ 32`). -/
def spec_spanning_covers (impl : RepoImpl) : Prop :=
  ∀ (xs : List Cidr) (a : Addr) (c : Cidr),
    a < 2 ^ 32 →
    (∀ d ∈ xs, d.network < 2 ^ 32 ∧ d.prefixLen ≤ 32) →
    c ∈ xs →
    memNet a c = true →
    impl.netaddr.containsAddr a (impl.netaddr.spanningCidr xs) = true

/-- Maximal-prefix optimality: any aligned block `c'` that covers every input
    block (via the frozen `coversAll`) has a prefix length no longer than the
    spanning block's. Since a longer prefix means a smaller block, the spanning
    block is the smallest (tightest) aligned cover. -/
def spec_spanning_maximal_prefix (impl : RepoImpl) : Prop :=
  ∀ (xs : List Cidr) (c' : Cidr),
    xs ≠ [] →
    (∀ d ∈ xs, d.prefixLen ≤ 32) →
    isAligned c' →
    c'.prefixLen ≤ 32 →
    coversAll c' xs →
    c'.prefixLen ≤ (impl.netaddr.spanningCidr xs).prefixLen

/-- Well-formedness: the spanning block has `prefixLen ≤ 32`. -/
def spec_spanning_wf (impl : RepoImpl) : Prop :=
  ∀ (xs : List Cidr), (impl.netaddr.spanningCidr xs).prefixLen ≤ 32

/-- The spanning block is itself a cover (frozen `coversAll`): for well-formed
    inputs every input block's endpoints lie in the output. -/
def spec_spanning_coversAll (impl : RepoImpl) : Prop :=
  ∀ (xs : List Cidr),
    (∀ d ∈ xs, d.network < 2 ^ 32 ∧ d.prefixLen ≤ 32) →
    coversAll (impl.netaddr.spanningCidr xs) xs

/-- The spanning block is never more specific than any input: its prefix length
    is at most every input block's prefix length, so it can only be the same size
    or coarser. Pins the monotone "spanning only coarsens" direction. -/
def spec_spanning_le_each (impl : RepoImpl) : Prop :=
  ∀ (xs : List Cidr) (c : Cidr),
    c ∈ xs →
    (∀ d ∈ xs, d.network < 2 ^ 32 ∧ d.prefixLen ≤ 32) →
    (impl.netaddr.spanningCidr xs).prefixLen ≤ c.prefixLen

/-- Tightness on a singleton aligned input: a single already-aligned block spans
    to *itself* — `spanningCidr [c] = c`. -/
def spec_spanning_singleton (impl : RepoImpl) : Prop :=
  ∀ (c : Cidr), isAligned c → c.network < 2 ^ 32 → c.prefixLen ≤ 32 →
    impl.netaddr.spanningCidr [c] = c

-- ── iprangeToCidrs: minimal aligned cover of [lo, hi] ───────────

/-- Exact coverage (full domain): an address is covered by some block of
    `iprangeToCidrs lo hi` iff it lies in the inclusive range `[lo, hi]`.
    Quantifies over the entire `∀ a < 2^32` space, so the output covers the range
    exactly — no more, no less. -/
def spec_iprange_covers_exact (impl : RepoImpl) : Prop :=
  ∀ (lo hi : Addr) (a : Addr),
    a < 2 ^ 32 →
    ((∃ c ∈ impl.netaddr.iprangeToCidrs lo hi, impl.netaddr.containsAddr a c = true) ↔
     (lo ≤ a ∧ a ≤ hi))

/-- Every output block is aligned (canonical form): each `⟨network, prefixLen⟩`
    in `iprangeToCidrs lo hi` is a genuine CIDR network address. -/
def spec_iprange_all_aligned (impl : RepoImpl) : Prop :=
  ∀ (lo hi : Addr) (c : Cidr),
    c ∈ impl.netaddr.iprangeToCidrs lo hi → isAligned c

/-- Well-formedness: every output block has `prefixLen ≤ 32`. -/
def spec_iprange_wf (impl : RepoImpl) : Prop :=
  ∀ (lo hi : Addr) (c : Cidr),
    c ∈ impl.netaddr.iprangeToCidrs lo hi → c.prefixLen ≤ 32

/-- Within-range (no overshoot): every output block lies entirely inside
    `[lo, hi]` — its network address is `≥ lo` and its broadcast is `≤ hi`. The
    decomposition never emits a block that spills past the requested range. -/
def spec_iprange_within (impl : RepoImpl) : Prop :=
  ∀ (lo hi : Addr) (c : Cidr),
    c ∈ impl.netaddr.iprangeToCidrs lo hi →
      lo ≤ impl.netaddr.networkAddr c ∧ impl.netaddr.broadcast c ≤ hi

/-- Minimality: no two *consecutive* output blocks could be replaced by a single
    aligned block. For adjacent outputs `c₁, c₂` (`c₁` immediately followed by
    `c₂`), they are NOT mergeable siblings (`mergeableSpec`). -/
def spec_iprange_minimal_no_merge (impl : RepoImpl) : Prop :=
  ∀ (lo hi : Addr) (c1 c2 : Cidr) (pre post : List Cidr),
    impl.netaddr.iprangeToCidrs lo hi = pre ++ c1 :: c2 :: post →
      ¬ mergeableSpec c1 c2

/-- Empty range: when `hi < lo` the range is empty and the decomposition is the
    empty list. -/
def spec_iprange_empty (impl : RepoImpl) : Prop :=
  ∀ (lo hi : Addr), hi < lo → impl.netaddr.iprangeToCidrs lo hi = []

/-- Single point: a degenerate range `[a, a]` decomposes to the single `/32`
    host block `⟨a, 32⟩`. -/
def spec_iprange_point (impl : RepoImpl) : Prop :=
  ∀ (a : Addr), impl.netaddr.iprangeToCidrs a a = [⟨a, 32⟩]

/-- A whole aligned block decomposes to itself: if `[lo, hi]` is exactly the
    address range of an aligned `/p` block (`lo` aligned to `p` and
    `hi = lo + 2^(32-p) - 1`), then `iprangeToCidrs lo hi = [⟨lo, p⟩]` — a single
    block, the tightest possible cover. -/
def spec_iprange_aligned_block (impl : RepoImpl) : Prop :=
  ∀ (lo p : Nat),
    p ≤ 32 →
    lo % blockSize p = 0 →
    impl.netaddr.iprangeToCidrs lo (lo + blockSize p - 1) = [⟨lo, p⟩]

-- ── iprangeToCidrs: deep structural / counting obligations ──────

/-- Disjointness: any two *distinct* output blocks of a range decomposition are
    disjoint — neither block's network address lies in the other. -/
def spec_iprange_disjoint (impl : RepoImpl) : Prop :=
  ∀ (lo hi : Addr) (c1 c2 : Cidr),
    c1 ∈ impl.netaddr.iprangeToCidrs lo hi →
    c2 ∈ impl.netaddr.iprangeToCidrs lo hi →
    c1 ≠ c2 →
    memNet c2.network c1 = false ∧ memNet c1.network c2 = false

/-- Strictly ascending output (canonical order): the network addresses of
    `iprangeToCidrs lo hi` are strictly increasing along the list. This forbids
    duplicate blocks and pins a unique left-to-right order. -/
def spec_iprange_ascending (impl : RepoImpl) : Prop :=
  ∀ (lo hi : Addr),
    List.Pairwise (fun a b => a.network < b.network)
      (impl.netaddr.iprangeToCidrs lo hi)

/-- Coverage of each endpoint (witness anchors): for a non-empty range
    (`lo ≤ hi`), both `lo` and `hi` are covered by some output block. A direct
    membership witness pinning the two boundary addresses, complementing the
    full-domain `spec_iprange_covers_exact`. -/
def spec_iprange_covers_endpoints (impl : RepoImpl) : Prop :=
  ∀ (lo hi : Addr),
    lo ≤ hi →
      (∃ c ∈ impl.netaddr.iprangeToCidrs lo hi, impl.netaddr.containsAddr lo c = true) ∧
      (∃ c ∈ impl.netaddr.iprangeToCidrs lo hi, impl.netaddr.containsAddr hi c = true)

/-- Exact contiguous tiling: any two *consecutive* output blocks abut with no gap
    and no overlap — the broadcast of the earlier block is exactly one below the
    network address of the next (`broadcast c1 + 1 = networkAddr c2`). Together
    with `spec_iprange_ascending` and `spec_iprange_disjoint` this pins the output
    as an exact partition of `[lo, hi]` into abutting aligned blocks. -/
def spec_iprange_contiguous (impl : RepoImpl) : Prop :=
  ∀ (lo hi : Addr) (c1 c2 : Cidr) (pre post : List Cidr),
    impl.netaddr.iprangeToCidrs lo hi = pre ++ c1 :: c2 :: post →
      impl.netaddr.broadcast c1 + 1 = impl.netaddr.networkAddr c2

/-- Head maximality: for a non-empty range (`lo ≤ hi`) the decomposition is a
    non-empty list whose *first* block is based exactly at `lo`, and that head
    block is the largest aligned block startable at `lo` that still fits inside
    `[lo, hi]`: any aligned prefix length `q` whose `/q` block based at `lo` fits
    in the range (`lo` aligned to `q`, `lo + blockSize q - 1 ≤ hi`) is no finer
    than the head (`head.prefixLen ≤ q`). -/
def spec_iprange_head_greedy (impl : RepoImpl) : Prop :=
  ∀ (lo hi : Addr),
    lo ≤ hi →
      ∃ (c : Cidr) (rest : List Cidr),
        impl.netaddr.iprangeToCidrs lo hi = c :: rest ∧
        c.network = lo ∧
        (∀ q : Nat, q ≤ 32 → lo % blockSize q = 0 → lo + blockSize q - 1 ≤ hi →
          c.prefixLen ≤ q)

/-- Spanning is the least aligned cover (containment): the spanning block is
    *contained in* every aligned block `c'` that covers all inputs — both its
    network address and its broadcast lie in `c'` (via the frozen `memNet`).
    Stronger than the prefix-length bound: the spanning block is the least upper
    bound in the containment order. -/
def spec_spanning_least_cover (impl : RepoImpl) : Prop :=
  ∀ (xs : List Cidr) (c' : Cidr),
    xs ≠ [] →
    (∀ d ∈ xs, d.network < 2 ^ 32 ∧ d.prefixLen ≤ 32) →
    isAligned c' →
    c'.prefixLen ≤ 32 →
    coversAll c' xs →
    memNet (impl.netaddr.networkAddr (impl.netaddr.spanningCidr xs)) c' = true ∧
    memNet (impl.netaddr.broadcast (impl.netaddr.spanningCidr xs)) c' = true

-- ── new candidate hardening specs (statements only) ───────────

/-- Exact per-address ownership: for every IPv4 address, the range
    decomposition contains exactly one block covering it when the address is in
    the requested interval, and no covering block otherwise. -/
def spec_iprange_cover_count (impl : RepoImpl) : Prop :=
  ∀ (lo hi a : Addr),
    a < 2 ^ 32 →
      ((impl.netaddr.iprangeToCidrs lo hi).filter
        (fun c => impl.netaddr.containsAddr a c)).length
        = if decide (lo ≤ a ∧ a ≤ hi) then 1 else 0

/-- Every suffix of a range decomposition is exactly the decomposition of the
    still-uncovered interval immediately after the preceding block. -/
def spec_iprange_suffix_restarts (impl : RepoImpl) : Prop :=
  ∀ (lo hi : Addr) (c : Cidr) (pre post : List Cidr),
    impl.netaddr.iprangeToCidrs lo hi = pre ++ c :: post →
      post = impl.netaddr.iprangeToCidrs (impl.netaddr.broadcast c + 1) hi

/-- Decomposing a non-empty IPv4 interval and then spanning the emitted blocks
    gives the same block as spanning the interval's two endpoint host blocks. -/
def spec_iprange_spanning_roundtrip (impl : RepoImpl) : Prop :=
  ∀ (lo hi : Addr),
    lo ≤ hi →
    hi < 2 ^ 32 →
      impl.netaddr.spanningCidr (impl.netaddr.iprangeToCidrs lo hi)
        = impl.netaddr.spanningCidr [⟨lo, 32⟩, ⟨hi, 32⟩]

/-- The spanning result depends only on which input blocks are present, not on
    their order or repeated occurrences. -/
def spec_spanning_membership_invariant (impl : RepoImpl) : Prop :=
  ∀ (xs ys : List Cidr),
    xs ≠ [] →
    ys ≠ [] →
    (∀ c : Cidr, c ∈ xs ↔ c ∈ ys) →
      impl.netaddr.spanningCidr xs = impl.netaddr.spanningCidr ys

-- ── frozen spec vocabulary for positional / counting laws ──────

/-- Total address count of a list of blocks: the sum of their block sizes.
    Frozen `^`, `+` only. -/
def specBlockCount : List Cidr → Nat
  | [] => 0
  | c :: cs => blockSize c.prefixLen + specBlockCount cs

/-- The addresses of a single block, listed in ascending order. Frozen `^`, `+`. -/
def specBlockAddrs (c : Cidr) : List Addr :=
  (List.range (blockSize c.prefixLen)).map (fun i => c.network + i)

/-- The addresses of a list of blocks, concatenated left to right. -/
def specCidrsAddrs : List Cidr → List Addr
  | [] => []
  | c :: cs => specBlockAddrs c ++ specCidrsAddrs cs

/-- The inclusive integer interval `[lo, hi]`, listed in ascending order.
    Frozen `+`, `-`. -/
def specRangeAddrs (lo hi : Addr) : List Addr :=
  (List.range (hi + 1 - lo)).map (fun i => lo + i)

-- ── iprangeToCidrs: positional / enumeration / counting laws ────

/-- Exact enumeration: concatenating the addresses of every block of
    `iprangeToCidrs lo hi` (in list order) yields exactly the interval `[lo, hi]`
    in ascending order, with no repeats and with total length `hi + 1 - lo`. -/
def spec_iprange_enumerates_range (impl : RepoImpl) : Prop :=
  ∀ (lo hi : Addr),
    lo ≤ hi →
    hi < 2 ^ 32 →
      let addrs := specCidrsAddrs (impl.netaddr.iprangeToCidrs lo hi)
      addrs.Nodup ∧
      addrs.length = hi + 1 - lo ∧
      addrs = specRangeAddrs lo hi

/-- Positional base law: the network address of any block equals `lo` plus the
    combined address count of all blocks preceding it in the output list. -/
def spec_iprange_prefix_base (impl : RepoImpl) : Prop :=
  ∀ (lo hi : Addr) (c : Cidr) (pre post : List Cidr),
    lo ≤ hi →
    hi < 2 ^ 32 →
    impl.netaddr.iprangeToCidrs lo hi = pre ++ c :: post →
      c.network = lo + specBlockCount pre

/-- Prefix self-similarity: any non-empty consumed prefix of a decomposition is
    itself the decomposition of the sub-interval it covers, `[lo, c.network - 1]`
    for the block `c` immediately after the prefix. -/
def spec_iprange_prefix_selfsimilar (impl : RepoImpl) : Prop :=
  ∀ (lo hi : Addr) (c : Cidr) (pre post : List Cidr),
    lo ≤ hi →
    hi < 2 ^ 32 →
    impl.netaddr.iprangeToCidrs lo hi = pre ++ c :: post →
    pre ≠ [] →
      pre = impl.netaddr.iprangeToCidrs lo (c.network - 1)

/-- No duplicate blocks and no duplicate network bases; every block occurs
    exactly once in the output list. -/
def spec_iprange_nodup_count (impl : RepoImpl) : Prop :=
  ∀ (lo hi : Addr),
    hi < 2 ^ 32 →
      let out := impl.netaddr.iprangeToCidrs lo hi
      out.Nodup ∧
      (out.map (fun c => c.network)).Nodup ∧
      (∀ c : Cidr,
        (out.filter (fun d => decide (d = c))).length =
          if decide (c ∈ out) then 1 else 0)

/-- Uniqueness of the decomposition: any aligned, strictly-ascending,
    no-adjacent-mergeable list of blocks whose concatenated addresses are exactly
    the interval `[lo, hi]` equals `iprangeToCidrs lo hi`. -/
def spec_iprange_unique_cover (impl : RepoImpl) : Prop :=
  ∀ (lo hi : Addr) (ys : List Cidr),
    hi < 2 ^ 32 →
    (∀ c ∈ ys, isAligned c ∧ c.prefixLen ≤ 32) →
    List.Pairwise (fun a b => a.network < b.network) ys →
    (∀ (c1 c2 : Cidr) (pre post : List Cidr),
      ys = pre ++ c1 :: c2 :: post → ¬ mergeableSpec c1 c2) →
    specCidrsAddrs ys = specRangeAddrs lo hi →
      ys = impl.netaddr.iprangeToCidrs lo hi

-- ── spanningCidr: first-survivor / uniqueness / obstruction ─────

/-- First-survivor: if the head block is already aligned and covers every block
    in the tail, spanning the whole list returns that head block unchanged. -/
def spec_spanning_head_survivor (impl : RepoImpl) : Prop :=
  ∀ (c : Cidr) (xs : List Cidr),
    isAligned c →
    c.network < 2 ^ 32 →
    c.prefixLen ≤ 32 →
    (∀ d ∈ xs, d.network < 2 ^ 32 ∧ d.prefixLen ≤ 32) →
    coversAll c xs →
      impl.netaddr.spanningCidr (c :: xs) = c

/-- Same-prefix uniqueness: an aligned cover of the inputs whose prefix length
    equals the spanning block's is exactly the spanning block. -/
def spec_spanning_prefix_unique (impl : RepoImpl) : Prop :=
  ∀ (xs : List Cidr) (c' : Cidr),
    xs ≠ [] →
    (∀ d ∈ xs, d.network < 2 ^ 32 ∧ d.prefixLen ≤ 32) →
    isAligned c' →
    c'.prefixLen ≤ 32 →
    coversAll c' xs →
    c'.prefixLen = (impl.netaddr.spanningCidr xs).prefixLen →
      c' = impl.netaddr.spanningCidr xs

/-- Endpoint obstruction: whenever the spanning block is coarser than `/32`,
    there are input blocks whose lowest and highest addresses already disagree at
    the bit just past the spanning prefix. -/
def spec_spanning_next_bit_witness (impl : RepoImpl) : Prop :=
  ∀ (xs : List Cidr),
    xs ≠ [] →
    (∀ d ∈ xs, d.network < 2 ^ 32 ∧ d.prefixLen ≤ 32) →
    (impl.netaddr.spanningCidr xs).prefixLen < 32 →
      ∃ dLo, dLo ∈ xs ∧
        ∃ dHi, dHi ∈ xs ∧
          keyAt (alignBase dLo.network dLo.prefixLen)
              ((impl.netaddr.spanningCidr xs).prefixLen + 1) ≠
            keyAt (alignBase dHi.network dHi.prefixLen + blockSize dHi.prefixLen - 1)
              ((impl.netaddr.spanningCidr xs).prefixLen + 1)

/-- Ordered-run reduction: for a list whose first block supplies the lowest base
    and whose last block supplies the highest broadcast, the interior blocks do
    not affect the span — it equals the span of the two endpoint blocks alone. -/
def spec_spanning_ordered_run (impl : RepoImpl) : Prop :=
  ∀ (first last : Cidr) (middle : List Cidr),
    (∀ d ∈ first :: middle ++ [last], d.network < 2 ^ 32 ∧ d.prefixLen ≤ 32) →
    (∀ d ∈ middle ++ [last],
      alignBase first.network first.prefixLen ≤ alignBase d.network d.prefixLen) →
    (∀ d ∈ first :: middle,
      alignBase d.network d.prefixLen + blockSize d.prefixLen - 1 ≤
        alignBase last.network last.prefixLen + blockSize last.prefixLen - 1) →
      impl.netaddr.spanningCidr (first :: middle ++ [last]) =
        impl.netaddr.spanningCidr [first, last]
