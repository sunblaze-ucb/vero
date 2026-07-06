import Difflib.Harness

/-!
# Difflib.Spec.SequenceMatcher

Specifications for the sequence-matching operations. Each `spec_*` is a
property over an arbitrary `impl : RepoImpl`; an API is always reached
through `impl.difflib.<fn>`.

The obligations are stated against a frozen ground-truth notion of a common
contiguous block: `isCommonBlock a b i j k` holds when `a[i:i+k] = b[j:j+k]`
and the window fits both sequences. `findLongestMatch` must return a common
block that is longest and canonically least under
*k maximal → i minimal → j minimal*. `getMatchingBlocks` is specified by
structural invariants anchored to `findLongestMatch`; no spec claims global
optimality of the block decomposition.

`isCommonBlock` never refers to `impl`, so it is the specification's own
ground truth. DO NOT MODIFY.
-/

-- ── Frozen ground-truth block machinery (DO NOT MODIFY) ─────────

/-- `isCommonBlock a b i j k`: `(i, j, k)` is a genuine common contiguous
    block of `a` and `b` — the index window fits in both sequences and the
    two `k`-length slices are equal. The specification's own ground truth,
    independent of any implementation. The empty block `(i, j, 0)` with
    `i ≤ |a|`, `j ≤ |b|` is always common. -/
def isCommonBlock (a b : Sequence) (i j k : Nat) : Prop :=
  i + k ≤ a.length ∧ j + k ≤ b.length ∧ (a.drop i).take k = (b.drop j).take k

-- ════════════════════════════════════════════════════════════════
-- findLongestMatch: witness ∧ maximality ∧ canonical tie-break.
-- ════════════════════════════════════════════════════════════════

/-- Witness: the returned block is a genuine common block — its two
    `k`-length slices are equal and its window fits in both sequences. -/
def spec_flm_witness (impl : RepoImpl) : Prop :=
  ∀ (a b : Sequence) (i j k : Nat),
    impl.difflib.findLongestMatch a b = (i, j, k) → isCommonBlock a b i j k

/-- Maximality: the returned length `k` is no smaller than the length of
    any common block of `a` and `b`. -/
def spec_flm_maximal (impl : RepoImpl) : Prop :=
  ∀ (a b : Sequence) (i j k : Nat),
    impl.difflib.findLongestMatch a b = (i, j, k) →
      ∀ (i' j' k' : Nat), isCommonBlock a b i' j' k' → k' ≤ k

/-- Index bounds: the returned start indices and length fit inside the
    sequences — `i + k ≤ |a|` and `j + k ≤ |b|`. -/
def spec_flm_bounds (impl : RepoImpl) : Prop :=
  ∀ (a b : Sequence) (i j k : Nat),
    impl.difflib.findLongestMatch a b = (i, j, k) →
      i + k ≤ a.length ∧ j + k ≤ b.length

/-- Tie-break in `a` (canonical `i` minimal): among all maximal common
    blocks (length equal to the returned `k`), the returned `i` is the
    smallest. -/
def spec_flm_tiebreak_i (impl : RepoImpl) : Prop :=
  ∀ (a b : Sequence) (i j k : Nat),
    impl.difflib.findLongestMatch a b = (i, j, k) →
      ∀ (i' j' : Nat), isCommonBlock a b i' j' k → i ≤ i'

/-- Tie-break in `b` (canonical `j` minimal at the chosen `i`): among all
    maximal common blocks that also start at the returned `i`, the returned
    `j` is the smallest. -/
def spec_flm_tiebreak_j (impl : RepoImpl) : Prop :=
  ∀ (a b : Sequence) (i j k : Nat),
    impl.difflib.findLongestMatch a b = (i, j, k) →
      ∀ (j' : Nat), isCommonBlock a b i j' k → j ≤ j'

/-- Uniqueness: any block that is itself a witness, maximal, and canonically
    least under *k maximal → i minimal → j minimal* must equal the returned
    block — the canonical longest match is unique. -/
def spec_flm_unique (impl : RepoImpl) : Prop :=
  ∀ (a b : Sequence) (i j k : Nat),
    impl.difflib.findLongestMatch a b = (i, j, k) →
      ∀ (i' j' k' : Nat),
        isCommonBlock a b i' j' k' →
        (∀ i'' j'' k'', isCommonBlock a b i'' j'' k'' → k'' ≤ k') →
        (∀ i'' j'', isCommonBlock a b i'' j'' k' → i' ≤ i'') →
        (∀ j'', isCommonBlock a b i' j'' k' → j' ≤ j'') →
          (i', j', k') = (i, j, k)

/-- Empty first sequence: `findLongestMatch [] b = (0, 0, 0)`. -/
def spec_flm_empty_left (impl : RepoImpl) : Prop :=
  ∀ (b : Sequence),
    impl.difflib.findLongestMatch [] b = (0, 0, 0)

/-- Empty second sequence: `findLongestMatch a [] = (0, 0, 0)`. -/
def spec_flm_empty_right (impl : RepoImpl) : Prop :=
  ∀ (a : Sequence),
    impl.difflib.findLongestMatch a [] = (0, 0, 0)

/-- Size positivity is exactly common-element existence: the longest match
    has positive length iff `a` and `b` share some element at some
    positions. -/
def spec_flm_size_pos_iff (impl : RepoImpl) : Prop :=
  ∀ (a b : Sequence) (i j k : Nat),
    impl.difflib.findLongestMatch a b = (i, j, k) →
      (0 < k ↔ ∃ p q, p < a.length ∧ q < b.length ∧ a[p]! = b[q]!)

/-- Match length is bounded by both sequence lengths: `k ≤ |a|` and
    `k ≤ |b|`. -/
def spec_flm_size_le (impl : RepoImpl) : Prop :=
  ∀ (a b : Sequence) (i j k : Nat),
    impl.difflib.findLongestMatch a b = (i, j, k) →
      k ≤ a.length ∧ k ≤ b.length

/-- Self-match is total: a nonempty sequence matched against itself returns
    the whole sequence, `(0, 0, |a|)`. -/
def spec_flm_self (impl : RepoImpl) : Prop :=
  ∀ (a : Sequence),
    a ≠ [] → impl.difflib.findLongestMatch a a = (0, 0, a.length)

-- ── matchSize: ties the observer to findLongestMatch ────────────

/-- `matchSize` is the third component of `findLongestMatch`: the two APIs
    agree on the match length. -/
def spec_matchSize_correct (impl : RepoImpl) : Prop :=
  ∀ (a b : Sequence),
    impl.difflib.matchSize a b = (impl.difflib.findLongestMatch a b).2.2

/-- `matchSize` is maximal: it is no smaller than the length of any common
    block. -/
def spec_matchSize_maximal (impl : RepoImpl) : Prop :=
  ∀ (a b : Sequence) (i' j' k' : Nat),
    isCommonBlock a b i' j' k' → k' ≤ impl.difflib.matchSize a b

-- ════════════════════════════════════════════════════════════════
-- getMatchingBlocks: structural invariants anchored to findLongestMatch.
-- No spec claims global optimality of the decomposition.
-- ════════════════════════════════════════════════════════════════

/-- Sentinel terminator: the last block is always `(|a|, |b|, 0)`. -/
def spec_gmb_sentinel (impl : RepoImpl) : Prop :=
  ∀ (a b : Sequence),
    (impl.difflib.getMatchingBlocks a b).getLast? = some (a.length, b.length, 0)

/-- Non-emptiness: `getMatchingBlocks` always returns at least the sentinel,
    so the list is never empty. -/
def spec_gmb_nonempty (impl : RepoImpl) : Prop :=
  ∀ (a b : Sequence),
    impl.difflib.getMatchingBlocks a b ≠ []

/-- Every emitted block is a genuine common block: each `(i, j, k)` in the
    list satisfies `isCommonBlock`. -/
def spec_gmb_blocks_common (impl : RepoImpl) : Prop :=
  ∀ (a b : Sequence) (blk : Block),
    blk ∈ impl.difflib.getMatchingBlocks a b →
      isCommonBlock a b blk.1 blk.2.1 blk.2.2

/-- Each emitted block's length is bounded by the global longest match: no
    block in the decomposition is longer than `findLongestMatch a b`'s
    size. -/
def spec_gmb_block_size_le_flm (impl : RepoImpl) : Prop :=
  ∀ (a b : Sequence) (blk : Block),
    blk ∈ impl.difflib.getMatchingBlocks a b →
      blk.2.2 ≤ (impl.difflib.findLongestMatch a b).2.2

/-- Empty-empty case: `getMatchingBlocks [] [] = [(0, 0, 0)]` — exactly the
    sentinel and nothing else. -/
def spec_gmb_empty (impl : RepoImpl) : Prop :=
  impl.difflib.getMatchingBlocks [] [] = [(0, 0, 0)]

-- ════════════════════════════════════════════════════════════════
-- Further structural laws over the whole block list: the global longest
-- match appears in the list, the blocks tile the sequences without
-- overlapping, the total matched length is bounded, and the maximum block
-- length equals the global match. No claim of global optimality.
-- ════════════════════════════════════════════════════════════════

/-- The global longest match is one of the emitted blocks. When
    `findLongestMatch a b` has positive length, the same `(i, j, k)` occurs
    in `getMatchingBlocks a b`. The positivity guard is essential: when
    `k = 0` the list is just the sentinel `(|a|, |b|, 0)`. -/
def spec_gmb_contains_flm (impl : RepoImpl) : Prop :=
  ∀ (a b : Sequence) (i j k : Nat),
    impl.difflib.findLongestMatch a b = (i, j, k) →
      0 < k → (i, j, k) ∈ impl.difflib.getMatchingBlocks a b

/-- Adjacent blocks are non-overlapping and increasing in both coordinates:
    for consecutive entries `(i₁,j₁,k₁)` then `(i₂,j₂,k₂)`, the first block
    ends no later than the second begins, in `a` (`i₁ + k₁ ≤ i₂`) and in `b`
    (`j₁ + k₁ ≤ j₂`). The matched windows tile the two sequences
    left-to-right with no overlap, up to and including the trailing
    sentinel. -/
def spec_gmb_adjacent_nonoverlap (impl : RepoImpl) : Prop :=
  ∀ (a b : Sequence) (n : Nat),
    n + 1 < (impl.difflib.getMatchingBlocks a b).length →
      let p := (impl.difflib.getMatchingBlocks a b)[n]!
      let q := (impl.difflib.getMatchingBlocks a b)[n + 1]!
      p.1 + p.2.2 ≤ q.1 ∧ p.2.1 + p.2.2 ≤ q.2.1

/-- Every emitted block other than the trailing sentinel has positive
    length: the only size-`0` block is the final sentinel `(|a|, |b|, 0)`. -/
def spec_gmb_interior_positive (impl : RepoImpl) : Prop :=
  ∀ (a b : Sequence) (blk : Block),
    blk ∈ impl.difflib.getMatchingBlocks a b →
      blk = (a.length, b.length, 0) ∨ 0 < blk.2.2

/-- The total matched length is bounded by the shorter sequence: summing the
    block lengths over the whole list yields at most `min |a| |b|`. -/
def spec_gmb_total_len_le (impl : RepoImpl) : Prop :=
  ∀ (a b : Sequence),
    ((impl.difflib.getMatchingBlocks a b).map (fun blk => blk.2.2)).sum
      ≤ min a.length b.length

/-- The longest block in the decomposition is exactly the global longest
    match: the maximum block length over `getMatchingBlocks a b` equals
    `(findLongestMatch a b).2.2`. -/
def spec_gmb_max_block_is_flm (impl : RepoImpl) : Prop :=
  ∀ (a b : Sequence),
    ((impl.difflib.getMatchingBlocks a b).map (fun blk => blk.2.2)).foldl Nat.max 0
      = (impl.difflib.findLongestMatch a b).2.2

/-- A second real match must be surfaced. Whenever the global longest match
    `(i, j, k)` is positive and the residual sequences after it — `a[i+k:]`
    and `b[j+k:]` — still share a common element (their `matchSize` is
    positive), `getMatchingBlocks a b` must contain a positive-length block
    distinct from `(i, j, k)`. Stated for all `a`, `b` under this structural
    precondition, it rules out a diff that stops after the first match. It
    does not claim global optimality of the decomposition. -/
def spec_gmb_recursive_second_block (impl : RepoImpl) : Prop :=
  ∀ (a b : Sequence) (i j k : Nat),
    impl.difflib.findLongestMatch a b = (i, j, k) →
      0 < k →
      0 < impl.difflib.matchSize (a.drop (i + k)) (b.drop (j + k)) →
        ∃ blk ∈ impl.difflib.getMatchingBlocks a b,
          0 < blk.2.2 ∧ blk ≠ (i, j, k)

-- ════════════════════════════════════════════════════════════════
-- findLongestMatch: two more whole-domain laws.
-- ════════════════════════════════════════════════════════════════

/-- Global canonical domination: the returned block is canonically at least
    as good as every common block under the full order
    *k maximal → i minimal → j minimal*, stated as one disjunction. For any
    common block `(i', j', k')`, either the returned `k` is strictly larger,
    or the lengths tie and the returned `i` is strictly smaller, or length
    and `i` tie and the returned `j` is no larger. -/
def spec_flm_dominates_all (impl : RepoImpl) : Prop :=
  ∀ (a b : Sequence) (i j k : Nat),
    impl.difflib.findLongestMatch a b = (i, j, k) →
      ∀ (i' j' k' : Nat), isCommonBlock a b i' j' k' →
        k > k' ∨ (k = k' ∧ i < i') ∨ (k = k' ∧ i = i' ∧ j ≤ j')

/-- The longest match cannot be extended on the right: when the returned
    block has room to grow in both sequences (`i + k < |a|` and
    `j + k < |b|`), the next elements differ — `a[i+k]! ≠ b[j+k]!`. -/
def spec_flm_extend_blocked (impl : RepoImpl) : Prop :=
  ∀ (a b : Sequence) (i j k : Nat),
    impl.difflib.findLongestMatch a b = (i, j, k) →
      i + k < a.length → j + k < b.length → a[i + k]! ≠ b[j + k]!

-- ════════════════════════════════════════════════════════════════
-- Whole-list positional / counting / canonical-form laws over the
-- block decomposition and the first-occurrence law for the match.
-- ════════════════════════════════════════════════════════════════

/-- The block start in the first sequence is strictly increasing across the
    whole emitted list: for any two positions `m < n` into
    `getMatchingBlocks a b`, the `m`-th block starts strictly before the
    `n`-th in `a`. -/
def spec_gmb_start_i_strict (impl : RepoImpl) : Prop :=
  ∀ (a b : Sequence) (m n : Nat),
    m < n →
    n < (impl.difflib.getMatchingBlocks a b).length →
      ((impl.difflib.getMatchingBlocks a b)[m]!).1 <
        ((impl.difflib.getMatchingBlocks a b)[n]!).1

/-- No two emitted blocks start at the same index in the first sequence: the
    list of first coordinates of `getMatchingBlocks a b` has no duplicates. -/
def spec_gmb_start_i_nodup (impl : RepoImpl) : Prop :=
  ∀ (a b : Sequence),
    ((impl.difflib.getMatchingBlocks a b).map (fun blk => blk.1)).Nodup

/-- The block start in the second sequence is strictly increasing across the
    whole emitted list: for any two positions `m < n` into
    `getMatchingBlocks a b`, the `m`-th block starts strictly before the
    `n`-th in `b`. Together with the `a`-coordinate law this fixes the
    emitted order in both coordinates. -/
def spec_gmb_start_j_strict (impl : RepoImpl) : Prop :=
  ∀ (a b : Sequence) (m n : Nat),
    m < n →
    n < (impl.difflib.getMatchingBlocks a b).length →
      ((impl.difflib.getMatchingBlocks a b)[m]!).2.1 <
        ((impl.difflib.getMatchingBlocks a b)[n]!).2.1

/-- There is exactly one zero-length block in the emitted list: the multiset
    of block lengths of `getMatchingBlocks a b` contains the value `0` exactly
    once (the trailing sentinel). -/
def spec_gmb_exactly_one_zero_length (impl : RepoImpl) : Prop :=
  ∀ (a b : Sequence),
    ((impl.difflib.getMatchingBlocks a b).map (fun blk => blk.2.2)).count 0 = 1

/-- First-occurrence in `a`: when a positive match exists, the returned start
    index `i` is the least index in `a` at which a common block of length
    `matchSize a b` starts — some `b`-position realizes a length-`matchSize`
    common block at `i`, and no smaller index in `a` admits one. -/
def spec_flm_first_i_common (impl : RepoImpl) : Prop :=
  ∀ (a b : Sequence),
    0 < impl.difflib.matchSize a b →
      let m := impl.difflib.matchSize a b
      let i := (impl.difflib.findLongestMatch a b).1
      (∃ j, isCommonBlock a b i j m) ∧
        ∀ i', i' < i → ¬ ∃ j, isCommonBlock a b i' j m

/-- First-occurrence in `b` at the chosen row: when a positive match exists,
    at the returned start index `i` the returned `j` is the least index in `b`
    admitting a common block of length `matchSize a b` — `(i, j)` realizes one
    and no smaller `j` does. -/
def spec_flm_first_j_common (impl : RepoImpl) : Prop :=
  ∀ (a b : Sequence),
    0 < impl.difflib.matchSize a b →
      let m := impl.difflib.matchSize a b
      let flm := impl.difflib.findLongestMatch a b
      let i := flm.1
      let j := flm.2.1
      isCommonBlock a b i j m ∧
        ∀ j', j' < j → ¬ isCommonBlock a b i j' m

-- ════════════════════════════════════════════════════════════════
-- getMatchingBlocks completeness: residual matches on both sides of the
-- global longest block are surfaced, and no positive common block hides
-- before the first emitted block or between consecutive blocks. Anchored
-- only on `isCommonBlock` and the frozen APIs.
-- ════════════════════════════════════════════════════════════════

/-- Left-residual completeness: if any positive common block fits inside the
    prefix window `a[0:i0] × b[0:j0]` cut off by the global longest match
    `(i0, j0, _) = findLongestMatch a b`, then `getMatchingBlocks a b` emits a
    positive block wholly inside that prefix window. -/
def spec_gmb_left_residual_emitted (impl : RepoImpl) : Prop :=
  ∀ (a b : Sequence),
    let top := impl.difflib.findLongestMatch a b
    (∃ i j k, 0 < k ∧ isCommonBlock (a.take top.1) (b.take top.2.1) i j k) →
      ∃ blk ∈ impl.difflib.getMatchingBlocks a b,
        0 < blk.2.2 ∧ blk.1 + blk.2.2 ≤ top.1 ∧ blk.2.1 + blk.2.2 ≤ top.2.1

/-- Left-residual canonical block: the global longest match of the prefix
    window `a[0:i0] × b[0:j0]` (with `(i0, j0, _) = findLongestMatch a b`), when
    positive, appears verbatim in `getMatchingBlocks a b` and lies wholly
    inside that prefix window. -/
def spec_gmb_left_residual_flm (impl : RepoImpl) : Prop :=
  ∀ (a b : Sequence),
    let top := impl.difflib.findLongestMatch a b
    let left := impl.difflib.findLongestMatch (a.take top.1) (b.take top.2.1)
    0 < left.2.2 →
      left ∈ impl.difflib.getMatchingBlocks a b ∧
        left.1 + left.2.2 ≤ top.1 ∧ left.2.1 + left.2.2 ≤ top.2.1

/-- Right-residual completeness: if any positive common block fits inside the
    suffix window `a[i0+k0:] × b[j0+k0:]` after the global longest match
    `(i0, j0, k0) = findLongestMatch a b`, then `getMatchingBlocks a b` emits a
    positive block that starts no earlier than the end of the global block in
    both sequences. -/
def spec_gmb_right_residual_emitted (impl : RepoImpl) : Prop :=
  ∀ (a b : Sequence),
    let top := impl.difflib.findLongestMatch a b
    let iEnd := top.1 + top.2.2
    let jEnd := top.2.1 + top.2.2
    (∃ i j k, 0 < k ∧ isCommonBlock (a.drop iEnd) (b.drop jEnd) i j k) →
      ∃ blk ∈ impl.difflib.getMatchingBlocks a b,
        0 < blk.2.2 ∧ iEnd ≤ blk.1 ∧ jEnd ≤ blk.2.1

/-- Right-residual canonical block: the global longest match of the suffix
    window `a[i0+k0:] × b[j0+k0:]` (with `(i0, j0, k0) = findLongestMatch a b`),
    when positive, appears in `getMatchingBlocks a b` with its coordinates
    translated back by `(i0 + k0, j0 + k0)`. -/
def spec_gmb_right_residual_flm (impl : RepoImpl) : Prop :=
  ∀ (a b : Sequence),
    let top := impl.difflib.findLongestMatch a b
    let iEnd := top.1 + top.2.2
    let jEnd := top.2.1 + top.2.2
    let right := impl.difflib.findLongestMatch (a.drop iEnd) (b.drop jEnd)
    0 < right.2.2 →
      (iEnd + right.1, jEnd + right.2.1, right.2.2) ∈
        impl.difflib.getMatchingBlocks a b

/-- Leftmost completeness: nothing positive is skipped before the first
    emitted block — no positive common block fits inside the prefix window
    `a[0:i₀] × b[0:j₀]` cut off by the first block `(i₀, j₀, _)` of
    `getMatchingBlocks a b`. -/
def spec_gmb_prefix_before_first_empty (impl : RepoImpl) : Prop :=
  ∀ (a b : Sequence),
    let first := (impl.difflib.getMatchingBlocks a b)[0]!
    ¬ ∃ i j k, 0 < k ∧ isCommonBlock (a.take first.1) (b.take first.2.1) i j k

/-- Gap completeness: the rectangular gap between any two consecutive emitted
    blocks holds no positive common block. For consecutive entries
    `(i₁,j₁,k₁)` then `(i₂,j₂,k₂)` in `getMatchingBlocks a b`, the window
    `a[i₁+k₁ : i₂] × b[j₁+k₁ : j₂]` has no positive common block. -/
def spec_gmb_gap_empty (impl : RepoImpl) : Prop :=
  ∀ (a b : Sequence) (n : Nat),
    n + 1 < (impl.difflib.getMatchingBlocks a b).length →
      let p := (impl.difflib.getMatchingBlocks a b)[n]!
      let q := (impl.difflib.getMatchingBlocks a b)[n + 1]!
      ¬ ∃ i j k, 0 < k ∧
        isCommonBlock
          ((a.drop (p.1 + p.2.2)).take (q.1 - (p.1 + p.2.2)))
          ((b.drop (p.2.1 + p.2.2)).take (q.2.1 - (p.2.1 + p.2.2)))
          i j k

-- ════════════════════════════════════════════════════════════════
-- findLongestMatch: left-maximality and run-length exactness at the
-- returned start. Anchored on `isCommonBlock` and indexed access.
-- ════════════════════════════════════════════════════════════════

/-- Left maximality: when the returned block has room to grow on the left in
    both sequences (`0 < i` and `0 < j`), the preceding elements differ —
    `a[i-1]! ≠ b[j-1]!`. -/
def spec_flm_left_extend_blocked (impl : RepoImpl) : Prop :=
  ∀ (a b : Sequence) (i j k : Nat),
    impl.difflib.findLongestMatch a b = (i, j, k) →
      0 < i → 0 < j → a[i - 1]! ≠ b[j - 1]!

/-- Run-length exactness at the returned start: the returned `k` is exactly the
    common-run length at `(i, j)` — for every `r`, `(i, j, r)` is a common block
    iff `r ≤ k`. -/
def spec_flm_run_exact_at_result (impl : RepoImpl) : Prop :=
  ∀ (a b : Sequence) (i j k : Nat),
    impl.difflib.findLongestMatch a b = (i, j, k) →
      ∀ (r : Nat), isCommonBlock a b i j r ↔ r ≤ k

/-- No diagonal left superblock: no positive diagonal shift of the returned
    block toward the origin yields a common block — for every `t` with
    `0 < t ≤ i` and `t ≤ j`, `(i-t, j-t, k+t)` is not a common block. -/
def spec_flm_no_diagonal_left_superblock (impl : RepoImpl) : Prop :=
  ∀ (a b : Sequence) (i j k : Nat),
    impl.difflib.findLongestMatch a b = (i, j, k) →
      ∀ (t : Nat), 0 < t → t ≤ i → t ≤ j →
        ¬ isCommonBlock a b (i - t) (j - t) (k + t)

-- ════════════════════════════════════════════════════════════════
-- getMatchingBlocks: partition around the global match, exact lexicographic
-- ordering, and a block-count bound. Anchored on the frozen APIs.
-- ════════════════════════════════════════════════════════════════

/-- Partition around the global match: every emitted block other than the
    global longest match `top = findLongestMatch a b` lies wholly to its
    upper-left (`blk.1 + blk.2.2 ≤ top.1 ∧ blk.2.1 + blk.2.2 ≤ top.2.1`) or
    wholly to its lower-right (`top.1 + top.2.2 ≤ blk.1 ∧
    top.2.1 + top.2.2 ≤ blk.2.1`). -/
def spec_gmb_partition_around_flm (impl : RepoImpl) : Prop :=
  ∀ (a b : Sequence) (blk : Block),
    let top := impl.difflib.findLongestMatch a b
    blk ∈ impl.difflib.getMatchingBlocks a b →
      blk ≠ top →
        (blk.1 + blk.2.2 ≤ top.1 ∧ blk.2.1 + blk.2.2 ≤ top.2.1) ∨
          (top.1 + top.2.2 ≤ blk.1 ∧ top.2.1 + top.2.2 ≤ blk.2.1)

/-- Order reflects indices: list position in `getMatchingBlocks a b` is
    exactly lexicographic order by `(i, j)`. For positions `m`, `n`,
    `m ≤ n` iff the `m`-th block precedes the `n`-th lexicographically in
    `(start-in-a, start-in-b)`. -/
def spec_gmb_lex_order_reflects_indices (impl : RepoImpl) : Prop :=
  ∀ (a b : Sequence) (m n : Nat),
    let blocks := impl.difflib.getMatchingBlocks a b
    m < blocks.length →
      n < blocks.length →
        (m ≤ n ↔
          (blocks[m]!).1 < (blocks[n]!).1 ∨
            ((blocks[m]!).1 = (blocks[n]!).1 ∧
              (blocks[m]!).2.1 ≤ (blocks[n]!).2.1))

/-- Block-count bound: the emitted list has at most one entry per element of
    the shorter sequence, plus the sentinel —
    `(getMatchingBlocks a b).length ≤ min |a| |b| + 1`. -/
def spec_gmb_length_le_shorter_plus_one (impl : RepoImpl) : Prop :=
  ∀ (a b : Sequence),
    (impl.difflib.getMatchingBlocks a b).length ≤ min a.length b.length + 1

-- ════════════════════════════════════════════════════════════════
-- getMatchingBlocks self-similarity: each emitted block agrees with
-- findLongestMatch on its local window, gaps are empty, and the whole list
-- is the split around the global match. Anchored on the frozen APIs.
-- ════════════════════════════════════════════════════════════════

/-- Local self-similarity: every positive emitted block is the canonical
    longest match of the window bounded by its neighbours. For the `n`-th
    block, with `loI, loJ` the end of the previous block (or `0` at `n = 0`)
    and `hiI, hiJ` the start of the next block,
    `findLongestMatch a[loI:hiI] b[loJ:hiJ] = (i-loI, j-loJ, k)`. -/
def spec_gmb_each_positive_block_local_flm (impl : RepoImpl) : Prop :=
  ∀ (a b : Sequence) (n : Nat),
    n < (impl.difflib.getMatchingBlocks a b).length →
      let blocks := impl.difflib.getMatchingBlocks a b
      let blk := blocks[n]!
      0 < blk.2.2 →
        let loI := if n = 0 then 0 else (blocks[n - 1]!).1 + (blocks[n - 1]!).2.2
        let loJ := if n = 0 then 0 else (blocks[n - 1]!).2.1 + (blocks[n - 1]!).2.2
        let hiI := (blocks[n + 1]!).1
        let hiJ := (blocks[n + 1]!).2.1
        impl.difflib.findLongestMatch
            ((a.drop loI).take (hiI - loI))
            ((b.drop loJ).take (hiJ - loJ)) =
          (blk.1 - loI, blk.2.1 - loJ, blk.2.2)

/-- Gaps are terminal: the window between two consecutive emitted blocks
    decomposes to only its own sentinel. For consecutive `p = blocks[n]`,
    `q = blocks[n+1]`, with `gapA = a[p.1+p.2.2 : q.1]` and
    `gapB = b[p.2.1+p.2.2 : q.2.1]`,
    `getMatchingBlocks gapA gapB = [(|gapA|, |gapB|, 0)]`. -/
def spec_gmb_gap_blocks_sentinel_only (impl : RepoImpl) : Prop :=
  ∀ (a b : Sequence) (n : Nat),
    let blocks := impl.difflib.getMatchingBlocks a b
    n + 1 < blocks.length →
      let p := blocks[n]!
      let q := blocks[n + 1]!
      let gapA := (a.drop (p.1 + p.2.2)).take (q.1 - (p.1 + p.2.2))
      let gapB := (b.drop (p.2.1 + p.2.2)).take (q.2.1 - (p.2.1 + p.2.2))
      impl.difflib.getMatchingBlocks gapA gapB = [(gapA.length, gapB.length, 0)]

/-- Neighbour-window decomposition: the window bounded by the neighbours of a
    positive emitted block decomposes to exactly that block and the local
    sentinel. With `loA, loB, hiA, hiB` as in `spec_gmb_each_positive_block_local_flm`,
    `getMatchingBlocks a[loA:hiA] b[loB:hiB] =
    [(i-loA, j-loB, k), (hiA-loA, hiB-loB, 0)]`. -/
def spec_gmb_neighbor_window_blocks_exact (impl : RepoImpl) : Prop :=
  ∀ (a b : Sequence) (n : Nat),
    let blocks := impl.difflib.getMatchingBlocks a b
    n + 1 < blocks.length →
      let blk := blocks[n]!
      let loA := if n = 0 then 0 else (blocks[n - 1]!).1 + (blocks[n - 1]!).2.2
      let loB := if n = 0 then 0 else (blocks[n - 1]!).2.1 + (blocks[n - 1]!).2.2
      let hiA := (blocks[n + 1]!).1
      let hiB := (blocks[n + 1]!).2.1
      0 < blk.2.2 →
        impl.difflib.getMatchingBlocks
            ((a.drop loA).take (hiA - loA))
            ((b.drop loB).take (hiB - loB)) =
          [(blk.1 - loA, blk.2.1 - loB, blk.2.2), (hiA - loA, hiB - loB, 0)]

/-- Split around the global match: the whole emitted list is the left window's
    blocks, then the global longest match `(i, j, k)`, then the right window's
    blocks translated by `(i+k, j+k)`, then the global sentinel — where the
    left window is `a[:i] × b[:j]`, the right window is `a[i+k:] × b[j+k:]`, and
    each sub-list has its own trailing sentinel dropped. -/
def spec_gmb_recursive_split_exact (impl : RepoImpl) : Prop :=
  ∀ (a b : Sequence) (i j k : Nat),
    impl.difflib.findLongestMatch a b = (i, j, k) →
      0 < k →
        let leftBlocks :=
          (impl.difflib.getMatchingBlocks (a.take i) (b.take j)).dropLast
        let rightBlocks :=
          (impl.difflib.getMatchingBlocks (a.drop (i + k)) (b.drop (j + k))).dropLast
        impl.difflib.getMatchingBlocks a b =
          leftBlocks ++ [(i, j, k)] ++
            (rightBlocks.map (fun blk =>
              (i + k + blk.1, j + k + blk.2.1, blk.2.2))) ++
            [(a.length, b.length, 0)]

/-- First block iff no left residual: when the global longest match `top` is
    positive, it is the head of `getMatchingBlocks a b` exactly when the prefix
    window `a[:top.1] × b[:top.2.1]` holds no positive common block. -/
def spec_gmb_first_block_is_flm_iff_no_left_residual (impl : RepoImpl) : Prop :=
  ∀ (a b : Sequence),
    let top := impl.difflib.findLongestMatch a b
    0 < top.2.2 →
      ((impl.difflib.getMatchingBlocks a b)[0]! = top ↔
        ¬ ∃ i j k, 0 < k ∧
          isCommonBlock (a.take top.1) (b.take top.2.1) i j k)
