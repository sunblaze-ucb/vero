import Textdistance.Harness

/-!
# Textdistance.Spec.Edit

Specifications for the edit-distance operations. Each `spec_*` is a
property over an arbitrary `impl : RepoImpl`, reached through
`impl.textdistance.<fn>`.

The `levenshtein` optimality specs use a witness ∧ minimality pattern,
anchored on the frozen inductive `Edit` script with frozen `applyScript`
/ `cost`: some edit script transforming `a` into `b` has cost equal to
the claimed distance (witness), and no such script is cheaper
(minimality). The `lcs` specs use a witness ∧ maximality pattern anchored
on `List.Sublist`: some common subsequence has length equal to the
claimed value, and none is longer (maximality). Each pair pins a unique
optimal value.

The rest of the file states the algebraic structure of both operations:
boundary equations, the cons/cons recursions and equal-head
simplifications, the metric axioms of `levenshtein` (identity of
indiscernibles, symmetry, triangle inequality), upper and lower bounds,
concatenation laws (prefix/suffix cancellation, subadditivity, the
one-step characterization), lev/lcs coupling bounds, the monotonicity and
subadditivity laws of `lcs`, shared-prefix/suffix exact accounting,
single-symbol sandwich bounds, reversal invariance, the LCS triangle
inequality, general `Sublist`-monotonicity, and a block-swap bound. Each
statement exposes only its end relation.

DO NOT MODIFY.
-/

-- ── Frozen edit-script machinery (DO NOT MODIFY) ───────────────

/-- A single edit operation applied left-to-right while consuming a
    source sequence:
    * `ins c` inserts symbol `c` into the output (consumes no source);
    * `del` deletes the head of the source (emits nothing);
    * `sub c` replaces the head of the source with `c`;
    * `keep` copies the head of the source unchanged. -/
inductive Edit where
  | ins (c : Nat) : Edit
  | del : Edit
  | sub (c : Nat) : Edit
  | keep : Edit
  deriving DecidableEq

/-- Apply an edit script to a source sequence, producing the result
    sequence, or `none` if the script is inconsistent with the source
    (a `del`/`sub`/`keep` with no remaining source symbol, or leftover
    source symbols once the script is exhausted). -/
def applyScript : List Edit → Symbols → Option Symbols
  | [],            a       => if a.isEmpty then some [] else none
  | Edit.ins c :: s, a       => (applyScript s a).map (fun r => c :: r)
  | Edit.del    :: s, _ :: xs => applyScript s xs
  | Edit.del    :: _, []      => none
  | Edit.sub c :: s, _ :: xs => (applyScript s xs).map (fun r => c :: r)
  | Edit.sub _ :: _, []      => none
  | Edit.keep   :: s, x :: xs => (applyScript s xs).map (fun r => x :: r)
  | Edit.keep   :: _, []      => none

/-- The cost of an edit script: `keep` is free, every other operation
    costs one. -/
def cost : List Edit → Nat
  | []               => 0
  | Edit.keep :: s   => cost s
  | _ :: s           => 1 + cost s

-- ── levenshtein: witness ∧ minimality ──────────────────────────

/-- Witness: there EXISTS an edit script transforming `a` into `b` whose
    cost equals the claimed Levenshtein distance. -/
def spec_lev_witness (impl : RepoImpl) : Prop :=
  ∀ (a b : Symbols),
    ∃ s : List Edit, applyScript s a = some b ∧ cost s = impl.textdistance.levenshtein a b

/-- Minimality (load-bearing): no edit script transforming `a` into `b`
    is cheaper than the claimed Levenshtein distance. -/
def spec_lev_minimal (impl : RepoImpl) : Prop :=
  ∀ (a b : Symbols) (s : List Edit),
    applyScript s a = some b → impl.textdistance.levenshtein a b ≤ cost s

/-- Frozen-op anchor: transforming a sequence into itself costs nothing. -/
def spec_lev_self_zero (impl : RepoImpl) : Prop :=
  ∀ (a : Symbols), impl.textdistance.levenshtein a a = 0

/-- Frozen-op anchor: transforming the empty sequence into `b` costs
    exactly `b.length` (insert every symbol). -/
def spec_lev_empty_left (impl : RepoImpl) : Prop :=
  ∀ (b : Symbols), impl.textdistance.levenshtein [] b = b.length

/-- Boundary (right): transforming `a` into the empty sequence costs
    exactly `a.length` (delete every symbol). -/
def spec_lev_empty_right (impl : RepoImpl) : Prop :=
  ∀ (a : Symbols), impl.textdistance.levenshtein a [] = a.length

-- ── levenshtein: metric structure ──────────────────────────────

/-- Identity of indiscernibles: the Levenshtein distance is zero exactly
    when the two sequences coincide. Pins both that equal inputs have
    distance zero AND that zero distance forces equality (the `→`
    direction rejects any impl that under-counts). -/
def spec_lev_zero_iff_eq (impl : RepoImpl) : Prop :=
  ∀ (a b : Symbols), impl.textdistance.levenshtein a b = 0 ↔ a = b

/-- Symmetry: edit distance does not depend on the direction of the
    transformation. A core metric axiom. -/
def spec_lev_symm (impl : RepoImpl) : Prop :=
  ∀ (a b : Symbols),
    impl.textdistance.levenshtein a b = impl.textdistance.levenshtein b a

/-- Triangle inequality: composing a transformation `a → b` with `b → c`
    can be no worse than transforming `a → c` directly. The defining
    metric axiom. -/
def spec_lev_triangle (impl : RepoImpl) : Prop :=
  ∀ (a b c : Symbols),
    impl.textdistance.levenshtein a c
      ≤ impl.textdistance.levenshtein a b + impl.textdistance.levenshtein b c

-- ── levenshtein: bounds ─────────────────────────────────────────

/-- Upper bound: deleting all of `a` then inserting all of `b` costs
    `a.length + b.length`, so the optimum is no larger. -/
def spec_lev_le_add (impl : RepoImpl) : Prop :=
  ∀ (a b : Symbols),
    impl.textdistance.levenshtein a b ≤ a.length + b.length

/-- Tighter upper bound: the distance never exceeds the longer of the two
    lengths. Rejects an impl that over-reports the cost of editing a shorter
    sequence into a longer one. -/
def spec_lev_le_max (impl : RepoImpl) : Prop :=
  ∀ (a b : Symbols),
    impl.textdistance.levenshtein a b ≤ max a.length b.length

/-- Length-difference lower bound: at least `|a.length - b.length|` edits
    are needed, stated as the full two-sided magnitude-free bound
    `a.length ≤ b.length + lev a b ∧ b.length ≤ a.length + lev a b`
    (equivalently `|a.length - b.length| ≤ lev a b`). Both directions are
    load-bearing — whichever sequence is longer, the distance must cover
    the length gap — so the spec rejects any impl that under-counts when
    the lengths differ in either direction. -/
def spec_lev_len_lower_bound (impl : RepoImpl) : Prop :=
  ∀ (a b : Symbols),
    a.length ≤ b.length + impl.textdistance.levenshtein a b
      ∧ b.length ≤ a.length + impl.textdistance.levenshtein a b

/-- Symbol-count lower bound: for every symbol, each input's multiplicity
    is bounded by the other input's multiplicity plus the edit distance. -/
def spec_lev_count_lower_bound (impl : RepoImpl) : Prop :=
  ∀ (a b : Symbols) (x : Nat),
    a.count x ≤ b.count x + impl.textdistance.levenshtein a b
      ∧ b.count x ≤ a.count x + impl.textdistance.levenshtein a b

-- ── levenshtein: defining recursion ─────────────────────────────

/-- Equal-head simplification: a shared leading symbol is free, so the
    distance reduces to that of the tails. -/
def spec_lev_cons_eq_head (impl : RepoImpl) : Prop :=
  ∀ (x : Nat) (xs ys : Symbols),
    impl.textdistance.levenshtein (x :: xs) (x :: ys)
      = impl.textdistance.levenshtein xs ys

/-- The full cons/cons defining equation: on a shared head recurse on the
    tails; otherwise pay one edit and take the best of delete / insert /
    substitute. -/
def spec_lev_cons_cons (impl : RepoImpl) : Prop :=
  ∀ (x y : Nat) (xs ys : Symbols),
    impl.textdistance.levenshtein (x :: xs) (y :: ys)
      = (if x = y then impl.textdistance.levenshtein xs ys
         else 1 + min (impl.textdistance.levenshtein xs (y :: ys))
                      (min (impl.textdistance.levenshtein (x :: xs) ys)
                           (impl.textdistance.levenshtein xs ys)))

-- ── lcs: witness ∧ maximality ──────────────────────────────────

/-- Witness: there EXISTS a common subsequence of `a` and `b` whose
    length equals the claimed LCS length. -/
def spec_lcs_witness (impl : RepoImpl) : Prop :=
  ∀ (a b : Symbols),
    ∃ cs : Symbols, cs.Sublist a ∧ cs.Sublist b ∧ cs.length = impl.textdistance.lcs a b

/-- Maximality (load-bearing): no common subsequence of `a` and `b` is
    longer than the claimed LCS length. -/
def spec_lcs_maximal (impl : RepoImpl) : Prop :=
  ∀ (a b : Symbols) (cs : Symbols),
    cs.Sublist a → cs.Sublist b → cs.length ≤ impl.textdistance.lcs a b

/-- Frozen-op anchor: the empty sequence shares no subsequence symbols. -/
def spec_lcs_empty (impl : RepoImpl) : Prop :=
  ∀ (b : Symbols), impl.textdistance.lcs [] b = 0

/-- Frozen-op anchor: a common subsequence cannot exceed either input. -/
def spec_lcs_le_min_length (impl : RepoImpl) : Prop :=
  ∀ (a b : Symbols), impl.textdistance.lcs a b ≤ min a.length b.length

/-- Constant-sequence LCS: matching against copies of one symbol has length
    equal to the smaller available multiplicity. -/
def spec_lcs_replicate_count (impl : RepoImpl) : Prop :=
  ∀ (a : Symbols) (x n : Nat),
    impl.textdistance.lcs a (List.replicate n x) = min (a.count x) n

/-- Single-symbol filtered LCS: after keeping only one symbol on both
    sides, the shared length is the smaller retained multiplicity. -/
def spec_lcs_filtered_count (impl : RepoImpl) : Prop :=
  ∀ (a b : Symbols) (x : Nat),
    impl.textdistance.lcs (a.filter (fun y => y == x)) (b.filter (fun y => y == x))
      = min (a.count x) (b.count x)

/-- Per-symbol lower bound: for any chosen symbol, the LCS is at least the
    smaller of its two multiplicities. -/
def spec_lcs_count_le (impl : RepoImpl) : Prop :=
  ∀ (a b : Symbols) (x : Nat),
    (List.replicate (min (a.count x) (b.count x)) x).length
      ≤ impl.textdistance.lcs a b

/-- Counting upper bound: the LCS length is at most the summed shared
    multiplicity over the symbols present in the inputs. -/
def spec_lcs_counting_upper (impl : RepoImpl) : Prop :=
  ∀ (a b : Symbols),
    impl.textdistance.lcs a b ≤
      ((a ++ b).eraseDups.foldl
        (fun acc x => acc + min (a.count x) (b.count x)) 0)

/-- Boundary (right): nothing is shared with the empty sequence. -/
def spec_lcs_empty_right (impl : RepoImpl) : Prop :=
  ∀ (a : Symbols), impl.textdistance.lcs a [] = 0

-- ── lcs: structural properties ──────────────────────────────────

/-- Symmetry: the longest common subsequence length is order-independent. -/
def spec_lcs_symm (impl : RepoImpl) : Prop :=
  ∀ (a b : Symbols), impl.textdistance.lcs a b = impl.textdistance.lcs b a

/-- A sequence is its own longest common subsequence with itself, so the
    LCS length equals the input length. -/
def spec_lcs_self (impl : RepoImpl) : Prop :=
  ∀ (a : Symbols), impl.textdistance.lcs a a = a.length

/-- Equal-head simplification: when both inputs start with the same
    symbol, the longest common subsequence is exactly one longer than the
    LCS of the two tails. Pins how a matched leading symbol must be
    counted. -/
def spec_lcs_cons_eq_head (impl : RepoImpl) : Prop :=
  ∀ (x : Nat) (xs ys : Symbols),
    impl.textdistance.lcs (x :: xs) (x :: ys)
      = 1 + impl.textdistance.lcs xs ys

/-- The full cons/cons defining equation: on a shared head take it and
    recurse; otherwise take the better of dropping `a`'s head or `b`'s
    head. -/
def spec_lcs_cons_cons (impl : RepoImpl) : Prop :=
  ∀ (x y : Nat) (xs ys : Symbols),
    impl.textdistance.lcs (x :: xs) (y :: ys)
      = (if x = y then 1 + impl.textdistance.lcs xs ys
         else max (impl.textdistance.lcs xs (y :: ys))
                  (impl.textdistance.lcs (x :: xs) ys))

-- ── levenshtein: concatenation laws (cancellation & subadditivity) ──

/-- Common-prefix cancellation: a shared prefix `c` contributes nothing
    to the edit distance, so it can be stripped from both sequences.
    Pins that aligning identical leading blocks is always free, no matter
    how long the prefix is. -/
def spec_lev_prefix_cancel (impl : RepoImpl) : Prop :=
  ∀ (a b c : Symbols),
    impl.textdistance.levenshtein (c ++ a) (c ++ b)
      = impl.textdistance.levenshtein a b

/-- Common-suffix cancellation: a shared suffix `c` contributes nothing,
    so it can be stripped from both sequences. The trailing-block analogue
    of prefix cancellation. -/
def spec_lev_suffix_cancel (impl : RepoImpl) : Prop :=
  ∀ (a b c : Symbols),
    impl.textdistance.levenshtein (a ++ c) (b ++ c)
      = impl.textdistance.levenshtein a b

/-- Subadditivity over concatenation: editing `a ++ b` into `c ++ d` is
    no costlier than independently editing the two halves. Pins that
    handling the two segments together can never be worse than handling
    them in isolation — a global optimum dominates the segment-wise sum. -/
def spec_lev_concat_subadditive (impl : RepoImpl) : Prop :=
  ∀ (a b c d : Symbols),
    impl.textdistance.levenshtein (a ++ b) (c ++ d)
      ≤ impl.textdistance.levenshtein a c + impl.textdistance.levenshtein b d

/-- One-step characterization: the distance is at most one exactly when
    the sequences are already equal or are bridged by a single
    (cost-one) edit script. Bidirectional — it pins both that a cheap
    distance forces a near-trivial transformation and that any such
    transformation keeps the distance small. -/
def spec_lev_one_step (impl : RepoImpl) : Prop :=
  ∀ (a b : Symbols),
    impl.textdistance.levenshtein a b ≤ 1
      ↔ (a = b ∨ ∃ s : List Edit, applyScript s a = some b ∧ cost s = 1)

/-- lev/lcs duality lower bound: `max a.length b.length ≤ lev a b + lcs a b`.
    Couples the edit distance and the shared-subsequence length; the `max`
    form pins both sides at once. -/
def spec_lev_len_lcs_lower_bound (impl : RepoImpl) : Prop :=
  ∀ (a b : Symbols),
    max a.length b.length
      ≤ impl.textdistance.levenshtein a b + impl.textdistance.lcs a b

-- ── lcs: monotonicity & subadditivity over concatenation ───────────

/-- Appending a common suffix can only grow the longest common
    subsequence: `lcs a b ≤ lcs (a ++ c) (b ++ c)`. Pins that adding the
    same trailing block to both inputs never destroys existing shared
    structure — the shared length is monotone under a common append. -/
def spec_lcs_suffix_monotone (impl : RepoImpl) : Prop :=
  ∀ (a b c : Symbols),
    impl.textdistance.lcs a b ≤ impl.textdistance.lcs (a ++ c) (b ++ c)

/-- Prepending to the second argument can only grow the LCS:
    `lcs a b ≤ lcs a (c ++ b)`. -/
def spec_lcs_grow_prefix_right (impl : RepoImpl) : Prop :=
  ∀ (a b c : Symbols),
    impl.textdistance.lcs a b ≤ impl.textdistance.lcs a (c ++ b)

/-- Appending to the second argument can only grow the LCS:
    `lcs a b ≤ lcs a (b ++ c)`. -/
def spec_lcs_grow_suffix_right (impl : RepoImpl) : Prop :=
  ∀ (a b c : Symbols),
    impl.textdistance.lcs a b ≤ impl.textdistance.lcs a (b ++ c)

/-- Subadditivity of LCS in the first argument: splitting the first
    sequence cannot lose common-subsequence length —
    `lcs (a ++ b) c ≤ lcs a c + lcs b c`. Rejects an impl whose LCS of a
    concatenation exceeds the sum of the per-part LCS lengths. -/
def spec_lcs_subadditive_left (impl : RepoImpl) : Prop :=
  ∀ (a b c : Symbols),
    impl.textdistance.lcs (a ++ b) c
      ≤ impl.textdistance.lcs a c + impl.textdistance.lcs b c

/-- Subadditivity of LCS in the second argument:
    `lcs c (a ++ b) ≤ lcs c a + lcs c b`. -/
def spec_lcs_subadditive_right (impl : RepoImpl) : Prop :=
  ∀ (a b c : Symbols),
    impl.textdistance.lcs c (a ++ b)
      ≤ impl.textdistance.lcs c a + impl.textdistance.lcs c b

-- ── lcs: shared-prefix / shared-suffix exact accounting ─────────────

/-- A common prefix is accounted for exactly: prepending the same block
    `a` to both inputs increases the longest-common-subsequence length by
    precisely `a.length`, on top of the LCS of the remainders.
    `lcs (a ++ b) (a ++ c) = a.length + lcs b c`. Both directions are
    load-bearing — the prefix contributes its full length (not merely at
    most it), which constrains the value far more tightly than the
    one-sided growth laws. -/
def spec_lcs_shared_prefix (impl : RepoImpl) : Prop :=
  ∀ (a b c : Symbols),
    impl.textdistance.lcs (a ++ b) (a ++ c)
      = a.length + impl.textdistance.lcs b c

/-- A common suffix is accounted for exactly: appending the same block
    `a` to both inputs increases the LCS length by precisely `a.length`.
    `lcs (b ++ a) (c ++ a) = a.length + lcs b c`. The suffix analogue of
    `spec_lcs_shared_prefix`; equally tight in both directions. -/
def spec_lcs_shared_suffix (impl : RepoImpl) : Prop :=
  ∀ (a b c : Symbols),
    impl.textdistance.lcs (b ++ a) (c ++ a)
      = a.length + impl.textdistance.lcs b c

-- ── lcs: single-symbol sensitivity (adjacency) ──────────────────────

/-- Prepending one symbol to the first input is exactly 1-Lipschitz: it
    raises the LCS length by at most one and never lowers it,
    `lcs xs b ≤ lcs (x :: xs) b ≤ 1 + lcs xs b`. The two-sided sandwich
    pins a single symbol's contribution to `{0, 1}` — both the tight
    upper bound (a symbol contributes at most one) and the monotone lower
    bound (a symbol never destroys shared structure) are load-bearing. -/
def spec_lcs_drop_left (impl : RepoImpl) : Prop :=
  ∀ (x : Nat) (xs b : Symbols),
    impl.textdistance.lcs xs b ≤ impl.textdistance.lcs (x :: xs) b
      ∧ impl.textdistance.lcs (x :: xs) b ≤ 1 + impl.textdistance.lcs xs b

/-- Prepending one symbol to the second input is exactly 1-Lipschitz:
    `lcs a ys ≤ lcs a (y :: ys) ≤ 1 + lcs a ys`. The second-argument
    two-sided sandwich, pinning the symbol's contribution to `{0, 1}`. -/
def spec_lcs_drop_right (impl : RepoImpl) : Prop :=
  ∀ (y : Nat) (a ys : Symbols),
    impl.textdistance.lcs a ys ≤ impl.textdistance.lcs a (y :: ys)
      ∧ impl.textdistance.lcs a (y :: ys) ≤ 1 + impl.textdistance.lcs a ys

-- ── lcs: first-argument monotonicity (completing the symmetry) ──────

/-- Appending to the first input can only grow the LCS:
    `lcs a b ≤ lcs (a ++ c) b`. The first-argument suffix analogue of the
    second-argument growth laws. -/
def spec_lcs_grow_suffix_left (impl : RepoImpl) : Prop :=
  ∀ (a b c : Symbols),
    impl.textdistance.lcs a b ≤ impl.textdistance.lcs (a ++ c) b

/-- Prepending to the first input can only grow the LCS:
    `lcs a b ≤ lcs (c ++ a) b`. The first-argument prefix analogue. -/
def spec_lcs_grow_prefix_left (impl : RepoImpl) : Prop :=
  ∀ (a b c : Symbols),
    impl.textdistance.lcs a b ≤ impl.textdistance.lcs (c ++ a) b

-- ── reversal invariance of both operations ──────────────────────────

/-- LCS is invariant under reversing both inputs:
    `lcs a b = lcs a.reverse b.reverse`. -/
def spec_lcs_reverse (impl : RepoImpl) : Prop :=
  ∀ (a b : Symbols),
    impl.textdistance.lcs a b
      = impl.textdistance.lcs a.reverse b.reverse

/-- Levenshtein distance is invariant under reversing both inputs:
    `lev a b = lev a.reverse b.reverse`. A clean structural symmetry:
    reading both sequences back-to-front costs exactly the same number of
    edits as reading them front-to-back. -/
def spec_lev_reverse (impl : RepoImpl) : Prop :=
  ∀ (a b : Symbols),
    impl.textdistance.levenshtein a b
      = impl.textdistance.levenshtein a.reverse b.reverse

-- ── lev/lcs joint upper bound ───────────────────────────────────────

/-- Joint lev/lcs upper bound: twice the longest common subsequence plus
    the edit distance never exceeds the combined length,
    `2 * lcs a b + lev a b ≤ a.length + b.length`. The upper-bound
    companion to the `max a.length b.length ≤ lev + lcs` lower bound. -/
def spec_lev_lcs_upper (impl : RepoImpl) : Prop :=
  ∀ (a b : Symbols),
    2 * impl.textdistance.lcs a b + impl.textdistance.levenshtein a b
      ≤ a.length + b.length

-- ── deep-invariant family: LCS triangle, Sublist-monotonicity, block swap ──

/-- LCS triangle inequality: routing through a middle sequence `b` loses
    at most `b.length`, `lcs a b + lcs b c ≤ b.length + lcs a c`. The
    longest-common-subsequence analogue of the metric triangle
    inequality. -/
def spec_lcs_triangle (impl : RepoImpl) : Prop :=
  ∀ (a b c : Symbols),
    impl.textdistance.lcs a b + impl.textdistance.lcs b c
      ≤ b.length + impl.textdistance.lcs a c

/-- General first-argument monotonicity of LCS under the subsequence
    relation: enlarging the first input along `List.Sublist` can only grow
    the longest common subsequence,
    `a₁.Sublist a₂ → lcs a₁ b ≤ lcs a₂ b`. A single law subsuming every
    append/prepend growth spec (which are the special cases
    `a₂ = a₁ ++ c` and `a₂ = c ++ a₁`), stated over an arbitrary
    subsequence extension. -/
def spec_lcs_sublist_mono_left (impl : RepoImpl) : Prop :=
  ∀ (a₁ a₂ b : Symbols),
    a₁.Sublist a₂ → impl.textdistance.lcs a₁ b ≤ impl.textdistance.lcs a₂ b

/-- Block-swap edit-distance bound: exchanging two adjacent blocks costs at
    most twice the shorter block,
    `lev (a++b) (b++a) ≤ 2 * min a.length b.length`. -/
def spec_lev_block_swap (impl : RepoImpl) : Prop :=
  ∀ (a b : Symbols),
    impl.textdistance.levenshtein (a ++ b) (b ++ a)
      ≤ 2 * min a.length b.length

-- ── aligned-block LCS accounting: superadditivity & shared middle ──

/-- Superadditivity of LCS over aligned concatenation: the shared lengths of
    two independent block pairs add up under a common split,
    `lcs a c + lcs b d ≤ lcs (a ++ b) (c ++ d)`. The companion lower bound to
    the first/second-argument subadditivity laws, pinning that matched
    structure in aligned halves is never lost when the halves are joined. -/
def spec_lcs_concat_superadditive (impl : RepoImpl) : Prop :=
  ∀ (a b c d : Symbols),
    impl.textdistance.lcs a c + impl.textdistance.lcs b d
      ≤ impl.textdistance.lcs (a ++ b) (c ++ d)

/-- Shared-middle LCS lower bound: a common middle block is taken in full while
    the left and right flanks are matched independently,
    `mid.length + lcs a c + lcs b d ≤ lcs (a ++ mid ++ b) (c ++ mid ++ d)`.
    Strengthens `spec_lcs_shared_prefix` / `spec_lcs_shared_suffix` to an
    interior shared block with free flanks on both sides. -/
def spec_lcs_shared_middle_lower (impl : RepoImpl) : Prop :=
  ∀ (a b c d mid : Symbols),
    mid.length + impl.textdistance.lcs a c + impl.textdistance.lcs b d
      ≤ impl.textdistance.lcs (a ++ mid ++ b) (c ++ mid ++ d)

/-- Two-order middle overlap: matching two blocks against a shared list is
    captured across both concatenation orders,
    `lcs a m + lcs b m ≤ lcs (a ++ b) m + lcs (b ++ a) m`. Pins that the two
    per-block shared lengths against a common target can always be realised by
    one of the two orderings of the blocks. -/
def spec_lcs_two_order_middle_overlap (impl : RepoImpl) : Prop :=
  ∀ (a b m : Symbols),
    impl.textdistance.lcs a m + impl.textdistance.lcs b m
      ≤ impl.textdistance.lcs (a ++ b) m + impl.textdistance.lcs (b ++ a) m

-- ── single-position sensitivity (two-index Lipschitz) ──────────────

/-- Deleting one interior symbol from each side lowers the LCS by at most two,
    `lcs (a ++ x :: b) (c ++ y :: d) ≤ 2 + lcs (a ++ b) (c ++ d)`, for arbitrary
    split points and inserted symbols. Bounds the joint effect of one symbol on
    each input at an arbitrary position. -/
def spec_lcs_delete_one_each_middle (impl : RepoImpl) : Prop :=
  ∀ (a b c d : Symbols) (x y : Nat),
    impl.textdistance.lcs (a ++ (x :: b)) (c ++ (y :: d))
      ≤ 2 + impl.textdistance.lcs (a ++ b) (c ++ d)

/-- Inserting or deleting one interior symbol on each side changes the edit
    distance by at most two, `|lev (a ++ x :: b) (c ++ y :: d) − lev (a ++ b) (c ++ d)| ≤ 2`,
    stated as both one-sided bounds for arbitrary split points and symbols. -/
def spec_lev_delete_one_each_lipschitz (impl : RepoImpl) : Prop :=
  ∀ (a b c d : Symbols) (x y : Nat),
    impl.textdistance.levenshtein (a ++ (x :: b)) (c ++ (y :: d))
        ≤ 2 + impl.textdistance.levenshtein (a ++ b) (c ++ d)
      ∧ impl.textdistance.levenshtein (a ++ b) (c ++ d)
        ≤ 2 + impl.textdistance.levenshtein (a ++ (x :: b)) (c ++ (y :: d))

/-- Consing one leading symbol to each input changes the edit distance by at
    most one, `|lev (x :: xs) (y :: ys) − lev xs ys| ≤ 1`, stated as both
    one-sided bounds. The leading-pair sensitivity companion to the
    concatenation-cancellation laws. -/
def spec_lev_cons_pair_lipschitz (impl : RepoImpl) : Prop :=
  ∀ (x y : Nat) (xs ys : Symbols),
    impl.textdistance.levenshtein xs ys
        ≤ 1 + impl.textdistance.levenshtein (x :: xs) (y :: ys)
      ∧ impl.textdistance.levenshtein (x :: xs) (y :: ys)
        ≤ 1 + impl.textdistance.levenshtein xs ys

/-- Consing one leading symbol to each input raises the LCS by at most one and
    never lowers it, `lcs xs ys ≤ lcs (x :: xs) (y :: ys) ≤ 1 + lcs xs ys`. The
    two-input leading-pair analogue of the single-side 1-Lipschitz sandwiches. -/
def spec_lcs_cons_pair_lipschitz (impl : RepoImpl) : Prop :=
  ∀ (x y : Nat) (xs ys : Symbols),
    impl.textdistance.lcs xs ys ≤ impl.textdistance.lcs (x :: xs) (y :: ys)
      ∧ impl.textdistance.lcs (x :: xs) (y :: ys)
        ≤ 1 + impl.textdistance.lcs xs ys

-- ── lev / lcs coupling ─────────────────────────────────────────────

/-- LCS against a fixed third input is 1-Lipschitz in the edit distance of the
    varying argument, `lcs a c ≤ lev a b + lcs b c ∧ lcs b c ≤ lev a b + lcs a c`.
    Couples the two operations: moving the first argument by `lev a b` edits can
    shift its LCS against `c` by no more than that many. -/
def spec_lcs_lev_lipschitz_left (impl : RepoImpl) : Prop :=
  ∀ (a b c : Symbols),
    impl.textdistance.lcs a c
        ≤ impl.textdistance.levenshtein a b + impl.textdistance.lcs b c
      ∧ impl.textdistance.lcs b c
        ≤ impl.textdistance.levenshtein a b + impl.textdistance.lcs a c

-- ── LCS-aligned edit scripts (existential & universal) ─────────────

/-- LCS-aligned edit script: some longest common subsequence and some edit
    script from `a` to `b` share one alignment, with the script paying exactly
    for the unmatched symbols, `cost s + 2 * cs.length = a.length + b.length`
    where `cs` is a common subsequence of both with `cs.length = lcs a b`. -/
def spec_lcs_aligned_edit_witness (impl : RepoImpl) : Prop :=
  ∀ (a b : Symbols),
    ∃ (cs : Symbols) (s : List Edit),
      cs.Sublist a ∧ cs.Sublist b
        ∧ cs.length = impl.textdistance.lcs a b
        ∧ applyScript s a = some b
        ∧ cost s + 2 * cs.length = a.length + b.length

/-- Every successful edit script pays for all symbols outside its kept common
    subsequence, `max a.length b.length ≤ lcs a b + cost s` whenever
    `applyScript s a = some b`. The universal lower-bound companion to the
    existential aligned-script witness. -/
def spec_every_script_lcs_lower (impl : RepoImpl) : Prop :=
  ∀ (a b : Symbols) (s : List Edit),
    applyScript s a = some b →
      max a.length b.length ≤ impl.textdistance.lcs a b + cost s
