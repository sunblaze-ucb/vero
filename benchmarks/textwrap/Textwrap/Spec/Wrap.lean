import Textwrap.Harness

/-!
# Textwrap.Spec.Wrap

Specifications for the line-wrapping operations. Each `spec_*` is a
property over an arbitrary `impl : RepoImpl`; the API is always reached
through `impl.textwrap.<fn>`.

`lineWidth` is *not* an API: it is frozen vocabulary (the total occupied
width of a line), exposed as the plain `def Textwrap.lineWidth` so specs
can reference it directly, like the frozen `IsValidWrapping` /
`IsGreedyMaximal` predicates below.

The obligations pin `wrap` as the unique answer: words are preserved in
order, every line fits (given no over-long word), and each line is packed
maximally (the first word of every non-initial line could not have been
appended to the previous line). A further block characterises `wrap` as
the solution to a line-wrapping optimization problem against the frozen
`IsValidWrapping` predicate (contiguous, nonempty, within-width lines
recovering the input): `wrap` is a valid wrapping using the fewest lines,
conserves total word-width, and is a fixpoint on its own flattened output.
Companion laws cover `shorten` and cross-API relations.

DO NOT MODIFY — specification file.
-/

-- ── Frozen vocabulary: valid wrappings ─────────────────────────

/-- `IsValidWrapping width chunks lines`: `lines` is a *valid* way to break
    the word-lengths `chunks` into output lines under `width` — the lines,
    concatenated in order, recover exactly `chunks` (a contiguous partition,
    no word lost / duplicated / reordered / split); every line is nonempty;
    and every line's total width is within `width`. Frozen vocabulary, so
    specs can quantify over *all* valid wrappings without naming the
    implementation. -/
def IsValidWrapping (width : Nat) (chunks : List Nat) (lines : List Line) : Prop :=
  lines.flatten = chunks ∧
  (∀ l ∈ lines, l ≠ []) ∧
  (∀ l ∈ lines, l.sum ≤ width)

/-- `IsGreedyMaximal width lines`: every *adjacent* pair of output lines is
    "tight" — the earlier line's total width plus the first word of the next
    line exceeds `width`, so that first word genuinely could not have been
    appended to the previous line. Frozen vocabulary, so specs can
    characterise this property without naming the implementation. -/
def IsGreedyMaximal (width : Nat) : List Line → Prop
  | [] => True
  | [_] => True
  | x :: y :: rest => x.sum + (y.head?.getD 0) > width ∧ IsGreedyMaximal width (y :: rest)

-- ── wrap: words preserved (witness) ────────────────────────────

/-- Witness: flattening the wrapped lines recovers exactly the input
    words, in order — nothing is lost, duplicated, or reordered. -/
def spec_wrap_preserves_words (impl : RepoImpl) : Prop :=
  ∀ (chunks : List Nat) (w : Nat),
    (impl.textwrap.wrap chunks w).flatten = chunks

/-- Anchor: wrapping no words produces no lines. -/
def spec_wrap_empty (impl : RepoImpl) : Prop :=
  ∀ (w : Nat),
    impl.textwrap.wrap [] w = []

/-- Anchor: every emitted line is nonempty (so its `head?` is a real
    word and the maximality spec is meaningful). -/
def spec_wrap_lines_nonempty (impl : RepoImpl) : Prop :=
  ∀ (chunks : List Nat) (w : Nat),
    ∀ line ∈ impl.textwrap.wrap chunks w, line ≠ []

-- ── wrap: every line fits (bound) ──────────────────────────────

/-- Bound: when no single word exceeds the width, every emitted line's
    total width is within the width. (Over-long words are necessarily
    placed on their own over-wide line, so the precondition is needed.) -/
def spec_wrap_lines_fit (impl : RepoImpl) : Prop :=
  ∀ (chunks : List Nat) (w : Nat),
    (∀ c ∈ chunks, c ≤ w) →
      ∀ line ∈ impl.textwrap.wrap chunks w,
        Textwrap.lineWidth line ≤ w

-- ── wrap: greedy maximality ────────────────────────────────────

/-- Maximality: for every adjacent pair of output lines, the earlier line
    plus the first word of the next line would exceed the width — i.e. that
    word genuinely could not fit on the previous line. This pins the *greedy*
    answer: a wrap that breaks a line early (while the next word still fit)
    violates this. -/
def spec_wrap_greedy_maximal (impl : RepoImpl) : Prop :=
  ∀ (chunks : List Nat) (w : Nat),
    ∀ i, (h : i + 1 < (impl.textwrap.wrap chunks w).length) →
      Textwrap.lineWidth ((impl.textwrap.wrap chunks w)[i])
        + (((impl.textwrap.wrap chunks w)[i+1]'h).head?.getD 0) > w

-- ── wrap: structural / closure / boundary ─────────────────────

/-- Closure (no-split, contiguous): every output line is a *contiguous
    block* of the original input words — an infix `line <:+: chunks`, not
    merely a set of members drawn from `chunks`. Because we model
    `break_long_words=False`, a word is never broken; and because lines are
    cut at consecutive boundaries, each emitted line is a run of adjacent
    input words in their original order. Rejects any impl that splits,
    invents, reorders, or interleaves words across lines (all of which a
    bare membership test would still admit). -/
def spec_wrap_chunks_subset (impl : RepoImpl) : Prop :=
  ∀ (chunks : List Nat) (w : Nat),
    ∀ line ∈ impl.textwrap.wrap chunks w, line <:+: chunks

/-- Boundary: when there is at least one word and the whole sequence fits
    within the width, `wrap` emits a single line holding all the words.
    Pins the "don't break early" half of greedy packing. -/
def spec_wrap_single_line (impl : RepoImpl) : Prop :=
  ∀ (chunks : List Nat) (w : Nat),
    chunks ≠ [] →
    Textwrap.lineWidth chunks ≤ w →
      impl.textwrap.wrap chunks w = [chunks]

/-- Count bound: there are never more output lines than input words (every
    line carries at least one word). Rejects an impl that emits spurious
    empty lines or over-fragments. -/
def spec_wrap_lines_le_words (impl : RepoImpl) : Prop :=
  ∀ (chunks : List Nat) (w : Nat),
    (impl.textwrap.wrap chunks w).length ≤ chunks.length

-- ── wrap: monotonicity in width ────────────────────────────────

/-- Monotonicity: widening the line width never increases the number of
    output lines. Rejects impls whose line count behaves erratically in the
    width. -/
def spec_wrap_width_mono (impl : RepoImpl) : Prop :=
  ∀ (chunks : List Nat) (w₁ w₂ : Nat),
    w₁ ≤ w₂ →
      (impl.textwrap.wrap chunks w₂).length ≤ (impl.textwrap.wrap chunks w₁).length

-- ── shorten: prefix + fit anchors ──────────────────────────────

/-- Anchor: the shortened result is a prefix of the input words. -/
def spec_shorten_prefix (impl : RepoImpl) : Prop :=
  ∀ (chunks : List Nat) (w : Nat),
    impl.textwrap.shorten chunks w <+: chunks

/-- Anchor: the shortened result *always* fits within the width —
    unconditionally, with no hypothesis on the first word. Even when the
    leading word is over-long, the kept run's width is within `width` (in
    that case `shorten` keeps nothing). Rejects any `shorten` that can
    return a run wider than the limit. -/
def spec_shorten_fits (impl : RepoImpl) : Prop :=
  ∀ (chunks : List Nat) (w : Nat),
    Textwrap.lineWidth (impl.textwrap.shorten chunks w) ≤ w

-- ── shorten: defining base + closure + maximality ──────────────

/-- Defining base case: shortening nothing yields nothing. -/
def spec_shorten_nil (impl : RepoImpl) : Prop :=
  ∀ (w : Nat),
    impl.textwrap.shorten [] w = []

/-- Closure characterisation (both directions): `shorten` keeps *every*
    word exactly when the whole input fits within the width —
    `shorten chunks w = chunks ↔ lineWidth chunks ≤ w`. The forward
    direction rejects an impl that stops short while words still fit; the
    converse rejects an impl that keeps every word even when the total
    overflows. (Sound in both directions: an over-long total forces
    `shorten` to drop at least one word, so equality fails precisely when
    the fit hypothesis fails.) -/
def spec_shorten_all_fits (impl : RepoImpl) : Prop :=
  ∀ (chunks : List Nat) (w : Nat),
    (impl.textwrap.shorten chunks w = chunks ↔ Textwrap.lineWidth chunks ≤ w)

/-- Length bound: the shortened result is no longer than the input.
    Rejects a `shorten` that ever returns more words than it was given. -/
def spec_shorten_length_le (impl : RepoImpl) : Prop :=
  ∀ (chunks : List Nat) (w : Nat),
    (impl.textwrap.shorten chunks w).length ≤ chunks.length

/-- Maximality: when the result is a *strict* prefix (so some word was
    dropped), the very next word would overflow the width —
    `lineWidth (shorten …) + nextWord > w`. This pins `shorten` as the
    *maximal* fitting prefix: a result that stops one word too early
    (while that word still fit) violates it. -/
def spec_shorten_maximal (impl : RepoImpl) : Prop :=
  ∀ (chunks : List Nat) (w : Nat),
    (impl.textwrap.shorten chunks w).length < chunks.length →
      Textwrap.lineWidth (impl.textwrap.shorten chunks w)
        + (chunks[(impl.textwrap.shorten chunks w).length]?.getD 0) > w

-- ── cross-API: wrap's first line is shorten ────────────────────

/-- Cross-API law: when the first word fits within the width, the first
    output line of `wrap` is exactly `shorten chunks w` — i.e. the greedy
    first line of `wrap` coincides with the maximal fitting prefix
    computed by `shorten`. (The precondition is needed because an
    over-long first word still opens a `wrap` line of its own, whereas
    `shorten` keeps nothing.) -/
def spec_wrap_first_line_eq_shorten (impl : RepoImpl) : Prop :=
  ∀ (chunks : List Nat) (w : Nat),
    (chunks.head?.getD 0 ≤ w) →
      (impl.textwrap.wrap chunks w).head?.getD [] = impl.textwrap.shorten chunks w

-- ── wrap: global optimality block ──────────────────────────────

/-- Feasibility: when no single word exceeds the width, `wrap`'s own output
    is a *valid wrapping* of the input — a contiguous nonempty within-width
    partition. (The precondition is required because an over-long word forces
    `wrap` to emit a line wider than the width, which no valid wrapping may
    contain.) Pairs with `spec_wrap_min_lines`: the optimum is *attained*,
    not merely a lower bound. -/
def spec_wrap_is_valid_wrapping (impl : RepoImpl) : Prop :=
  ∀ (chunks : List Nat) (w : Nat),
    (∀ c ∈ chunks, c ≤ w) →
      IsValidWrapping w chunks (impl.textwrap.wrap chunks w)

/-- Greedy optimality: among *all* valid wrappings of the input under the
    width, the greedy `wrap` uses the fewest lines — its line count is `≤`
    that of any valid wrapping `lines`. A wrapping that ever breaks a line
    before it is full (leaving a word that still fit) can only use more lines,
    never fewer. No precondition is needed for the `≤` direction — when a word
    is over-long there simply are no valid wrappings to beat. Rejects any
    non-greedy / suboptimal packer. -/
def spec_wrap_min_lines (impl : RepoImpl) : Prop :=
  ∀ (chunks : List Nat) (w : Nat) (lines : List Line),
    IsValidWrapping w chunks lines →
      (impl.textwrap.wrap chunks w).length ≤ lines.length

/-- Conservation: summing the widths of all output lines recovers the total
    width of the input words — no word-length is lost, duplicated, or invented
    across the whole packing. -/
def spec_wrap_total_width_conserved (impl : RepoImpl) : Prop :=
  ∀ (chunks : List Nat) (w : Nat),
    ((impl.textwrap.wrap chunks w).map Textwrap.lineWidth).sum
      = Textwrap.lineWidth chunks

/-- Line-count lower bound: when no word is over-long, the number of output
    lines is large enough to hold the total width — `totalWidth ≤ #lines × w`.
    Rejects an impl that claims to fit more width than the lines can
    physically carry. -/
def spec_wrap_lines_lower_bound (impl : RepoImpl) : Prop :=
  ∀ (chunks : List Nat) (w : Nat),
    (∀ c ∈ chunks, c ≤ w) →
      Textwrap.lineWidth chunks ≤ (impl.textwrap.wrap chunks w).length * w

/-- Fixpoint: flattening `wrap`'s output back into a single word sequence and
    re-wrapping it at the same width reproduces the very same line structure.
    `wrap` is idempotent on its own flattened output — a stability property of
    the greedy packing (rejects an impl whose output depends on incidental
    line boundaries rather than only on the word sequence and width). -/
def spec_wrap_rewrap_fixpoint (impl : RepoImpl) : Prop :=
  ∀ (chunks : List Nat) (w : Nat),
    impl.textwrap.wrap ((impl.textwrap.wrap chunks w).flatten) w
      = impl.textwrap.wrap chunks w

-- ── wrap: prefix-domination / structural block ─────────────────

/-- Greedy domination on consumed words: for every line-prefix count `k`, the
    greedy `wrap` has consumed at least as many input words in its first `k`
    lines as *any* valid wrapping has in its first `k` lines —
    `(lines.take k).flatten.length ≤ ((wrap chunks w).take k).flatten.length`.
    Greedy never falls behind a competitor at any prefix boundary. Rejects any
    packer that ever lags a valid wrapping on consumed words. -/
def spec_wrap_stays_ahead (impl : RepoImpl) : Prop :=
  ∀ (chunks : List Nat) (w : Nat) (lines : List Line),
    IsValidWrapping w chunks lines →
      ∀ (k : Nat),
        (lines.take k).flatten.length
          ≤ ((impl.textwrap.wrap chunks w).take k).flatten.length

/-- Uniqueness: the greedy `wrap` is *the* valid wrapping that is also
    greedy-maximal — among all valid wrappings, the unique one in which every
    adjacent boundary satisfies `IsGreedyMaximal`. Any valid wrapping that
    never breaks a line early (while the next word still fit) must coincide
    with `wrap`. Rejects every non-greedy valid packing. -/
def spec_wrap_lex_maximal (impl : RepoImpl) : Prop :=
  ∀ (chunks : List Nat) (w : Nat) (lines : List Line),
    IsValidWrapping w chunks lines →
      IsGreedyMaximal w lines →
        impl.textwrap.wrap chunks w = lines

/-- Recursive structure: the wrap of `chunks` is its first output line followed
    by the wrap of the *leftover* words after that line —
    `wrap chunks w = firstLine :: wrap (chunks.drop firstLine.length) w`
    (for nonempty input), where `firstLine` is `wrap`'s own head line. Rejects
    an impl whose later lines depend on more than the leftover word sequence. -/
def spec_wrap_optimal_substructure (impl : RepoImpl) : Prop :=
  ∀ (chunks : List Nat) (w : Nat),
    chunks ≠ [] →
      impl.textwrap.wrap chunks w
        = ((impl.textwrap.wrap chunks w).headD [])
          :: impl.textwrap.wrap
              (chunks.drop ((impl.textwrap.wrap chunks w).headD []).length) w

/-- Line-count monotonicity under appending words: appending more words to the
    input never *decreases* the number of output lines —
    `(wrap chunks w).length ≤ (wrap (chunks ++ extra) w).length`. Extra words
    can only fill the last line or open new ones, never merge existing lines.
    Rejects an impl whose line count is non-monotone in the input length. -/
def spec_wrap_lines_mono_append (impl : RepoImpl) : Prop :=
  ∀ (chunks extra : List Nat) (w : Nat),
    (impl.textwrap.wrap chunks w).length
      ≤ (impl.textwrap.wrap (chunks ++ extra) w).length

/-- Combined feasibility + optimality (composed theorem): under the
    no-over-long-word precondition, the greedy `wrap` is simultaneously a valid
    wrapping of the input *and* uses no more lines than any valid wrapping —
    `IsValidWrapping w chunks (wrap chunks w) ∧ (∀ valid lines, #wrap ≤ #lines)`.
    The optimum is both feasible (attained) and a global lower bound, stated as
    one obligation: greedy solves the line-wrapping optimisation problem
    end-to-end. -/
def spec_wrap_feasible_optimal (impl : RepoImpl) : Prop :=
  ∀ (chunks : List Nat) (w : Nat),
    (∀ c ∈ chunks, c ≤ w) →
      IsValidWrapping w chunks (impl.textwrap.wrap chunks w) ∧
        ∀ (lines : List Line),
          IsValidWrapping w chunks lines →
            (impl.textwrap.wrap chunks w).length ≤ lines.length

/-- Two-sided line-count bound (counting argument, both directions): when no
    word is over-long, the output line count is sandwiched —
    `totalWidth ≤ #lines × w` (lower bound: each line holds at most `w` of
    width, so you need at least `⌈totalWidth / w⌉` lines) *and*
    `#lines ≤ #chunks` (upper bound: every line carries at least one word). The
    lower bound is tight precisely when the lines pack perfectly to width `w`;
    the upper bound is tight when every word lands on its own line. Pins the
    line count between the continuous total-length floor and the discrete
    word-count ceiling. -/
def spec_wrap_lines_count_bounds (impl : RepoImpl) : Prop :=
  ∀ (chunks : List Nat) (w : Nat),
    (∀ c ∈ chunks, c ≤ w) →
      Textwrap.lineWidth chunks ≤ (impl.textwrap.wrap chunks w).length * w ∧
        (impl.textwrap.wrap chunks w).length ≤ chunks.length

-- ── wrap: prefix-domination / substructure block ───────────────

/-- First-line word-count maximality: among *all* valid wrappings of the input
    under the width, none places more words on its first line than the greedy
    `wrap` does — `(lines.headD []).length ≤ (wrap …).headD []).length`. Greedy
    fills its opening line as far as the width allows, so no feasible packing can
    get more words onto its first line. Rejects any packer that breaks its first
    line early. -/
def spec_wrap_first_line_longest (impl : RepoImpl) : Prop :=
  ∀ (chunks : List Nat) (w : Nat) (lines : List Line),
    IsValidWrapping w chunks lines →
      (lines.headD []).length ≤ ((impl.textwrap.wrap chunks w).headD []).length

/-- Cumulative-width domination: for every line-prefix count `k`, the greedy
    `wrap` has packed at least as much *total width* into its first `k` lines as
    *any* valid wrapping has into its first `k` lines —
    `((lines.take k).map lineWidth).sum ≤ (((wrap …).take k).map lineWidth).sum`.
    A domination law in the *width* measure (distinct from the word-count one):
    greedy never falls behind a competitor on how much width it has packed by any
    prefix boundary. Rejects any packer that ever falls behind a valid wrapping
    on cumulative packed width. -/
def spec_wrap_width_stays_ahead (impl : RepoImpl) : Prop :=
  ∀ (chunks : List Nat) (w : Nat) (lines : List Line),
    IsValidWrapping w chunks lines →
      ∀ (k : Nat),
        ((lines.take k).map Textwrap.lineWidth).sum
          ≤ (((impl.textwrap.wrap chunks w).take k).map Textwrap.lineWidth).sum

/-- Drop-last substructure from the back: deleting the *last* output line of
    greedy reproduces exactly the greedy wrap of the words that precede that
    last line —
    `(wrap chunks w).dropLast = wrap (chunks.take (#chunks − #lastLine)) w`,
    where `lastLine` is `wrap`'s own final line. Rejects an impl whose earlier
    line breaks depend on later words. -/
def spec_wrap_dropLast_eq (impl : RepoImpl) : Prop :=
  ∀ (chunks : List Nat) (w : Nat),
    impl.textwrap.wrap chunks w ≠ [] →
      (impl.textwrap.wrap chunks w).dropLast
        = impl.textwrap.wrap
            (chunks.take (chunks.length - ((impl.textwrap.wrap chunks w).getLastD []).length)) w

/-- Line-count vs total-width bound: the output line count obeys
    `(#lines − 1) × w ≤ 2 × totalWidth`. You can never have many output lines
    while the total width stays small. Rejects an impl that emits many
    under-full lines. -/
def spec_wrap_lines_pair_width_bound (impl : RepoImpl) : Prop :=
  ∀ (chunks : List Nat) (w : Nat),
    ((impl.textwrap.wrap chunks w).length - 1) * w
      ≤ 2 * Textwrap.lineWidth chunks

-- ── wrap: substructure / composition block ─────────────────────

/-- Generalized substructure: dropping the first `k` output lines of greedy
    reproduces exactly the greedy wrap of the words that remain after those `k`
    lines —
    `(wrap chunks w).drop k = wrap (chunks.drop ((wrap chunks w).take k).flatten.length) w`.
    The *entire suffix* of the packing is a function of only the leftover word
    sequence after the first `k` lines, not of where the earlier breaks fell.
    Rejects an impl whose later lines depend on more than the leftover word
    sequence. -/
def spec_wrap_drop_substructure (impl : RepoImpl) : Prop :=
  ∀ (chunks : List Nat) (w : Nat) (k : Nat),
    (impl.textwrap.wrap chunks w).drop k
      = impl.textwrap.wrap
          (chunks.drop (((impl.textwrap.wrap chunks w).take k).flatten.length)) w

/-- Line-count subadditivity under concatenation: when no word is over-long,
    wrapping a concatenation uses no more lines than the sum of the line counts
    of the two parts wrapped separately —
    `(wrap (xs ++ ys) w).length ≤ (wrap xs w).length + (wrap ys w).length`.
    Splitting the input at an arbitrary boundary and wrapping each half can
    only waste line budget, never save it. Rejects any packer that is not
    line-count optimal. -/
def spec_wrap_lines_subadditive (impl : RepoImpl) : Prop :=
  ∀ (xs ys : List Nat) (w : Nat),
    (∀ c ∈ xs ++ ys, c ≤ w) →
      (impl.textwrap.wrap (xs ++ ys) w).length
        ≤ (impl.textwrap.wrap xs w).length + (impl.textwrap.wrap ys w).length

/-- Append stability: every output line of `wrap xs` *except its last*
    reappears, unchanged and in order, at the very front of `wrap (xs ++ ys)` —
    `(wrap (xs ++ ys) w).take ((wrap xs w).length - 1) = (wrap xs w).dropLast`
    (for nonempty `wrap xs`). Greedy's earlier line breaks are insensitive to
    *any* words appended after `xs`: only the final, still-open line of
    `wrap xs` can merge with the new words. Rejects an impl whose early breaks
    shift when input is extended. -/
def spec_wrap_append_realign (impl : RepoImpl) : Prop :=
  ∀ (xs ys : List Nat) (w : Nat),
    impl.textwrap.wrap xs w ≠ [] →
      (impl.textwrap.wrap (xs ++ ys) w).take ((impl.textwrap.wrap xs w).length - 1)
        = (impl.textwrap.wrap xs w).dropLast

/-- Exact append line-count identity: wrapping `xs ++ ys` costs exactly the
    all-but-last lines of `wrap xs` plus the cost of re-wrapping `xs`'s *last
    line* together with `ys` —
    `(wrap (xs ++ ys) w).length = ((wrap xs w).length - 1) + (wrap (lastLine ++ ys) w).length`,
    where `lastLine = (wrap xs w).getLastD []` (and `= (wrap ys w).length` when
    `wrap xs` is empty, i.e. `xs = []`). The line count of a concatenation is a
    compositional function of the two parts — all earlier lines are fixed, and
    only the boundary between them is recomputed. Rejects an impl with a
    non-compositional line count. -/
def spec_wrap_append_count_realign (impl : RepoImpl) : Prop :=
  ∀ (xs ys : List Nat) (w : Nat),
    (impl.textwrap.wrap (xs ++ ys) w).length
      = (if impl.textwrap.wrap xs w = [] then
            (impl.textwrap.wrap ys w).length
         else
            ((impl.textwrap.wrap xs w).length - 1)
              + (impl.textwrap.wrap ((impl.textwrap.wrap xs w).getLastD [] ++ ys) w).length)

-- ── shorten: deeper width-maximality / locality / monotonicity ─

/-- Shorten width-maximality: among *all* fitting prefixes of the input, none
    packs more total WIDTH than `shorten` does —
    `b <+: chunks → lineWidth b ≤ w → lineWidth b ≤ lineWidth (shorten chunks w)`.
    `shorten` extracts the most width any within-width prefix can hold. Rejects a
    `shorten` that stops while a wider fitting prefix remains. -/
def spec_shorten_width_maximal (impl : RepoImpl) : Prop :=
  ∀ (chunks : List Nat) (w : Nat) (b : List Nat),
    b <+: chunks → Textwrap.lineWidth b ≤ w →
      Textwrap.lineWidth b ≤ Textwrap.lineWidth (impl.textwrap.shorten chunks w)

/-- Shorten word-count monotonicity in the width: a wider width never keeps
    fewer words —
    `w₁ ≤ w₂ → (shorten chunks w₁).length ≤ (shorten chunks w₂).length`. More
    room can only let `shorten` keep at least as many words, never fewer.
    Rejects a `shorten` whose kept count is non-monotone in the width. -/
def spec_shorten_len_mono_width (impl : RepoImpl) : Prop :=
  ∀ (chunks : List Nat) (w₁ w₂ : Nat),
    w₁ ≤ w₂ →
      (impl.textwrap.shorten chunks w₁).length ≤ (impl.textwrap.shorten chunks w₂).length

/-- Shorten input-prefix monotonicity: shortening a *prefix* of the input yields
    a prefix of shortening the whole —
    `shorten (chunks.take k) w <+: shorten chunks w`. Truncating the input can
    only stop `shorten` earlier or at the same place, keeping a prefix of what it
    would keep on the full input. Rejects a `shorten` that reorders or shifts its
    kept run when the input is truncated. -/
def spec_shorten_prefix_mono (impl : RepoImpl) : Prop :=
  ∀ (chunks : List Nat) (w : Nat) (k : Nat),
    impl.textwrap.shorten (chunks.take k) w <+: impl.textwrap.shorten chunks w

/-- Shorten locality: the result depends only on the kept run plus the single
    word that first overflows —
    `shorten chunks w = shorten (chunks.take ((shorten chunks w).length + 1)) w`.
    The stop point is a *local* decision — words beyond the first dropped one
    cannot change where `shorten` stops. Rejects a `shorten` whose stop point
    depends on words further down the input. -/
def spec_shorten_local (impl : RepoImpl) : Prop :=
  ∀ (chunks : List Nat) (w : Nat),
    impl.textwrap.shorten chunks w
      = impl.textwrap.shorten (chunks.take ((impl.textwrap.shorten chunks w).length + 1)) w

/-- Shorten idempotence (fixpoint): re-shortening an already shortened result
    changes nothing —
    `shorten (shorten chunks w) w = shorten chunks w`. `shorten`'s output is a
    stable representative under repeated application. Rejects a `shorten` whose
    output is not a stable fitting prefix. -/
def spec_shorten_idempotent (impl : RepoImpl) : Prop :=
  ∀ (chunks : List Nat) (w : Nat),
    impl.textwrap.shorten (impl.textwrap.shorten chunks w) w
      = impl.textwrap.shorten chunks w

-- ── wrap: over-long word isolation ─────────────────────────────
-- The fit/optimality block above is *guarded* by the no-over-long-word
-- precondition `∀ c ∈ chunks, c ≤ w`, and `IsValidWrapping` rules out any
-- over-wide line — so when a single word exceeds the width, those specs go
-- vacuous and say nothing about how the over-long word is placed. The two
-- obligations below pin exactly that uncovered case: an over-wide output line
-- must be a *lone* over-long word (no other word — not even a zero-width one —
-- may share its line), matching `textwrap`'s `break_long_words=False` behaviour.

/-- Over-long-word isolation: any emitted line whose total width *exceeds* the
    line width must hold exactly one word. Since a line can only become
    over-wide by carrying a single word longer than the width (greedy never
    appends to, nor extends, an over-long line), such a line is a singleton.
    This is the direction the guarded `spec_wrap_lines_fit` cannot reach: it
    rules out an impl that merges a following word — including a *zero-width*
    word — onto an over-long word's line (e.g. returning `[[4, 0]]` rather than
    `[[4], [0]]` for chunks `[4, 0]` at width `3`). -/
def spec_wrap_overlong_isolated (impl : RepoImpl) : Prop :=
  ∀ (chunks : List Nat) (w : Nat),
    ∀ line ∈ impl.textwrap.wrap chunks w,
      Textwrap.lineWidth line > w → line.length = 1

-- ── Additional occurrence and boundary obligations ────────────

/-- The occurrence summary of all wrapped output words. -/
def Textwrap.wrappedValueCounts (lines : List Line) : List (Nat × Nat) :=
  (lines.flatten.eraseDups.mergeSort (fun a b => a ≤ b)).map
    (fun a => (a, (lines.map (fun line => line.count a)).sum))

/-- The occurrence summary of the input words. -/
def Textwrap.inputValueCounts (chunks : List Nat) : List (Nat × Nat) :=
  (chunks.eraseDups.mergeSort (fun a b => a ≤ b)).map
    (fun a => (a, chunks.count a))

/-- The input offsets where output lines begin. -/
def Textwrap.lineStartOffsets (lines : List Line) : List Nat :=
  (lines.map (fun line => line.length)).foldl
    (fun acc n => (acc.headD 0 + n) :: acc) [0] |>.reverse.dropLast

/-- Per-word occurrence summaries agree between the wrapped output and input. -/
def spec_wrap_value_count_table (impl : RepoImpl) : Prop :=
  ∀ (chunks : List Nat) (w : Nat),
    Textwrap.wrappedValueCounts (impl.textwrap.wrap chunks w)
      = Textwrap.inputValueCounts chunks

/-- A word value can appear on no more output lines than it appears in the input. -/
def spec_wrap_duplicate_value_lines_count (impl : RepoImpl) : Prop :=
  ∀ (chunks : List Nat) (w a : Nat),
    ((impl.textwrap.wrap chunks w).filter (fun line => decide (a ∈ line))).length
      ≤ chunks.count a

/-- Each recorded line-start offset reads the head of the corresponding line. -/
def spec_wrap_start_offsets_index_heads (impl : RepoImpl) : Prop :=
  ∀ (chunks : List Nat) (w : Nat),
    (Textwrap.lineStartOffsets (impl.textwrap.wrap chunks w)).map
      (fun i => chunks[i]?)
        = (impl.textwrap.wrap chunks w).map (fun line => line.head?)

/-- Each output line's last word is at the computed end of that line in the input. -/
def spec_wrap_line_last_at_boundary (impl : RepoImpl) : Prop :=
  ∀ (chunks : List Nat) (w i : Nat)
    (h : i < (impl.textwrap.wrap chunks w).length),
      ((impl.textwrap.wrap chunks w)[i]'h).getLast?
        = chunks[(((impl.textwrap.wrap chunks w).take (i + 1)).flatten.length - 1)]?

/-- Each internal output boundary is exactly where the next input word no longer fits. -/
def spec_wrap_boundary_width_exact (impl : RepoImpl) : Prop :=
  ∀ (chunks : List Nat) (w i : Nat)
    (h : i + 1 < (impl.textwrap.wrap chunks w).length),
      Textwrap.lineWidth ((impl.textwrap.wrap chunks w)[i])
        + (chunks[((impl.textwrap.wrap chunks w).take (i + 1)).flatten.length]?).getD 0 > w

/-- Every input position is realized at a matching output line and in-line offset. -/
def spec_wrap_word_index_locator (impl : RepoImpl) : Prop :=
  ∀ (chunks : List Nat) (w j : Nat) (hj : j < chunks.length),
    ∃ i, ∃ hi : i < (impl.textwrap.wrap chunks w).length,
      ∃ k, ∃ hk : k < ((impl.textwrap.wrap chunks w)[i]'hi).length,
        ((impl.textwrap.wrap chunks w)[i]'hi)[k]'hk = chunks[j]'hj ∧
          ((impl.textwrap.wrap chunks w).take i).flatten.length + k = j

/-- The shortened prefix and the remaining suffix account for every input occurrence. -/
def spec_shorten_kept_drop_count (impl : RepoImpl) : Prop :=
  ∀ (chunks : List Nat) (w a : Nat),
    (impl.textwrap.shorten chunks w).count a
      + (chunks.drop (impl.textwrap.shorten chunks w).length).count a
        = chunks.count a

-- ── wrap: deep uniqueness / structural / edit-sensitivity block ─

/-- Prefix realignment: any valid, greedy-maximal wrapping that agrees with `wrap`
    on how many words it has consumed after its first `k` lines already agrees with
    `wrap` line-for-line on those `k` lines, and its remaining suffix is itself the
    `wrap` of its own flattened words —
    `lines.take k = (wrap …).take k ∧ lines.drop k = wrap ((lines.drop k).flatten) w`.
    Ties on consumed-count force ties on the actual line breaks. Rejects any valid
    greedy-maximal wrapping that reaches the same word boundary via different cuts. -/
def spec_wrap_prefix_tie_recursive_suffix (impl : RepoImpl) : Prop :=
  ∀ (chunks : List Nat) (w : Nat) (lines : List Line) (k : Nat),
    IsValidWrapping w chunks lines →
      IsGreedyMaximal w lines →
        (lines.take k).flatten.length =
          ((impl.textwrap.wrap chunks w).take k).flatten.length →
          lines.take k = (impl.textwrap.wrap chunks w).take k ∧
            lines.drop k = impl.textwrap.wrap ((lines.drop k).flatten) w

/-- Width-indexed consumed-word domination: at every fixed line budget `k`, wrapping
    with a wider width has consumed at least as many input words in its first `k`
    lines as wrapping with a narrower width —
    `w₁ ≤ w₂ → ((wrap chunks w₁).take k).flatten.length ≤ ((wrap chunks w₂).take k).flatten.length`.
    A per-prefix refinement of width monotonicity. Rejects an impl whose consumed-word
    progress is non-monotone in the width. -/
def spec_wrap_width_mono_prefix_consumed (impl : RepoImpl) : Prop :=
  ∀ (chunks : List Nat) (w₁ w₂ k : Nat),
    w₁ ≤ w₂ →
      ((impl.textwrap.wrap chunks w₁).take k).flatten.length
        ≤ ((impl.textwrap.wrap chunks w₂).take k).flatten.length

/-- Mid-line prefix truncation: taking the input up to an arbitrary point `j` inside
    output line `k` reproduces exactly the earlier `k` full output lines followed by
    the corresponding `j`-word prefix of line `k` —
    `wrap (chunks.take ((wrap …).take k).flatten.length + j) w = (wrap …).take k ++ (if j = 0 then [] else [line_k.take j])`.
    The truncation point need not be a line boundary. Rejects an impl whose earlier
    line breaks shift when the input is truncated inside a later line. -/
def spec_wrap_take_midline_prefix (impl : RepoImpl) : Prop :=
  ∀ (chunks : List Nat) (w k j : Nat),
    let lines := impl.textwrap.wrap chunks w
    ∀ (h : k < lines.length),
      j ≤ (lines[k]'h).length →
        impl.textwrap.wrap (chunks.take ((lines.take k).flatten.length + j)) w
          = lines.take k ++ (if j = 0 then [] else [(lines[k]'h).take j])

/-- Append-one line-count recurrence: appending a single word `c` either fills the
    existing last line (line count unchanged) or opens exactly one new line (line count
    +1), with the empty-input case yielding a single line —
    `#wrap (chunks ++ [c]) = if wrap chunks = [] then 1 else if lineWidth lastLine + c ≤ w then #wrap chunks else #wrap chunks + 1`.
    An exact recurrence for the line count under a one-word append. Rejects an impl
    with a non-compositional last-line append behaviour. -/
def spec_wrap_append_one_count_exact (impl : RepoImpl) : Prop :=
  ∀ (chunks : List Nat) (w c : Nat),
    (impl.textwrap.wrap (chunks ++ [c]) w).length =
      (if impl.textwrap.wrap chunks w = [] then
        1
      else if Textwrap.lineWidth ((impl.textwrap.wrap chunks w).getLastD []) + c ≤ w then
        (impl.textwrap.wrap chunks w).length
      else
        (impl.textwrap.wrap chunks w).length + 1)

/-- Physical uniqueness: `wrap` is the unique contiguous partition of the input whose
    lines are all nonempty, each physically admissible (within width, or a single
    over-long word), and greedy-maximal at every adjacent boundary —
    any `lines` meeting all four conditions equals `wrap chunks w`. Unifies the
    within-width and lone-over-long-word regimes in one uniqueness law. Rejects every
    non-greedy admissible packing, including ones that mis-place an over-long word. -/
def spec_wrap_physical_greedy_unique (impl : RepoImpl) : Prop :=
  ∀ (chunks : List Nat) (w : Nat) (lines : List Line),
    lines.flatten = chunks →
      (∀ line ∈ lines, line ≠ []) →
        (∀ line ∈ lines, Textwrap.lineWidth line ≤ w ∨ line.length = 1) →
          IsGreedyMaximal w lines →
            impl.textwrap.wrap chunks w = lines

/-- Local-fixpoint uniqueness: `wrap` is the unique contiguous partition of the input
    in which every line is stable under re-wrapping on its own (`wrap line w = [line]`)
    and every adjacent pair of lines is stable under re-wrapping the two together
    (`wrap (lᵢ ++ lᵢ₊₁) w = [lᵢ, lᵢ₊₁]`). Local stability at every single line and every
    adjacent pair pins the whole global packing. Rejects any partition that is locally
    stable yet differs from greedy. -/
def spec_wrap_pairwise_rewrap_fixpoint_unique (impl : RepoImpl) : Prop :=
  ∀ (chunks : List Nat) (w : Nat) (lines : List Line),
    lines.flatten = chunks →
      (∀ line ∈ lines, impl.textwrap.wrap line w = [line]) →
        (∀ i, i + 1 < lines.length →
          impl.textwrap.wrap ((lines[i]?.getD []) ++ (lines[i + 1]?.getD [])) w
            = [lines[i]?.getD [], lines[i + 1]?.getD []]) →
          impl.textwrap.wrap chunks w = lines

/-- Line = shorten of the remaining suffix: each output line `i` is the maximal fitting
    prefix (`shorten`) of the input words remaining after the first `i` lines, falling
    back to a lone leading word when that prefix would be empty (the over-long case) —
    `line_i = rest.take (if shorten rest w = [] then 1 else (shorten rest w).length)`,
    where `rest = chunks.drop ((wrap …).take i).flatten.length`. Couples `wrap`'s
    per-line structure to `shorten` at every line, not just the first. Rejects an impl
    whose lines are not the greedy fitting prefixes of their suffixes. -/
def spec_wrap_each_line_shorten_or_head (impl : RepoImpl) : Prop :=
  ∀ (chunks : List Nat) (w i : Nat)
    (h : i < (impl.textwrap.wrap chunks w).length),
      let rest := chunks.drop (((impl.textwrap.wrap chunks w).take i).flatten.length)
      let kept := impl.textwrap.shorten rest w
      let n := if kept = [] then 1 else kept.length
      (impl.textwrap.wrap chunks w)[i]'h = rest.take n

/-- Arbitrary-split recomposition: wrapping the whole input equals wrapping the first
    `k` words, dropping their last (still-open) line, and re-wrapping that dropped line
    concatenated with the remaining words —
    `wrap chunks w = if wrap (chunks.take k) = [] then wrap (chunks.drop k) w else (wrap (chunks.take k)).dropLast ++ wrap (lastLine ++ chunks.drop k) w`.
    The split point `k` need not fall on a line boundary. Rejects an impl whose output
    is not recomposable across an arbitrary word split. -/
def spec_wrap_take_drop_recompose (impl : RepoImpl) : Prop :=
  ∀ (chunks : List Nat) (w k : Nat),
    impl.textwrap.wrap chunks w =
      if impl.textwrap.wrap (chunks.take k) w = [] then
        impl.textwrap.wrap (chunks.drop k) w
      else
        (impl.textwrap.wrap (chunks.take k) w).dropLast ++
          impl.textwrap.wrap
            (((impl.textwrap.wrap (chunks.take k) w).getLastD []) ++ chunks.drop k) w

/-- Deletion line-count monotonicity: removing one word from the middle of the input
    never increases the number of output lines —
    `#wrap (xs ++ ys) w ≤ #wrap (xs ++ (c :: ys)) w`. A word can only ever be repacked
    to fill space or open a line, so deleting it cannot force more lines. Rejects an
    impl whose line count can rise when a word is removed. -/
def spec_wrap_delete_middle_count_mono (impl : RepoImpl) : Prop :=
  ∀ (xs ys : List Nat) (c w : Nat),
    (impl.textwrap.wrap (xs ++ ys) w).length
      ≤ (impl.textwrap.wrap (xs ++ (c :: ys)) w).length

/-- Insertion line-count bound: inserting one word into the middle of the input raises
    the number of output lines by at most two —
    `#wrap (xs ++ (c :: ys)) w ≤ #wrap (xs ++ ys) w + 2`. A single inserted word can
    split at most one existing line into three pieces. Rejects an impl whose line count
    can jump by more than two on a one-word insertion. -/
def spec_wrap_insert_middle_count_at_most_two (impl : RepoImpl) : Prop :=
  ∀ (xs ys : List Nat) (c w : Nat),
    (impl.textwrap.wrap (xs ++ (c :: ys)) w).length
      ≤ (impl.textwrap.wrap (xs ++ ys) w).length + 2

/-- Forced-boundary line-count lower bound: for nonempty input the number of output
    lines is at least one plus the number of adjacent input pairs whose two word-widths
    already sum to more than the width —
    `(if chunks = [] then 0 else 1 + #{i | chunksᵢ + chunksᵢ₊₁ > w}) ≤ #wrap chunks w`.
    Every such adjacent overflow pair forces a distinct real line break. Rejects an impl
    that packs two words together whose combined width already exceeds the limit. -/
def spec_wrap_adjacent_overflow_lower_bound (impl : RepoImpl) : Prop :=
  ∀ (chunks : List Nat) (w : Nat),
    (if chunks = [] then
       0
     else
       1 + ((chunks.zip chunks.tail).filter (fun p => decide (p.1 + p.2 > w))).length)
      ≤ (impl.textwrap.wrap chunks w).length

/-- Shorten append decomposition: shortening a concatenation either fully consumes the
    prefix `xs` and continues shortening `ys` against the residual width, or stops
    inside `xs` and ignores `ys` entirely —
    `shorten (xs ++ ys) w = if lineWidth xs ≤ w then xs ++ shorten ys (w - lineWidth xs) else shorten xs w`.
    The kept run splits compositionally at the `xs`/`ys` boundary. Rejects an impl whose
    `shorten` is not compositional across an append. -/
def spec_shorten_append_decompose (impl : RepoImpl) : Prop :=
  ∀ (xs ys : List Nat) (w : Nat),
    impl.textwrap.shorten (xs ++ ys) w =
      if Textwrap.lineWidth xs ≤ w then
        xs ++ impl.textwrap.shorten ys (w - Textwrap.lineWidth xs)
      else
        impl.textwrap.shorten xs w
