import Croniter.Harness

/-!
# Croniter.Spec.Cron

Specifications for the cron next-fire operations. Each `spec_*` is a
property over an arbitrary `impl : RepoImpl`; the API is always reached
through `impl.croniter.<fn>`, never by calling `Croniter.<fn>` directly.

`nextFire` is pinned as the smallest firing time strictly after the
query (a witness that fires, and nothing firing before it); `prevFire`
symmetrically as the largest strictly before. Properties are anchored on
the frozen field extractors `minOf` / `hourOf` / `dowOf`.

DO NOT MODIFY.
-/

/-- A spec is well-formed when each field lists at least one value and
    every listed value is within the field's range. This guarantees the
    schedule fires somewhere in any one-week window. -/
def wellFormed (s : CronSpec) : Prop :=
  (s.minutes ≠ [] ∧ ∀ m ∈ s.minutes, m < 60) ∧
  (s.hours ≠ [] ∧ ∀ h ∈ s.hours, h < 24) ∧
  (s.dows ≠ [] ∧ ∀ d ∈ s.dows, d < 7)

/-- Frozen generic iterator: `iterStep f t n` applies the step function `f`
    exactly `n` times starting from `t`. It references no implementation —
    the specs apply it to `impl.croniter.nextFire s`, so that `iterStep
    (impl.croniter.nextFire s) t n` is the `n`-th firing time after `t`. -/
def iterStep (f : Nat → Nat) (t : Nat) : Nat → Nat
  | 0 => t
  | n + 1 => f (iterStep f t n)

/-- Frozen counter: the number of consecutive non-matching minutes starting
    from `lo` (within `fuel` steps) before the first match. References only
    the frozen matcher `matchAt`, never `impl`. -/
def countNoMatch (s : CronSpec) (lo : Nat) : Nat → Nat
  | 0 => 0
  | fuel + 1 =>
      if matchAt s lo then 0
      else 1 + countNoMatch s (lo + 1) fuel

/-- Frozen window counter: the number of minutes in the half-open window
    `[lo, lo + fuel)` at which the predicate `p` holds. References no
    implementation — the specs instantiate `p` with `impl.croniter.cronMatches s`,
    so the count is genuinely a count of the implementation's firing minutes. -/
def countMatch (p : Nat → Bool) (lo : Nat) : Nat → Nat
  | 0 => 0
  | fuel + 1 => (if p lo then 1 else 0) + countMatch p (lo + 1) fuel

/-- Frozen gap-sum: the sum of the gaps between the first `n` consecutive
    iterates of a step function `f` starting from `t`. References no
    implementation — the specs apply it to `impl.croniter.nextFire s`, so
    `sumGaps (impl.croniter.nextFire s) t n` is the total span swept by the
    first `n` fires after `t` expressed as a telescoping sum of inter-fire
    gaps. -/
def sumGaps (f : Nat → Nat) (t : Nat) : Nat → Nat
  | 0 => 0
  | n + 1 => sumGaps f t n + (iterStep f t (n + 1) - iterStep f t n)

/-- A spec has de-duplicated fields when each field list is `Nodup`. Together
    with `wellFormed` (each value in range) this makes each field's length the
    true number of distinct allowed values. References no `impl`. -/
def noDupFields (s : CronSpec) : Prop :=
  s.minutes.Nodup ∧ s.hours.Nodup ∧ s.dows.Nodup

-- ── cronMatches: frozen anchor ─────────────────────────────────

/-- `cronMatches` is exactly the frozen field-extractor conjunction.
    Ties the matcher to `minOf` / `hourOf` / `dowOf` so the rest of the
    specs are anchored on fixed vocabulary. -/
def spec_cronMatches_iff (impl : RepoImpl) : Prop :=
  ∀ (s : CronSpec) (t : Nat),
    impl.croniter.cronMatches s t =
      (s.minutes.contains (minOf t) && s.hours.contains (hourOf t) && s.dows.contains (dowOf t))

/-- Membership characterisation (biconditional): the schedule fires at `t`
    iff every field of `t` is allowed, stated as membership rather than
    `contains`. This is the merge of the forward conjunction direction and
    its converse into a single `↔`, pinning the matcher exactly against an
    impl that ignores a field or fires on a disallowed one — strictly
    stronger than either one-directional implication alone. -/
def spec_cronMatches_fields (impl : RepoImpl) : Prop :=
  ∀ (s : CronSpec) (t : Nat),
    impl.croniter.cronMatches s t = true ↔
      (minOf t ∈ s.minutes ∧ hourOf t ∈ s.hours ∧ dowOf t ∈ s.dows)

/-- A `*` (full-range) minutes field never blocks a match: when `s.minutes`
    contains every minute `0..59`, whether `s` fires at `t` depends only on
    the hours and days-of-week fields. This is the `* * * *`-style wildcard
    behaviour a scheduler relies on — a saturated field drops out of the
    firing decision entirely. -/
def spec_cronMatches_full_minutes (impl : RepoImpl) : Prop :=
  ∀ (s : CronSpec) (t : Nat),
    (∀ m, m < 60 → m ∈ s.minutes) →
      impl.croniter.cronMatches s t =
        (s.hours.contains (hourOf t) && s.dows.contains (dowOf t))

/-- The all-wildcards schedule `* * * *` fires at every minute: when all three
    fields are full-range, `cronMatches` is constantly `true`. This is the
    degenerate "always on" schedule, and the property pins the implementation to
    accept every calendar time once nothing is being filtered out. -/
def spec_cronMatches_full_all (impl : RepoImpl) : Prop :=
  ∀ (s : CronSpec) (t : Nat),
    (∀ m, m < 60 → m ∈ s.minutes) →
    (∀ h, h < 24 → h ∈ s.hours) →
    (∀ d, d < 7 → d ∈ s.dows) →
      impl.croniter.cronMatches s t = true

-- ── nextFire: witness ∧ minimality ─────────────────────────────

/-- For a well-formed spec, the next fire time is a genuine firing time and is
    strictly later than the current time. This is the basic correctness
    contract of `nextFire`: a scheduler that returns a time which does not
    actually fire, or one that fails to move forward, is broken. -/
def spec_nextFire_matches (impl : RepoImpl) : Prop :=
  ∀ (s : CronSpec) (t : Nat),
    wellFormed s →
      impl.croniter.cronMatches s (impl.croniter.nextFire s t) = true ∧
      impl.croniter.nextFire s t > t

/-- Nothing strictly between the current time and the returned next fire time
    is a firing time: `nextFire` never skips an earlier match. A scheduler that
    jumped past a closer firing would silently drop a scheduled run, so this
    rules out any impl that overshoots the genuinely next occurrence. -/
def spec_nextFire_minimal (impl : RepoImpl) : Prop :=
  ∀ (s : CronSpec) (t u : Nat),
    t < u → u < impl.croniter.nextFire s t →
      impl.croniter.cronMatches s u = false

/-- `nextFire` is always strictly after the current time, with no
    well-formedness hypothesis. -/
def spec_nextFire_gt (impl : RepoImpl) : Prop :=
  ∀ (s : CronSpec) (t : Nat),
    impl.croniter.nextFire s t > t

/-- `nextFire` lands on a genuine firing time (standalone restatement of the
    witness's match component, isolating it from the strict-ordering part). -/
def spec_nextFire_self_matches (impl : RepoImpl) : Prop :=
  ∀ (s : CronSpec) (t : Nat),
    wellFormed s →
      impl.croniter.cronMatches s (impl.croniter.nextFire s t) = true

/-- Idempotent step: iterating `nextFire` strictly advances — the next fire
    after `nextFire s t` is itself strictly greater. Distinguishes a genuine
    forward step from a fixed-point/identity impl. -/
def spec_nextFire_step (impl : RepoImpl) : Prop :=
  ∀ (s : CronSpec) (t : Nat),
    impl.croniter.nextFire s (impl.croniter.nextFire s t) > impl.croniter.nextFire s t

/-- Boundedness: for a well-formed spec the gap to the next fire is at most
    one week — a useful liveness guarantee for any consumer of the API, and one
    a scheduler that could stall past a week-long window would violate. -/
def spec_nextFire_bounded (impl : RepoImpl) : Prop :=
  ∀ (s : CronSpec) (t : Nat),
    wellFormed s →
      impl.croniter.nextFire s t ≤ t + weekMinutes

/-- Monotonicity: for a well-formed spec, the next fire time is monotone in the
    query time. Since the set of firing times strictly after `t` shrinks as `t`
    grows, its minimum (which `nextFire` computes) can only increase. -/
def spec_nextFire_monotone (impl : RepoImpl) : Prop :=
  ∀ (s : CronSpec) (t₁ t₂ : Nat),
    wellFormed s → t₁ ≤ t₂ →
      impl.croniter.nextFire s t₁ ≤ impl.croniter.nextFire s t₂

-- ── prevFire: witness ∧ maximality ─────────────────────────────

/-- For a well-formed spec at a time at least one week past the epoch, the
    previous fire time is a genuine firing time and is strictly earlier than
    the current time. This is the basic correctness contract of `prevFire`,
    the backward counterpart of `nextFire`. The `weekMinutes ≤ t` guard simply
    ensures a full week of history lies below `t`, so a weekly schedule has
    definitely fired at least once before `t`. -/
def spec_prevFire_matches (impl : RepoImpl) : Prop :=
  ∀ (s : CronSpec) (t : Nat),
    wellFormed s → weekMinutes ≤ t →
      impl.croniter.cronMatches s (impl.croniter.prevFire s t) = true ∧
      impl.croniter.prevFire s t < t

/-- Nothing strictly between the returned previous fire time and the current
    time is a firing time: `prevFire` never reports a stale match when a more
    recent one exists. A scheduler that returned an older firing while skipping
    a closer one would misreport when the schedule last ran, so this rules out
    any such impl. -/
def spec_prevFire_maximal (impl : RepoImpl) : Prop :=
  ∀ (s : CronSpec) (t u : Nat),
    impl.croniter.prevFire s t < u → u < t →
      impl.croniter.cronMatches s u = false

/-- `prevFire` is strictly before the current time (standalone restatement of
    the witness's ordering component, under the same one-week guard). -/
def spec_prevFire_lt (impl : RepoImpl) : Prop :=
  ∀ (s : CronSpec) (t : Nat),
    wellFormed s → weekMinutes ≤ t →
      impl.croniter.prevFire s t < t

/-- `prevFire` lands on a genuine firing time (standalone restatement of the
    witness's match component). -/
def spec_prevFire_self_matches (impl : RepoImpl) : Prop :=
  ∀ (s : CronSpec) (t : Nat),
    wellFormed s → weekMinutes ≤ t →
      impl.croniter.cronMatches s (impl.croniter.prevFire s t) = true

/-- Boundedness (tight): the previous fire is no more than EXACTLY one week
    back — `t ≤ prevFire s t + weekMinutes`, with no slack. Because a cron
    schedule repeats weekly, a non-empty schedule fires at least once in the
    week `[t - weekMinutes, t)`, so its most recent firing is never more than a
    full week behind. The bound is attained (a once-per-week schedule queried
    just past a fire has its previous fire exactly a week back), so the
    constant cannot be lowered. -/
def spec_prevFire_bounded (impl : RepoImpl) : Prop :=
  ∀ (s : CronSpec) (t : Nat),
    wellFormed s → weekMinutes ≤ t →
      t ≤ impl.croniter.prevFire s t + weekMinutes

-- ── cross-API: nextFire / prevFire consistency ─────────────────

/-- No genuine firing time lies strictly between the previous and next fire
    around `t` other than `t` itself: on the open interval
    `(prevFire s t, nextFire s t)` the only possible match is `t`. This pins
    `prevFire` and `nextFire` as the immediately adjacent fires around `t`, with
    no firing minute hiding between them. -/
def spec_no_match_between (impl : RepoImpl) : Prop :=
  ∀ (s : CronSpec) (t u : Nat),
    impl.croniter.prevFire s t < u → u < impl.croniter.nextFire s t → u ≠ t →
      impl.croniter.cronMatches s u = false

/-- Inverse round-trip: stepping forward then back returns to a time no later
    than `t`, and `t` sits strictly below the forward step
    (`prevFire (nextFire t) ≤ t < nextFire t`). This says `prevFire` undoes a
    `nextFire` step without overshooting `t` — the consistency a scheduler needs
    when it pages back and forth through a schedule. The `weekMinutes ≤ t` guard
    just ensures a full week of history lies below the forward step. -/
def spec_prevFire_nextFire_roundtrip (impl : RepoImpl) : Prop :=
  ∀ (s : CronSpec) (t : Nat),
    wellFormed s → weekMinutes ≤ t →
      impl.croniter.prevFire s (impl.croniter.nextFire s t) ≤ t ∧
      t < impl.croniter.nextFire s t

-- ── periodicity ────────────────────────────────────────────────

/-- Periodicity: the schedule repeats every full week, for an ARBITRARY number
    of weeks `k`. A cron schedule's minute/hour/day-of-week fields all line up
    again after exactly one week, so the matcher takes the same value at `t` and
    at `t + k · weekMinutes`. This weekly repetition is the defining behaviour of
    cron and is what lets a scheduler reason about an unbounded future from a
    single week's pattern. -/
def spec_cronMatches_periodic (impl : RepoImpl) : Prop :=
  ∀ (s : CronSpec) (t k : Nat),
    impl.croniter.cronMatches s (t + k * weekMinutes) = impl.croniter.cronMatches s t

/-- Shift-equivariance: advancing the query time by one full week shifts the
    next fire time by exactly one full week. Because the schedule repeats weekly,
    the next firing after `t + weekMinutes` is precisely the next firing after
    `t` translated forward by one week. This is what makes "the same schedule
    one week later" mean exactly that for a scheduler. -/
def spec_nextFire_shift (impl : RepoImpl) : Prop :=
  ∀ (s : CronSpec) (t : Nat),
    wellFormed s →
      impl.croniter.nextFire s (t + weekMinutes) = impl.croniter.nextFire s t + weekMinutes

-- ── nthFire: iterating nextFire enumerates the match set ───────

/-- Each iterate of `nextFire` is a genuine firing time: applying `nextFire`
    `n + 1` times from `t` lands on a match. The `n + 1` (rather than `n`)
    guarantees at least one step has been taken so the result genuinely fires
    (the `0`-th iterate is just `t`, which need not match). -/
def spec_nthFire_matches (impl : RepoImpl) : Prop :=
  ∀ (s : CronSpec) (t n : Nat),
    wellFormed s →
      impl.croniter.cronMatches s (iterStep (impl.croniter.nextFire s) t (n + 1)) = true

/-- The iterates of `nextFire` are strictly increasing: the `n + 1`-th firing
    time after `t` is strictly later than the `n`-th. Together with
    `spec_nthFire_no_gap` this is the monotone-enumeration property — iterating
    `nextFire` walks the match set strictly forward with no repeats. -/
def spec_nthFire_monotone (impl : RepoImpl) : Prop :=
  ∀ (s : CronSpec) (t n : Nat),
    iterStep (impl.croniter.nextFire s) t n < iterStep (impl.croniter.nextFire s) t (n + 1)

/-- No gaps: between two consecutive iterates of `nextFire` there is no other
    firing time. Combined with `spec_nthFire_matches` and
    `spec_nthFire_monotone`, this states that iterating `nextFire` enumerates
    the entire match set in strictly increasing order with no match skipped —
    the headline enumeration property. -/
def spec_nthFire_no_gap (impl : RepoImpl) : Prop :=
  ∀ (s : CronSpec) (t n u : Nat),
    iterStep (impl.croniter.nextFire s) t n < u →
    u < iterStep (impl.croniter.nextFire s) t (n + 1) →
      impl.croniter.cronMatches s u = false

-- ── skip-count: jump size equals the non-matching block ────────

/-- The jump `nextFire` takes equals the size of the non-matching block it
    skips: starting one minute past `t`, the next fire time is reached after
    skipping exactly the `countNoMatch` non-matching minutes that precede it,
    so `nextFire s t = (t + 1) + countNoMatch s (t + 1) weekMinutes`. This
    relates the size of the forward jump to the run of consecutive non-firing
    minutes between consecutive fires — the "how long until the next run" that a
    scheduler reports. -/
def spec_nextFire_skip_count (impl : RepoImpl) : Prop :=
  ∀ (s : CronSpec) (t : Nat),
    wellFormed s →
      impl.croniter.nextFire s t = (t + 1) + countNoMatch s (t + 1) weekMinutes

-- ── window cardinality: matches per week = product of field counts ─────

/-- Window cardinality (centerpiece): the number of matching minutes in any
    one-week window `[t, t + weekMinutes)` equals the product of the three
    field cardinalities `|dows| · |hours| · |minutes|`. For a `wellFormed`
    (in-range) and `noDupFields` (de-duplicated) spec, a schedule like
    "every 15 minutes on weekdays" fires a precisely predictable number of
    times per week. This pins down the exact firing density — a scheduler that
    double-counts, drops, or mis-multiplies the fields would get a different
    total. -/
def spec_countMatch_window_card (impl : RepoImpl) : Prop :=
  ∀ (s : CronSpec) (t : Nat),
    wellFormed s → noDupFields s →
      countMatch (impl.croniter.cronMatches s) t weekMinutes =
        s.dows.length * (s.hours.length * s.minutes.length)

/-- Monotone count under field refinement: enlarging every field can only add
    matches, so the per-week matching count of the sparser spec `A` never
    exceeds that of the denser spec `B`. Broadening a schedule (allowing more
    minutes, hours, or days) only ever increases how often it fires — it can
    never make the schedule fire less. -/
def spec_countMatch_subset_mono (impl : RepoImpl) : Prop :=
  ∀ (A B : CronSpec) (t : Nat),
    A.minutes ⊆ B.minutes → A.hours ⊆ B.hours → A.dows ⊆ B.dows →
      countMatch (impl.croniter.cronMatches A) t weekMinutes
        ≤ countMatch (impl.croniter.cronMatches B) t weekMinutes

-- ── nthFire shift-equivariance and telescoping ─────────────────────────

/-- Shift-equivariance of the enumeration: advancing the start by one full
    week shifts every iterate of `nextFire` by exactly one week. The entire
    firing sequence after `t + weekMinutes` is just the sequence after `t`
    translated forward by one period, for every iterate `n`. This is the
    sequence-level form of weekly repetition: the whole future firing schedule
    looks identical from one week to the next. -/
def spec_nthFire_shift (impl : RepoImpl) : Prop :=
  ∀ (s : CronSpec) (t n : Nat),
    wellFormed s →
      iterStep (impl.croniter.nextFire s) (t + weekMinutes) n =
        iterStep (impl.croniter.nextFire s) t n + weekMinutes

/-- Total span equals the sum of the gaps: adding up the inter-fire gaps
    between the first `n` consecutive fires after `t` gives the total distance
    from `t` to the `n`-th fire. This is the accounting identity a scheduler
    relies on when summing wait times — the individual gaps between fires must
    add up to the overall elapsed span, with nothing lost or double-counted. -/
def spec_nthFire_telescope (impl : RepoImpl) : Prop :=
  ∀ (s : CronSpec) (t n : Nat),
    sumGaps (impl.croniter.nextFire s) t n =
      iterStep (impl.croniter.nextFire s) t n - t

-- ── field-refinement (density) cross-spec laws ─────────────────────────

/-- Membership monotonicity under field containment: if every field of `A` is
    contained in the corresponding field of `B`, then every `A`-match is a
    `B`-match. The refinement direction of the matcher — a denser schedule
    fires at least as often. -/
def spec_cronMatches_subset_mono (impl : RepoImpl) : Prop :=
  ∀ (A B : CronSpec) (t : Nat),
    A.minutes ⊆ B.minutes → A.hours ⊆ B.hours → A.dows ⊆ B.dows →
      impl.croniter.cronMatches A t = true →
        impl.croniter.cronMatches B t = true

/-- Density monotonicity of `nextFire`: refining the schedule (enlarging every
    field) can only move the next fire earlier-or-equal, so the denser spec `B`
    fires no later than the sparser spec `A`. Adding more allowed times to a
    schedule can only bring the next firing closer, never push it further out —
    a comparison guarantee between two related schedules. -/
def spec_nextFire_subset_le (impl : RepoImpl) : Prop :=
  ∀ (A B : CronSpec) (t : Nat),
    wellFormed A →
      A.minutes ⊆ B.minutes → A.hours ⊆ B.hours → A.dows ⊆ B.dows →
        impl.croniter.nextFire B t ≤ impl.croniter.nextFire A t

-- ── counting laws relating iteration to per-window match count ─────────
--
-- These four specs state clean end-facts about how many firings lie in a
-- window. Each is stated only through the frozen window counter `countMatch`
-- and the frozen iterator `iterStep` applied to `impl.croniter.{cronMatches,
-- nextFire}`.

/-- No firing lies strictly before the first one: the number of matches in the
    open window `(t, nextFire s t)` is zero. This is the "next fire is genuinely
    next" guarantee phrased as a count — there are exactly zero scheduled runs in
    the gap between now and the next fire, so a scheduler that reported any
    intervening firing would be wrong. -/
def spec_nextFire_gap_count_zero (impl : RepoImpl) : Prop :=
  ∀ (s : CronSpec) (t : Nat),
    wellFormed s →
      countMatch (impl.croniter.cronMatches s) (t + 1)
        (impl.croniter.nextFire s t - (t + 1)) = 0

/-- Exactly one firing per inter-fire step: the number of matches in the
    half-open window `(iterStep k, iterStep (k + 1)]` — between two consecutive
    iterates of `nextFire` and including the upper one — is exactly `1`. Each
    `nextFire` step lands on exactly one new firing and skips no others, so
    stepping the iterator once advances past precisely one scheduled run. This
    is what makes the iterate count a faithful tally of fires. -/
def spec_nthFire_step_count_one (impl : RepoImpl) : Prop :=
  ∀ (s : CronSpec) (t k : Nat),
    wellFormed s →
      countMatch (impl.croniter.cronMatches s)
        (iterStep (impl.croniter.nextFire s) t k + 1)
        (iterStep (impl.croniter.nextFire s) t (k + 1)
          - iterStep (impl.croniter.nextFire s) t k) = 1

/-- The `k`-th fire counts `k` firings: the number of matches in the half-open
    window `(t, iterStep k]` from `t` up to and including the `k`-th iterate of
    `nextFire` is exactly `k`. This is the headline enumeration-counting law —
    iterating `nextFire` `k` times steps past exactly `k` firings, no more and no
    fewer. It ties the iteration depth to the firing count, the guarantee that
    "advance the schedule `k` times" really does land on the `k`-th run. -/
def spec_nextFire_kth_count (impl : RepoImpl) : Prop :=
  ∀ (s : CronSpec) (t k : Nat),
    wellFormed s →
      countMatch (impl.croniter.cronMatches s) (t + 1)
        (iterStep (impl.croniter.nextFire s) t k - t) = k

-- ── periodicity composed over many weeks ───────────────────────────────

/-- Multi-week shift-equivariance: advancing the query time by `k` full weeks
    shifts the next fire time by exactly `k` weeks, for every `k` — the clean
    end-fact `nextFire (t + k·week) = nextFire t + k·week`. Because a cron
    schedule repeats every week, looking `k` weeks ahead reproduces the same
    firing pattern shifted by `k` weeks, so a scheduler can project far into the
    future without re-scanning each period. -/
def spec_nextFire_kweek_shift (impl : RepoImpl) : Prop :=
  ∀ (s : CronSpec) (t k : Nat),
    wellFormed s →
      impl.croniter.nextFire s (t + k * weekMinutes)
        = impl.croniter.nextFire s t + k * weekMinutes

-- ── prevFire counting / monotonicity (backward mirrors) ──────────────────

/-- Backward gap-count-zero: the number of firings strictly between the previous
    fire and the current time is zero — `countMatch` over the open window
    `(prevFire s t, t)` evaluates to `0`. The downward counterpart of
    `spec_nextFire_gap_count_zero`: there are exactly zero scheduled runs between
    the most recent fire and now, so `prevFire` really does report the latest
    firing with nothing newer in between. -/
def spec_prevFire_gap_count_zero (impl : RepoImpl) : Prop :=
  ∀ (s : CronSpec) (t : Nat),
    wellFormed s → weekMinutes ≤ t →
      countMatch (impl.croniter.cronMatches s) (impl.croniter.prevFire s t + 1)
        (t - (impl.croniter.prevFire s t + 1)) = 0

/-- Monotonicity of `prevFire` in the query time, across arbitrary gaps: as the
    query time grows the previous fire can only move later-or-equal. The
    backward counterpart of `spec_nextFire_monotone`. As "now" advances, the
    most recent firing reported can only stay the same or become more recent —
    it never jumps backward — so a scheduler's notion of "last run" is monotone
    in the current time. -/
def spec_prevFire_monotone (impl : RepoImpl) : Prop :=
  ∀ (s : CronSpec) (t₁ t₂ : Nat),
    wellFormed s → weekMinutes ≤ t₁ → t₁ ≤ t₂ →
      impl.croniter.prevFire s t₁ ≤ impl.croniter.prevFire s t₂

-- ── nextFire / prevFire adjacency: each is the other's inverse on matches ──

/-- Step-back-after-step-forward on a firing minute is the identity: if `t`
    itself fires, then the previous fire before the next fire after `t` is `t`
    (`prevFire (nextFire t) = t`). On a genuine firing minute, advancing then
    stepping back returns exactly where you started — the consistency a scheduler
    needs so that paging one step forward and one step back is a no-op. -/
def spec_prevFire_nextFire_eq (impl : RepoImpl) : Prop :=
  ∀ (s : CronSpec) (t : Nat),
    wellFormed s → impl.croniter.cronMatches s t = true →
      impl.croniter.prevFire s (impl.croniter.nextFire s t) = t

/-- Step-forward-after-step-back on a firing minute is the identity: if `t`
    itself fires, then the next fire after the previous fire before `t` is `t`
    (`nextFire (prevFire t) = t`). The dual of `spec_prevFire_nextFire_eq`:
    stepping back then forward from a genuine firing minute returns exactly to
    it. The `weekMinutes ≤ t` guard just ensures a full week of history lies
    below `t` so `prevFire` lands on a genuine earlier firing. -/
def spec_nextFire_prevFire_eq (impl : RepoImpl) : Prop :=
  ∀ (s : CronSpec) (t : Nat),
    wellFormed s → weekMinutes ≤ t → impl.croniter.cronMatches s t = true →
      impl.croniter.nextFire s (impl.croniter.prevFire s t) = t

/-- Next-fire collapses the previous fire: the next fire after the previous fire
    before `t` equals the next fire after `t - 1`
    (`nextFire (prevFire t) = nextFire (t - 1)`). Both sides denote the first
    firing at or after `t`: stepping back to the most recent fire and then asking
    for the following one lands in the same place as scanning forward from just
    before `t`. This consistency lets a scheduler re-anchor on the last firing
    without changing which run comes next. -/
def spec_nextFire_prevFire_pred (impl : RepoImpl) : Prop :=
  ∀ (s : CronSpec) (t : Nat),
    wellFormed s → weekMinutes ≤ t →
      impl.croniter.nextFire s (impl.croniter.prevFire s t) =
        impl.croniter.nextFire s (t - 1)

-- ── multi-period density: count over k weeks = k · per-week count ──

/-- Multi-week density: the number of firings in any `k`-week window equals `k`
    times the number of firings in one week. `countMatch` over `[t, t + k·week)`
    is `k ·` the per-week count, for every `k` and every starting `t`. This lets
    a scheduler estimate the load over any horizon by multiplying the single-week
    count, with no surprises across period boundaries — and rejects an impl whose
    multi-week tally drifts from `k ·` the weekly one. -/
def spec_countMatch_kweek (impl : RepoImpl) : Prop :=
  ∀ (s : CronSpec) (t k : Nat),
    countMatch (impl.croniter.cronMatches s) t (k * weekMinutes) =
      k * countMatch (impl.croniter.cronMatches s) t weekMinutes

-- ── one period of fires spans exactly one week ──

/-- One period of firings spans exactly one week: starting from a firing minute
    `m`, iterating `nextFire` as many times as there are firings in the next week
    `(m, m + week]` lands exactly one week later, on `m + week`. The iteration
    depth is supplied as the frozen window count `countMatch (cronMatches s)
    (m + 1) week`. In other words, stepping through all of the fires in one week
    advances the schedule by precisely one period — the closure property that
    makes a week a genuine repeating cycle of the firing pattern. -/
def spec_nextFire_period_iterate (impl : RepoImpl) : Prop :=
  ∀ (s : CronSpec) (m : Nat),
    wellFormed s → impl.croniter.cronMatches s m = true →
      iterStep (impl.croniter.nextFire s) m
        (countMatch (impl.croniter.cronMatches s) (m + 1) weekMinutes) = m + weekMinutes

/-- Frozen finite sum: `sumNat f n = f 0 + f 1 + … + f (n-1)`. References no
    implementation. -/
def sumNat (f : Nat → Nat) : Nat → Nat
  | 0 => 0
  | n + 1 => sumNat f n + f n

/-- Frozen calendar-cell counter: within the window `[lo, lo + fuel)`, the number
    of minutes at which the predicate `p` holds AND whose calendar fields are
    exactly `(d, h, m)`. The specs instantiate `p` with `impl.croniter.cronMatches
    s`, so this counts the firings landing in one specific `(day, hour, minute)`
    slot. References only the frozen extractors. -/
def countCalendarCell (p : Nat → Bool) (d h m lo fuel : Nat) : Nat :=
  countMatch
    (fun u =>
      p u &&
      decide (dowOf u = d) &&
      decide (hourOf u = h) &&
      decide (minOf u = m))
    lo fuel

/-- Frozen per-slot re-tally: the sum, over every calendar slot `(d < 7, h < 24,
    m < 60)`, of the per-slot count `countCalendarCell`. References no
    implementation beyond the supplied predicate `p`. -/
def countCalendarCells (p : Nat → Bool) (lo fuel : Nat) : Nat :=
  sumNat
    (fun d =>
      sumNat
        (fun h =>
          sumNat
            (fun m => countCalendarCell p d h m lo fuel)
            60)
        24)
    7

/-- Frozen match enumerator: the list, in increasing time order, of the minutes
    in `[lo, lo + fuel)` at which `p` holds. The specs instantiate `p` with
    `impl.croniter.cronMatches s`, so this is the ordered list of firing minutes
    in the window. References no implementation beyond `p`. -/
def matchList (p : Nat → Bool) (lo : Nat) : Nat → List Nat
  | 0 => []
  | fuel + 1 =>
      if p lo then lo :: matchList p (lo + 1) fuel
      else matchList p (lo + 1) fuel

/-- Frozen iterate enumerator: the list of the first `n` iterates of a step
    function `f` starting from `t` (excluding `t` itself). The specs apply it to
    `impl.croniter.{nextFire, prevFire} s`, giving the successive fires. -/
def iterList (f : Nat → Nat) (t : Nat) : Nat → List Nat
  | 0 => []
  | n + 1 =>
      let u := f t
      u :: iterList f u n

/-- Frozen field canonicaliser: the in-range values of `bound` that appear in
    `xs`, de-duplicated and sorted (it is `List.range bound` filtered by
    membership in `xs`). References no implementation. -/
def fieldCanon (xs : List Nat) (bound : Nat) : List Nat :=
  (List.range bound).filter (fun v => xs.contains v)

/-- Frozen spec normaliser: canonicalise each field of a `CronSpec` (drop
    out-of-range and duplicate entries) via `fieldCanon`. -/
def normalizeSpec (s : CronSpec) : CronSpec :=
  { minutes := fieldCanon s.minutes 60
    hours := fieldCanon s.hours 24
    dows := fieldCanon s.dows 7 }

/-- The observable API frame at time `t`: the triple of `(cronMatches, nextFire,
    prevFire)` outputs — the complete state a consumer of the scheduler can see. -/
def apiFrame (impl : RepoImpl) (s : CronSpec) (t : Nat) : Bool × Nat × Nat :=
  (impl.croniter.cronMatches s t, impl.croniter.nextFire s t, impl.croniter.prevFire s t)

/-- Per-week firing count split across calendar cells: the number of firings in
    a one-week window equals the same total re-tallied cell-by-cell over every
    `(day-of-week, hour, minute)` slot. Counting the week's runs directly agrees
    with bucketing each run into its calendar slot and summing the buckets — a
    scheduler's per-week total is the sum of its per-slot totals, with nothing
    lost or double-counted across the 7·24·60 slots. -/
def spec_countMatch_calendar_partition (impl : RepoImpl) : Prop :=
  ∀ (s : CronSpec) (t : Nat),
    countMatch (impl.croniter.cronMatches s) t weekMinutes =
      countCalendarCells (impl.croniter.cronMatches s) t weekMinutes

/-- The next fire is the first entry of the week's firing list: listing the
    firing minutes of the coming week `[t+1, t+1+week)` in time order, the very
    first one is exactly `nextFire s t`. The head of the enumerated schedule for
    the next week is the next run — what a scheduler reports as "up next". -/
def spec_nextFire_head_week_list (impl : RepoImpl) : Prop :=
  ∀ (s : CronSpec) (t : Nat),
    wellFormed s →
      (matchList (impl.croniter.cronMatches s) (t + 1) weekMinutes).head? =
        some (impl.croniter.nextFire s t)

/-- Positional agreement between the week's firing list and iterated `nextFire`:
    the `k`-th entry (0-indexed) of the coming week's firing list is exactly the
    `(k+1)`-th fire reached by iterating `nextFire` from `t`. Reading the schedule
    off by position and stepping the scheduler forward that many times land on the
    same run, as long as position `k` lies within the week's firings. -/
def spec_nextFire_get_week_list (impl : RepoImpl) : Prop :=
  ∀ (s : CronSpec) (t k : Nat),
    wellFormed s →
    k < countMatch (impl.croniter.cronMatches s) (t + 1) weekMinutes →
      (matchList (impl.croniter.cronMatches s) (t + 1) weekMinutes)[k]? =
        some (iterStep (impl.croniter.nextFire s) t (k + 1))

/-- The iterated-`nextFire` sequence IS the week's firing list: iterating
    `nextFire` from `t` as many times as there are firings in the coming week
    produces exactly the time-ordered list of those firing minutes. Walking the
    schedule forward run-by-run reconstructs precisely the enumerated firing list
    of the week — the two ways of listing the next week's runs coincide as lists,
    not merely as sets. -/
def spec_nextFire_week_list_eq (impl : RepoImpl) : Prop :=
  ∀ (s : CronSpec) (t : Nat),
    wellFormed s →
      iterList (impl.croniter.nextFire s) t
        (countMatch (impl.croniter.cronMatches s) (t + 1) weekMinutes) =
        matchList (impl.croniter.cronMatches s) (t + 1) weekMinutes

/-- Stepping `prevFire` backward enumerates the previous week's firings in
    reverse: iterating `prevFire` from `t` once per firing in the past week
    `[t-week, t)` yields those firing minutes newest-first, so reversing the
    result gives the same time-ordered firing list produced by scanning that
    window forward. Paging backward through the schedule visits exactly the
    prior week's runs, in the mirror order of listing them forward. -/
def spec_prevFire_reverse_week_list (impl : RepoImpl) : Prop :=
  ∀ (s : CronSpec) (t : Nat),
    wellFormed s → weekMinutes ≤ t →
      (iterList (impl.croniter.prevFire s) t
        (countMatch (impl.croniter.cronMatches s) (t - weekMinutes) weekMinutes)).reverse =
        matchList (impl.croniter.cronMatches s) (t - weekMinutes) weekMinutes

/-- Canonicalising a spec's fields leaves the entire scheduler behaviour
    unchanged: dropping out-of-range and duplicate field entries (`normalizeSpec`)
    changes neither whether the schedule fires, nor its next fire, nor its
    previous fire — the whole `(matches, nextFire, prevFire)` API frame is
    identical for the normalised and original spec. Cleaning up a schedule's
    field lists is a genuine no-op on everything a consumer can observe. -/
def spec_normalize_api_frame (impl : RepoImpl) : Prop :=
  ∀ (s : CronSpec) (t : Nat),
    apiFrame impl (normalizeSpec s) (t + weekMinutes) =
      apiFrame impl s (t + weekMinutes)

-- ── nextFire / prevFire: first-occurrence characterisation ──────────────

/-- First-occurrence characterisation of `nextFire`: any firing minute `u`
    strictly after `t` with no firing strictly between `t` and `u` is exactly
    `nextFire s t`. This is the converse of minimality — it pins `nextFire` as
    the unique first firing after `t`, so a scheduler that returned any other
    minute meeting this description would be wrong. -/
def spec_nextFire_first_hit_unique (impl : RepoImpl) : Prop :=
  ∀ (s : CronSpec) (t u : Nat),
    wellFormed s → t < u →
    impl.croniter.cronMatches s u = true →
    (∀ v, t < v → v < u → impl.croniter.cronMatches s v = false) →
      impl.croniter.nextFire s t = u

/-- Last-occurrence characterisation of `prevFire`: any firing minute `u`
    strictly before `t` with no firing strictly between `u` and `t` is exactly
    `prevFire s t`. The backward dual of `spec_nextFire_first_hit_unique`: it
    pins `prevFire` as the unique most-recent firing before `t`. The
    `weekMinutes ≤ t` guard ensures a full week of history lies below `t`. -/
def spec_prevFire_last_hit_unique (impl : RepoImpl) : Prop :=
  ∀ (s : CronSpec) (t u : Nat),
    wellFormed s → weekMinutes ≤ t → u < t →
    impl.croniter.cronMatches s u = true →
    (∀ v, u < v → v < t → impl.croniter.cronMatches s v = false) →
      impl.croniter.prevFire s t = u

-- ── nextFire / prevFire: gap-stability ──────────────────────────────────

/-- `nextFire` is constant across the whole gap that precedes it: for any query
    `q` with `t ≤ q < nextFire s t`, the next fire from `q` equals the next fire
    from `t`. Moving "now" forward without crossing a firing minute never changes
    what the scheduler reports as up next. -/
def spec_nextFire_stable_before_first_hit (impl : RepoImpl) : Prop :=
  ∀ (s : CronSpec) (t q : Nat),
    wellFormed s → t ≤ q → q < impl.croniter.nextFire s t →
      impl.croniter.nextFire s q = impl.croniter.nextFire s t

/-- `prevFire` is constant across the whole gap that follows it: for any query
    `q` with `prevFire s t < q ≤ t`, the previous fire from `q` equals the
    previous fire from `t`. The backward dual — the reported last run stays fixed
    until another firing minute actually occurs. -/
def spec_prevFire_stable_after_last_hit (impl : RepoImpl) : Prop :=
  ∀ (s : CronSpec) (t q : Nat),
    wellFormed s → weekMinutes ≤ t →
    impl.croniter.prevFire s t < q → q ≤ t →
      impl.croniter.prevFire s q = impl.croniter.prevFire s t

-- ── nextFire / prevFire: strict positional monotonicity ─────────────────

/-- Strict positional monotonicity of `nextFire`: if the query advances from
    `t₁` past a firing minute `u` (with `t₁ < u ≤ t₂`), the next fire advances
    strictly. Crossing a scheduled run forces the reported next fire to move to a
    strictly later one — a sharpening of plain monotonicity. -/
def spec_nextFire_strict_mono_crosses_match (impl : RepoImpl) : Prop :=
  ∀ (s : CronSpec) (t₁ t₂ u : Nat),
    wellFormed s → t₁ < u → u ≤ t₂ →
    impl.croniter.cronMatches s u = true →
      impl.croniter.nextFire s t₁ < impl.croniter.nextFire s t₂

/-- Strict positional monotonicity of `prevFire`: if the query advances from
    `t₁` across a firing minute `u` (with `t₁ ≤ u < t₂`), the previous fire
    advances strictly. The backward dual — crossing a scheduled run forces the
    reported last run to move to a strictly later one. -/
def spec_prevFire_strict_mono_crosses_match (impl : RepoImpl) : Prop :=
  ∀ (s : CronSpec) (t₁ t₂ u : Nat),
    wellFormed s → weekMinutes ≤ t₁ → t₁ ≤ u → u < t₂ →
    impl.croniter.cronMatches s u = true →
      impl.croniter.prevFire s t₁ < impl.croniter.prevFire s t₂

-- ── nextFire / prevFire: boundary fixed points ──────────────────────────

/-- Predecessor fixed point of `nextFire`: querying from the minute immediately
    before the next fire still lands on that same next fire —
    `nextFire s (nextFire s t - 1) = nextFire s t`. The reported next run is
    stable right up to the minute before it occurs. -/
def spec_nextFire_pred_fixpoint (impl : RepoImpl) : Prop :=
  ∀ (s : CronSpec) (t : Nat),
    wellFormed s →
      impl.croniter.nextFire s (impl.croniter.nextFire s t - 1) =
        impl.croniter.nextFire s t

/-- Successor fixed point of `prevFire`: querying from the minute immediately
    after the previous fire still reports that same previous fire —
    `prevFire s (prevFire s t + 1) = prevFire s t`. The backward dual — the
    reported last run is stable from the minute right after it occurs. -/
def spec_prevFire_succ_fixpoint (impl : RepoImpl) : Prop :=
  ∀ (s : CronSpec) (t : Nat),
    wellFormed s → weekMinutes ≤ t →
      impl.croniter.prevFire s (impl.croniter.prevFire s t + 1) =
        impl.croniter.prevFire s t
