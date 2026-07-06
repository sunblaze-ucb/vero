import ProlepticGregorian.Harness

/-!
# ProlepticGregorian.Spec.Ordinal

Specifications for the proleptic-Gregorian ordinal core. Each `spec_*`
is a property over an arbitrary `impl : RepoImpl`; the API is always
reached through `impl.prolepticGregorian.<fn>`, never by calling the
reference `ProlepticGregorian.<fn>` directly.

The specs characterize `ymd2ord` as an order-isomorphism from valid
dates onto an interval of the naturals — an absolute anchor, a `+1`
step to the immediately following calendar date, and strict
monotonicity — together with the inverse `ord2ymd`, the `weekday`
cycle, and `isLeap` / `daysInMonth` / `validDate`.

The frozen calendar vocabulary below (`daysInMonthFrozen`, `dateLt`,
`isImmediateSucc`, `leapCount`) is built only from Lean's frozen `+`,
`<`, `≤`, `=`, `%` and the fixed month-length table; it does not depend
on `impl`.

DO NOT MODIFY — this file is frozen.
-/

namespace ProlepticGregorian.Spec

/-- Frozen month length: days in month `m` of year `y`, defined purely
    from the frozen month table and the frozen leap rule. Independent of
    any `impl`; used only to phrase the calendar-adjacency predicate. -/
def daysInMonthFrozen (y m : Nat) : Nat :=
  if m = 2 then (if (y % 4 = 0 ∧ (y % 100 ≠ 0 ∨ y % 400 = 0)) then 29 else 28)
  else daysInMonthTable m

/-- Frozen lexicographic order on dates: earlier year, then earlier
    month, then earlier day. -/
def dateLt (d1 d2 : Date) : Prop :=
  d1.year < d2.year ∨
  (d1.year = d2.year ∧
    (d1.month < d2.month ∨ (d1.month = d2.month ∧ d1.day < d2.day)))

/-- Frozen calendar adjacency: `d2` is the date immediately after `d1`.
    Three disjoint cases — mid-month, month boundary, year boundary. -/
def isImmediateSucc (d1 d2 : Date) : Prop :=
  -- mid-month: same year and month, next day
  (d2.year = d1.year ∧ d2.month = d1.month ∧ d2.day = d1.day + 1) ∨
  -- month boundary: last day of month m (< 12), wrap to the 1st of m+1
  (d1.month < 12 ∧ d1.day = daysInMonthFrozen d1.year d1.month ∧
    d2.year = d1.year ∧ d2.month = d1.month + 1 ∧ d2.day = 1) ∨
  -- year boundary: 31 December, wrap to 1 January of the next year
  (d1.month = 12 ∧ d1.day = 31 ∧
    d2.year = d1.year + 1 ∧ d2.month = 1 ∧ d2.day = 1)

/-- Frozen leap-year counter: the number of leap years in the interval
    `[1, y]`, defined directly by recursion on the frozen divisibility rule.
    Independent of any `impl`; used only to phrase the leap-count spec. -/
def leapCount : Nat → Nat
  | 0 => 0
  | Nat.succ k =>
    (if ((k + 1) % 4 = 0 ∧ ((k + 1) % 100 ≠ 0 ∨ (k + 1) % 400 = 0)) then 1 else 0)
      + leapCount k

/-- Frozen enumeration of the leap years in `[1, y]`, as a filtered
    `List.range`. A count-over-enumeration view of the leap density,
    independent of any `impl`. -/
def frozenLeapYearsUpTo (y : Nat) : List Nat :=
  (List.range y).filter (fun k =>
    decide ((k + 1) % 4 = 0 ∧ ((k + 1) % 100 ≠ 0 ∨ (k + 1) % 400 = 0)))

/-- The ordinals of the days of month `m` in year `y`, listed by day. -/
def monthDayOrdinals (impl : RepoImpl) (y m : Nat) : List Nat :=
  (List.range (daysInMonthFrozen y m)).map
    (fun i => impl.prolepticGregorian.ymd2ord ⟨y, m, i + 1⟩)

/-- The seven weekday values of a window of seven consecutive ordinals
    starting at `n`. -/
def weekdayWindow (impl : RepoImpl) (n : Nat) : List Nat :=
  (List.range 7).map (fun i =>
    impl.prolepticGregorian.weekday (impl.prolepticGregorian.ord2ymd (n + i)))

/-- Frozen length of year `y`: `366` in a leap year, `365` otherwise. -/
def yearLengthFrozen (y : Nat) : Nat :=
  365 + (if (y % 4 = 0 ∧ (y % 100 ≠ 0 ∨ y % 400 = 0)) then 1 else 0)

/-- The ordinals of every calendar day of year `y`, month by month. -/
def wholeYearOrdinals (impl : RepoImpl) (y : Nat) : List Nat :=
  (List.range 12).flatMap (fun i => monthDayOrdinals impl y (i + 1))

/-- The weekday values over year `y`, scanned by ordinal from January 1st. -/
def yearWeekdayValues (impl : RepoImpl) (y : Nat) : List Nat :=
  (List.range (yearLengthFrozen y)).map (fun i =>
    impl.prolepticGregorian.weekday
      (impl.prolepticGregorian.ord2ymd
        (impl.prolepticGregorian.ymd2ord ⟨y, 1, 1⟩ + i)))

/-- The weekdays covered by the leftover days after the whole weeks of year `y`,
    starting at January 1st's weekday. -/
def yearSurplusWeekdays (impl : RepoImpl) (y : Nat) : List Nat :=
  (List.range (yearLengthFrozen y % 7)).map (fun i =>
    (impl.prolepticGregorian.weekday ⟨y, 1, 1⟩ + i) % 7)

/-- The weekday values over month `m` of year `y`, scanned by day. -/
def monthWeekdayValues (impl : RepoImpl) (y m : Nat) : List Nat :=
  (List.range (daysInMonthFrozen y m)).map (fun i =>
    impl.prolepticGregorian.weekday ⟨y, m, i + 1⟩)

/-- The zero-based within-month positions of weekday `w` in month `m` of year `y`. -/
def weekdayPositionsInMonth (impl : RepoImpl) (y m w : Nat) : List Nat :=
  (List.range (daysInMonthFrozen y m)).filter (fun i =>
    decide (impl.prolepticGregorian.weekday ⟨y, m, i + 1⟩ = w))

/-- The month components of year `y`, scanned by ordinal from January 1st. -/
def yearOrdinalMonths (impl : RepoImpl) (y : Nat) : List Nat :=
  (List.range (yearLengthFrozen y)).map (fun i =>
    (impl.prolepticGregorian.ord2ymd
      (impl.prolepticGregorian.ymd2ord ⟨y, 1, 1⟩ + i)).month)

/-- The decoded dates over the ordinal window `[lo, lo + len)`. -/
def ord2ymdWindow (impl : RepoImpl) (lo len : Nat) : List Date :=
  (List.range len).map (fun i => impl.prolepticGregorian.ord2ymd (lo + i))

/-- Frozen enumeration of the leap years in the half-open interval `[y, y + k)`,
    by the frozen divisibility rule. Independent of any `impl`. -/
def frozenLeapYearsInHalfOpen (y k : Nat) : List Nat :=
  (List.range k).filter (fun i =>
    decide (((y + i) % 4 = 0 ∧ ((y + i) % 100 ≠ 0 ∨ (y + i) % 400 = 0))))

/-- Frozen day-of-year index of a date: its position within its own year,
    from the frozen cumulative month table. -/
def dayOfYearFrozen (d : Date) : Nat :=
  daysBeforeMonth d.year d.month + d.day

end ProlepticGregorian.Spec

open ProlepticGregorian.Spec

-- ── isLeap / daysInMonth: frozen-op anchors ────────────────────

/-- `isLeap` is exactly the proleptic-Gregorian divisibility rule,
    pinned to Lean's frozen `%`. Both directions, so the predicate is
    unique. -/
def spec_leap_characterization (impl : RepoImpl) : Prop :=
  ∀ (y : Nat),
    impl.prolepticGregorian.isLeap y = true ↔
      (y % 4 = 0 ∧ (y % 100 ≠ 0 ∨ y % 400 = 0))

/-- February has 29 days in a leap year, 28 otherwise — tied to the
    impl's own `isLeap`. -/
def spec_days_in_month_feb (impl : RepoImpl) : Prop :=
  ∀ (y : Nat),
    impl.prolepticGregorian.daysInMonth y 2 =
      (if impl.prolepticGregorian.isLeap y then 29 else 28)

/-- Every non-February month agrees with the frozen table — for *all* `m ≠ 2`,
    including out-of-range months (where both sides are the table's `0`). The
    month-range bounds are dropped: `daysInMonth` is pinned to `daysInMonthTable`
    on the entire `m ≠ 2` domain. Pins the remaining 11 month lengths and the
    out-of-band behaviour in one shot. -/
def spec_days_in_month_table (impl : RepoImpl) : Prop :=
  ∀ (y m : Nat), m ≠ 2 →
    impl.prolepticGregorian.daysInMonth y m = daysInMonthTable m

/-- Concrete leap-rule grounding: pins three well-known years (2000 is a
    leap year, 1900 is not, 2004 is). A minority concrete spec that ties
    the abstract divisibility rule to the calendar everyone knows and
    rules out a flipped century-exception. -/
def spec_leap_known (impl : RepoImpl) : Prop :=
  impl.prolepticGregorian.isLeap 2000 = true ∧
  impl.prolepticGregorian.isLeap 1900 = false ∧
  impl.prolepticGregorian.isLeap 2004 = true

/-- The 400-year leap cycle: leap-ness is invariant under shifting the
    year by `400`. A strong structural law of the proleptic-Gregorian
    rule — any impl that gets the century/quad-century exceptions wrong
    breaks it. -/
def spec_leap_period (impl : RepoImpl) : Prop :=
  ∀ (y : Nat),
    impl.prolepticGregorian.isLeap (y + 400) = impl.prolepticGregorian.isLeap y

/-- Month lengths are always in `28..31` for the twelve real months.
    Pins the coarse range without restating the table; rejects any impl
    returning `0` or an out-of-band length for a valid month. -/
def spec_days_in_month_bounds (impl : RepoImpl) : Prop :=
  ∀ (y m : Nat), 1 ≤ m → m ≤ 12 →
    28 ≤ impl.prolepticGregorian.daysInMonth y m ∧
    impl.prolepticGregorian.daysInMonth y m ≤ 31

/-- The seven 31-day months (Jan, Mar, May, Jul, Aug, Oct, Dec) each have
    exactly 31 days, regardless of year. -/
def spec_days_in_month_31 (impl : RepoImpl) : Prop :=
  ∀ (y m : Nat),
    (m = 1 ∨ m = 3 ∨ m = 5 ∨ m = 7 ∨ m = 8 ∨ m = 10 ∨ m = 12) →
    impl.prolepticGregorian.daysInMonth y m = 31

/-- The four 30-day months (Apr, Jun, Sep, Nov) each have exactly 30
    days, regardless of year. -/
def spec_days_in_month_30 (impl : RepoImpl) : Prop :=
  ∀ (y m : Nat),
    (m = 4 ∨ m = 6 ∨ m = 9 ∨ m = 11) →
    impl.prolepticGregorian.daysInMonth y m = 30

-- ── ymd2ord: anchored order-isomorphism ────────────────────────

/-- Absolute anchor: the epoch `0001-01-01` is ordinal `1`. -/
def spec_ord_anchor (impl : RepoImpl) : Prop :=
  impl.prolepticGregorian.ymd2ord ⟨1, 1, 1⟩ = 1

/-- Unit step: consecutive calendar dates map to consecutive ordinals —
    stepping to the immediately following calendar date increases the
    ordinal by exactly `1` across mid-month, month-boundary and
    year-boundary transitions alike. Requires only `1 ≤ d1.year` (so the
    year-boundary case stays above the epoch), not full validity. -/
def spec_ord_unit_step (impl : RepoImpl) : Prop :=
  ∀ (d1 d2 : Date),
    1 ≤ d1.year →
    isImmediateSucc d1 d2 →
      impl.prolepticGregorian.ymd2ord d2 = impl.prolepticGregorian.ymd2ord d1 + 1

/-- Strict monotonicity: the lexicographic calendar order is reflected
    as strict `<` on ordinals. Rules out any order-scrambling impl. -/
def spec_ord_strict_mono (impl : RepoImpl) : Prop :=
  ∀ (d1 d2 : Date),
    impl.prolepticGregorian.validDate d1 = true →
    impl.prolepticGregorian.validDate d2 = true →
    dateLt d1 d2 →
      impl.prolepticGregorian.ymd2ord d1 < impl.prolepticGregorian.ymd2ord d2

/-- Ordinals are positive whenever the day component is (the epoch is `1`,
    nothing is earlier). Lower-bound counterpart to the anchor; requires
    only `1 ≤ d.day`. -/
def spec_ord_ge_one (impl : RepoImpl) : Prop :=
  ∀ (d : Date),
    1 ≤ d.day →
    1 ≤ impl.prolepticGregorian.ymd2ord d

/-- Defining offset: January 1st of year `y` sits one past the running
    day count `daysBeforeYear y`. Ties the ordinal's per-year phase to
    the frozen `daysBeforeYear` table. -/
def spec_ord_jan1 (impl : RepoImpl) : Prop :=
  ∀ (y : Nat),
    impl.prolepticGregorian.ymd2ord ⟨y, 1, 1⟩ = daysBeforeYear y + 1

/-- Consecutive New Year's days differ by the length of the intervening
    year: `366` if `y` is a leap year, else `365`. Forces the ordinal to
    advance by exactly one calendar year's worth of days. -/
def spec_ord_year_step (impl : RepoImpl) : Prop :=
  ∀ (y : Nat), 1 ≤ y →
    impl.prolepticGregorian.ymd2ord ⟨y + 1, 1, 1⟩ =
      impl.prolepticGregorian.ymd2ord ⟨y, 1, 1⟩ +
        (if impl.prolepticGregorian.isLeap y then 366 else 365)

/-- Within-month unit step: bumping the day component by one bumps the
    ordinal by one, for every `(y, m, d)` with no preconditions. -/
def spec_ord_day_step (impl : RepoImpl) : Prop :=
  ∀ (y m d : Nat),
    impl.prolepticGregorian.ymd2ord ⟨y, m, d + 1⟩ =
      impl.prolepticGregorian.ymd2ord ⟨y, m, d⟩ + 1

/-- Injectivity on valid dates: distinct calendar dates never collide on
    the ordinal. A strong global property — equal ordinals force equal
    dates, so `ymd2ord` assigns every valid date its own day number. Rules
    out any impl that maps two different calendar dates to the same
    ordinal. -/
def spec_ord_injective (impl : RepoImpl) : Prop :=
  ∀ (d1 d2 : Date),
    impl.prolepticGregorian.validDate d1 = true →
    impl.prolepticGregorian.validDate d2 = true →
    impl.prolepticGregorian.ymd2ord d1 = impl.prolepticGregorian.ymd2ord d2 →
    d1 = d2

-- ── weekday: derived step ──────────────────────────────────────

/-- The weekday advances by one (mod 7) across an immediate calendar
    successor: each new day is the next day of the week, wrapping Sunday
    back to Monday. Requires only `1 ≤ d1.year`, not full validity. -/
def spec_weekday_step (impl : RepoImpl) : Prop :=
  ∀ (d1 d2 : Date),
    1 ≤ d1.year →
    isImmediateSucc d1 d2 →
      impl.prolepticGregorian.weekday d2 =
        (impl.prolepticGregorian.weekday d1 + 1) % 7

/-- Absolute weekday phase anchor: the epoch `0001-01-01` is a Monday,
    `weekday = 0`. Pins the absolute phase of the weekday cycle. -/
def spec_weekday_anchor (impl : RepoImpl) : Prop :=
  impl.prolepticGregorian.weekday ⟨1, 1, 1⟩ = 0

/-- The weekday is always one of the seven days `0..6`. Range invariant
    of the `mod 7` convention; rejects any out-of-band weekday code. -/
def spec_weekday_range (impl : RepoImpl) : Prop :=
  ∀ (d : Date), impl.prolepticGregorian.weekday d < 7

/-- Year-boundary weekday shift: the weekday of next year's New Year is
    this year's New Year weekday advanced by the year length mod 7
    (`+1` for a common year, `+2` for a leap year). Pins how the weekday
    cycle threads across year boundaries. -/
def spec_weekday_year_step (impl : RepoImpl) : Prop :=
  ∀ (y : Nat), 1 ≤ y →
    impl.prolepticGregorian.weekday ⟨y + 1, 1, 1⟩ =
      (impl.prolepticGregorian.weekday ⟨y, 1, 1⟩ +
        (if impl.prolepticGregorian.isLeap y then 366 else 365)) % 7

/-- Concrete weekday grounding: `2000-01-01` was a Saturday, which is
    `5` under the Monday-`0` convention. A minority concrete spec that
    fixes the absolute weekday phase against a date everyone can check. -/
def spec_weekday_known (impl : RepoImpl) : Prop :=
  impl.prolepticGregorian.weekday ⟨2000, 1, 1⟩ = 5

-- ── validDate: characterization, rejection, leap Feb 29 ─────────

/-- `validDate` is exactly the conjunction of the calendar range
    conditions, with the day bound tied to the impl's own `daysInMonth`.
    Both directions, so the predicate is pinned uniquely. -/
def spec_valid_characterization (impl : RepoImpl) : Prop :=
  ∀ (d : Date),
    impl.prolepticGregorian.validDate d = true ↔
      (1 ≤ d.year ∧ 1 ≤ d.month ∧ d.month ≤ 12 ∧
        1 ≤ d.day ∧ d.day ≤ impl.prolepticGregorian.daysInMonth d.year d.month)

/-- Out-of-range months and the zero day are rejected: month `0`, *every*
    month `≥ 13`, and day `0` are never valid. Covers the whole upper-month
    rejection tail (all `m ≥ 13`, not just `13`), so an impl that accepts any
    out-of-range month or a zero day is rejected. -/
def spec_valid_invalid (impl : RepoImpl) : Prop :=
  ∀ (y d m : Nat),
    impl.prolepticGregorian.validDate ⟨y, 0, d⟩ = false ∧
    (13 ≤ m → impl.prolepticGregorian.validDate ⟨y, m, d⟩ = false) ∧
    impl.prolepticGregorian.validDate ⟨y, 1, 0⟩ = false

/-- February 29th is a valid date *exactly* in leap years `≥ 1`:
    `(y,2,29)` is valid iff `1 ≤ y` and `y` is leap. The leap-day edge
    case linking `validDate`, `daysInMonth`, and `isLeap`. -/
def spec_valid_leap_feb29 (impl : RepoImpl) : Prop :=
  ∀ (y : Nat),
    impl.prolepticGregorian.validDate ⟨y, 2, 29⟩ = true ↔
      (1 ≤ y ∧ impl.prolepticGregorian.isLeap y = true)

-- ── ord2ymd: the inverse (round-trip both directions + validity) ──

/-- Left inverse: converting a genuine calendar date to its ordinal and
    back recovers the date. `ord2ymd` inverts `ymd2ord` on the whole
    valid-date domain. -/
def spec_ord2ymd_left_inverse (impl : RepoImpl) : Prop :=
  ∀ (d : Date),
    impl.prolepticGregorian.validDate d = true →
    impl.prolepticGregorian.ord2ymd (impl.prolepticGregorian.ymd2ord d) = d

/-- Right inverse: converting an ordinal `n ≥ 1` to a date and back recovers
    `n`. Together with the left inverse this makes `ymd2ord`/`ord2ymd` a genuine
    bijection between dates and the positive ordinals. -/
def spec_ord2ymd_right_inverse (impl : RepoImpl) : Prop :=
  ∀ (n : Nat), 1 ≤ n →
    impl.prolepticGregorian.ymd2ord (impl.prolepticGregorian.ord2ymd n) = n

/-- The inverse always returns a genuine calendar date: for every `n ≥ 1`,
    `ord2ymd n` is valid. Rejects any impl whose inverse can emit a
    malformed `(year, month, day)` triple. -/
def spec_ord2ymd_valid (impl : RepoImpl) : Prop :=
  ∀ (n : Nat), 1 ≤ n →
    impl.prolepticGregorian.validDate (impl.prolepticGregorian.ord2ymd n) = true

-- ── deep structural laws of the ordinal / weekday ─────────────────

/-- Weekday is periodic with the 400-year Gregorian cycle: shifting the year by
    `400` leaves the weekday of any `(month, day)` unchanged. This is the famous
    property that the Gregorian calendar repeats its day-of-week pattern exactly
    every 400 years; an impl that mishandles the century/quad-century leap
    exceptions breaks the periodicity. -/
def spec_weekday_period_400 (impl : RepoImpl) : Prop :=
  ∀ (y m d : Nat), 1 ≤ y →
    impl.prolepticGregorian.weekday ⟨y + 400, m, d⟩ =
      impl.prolepticGregorian.weekday ⟨y, m, d⟩

/-- The twelve month lengths of any year sum to the year's length: `366` in a
    leap year, `365` otherwise. A whole-year fold over `daysInMonth`. -/
def spec_days_in_year_sum (impl : RepoImpl) : Prop :=
  ∀ (y : Nat),
    (impl.prolepticGregorian.daysInMonth y 1 + impl.prolepticGregorian.daysInMonth y 2 +
     impl.prolepticGregorian.daysInMonth y 3 + impl.prolepticGregorian.daysInMonth y 4 +
     impl.prolepticGregorian.daysInMonth y 5 + impl.prolepticGregorian.daysInMonth y 6 +
     impl.prolepticGregorian.daysInMonth y 7 + impl.prolepticGregorian.daysInMonth y 8 +
     impl.prolepticGregorian.daysInMonth y 9 + impl.prolepticGregorian.daysInMonth y 10 +
     impl.prolepticGregorian.daysInMonth y 11 + impl.prolepticGregorian.daysInMonth y 12)
      = (if impl.prolepticGregorian.isLeap y then 366 else 365)

/-- Within-year decomposition: the gap between a date's ordinal and its year's
    New-Year ordinal equals `daysBeforeMonth d.year d.month + d.day - 1` — how
    far into its year the date sits. -/
def spec_ord_within_year_decomp (impl : RepoImpl) : Prop :=
  ∀ (d : Date),
    impl.prolepticGregorian.ymd2ord d -
      impl.prolepticGregorian.ymd2ord ⟨d.year, 1, 1⟩
      = daysBeforeMonth d.year d.month + d.day - 1

/-- Inter-year gap lower bound: the ordinal distance between two New Year's days
    is at least `365` days per intervening year — every calendar year is at least
    a common year long. -/
def spec_year_gap_lower (impl : RepoImpl) : Prop :=
  ∀ (y1 y2 : Nat), 1 ≤ y1 → y1 ≤ y2 →
    impl.prolepticGregorian.ymd2ord ⟨y2, 1, 1⟩ -
      impl.prolepticGregorian.ymd2ord ⟨y1, 1, 1⟩
      ≥ 365 * (y2 - y1)

/-- Leap-count accumulation: New Year of year `y+1` sits `365 * y` days plus one
    day per leap year in `[1, y]` past the epoch (`leapCount y` counts those
    leaps). A cross-API law tying the impl's `ymd2ord` to the frozen `leapCount`
    count — an impl that miscounts leap days over a multi-year span fails it. -/
def spec_leap_count_formula (impl : RepoImpl) : Prop :=
  ∀ (y : Nat),
    impl.prolepticGregorian.ymd2ord ⟨y + 1, 1, 1⟩ = 365 * y + leapCount y + 1

-- ── year-boundary spans: last day of the year ─────────────────────

/-- The day after December 31st is New Year's Day of the next year: the ordinals
    of `(y,12,31)` and `(y+1,1,1)` are consecutive. The year-boundary case of the
    successor law, stated directly on the two endpoints — the calendar rolls over
    cleanly with no gap or overlap at the turn of the year. An impl that drops or
    duplicates a day at the year boundary fails it. -/
def spec_ord_dec31_succ (impl : RepoImpl) : Prop :=
  ∀ (y : Nat), 1 ≤ y →
    impl.prolepticGregorian.ymd2ord ⟨y, 12, 31⟩ + 1 =
      impl.prolepticGregorian.ymd2ord ⟨y + 1, 1, 1⟩

/-- Whole-year span: the ordinal distance from a year's first day to its last day,
    inclusive, is the year's length — `366` in a leap year, `365` otherwise.
    Couples `ymd2ord` at the two extreme dates of a year through the year-length
    fold; an impl that mislays a single month's days breaks it. -/
def spec_ord_year_span (impl : RepoImpl) : Prop :=
  ∀ (y : Nat), 1 ≤ y →
    impl.prolepticGregorian.ymd2ord ⟨y, 12, 31⟩ + 1 -
      impl.prolepticGregorian.ymd2ord ⟨y, 1, 1⟩
      = (if impl.prolepticGregorian.isLeap y then 366 else 365)

/-- Exact inter-year gap: the ordinal distance between two New Year's days equals
    `365` per intervening year plus one extra day for every leap year strictly
    between the epoch bounds (`leapCount (y2-1) - leapCount (y1-1)` counts the
    leaps in `[y1, y2)`). The exact-equality sharpening of `spec_year_gap_lower` —
    forces the running day-count to telescope precisely across the whole span. -/
def spec_year_gap_exact (impl : RepoImpl) : Prop :=
  ∀ (y1 y2 : Nat), 1 ≤ y1 → y1 ≤ y2 →
    impl.prolepticGregorian.ymd2ord ⟨y2, 1, 1⟩ -
      impl.prolepticGregorian.ymd2ord ⟨y1, 1, 1⟩
      = 365 * (y2 - y1) + (leapCount (y2 - 1) - leapCount (y1 - 1))

/-- Inter-year gap upper bound: the ordinal distance between two New Year's days
    is at most `366` days per intervening year — no calendar year is longer than
    a leap year. Dual of `spec_year_gap_lower`. An impl that over-counts a year's
    length fails it. -/
def spec_year_gap_upper (impl : RepoImpl) : Prop :=
  ∀ (y1 y2 : Nat), 1 ≤ y1 → y1 ≤ y2 →
    impl.prolepticGregorian.ymd2ord ⟨y2, 1, 1⟩ -
      impl.prolepticGregorian.ymd2ord ⟨y1, 1, 1⟩
      ≤ 366 * (y2 - y1)

/-- Leap-density bridge: the number of leap years in the half-open interval
    `[y1, y2)` (`leapCount (y2-1) - leapCount (y1-1)`) equals the inter-New-Year
    ordinal gap minus `365` per year. A cross-API law tying the impl's `ymd2ord`
    to the frozen `leapCount` — the calendar's leap density read off from the day
    count. An impl whose day count disagrees with the leap density fails it. -/
def spec_leap_count_in_range (impl : RepoImpl) : Prop :=
  ∀ (y1 y2 : Nat), 1 ≤ y1 → y1 ≤ y2 →
    leapCount (y2 - 1) - leapCount (y1 - 1)
      = (impl.prolepticGregorian.ymd2ord ⟨y2, 1, 1⟩ -
          impl.prolepticGregorian.ymd2ord ⟨y1, 1, 1⟩) - 365 * (y2 - y1)

/-- Multi-year weekday threading: the weekday of New Year's Day `k` years on is
    this year's New Year weekday advanced by the elapsed days mod 7 — `365` per
    year plus one per intervening leap year. Pins how the weekday cycle threads
    across an arbitrary multi-year span; an impl that loses track of the
    accumulated leap days lands on the wrong day of the week. -/
def spec_weekday_year_count (impl : RepoImpl) : Prop :=
  ∀ (y k : Nat), 1 ≤ y →
    impl.prolepticGregorian.weekday ⟨y + k, 1, 1⟩ =
      (impl.prolepticGregorian.weekday ⟨y, 1, 1⟩ +
        365 * k + (leapCount (y + k - 1) - leapCount (y - 1))) % 7

-- ── ord2ymd as a strictly increasing calendar walk ────────────────

/-- The inverse lands in the correct year band: if the ordinal `n` falls strictly
    after year `y`'s opening day-count (`daysBeforeYear y`) and at most after the
    next year's, then `ord2ymd n` reports year `y`. Pins the year coordinate of
    the inverse. -/
def spec_ord2ymd_year_band (impl : RepoImpl) : Prop :=
  ∀ (n y : Nat), daysBeforeYear y < n → n ≤ daysBeforeYear (y + 1) →
    (impl.prolepticGregorian.ord2ymd n).year = y

/-- The inverse pins New Year's Day exactly: the first ordinal of year `y+1`
    (`daysBeforeYear (y+1) + 1`) maps back to `(y+1, 1, 1)`, for every `y`.
    A grounding of the inverse at every year boundary — it must land precisely
    on the 1st of January, not the previous December. -/
def spec_ord2ymd_jan1 (impl : RepoImpl) : Prop :=
  ∀ (y : Nat),
    impl.prolepticGregorian.ord2ymd (daysBeforeYear (y + 1) + 1) = ⟨y + 1, 1, 1⟩

/-- The inverse is strictly calendar-monotone: a larger ordinal maps to a strictly
    later date. `ord2ymd` reflects `<` on positive ordinals into the lexicographic
    calendar order — the order-isomorphism read in the inverse direction. Rejects
    any impl whose inverse reorders dates relative to their day numbers. -/
def spec_ord2ymd_strict_mono (impl : RepoImpl) : Prop :=
  ∀ (n1 n2 : Nat), 1 ≤ n1 → n1 < n2 →
    dateLt (impl.prolepticGregorian.ord2ymd n1) (impl.prolepticGregorian.ord2ymd n2)

/-- The inverse walks the calendar one day at a time: `ord2ymd (n+1)` is the
    immediate calendar successor of `ord2ymd n` (for `n ≥ 1`). The strongest
    local law of the inverse — bumping the ordinal by one advances the date across
    whatever month/year boundary lies next. Forces `ord2ymd` to realise the exact
    successor relation `isImmediateSucc`, not merely "some later date". -/
def spec_ord2ymd_succ_step (impl : RepoImpl) : Prop :=
  ∀ (n : Nat), 1 ≤ n →
    isImmediateSucc (impl.prolepticGregorian.ord2ymd n)
                    (impl.prolepticGregorian.ord2ymd (n + 1))

-- ── order-isomorphism biconditionals + inverse month band ─────────

/-- Order-isomorphism, both directions: on valid dates the strict ordinal
    order and the lexicographic calendar order coincide. The forward
    direction (`dateLt → <`) is `spec_ord_strict_mono`; this biconditional
    also pins the *reverse* — a strictly smaller ordinal forces a strictly
    earlier calendar date. `ymd2ord` is thus a genuine order embedding of
    the valid dates into ℕ, not merely order-preserving. An impl that keeps
    the forward order but lets some out-of-order pair share the ordinal gap
    fails the reverse. -/
def spec_ord_strict_mono_iff (impl : RepoImpl) : Prop :=
  ∀ (d1 d2 : Date),
    impl.prolepticGregorian.validDate d1 = true →
    impl.prolepticGregorian.validDate d2 = true →
      (impl.prolepticGregorian.ymd2ord d1 < impl.prolepticGregorian.ymd2ord d2 ↔
        dateLt d1 d2)

/-- Successor characterization, both directions: on valid dates the ordinal
    jumps by exactly one *iff* the two dates are calendar-adjacent. The
    forward direction (`isImmediateSucc → +1`) is the valid-date restriction
    of `spec_ord_unit_step`; this biconditional also pins the *reverse* — an
    ordinal gap of one forces the second date to be the immediate calendar
    successor of the first, reconstructing the exact mid-month /
    month-boundary / year-boundary transition. An impl that advances by one
    ordinal between two non-adjacent dates fails the reverse. -/
def spec_ord_succ_iff (impl : RepoImpl) : Prop :=
  ∀ (d1 d2 : Date),
    impl.prolepticGregorian.validDate d1 = true →
    impl.prolepticGregorian.validDate d2 = true →
      (impl.prolepticGregorian.ymd2ord d2 = impl.prolepticGregorian.ymd2ord d1 + 1 ↔
        isImmediateSucc d1 d2)

/-- The inverse lands in the correct month band: once the inverse has fixed
    the year `y` of ordinal `n` (via `spec_ord2ymd_year_band`), the in-year
    offset `r = n - daysBeforeYear y` selects the month by the cumulative
    month table — `daysBeforeMonth y m < r`, and if the month is below
    December, `r ≤ daysBeforeMonth y (m+1)`. Pins the *month* coordinate of
    the inverse the way `spec_ord2ymd_year_band` pins the year. An impl whose
    inverse attributes a day to the wrong month within the right year fails
    it. -/
def spec_ord2ymd_month_band (impl : RepoImpl) : Prop :=
  ∀ (n y : Nat), 1 ≤ n →
    daysBeforeYear y < n → n ≤ daysBeforeYear (y + 1) →
      daysBeforeMonth y (impl.prolepticGregorian.ord2ymd n).month < n - daysBeforeYear y ∧
      ((impl.prolepticGregorian.ord2ymd n).month < 12 →
        n - daysBeforeYear y ≤
          daysBeforeMonth y ((impl.prolepticGregorian.ord2ymd n).month + 1))

/-- Weekday factors through the ordinal mod 7: two dates whose ordinals are
    congruent mod 7 share a weekday, and (conversely) equal weekdays force
    congruent ordinals mod 7. Pins the seven-day residue coupling between
    `ymd2ord` and `weekday`. -/
def spec_weekday_ord_congr (impl : RepoImpl) : Prop :=
  ∀ (d1 d2 : Date),
    (impl.prolepticGregorian.weekday d1 = impl.prolepticGregorian.weekday d2 ↔
      impl.prolepticGregorian.ymd2ord d1 % 7 = impl.prolepticGregorian.ymd2ord d2 % 7)

-- ── hardening round 3: counting / positional / existence laws ─────

/-- The number of leap years in `[1, y]`, read off a frozen filtered
    enumeration of the year range, equals the surplus of the New-Year
    ordinal advance over `365` days per year. A count-over-enumeration
    reading of the calendar's leap density. -/
def spec_leap_filter_count_gap (impl : RepoImpl) : Prop :=
  ∀ (y : Nat),
    (frozenLeapYearsUpTo y).length =
      impl.prolepticGregorian.ymd2ord ⟨y + 1, 1, 1⟩ -
        impl.prolepticGregorian.ymd2ord ⟨1, 1, 1⟩ - 365 * y

/-- The ordinals assigned to the days of a single calendar month are all
    distinct and fill exactly the contiguous block starting at that month's
    first-day ordinal and spanning the month's length. Pins `ymd2ord`, over
    a whole month at once, as a collision-free enumeration of a day interval. -/
def spec_month_ordinals_exact (impl : RepoImpl) : Prop :=
  ∀ (y m : Nat), 1 ≤ y → 1 ≤ m → m ≤ 12 →
    (monthDayOrdinals impl y m).Nodup ∧
    ∀ (n : Nat),
      n ∈ monthDayOrdinals impl y m ↔
        impl.prolepticGregorian.ymd2ord ⟨y, m, 1⟩ ≤ n ∧
        n < impl.prolepticGregorian.ymd2ord ⟨y, m, 1⟩ + daysInMonthFrozen y m

/-- Across any seven consecutive ordinals, each of the seven weekday values
    occurs exactly once — the calendar week is a perfect seven-fold cover.
    A counting/covering law of the weekday cycle, not a single-step
    congruence. -/
def spec_weekday_window_count (impl : RepoImpl) : Prop :=
  ∀ (n w : Nat), 1 ≤ n → w < 7 →
    (weekdayWindow impl n).count w = 1

/-- The first ordinal (scanning upward from `1`) whose inverse lands in year
    `y` sits exactly `daysBeforeYear y` positions in — i.e. New Year's Day of
    year `y` is the first day of that year. A first-occurrence reading of the
    inverse's year coordinate. -/
def spec_ord2ymd_first_year_index (impl : RepoImpl) : Prop :=
  ∀ (y : Nat), 1 ≤ y →
    (List.range (impl.prolepticGregorian.ymd2ord ⟨y + 1, 1, 1⟩)).findIdx
      (fun n => decide ((impl.prolepticGregorian.ord2ymd (n + 1)).year = y))
      = daysBeforeYear y

/-- Every weekday occurs in every year: for any target weekday `w` there is a
    genuine calendar date in year `y` falling on `w`. A surjectivity law of
    `weekday` restricted to a single year. -/
def spec_year_weekday_surjective (impl : RepoImpl) : Prop :=
  ∀ (y w : Nat), 1 ≤ y → w < 7 →
    ∃ (m d : Nat),
      impl.prolepticGregorian.validDate ⟨y, m, d⟩ = true ∧
      impl.prolepticGregorian.weekday ⟨y, m, d⟩ = w

/-- The month boundaries of a year strictly increase, and every in-year offset
    falls into exactly one month band — the inverse's month coordinate is the
    unique cell of that strict partition. Pins the month partition as a strict,
    collision-free cover of the year. -/
def spec_month_boundary_unique (impl : RepoImpl) : Prop :=
  ∀ (y r : Nat), 1 ≤ y → 1 ≤ r → r ≤ yearLengthFrozen y →
    ∃ (m : Nat),
      (1 ≤ m ∧ m ≤ 12 ∧
        daysBeforeMonth y m < r ∧
        (m < 12 → r ≤ daysBeforeMonth y (m + 1)) ∧
        (impl.prolepticGregorian.ord2ymd
          (impl.prolepticGregorian.ymd2ord ⟨y, 1, 1⟩ + (r - 1))).month = m) ∧
      ∀ (m' : Nat),
        (1 ≤ m' ∧ m' ≤ 12 ∧
          daysBeforeMonth y m' < r ∧
          (m' < 12 → r ≤ daysBeforeMonth y (m' + 1))) →
        m' = m

-- ── hardening round 4: telescoping / enumeration / positional laws ──

/-- Consecutive frozen month prefixes differ by the impl's own month length,
    and December's prefix plus its length closes the year at `yearLengthFrozen`.
    Anchored on `daysBeforeMonth` and `daysInMonth`. -/
def spec_month_prefix_telescope (impl : RepoImpl) : Prop :=
  ∀ (y : Nat), 1 ≤ y →
    (∀ (m : Nat), 1 ≤ m → m < 12 →
      daysBeforeMonth y m + impl.prolepticGregorian.daysInMonth y m =
        daysBeforeMonth y (m + 1)) ∧
    daysBeforeMonth y 12 + impl.prolepticGregorian.daysInMonth y 12 =
      yearLengthFrozen y

/-- The ordinals of all calendar days of a year are distinct, number
    `yearLengthFrozen y`, and fill exactly the contiguous ordinal block from
    New Year's Day onward. Anchored on `wholeYearOrdinals` and `yearLengthFrozen`. -/
def spec_whole_year_ordinals_exact (impl : RepoImpl) : Prop :=
  ∀ (y : Nat), 1 ≤ y →
    (wholeYearOrdinals impl y).Nodup ∧
    (wholeYearOrdinals impl y).length = yearLengthFrozen y ∧
    ∀ (n : Nat),
      n ∈ wholeYearOrdinals impl y ↔
        impl.prolepticGregorian.ymd2ord ⟨y, 1, 1⟩ ≤ n ∧
        n < impl.prolepticGregorian.ymd2ord ⟨y, 1, 1⟩ + yearLengthFrozen y

/-- The inverse decodes any window of consecutive positive ordinals into
    distinct dates. Anchored on `ord2ymd` and `List.range`. -/
def spec_ord2ymd_range_nodup (impl : RepoImpl) : Prop :=
  ∀ (lo len : Nat), 1 ≤ lo →
    (ord2ymdWindow impl lo len).Nodup

/-- The number of leap years in the half-open interval `[y, y + k)` equals the
    surplus of the New-Year ordinal advance over `365` days per year. Anchored on
    `frozenLeapYearsInHalfOpen` and `ymd2ord`. -/
def spec_leap_filter_count_range_gap (impl : RepoImpl) : Prop :=
  ∀ (y k : Nat), 1 ≤ y →
    (frozenLeapYearsInHalfOpen y k).length =
      impl.prolepticGregorian.ymd2ord ⟨y + k, 1, 1⟩ -
        impl.prolepticGregorian.ymd2ord ⟨y, 1, 1⟩ - 365 * k

/-- Every weekday occurs exactly fifty-two times over a year plus once more for
    each leftover day of the year, counting from New Year's weekday. Anchored on
    `yearWeekdayValues` and `yearSurplusWeekdays`. -/
def spec_year_weekday_occurrences (impl : RepoImpl) : Prop :=
  ∀ (y w : Nat), 1 ≤ y → w < 7 →
    (yearWeekdayValues impl y).count w =
      52 + (if w ∈ yearSurplusWeekdays impl y then 1 else 0)

/-- Every weekday occurs, over a month, once per whole week plus once more for
    each leftover day counting from the month's first weekday. Anchored on
    `monthWeekdayValues` and `daysInMonthFrozen`. -/
def spec_month_weekday_counts_exact (impl : RepoImpl) : Prop :=
  ∀ (y m w : Nat), 1 ≤ y → 1 ≤ m → m ≤ 12 → w < 7 →
    (monthWeekdayValues impl y m).count w =
      daysInMonthFrozen y m / 7 +
        ((List.range (daysInMonthFrozen y m % 7)).filter (fun i =>
          decide (((impl.prolepticGregorian.weekday ⟨y, m, 1⟩ + i) % 7) = w))).length

/-- The `k`-th occurrence of a weekday within a month sits at its first matching
    within-month offset plus `7 * k`. Anchored on `weekdayPositionsInMonth`. -/
def spec_kth_weekday_in_month_index (impl : RepoImpl) : Prop :=
  ∀ (y m w k : Nat), 1 ≤ y → 1 ≤ m → m ≤ 12 → w < 7 →
    k < (weekdayPositionsInMonth impl y m w).length →
      List.head? (List.drop k (weekdayPositionsInMonth impl y m w)) =
        some (((w + 7 - impl.prolepticGregorian.weekday ⟨y, m, 1⟩) % 7) + 7 * k)

/-- Scanning a year by ordinal, each month `m` first appears at position
    `daysBeforeMonth y m`. Anchored on `yearOrdinalMonths` and `daysBeforeMonth`. -/
def spec_month_findidx_in_year (impl : RepoImpl) : Prop :=
  ∀ (y m : Nat), 1 ≤ y → 1 ≤ m → m ≤ 12 →
    (yearOrdinalMonths impl y).findIdx (fun m' => decide (m' = m)) =
      daysBeforeMonth y m

/-- Every day-of-year index in `1 .. yearLengthFrozen y` is the day-of-year of
    exactly one valid calendar date in year `y`. Anchored on `dayOfYearFrozen`,
    `validDate`, and `yearLengthFrozen`. -/
def spec_day_of_year_unique_cover (impl : RepoImpl) : Prop :=
  ∀ (y r : Nat), 1 ≤ y → 1 ≤ r → r ≤ yearLengthFrozen y →
    ∃ (m d : Nat),
      impl.prolepticGregorian.validDate ⟨y, m, d⟩ = true ∧
      dayOfYearFrozen ⟨y, m, d⟩ = r ∧
      ∀ (m' d' : Nat),
        impl.prolepticGregorian.validDate ⟨y, m', d'⟩ = true →
        dayOfYearFrozen ⟨y, m', d'⟩ = r →
          m' = m ∧ d' = d
