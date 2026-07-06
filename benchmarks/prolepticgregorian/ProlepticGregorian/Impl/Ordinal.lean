-- !benchmark @start imports
-- !benchmark @end imports

/-!
# ProlepticGregorian.Impl.Ordinal

The proleptic-Gregorian *ordinal* core: pure integer date↔ordinal
arithmetic — leap-year classification, month lengths, and the conversion
of a `(year, month, day)` triple into its "ordinal", the count of days
since the epoch `0001-01-01` (which is ordinal `1`). The calendar is
*proleptic* Gregorian: the Gregorian leap rules run back to year 1, with
no historical Julian/Gregorian switch.

Everything is integer, float-free, and decidable. A date is a plain
`(year, month, day)` record; the routines are total and do not validate
their input, so `validDate` is the predicate that picks out the genuine
calendar dates.

Types, signatures, and the `global_aux` calendar tables are fixed
vocabulary (DO NOT MODIFY).
-/

-- ── Core data type (DO NOT MODIFY) ───────────────────────────

/-- A calendar date: a `(year, month, day)` triple of naturals.
    Months are `1..12`, days are `1..daysInMonth`, years are `≥ 1`
    for genuine proleptic-Gregorian dates (see `validDate`). -/
structure Date where
  year  : Nat
  month : Nat
  day   : Nat
deriving DecidableEq, Repr

namespace ProlepticGregorian

-- ── API signatures (DO NOT MODIFY) ───────────────────────────

/-- `isLeap y`: whether `y` is a leap year under the proleptic-Gregorian
    rule (divisible by 4, except centuries not divisible by 400). -/
abbrev IsLeapSig      := Nat → Bool

/-- `daysInMonth y m`: the number of days in month `m` of year `y`
    (28/29 for February depending on the leap rule). -/
abbrev DaysInMonthSig := Nat → Nat → Nat

/-- `ymd2ord d`: the proleptic-Gregorian ordinal of date `d` — the
    number of days from `0001-01-01` (ordinal `1`) up to and including
    `d`. -/
abbrev Ymd2ordSig     := Date → Nat

/-- `weekday d`: the day of the week of `d`, Monday `= 0` … Sunday `= 6`. -/
abbrev WeekdaySig     := Date → Nat

/-- `ord2ymd n`: the inverse of `ymd2ord` — the proleptic-Gregorian date
    whose ordinal is `n` (for `n ≥ 1`). -/
abbrev Ord2ymdSig     := Nat → Date

/-- `validDate d`: whether `d` is a genuine proleptic-Gregorian date —
    year `≥ 1`, month `1..12`, day `1..daysInMonth`. -/
abbrev ValidDateSig   := Date → Bool

end ProlepticGregorian

-- ── Frozen calendar tables (DO NOT MODIFY) ───────────────────
-- These are fixed calendar *data* — the month-length table and the
-- cumulative day-count offset tables. They are frozen problem vocabulary
-- that the Spec phrases its ordinal/weekday laws against (given to the
-- solving agent, not part of the algorithm they must write), so they live
-- OUTSIDE the agent-editable `global_aux` slot below. The API reference
-- bodies (`ymd2ord`, `ord2ymd`, …) build on top of them.

/-- Days in each month of a *non-leap* year, indexed by month `1..12`
    (out-of-range months give `0`). Frozen calendar constant. -/
def daysInMonthTable : Nat → Nat
  | 1 => 31 | 2 => 28 | 3 => 31 | 4 => 30  | 5 => 31  | 6 => 30
  | 7 => 31 | 8 => 31 | 9 => 30 | 10 => 31 | 11 => 30 | 12 => 31
  | _ => 0

/-- Cumulative number of days in a *non-leap* year strictly before the
    first of month `m` (so `daysBeforeMonthTable 1 = 0`,
    `daysBeforeMonthTable 3 = 59`). Frozen calendar constant. -/
def daysBeforeMonthTable : Nat → Nat
  | 1 => 0   | 2 => 31  | 3 => 59  | 4 => 90   | 5 => 120  | 6 => 151
  | 7 => 181 | 8 => 212 | 9 => 243 | 10 => 273 | 11 => 304 | 12 => 334
  | _ => 0

/-- `daysBeforeYear y`: the number of days before January 1st of year
    `y` (so `daysBeforeYear 1 = 0`). Frozen calendar constant. -/
def daysBeforeYear (y : Nat) : Nat :=
  365 * (y - 1) + (y - 1) / 4 - (y - 1) / 100 + (y - 1) / 400

/-- `daysBeforeMonth y m`: the number of days in year `y` before the
    first of month `m`, i.e. the non-leap cumulative table plus one extra
    day once we are past February in a leap year. Frozen. -/
def daysBeforeMonth (y m : Nat) : Nat :=
  daysBeforeMonthTable m + (if (m > 2 ∧ (y % 4 = 0 ∧ (y % 100 ≠ 0 ∨ y % 400 = 0))) then 1 else 0)

-- !benchmark @start global_aux
-- !benchmark @end global_aux

-- !benchmark @start code_aux def=isLeap
-- !benchmark @end code_aux def=isLeap

def ProlepticGregorian.isLeap : ProlepticGregorian.IsLeapSig :=
-- !benchmark @start code def=isLeap
  fun y => decide (y % 4 = 0 ∧ (y % 100 ≠ 0 ∨ y % 400 = 0))
-- !benchmark @end code def=isLeap

-- !benchmark @start code_aux def=daysInMonth
-- !benchmark @end code_aux def=daysInMonth

def ProlepticGregorian.daysInMonth : ProlepticGregorian.DaysInMonthSig :=
-- !benchmark @start code def=daysInMonth
  fun y m => if m = 2 then (if ProlepticGregorian.isLeap y then 29 else 28) else daysInMonthTable m
-- !benchmark @end code def=daysInMonth

-- !benchmark @start code_aux def=ymd2ord
-- !benchmark @end code_aux def=ymd2ord

def ProlepticGregorian.ymd2ord : ProlepticGregorian.Ymd2ordSig :=
-- !benchmark @start code def=ymd2ord
  fun d => daysBeforeYear d.year + daysBeforeMonth d.year d.month + d.day
-- !benchmark @end code def=ymd2ord

-- !benchmark @start code_aux def=weekday
-- !benchmark @end code_aux def=weekday

def ProlepticGregorian.weekday : ProlepticGregorian.WeekdaySig :=
-- !benchmark @start code def=weekday
  fun d => (ProlepticGregorian.ymd2ord d + 6) % 7
-- !benchmark @end code def=weekday

-- !benchmark @start code_aux def=validDate
-- !benchmark @end code_aux def=validDate

def ProlepticGregorian.validDate : ProlepticGregorian.ValidDateSig :=
-- !benchmark @start code def=validDate
  fun d => decide (1 ≤ d.year ∧ 1 ≤ d.month ∧ d.month ≤ 12 ∧
                   1 ≤ d.day ∧ d.day ≤ ProlepticGregorian.daysInMonth d.year d.month)
-- !benchmark @end code def=validDate

-- !benchmark @start code_aux def=ord2ymd
/-- Helper for `ord2ymd`: the year component for ordinal `n`. `fuel` bounds
    the recursion. -/
def ProlepticGregorian.ord2ymdGoYear (n : Nat) : Nat → Nat → Nat
  | y, 0 => y
  | y, Nat.succ f =>
      if daysBeforeYear (y + 1) < n then ProlepticGregorian.ord2ymdGoYear n (y + 1) f else y

/-- Helper for `ord2ymd`: the month component within year `y` for in-year
    offset `r`. `fuel` bounds the recursion. -/
def ProlepticGregorian.ord2ymdGoMonth (y r : Nat) : Nat → Nat → Nat
  | m, 0 => m
  | m, Nat.succ f =>
      if m < 12 ∧ daysBeforeMonth y (m + 1) < r then
        ProlepticGregorian.ord2ymdGoMonth y r (m + 1) f
      else m
-- !benchmark @end code_aux def=ord2ymd

def ProlepticGregorian.ord2ymd : ProlepticGregorian.Ord2ymdSig :=
-- !benchmark @start code def=ord2ymd
  fun n =>
    let y := ProlepticGregorian.ord2ymdGoYear n 1 n
    let r := n - daysBeforeYear y
    let m := ProlepticGregorian.ord2ymdGoMonth y r 1 11
    ⟨y, m, r - daysBeforeMonth y m⟩
-- !benchmark @end code def=ord2ymd
