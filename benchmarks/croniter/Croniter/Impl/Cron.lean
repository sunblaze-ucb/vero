-- !benchmark @start imports
-- !benchmark @end imports

/-!
# Croniter.Impl.Cron

Cron next-fire computation. A time `t : Nat` is an absolute minute index
since some epoch; its calendar fields are read off by the frozen
extractors

* `minOf  t = t % 60`            — minute of the hour (0..59)
* `hourOf t = (t / 60) % 24`     — hour of the day   (0..23)
* `dowOf  t = (t / 1440) % 7`    — day of the week   (0..6)

A `CronSpec` lists, per field, the explicit set of allowed values (a `*`
wildcard is the full range list). The schedule fires at `t` exactly when
each field of `t` is allowed. The API is `cronMatches` (does `s` fire at
`t`?), `nextFire` (smallest firing time strictly after `t`) and
`prevFire` (largest strictly before `t`).

Types and signatures are fixed vocabulary (DO NOT MODIFY).
-/

-- ── Core data types (DO NOT MODIFY) ──────────────────────────

/-- A cron specification: the explicit set of allowed minutes, hours and
    days-of-week. A `*` wildcard is the full range list for that field. -/
structure CronSpec where
  minutes : List Nat
  hours   : List Nat
  dows    : List Nat
deriving Repr, DecidableEq

/-- Minute-of-hour of an absolute minute index (frozen extractor). -/
abbrev minOf (t : Nat) : Nat := t % 60

/-- Hour-of-day of an absolute minute index (frozen extractor). -/
abbrev hourOf (t : Nat) : Nat := (t / 60) % 24

/-- Day-of-week of an absolute minute index (frozen extractor). -/
abbrev dowOf (t : Nat) : Nat := (t / 1440) % 7

/-- The number of minutes in one week — the period over which every
    minute/hour/day-of-week combination recurs. -/
abbrev weekMinutes : Nat := 1440 * 7

/-- The frozen matcher: the schedule fires at `t` iff each calendar field
    of `t` is allowed by the spec. (Named `matchAt` to avoid the `matches`
    keyword.) -/
abbrev matchAt (s : CronSpec) (t : Nat) : Bool :=
  s.minutes.contains (minOf t) && s.hours.contains (hourOf t) && s.dows.contains (dowOf t)

namespace Croniter

-- ── API signatures (DO NOT MODIFY) ───────────────────────────

/-- `cronMatches s t`: whether the schedule `s` fires at time `t`. -/
abbrev CronMatchesSig := CronSpec → Nat → Bool

/-- `nextFire s t`: the smallest time strictly greater than `t` at which
    `s` fires. -/
abbrev NextFireSig := CronSpec → Nat → Nat

/-- `prevFire s t`: the largest time strictly less than `t` at which `s`
    fires. -/
abbrev PrevFireSig := CronSpec → Nat → Nat

end Croniter

-- !benchmark @start global_aux
/-- Scan upward from `start`, returning the first time `≥ start` (within
    `fuel` steps) at which `s` fires, or `none` if none fires in range. -/
def scanUp (s : CronSpec) (start : Nat) : Nat → Option Nat
  | 0 => none
  | Nat.succ fuel => if matchAt s start then some start else scanUp s (start + 1) fuel

/-- Scan downward from `start`, returning the first time `≤ start` (within
    `fuel` steps, stopping at 0) at which `s` fires, or `none`. -/
def scanDown (s : CronSpec) (start : Nat) : Nat → Option Nat
  | 0 => if matchAt s start then some start else none
  | Nat.succ fuel =>
      if matchAt s start then some start
      else if start = 0 then none
      else scanDown s (start - 1) fuel
-- !benchmark @end global_aux

-- !benchmark @start code_aux def=cronMatches
-- !benchmark @end code_aux def=cronMatches

def Croniter.cronMatches : Croniter.CronMatchesSig :=
-- !benchmark @start code def=cronMatches
  fun s t => matchAt s t
-- !benchmark @end code def=cronMatches

-- !benchmark @start code_aux def=nextFire
-- !benchmark @end code_aux def=nextFire

def Croniter.nextFire : Croniter.NextFireSig :=
-- !benchmark @start code def=nextFire
  fun s t => (scanUp s (t + 1) (weekMinutes + 1)).getD (t + 1)
-- !benchmark @end code def=nextFire

-- !benchmark @start code_aux def=prevFire
-- !benchmark @end code_aux def=prevFire

def Croniter.prevFire : Croniter.PrevFireSig :=
-- !benchmark @start code def=prevFire
  fun s t =>
    match t with
    | 0 => 0
    | Nat.succ p => (scanDown s p (weekMinutes + 1)).getD p
-- !benchmark @end code def=prevFire
