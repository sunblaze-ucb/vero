import Croniter.Impl.Cron

/-!
# Croniter.Test

Executable conformance tests. `#guard` assertions run against the
reference implementations inside the `code` markers in `Impl/Cron.lean`.

`everyWeek` fires only at minute 0 of hour 0 on day-of-week 0, i.e. at
multiples of `weekMinutes` (10080). `mondayNine` fires at minute 0 or 30
of hour 9 on day-of-week 1, i.e. at 1980 and 2010 within the first week.

DO NOT MODIFY — infrastructure.
-/

open Croniter

/-- Fires only at multiples of one week (minute 0, hour 0, dow 0). -/
def everyWeek : CronSpec := { minutes := [0], hours := [0], dows := [0] }

/-- Fires at 09:00 and 09:30 on day-of-week 1. -/
def mondayNine : CronSpec := { minutes := [0, 30], hours := [9], dows := [1] }

-- ── cronMatches ─────────────────────────────────────────────────
#guard cronMatches everyWeek 0 == true
#guard cronMatches everyWeek 1 == false
#guard cronMatches everyWeek 10080 == true
#guard cronMatches mondayNine 1980 == true        -- dow 1, hour 9, minute 0
#guard cronMatches mondayNine 2010 == true        -- dow 1, hour 9, minute 30
#guard cronMatches mondayNine 1981 == false       -- minute 1 not allowed

-- ── nextFire: smallest firing time strictly later ─────────────
#guard nextFire everyWeek 0 == 10080
#guard nextFire everyWeek 5 == 10080
#guard nextFire mondayNine 0 == 1980
#guard nextFire mondayNine 1980 == 2010           -- strictly later: 2010, not 1980
#guard nextFire mondayNine 1985 == 2010

-- ── prevFire: largest firing time strictly earlier ────────────
#guard prevFire everyWeek 10081 == 10080
#guard prevFire mondayNine 2010 == 1980           -- strictly earlier: 1980, not 2010
#guard prevFire mondayNine 2011 == 2010
