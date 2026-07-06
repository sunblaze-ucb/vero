import ProlepticGregorian.Impl.Ordinal

/-!
# ProlepticGregorian.Test

Executable conformance tests: `#guard` assertions over the API in
`Impl/Ordinal.lean`, checked against known calendar values.

DO NOT MODIFY — infrastructure.
-/

open ProlepticGregorian

-- ── isLeap ──────────────────────────────────────────────────────
#guard isLeap 1 == false
#guard isLeap 4 == true
#guard isLeap 100 == false      -- century, not divisible by 400
#guard isLeap 400 == true       -- century divisible by 400
#guard isLeap 2000 == true
#guard isLeap 2024 == true

-- ── daysInMonth ─────────────────────────────────────────────────
#guard daysInMonth 2023 2 == 28
#guard daysInMonth 2024 2 == 29  -- leap February
#guard daysInMonth 2024 1 == 31
#guard daysInMonth 2024 4 == 30
#guard daysInMonth 2024 12 == 31

-- ── ymd2ord: days since 0001-01-01 (ordinal 1) ──────────────────
#guard ymd2ord ⟨1, 1, 1⟩ == 1
#guard ymd2ord ⟨1, 1, 2⟩ == 2
#guard ymd2ord ⟨1, 2, 1⟩ == 32
#guard ymd2ord ⟨1, 12, 31⟩ == 365
#guard ymd2ord ⟨2, 1, 1⟩ == 366
#guard ymd2ord ⟨2024, 2, 29⟩ == 738945
#guard ymd2ord ⟨2024, 3, 1⟩ == 738946     -- day after leap Feb 29
#guard ymd2ord ⟨2025, 1, 1⟩ == 739252     -- day after 2024-12-31

-- ── weekday: Monday = 0 … Sunday = 6 ────────────────────────────
#guard weekday ⟨1, 1, 1⟩ == 0             -- 0001-01-01 is a Monday
#guard weekday ⟨2024, 2, 29⟩ == 3         -- Thursday
#guard weekday ⟨2025, 1, 1⟩ == 2          -- Wednesday

-- ── validDate ───────────────────────────────────────────────────
#guard validDate ⟨2024, 2, 29⟩ == true
#guard validDate ⟨2023, 2, 29⟩ == false   -- not a leap year
#guard validDate ⟨2024, 13, 1⟩ == false   -- month out of range
#guard validDate ⟨2024, 4, 31⟩ == false   -- April has 30 days
#guard validDate ⟨0, 1, 1⟩ == false       -- year must be ≥ 1

-- ── ord2ymd: inverse of ymd2ord (date from ordinal) ─────────────
#guard ord2ymd 1 == (⟨1, 1, 1⟩ : Date)            -- epoch
#guard ord2ymd 365 == (⟨1, 12, 31⟩ : Date)        -- end of year 1
#guard ord2ymd 366 == (⟨2, 1, 1⟩ : Date)          -- start of year 2
#guard ord2ymd 738945 == (⟨2024, 2, 29⟩ : Date)   -- leap Feb 29
#guard ord2ymd 739252 == (⟨2025, 1, 1⟩ : Date)    -- New Year 2025
-- round-trips against ymd2ord
#guard ord2ymd (ymd2ord ⟨2024, 2, 29⟩) == (⟨2024, 2, 29⟩ : Date)
#guard ymd2ord (ord2ymd 738945) == 738945
