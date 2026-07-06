import ProlepticGregorian.Impl.Ordinal
import ProlepticGregorian.Bundle
import ProlepticGregorian.Harness
import ProlepticGregorian.Spec.Ordinal
import ProlepticGregorian.Test

/-!
# ProlepticGregorian

Root import hub for the proleptic-Gregorian ordinal-core benchmark:
pure integer date↔ordinal arithmetic over `(year, month, day)` dates.

The API is `isLeap`, `daysInMonth`, `ymd2ord` (date → day-count since
the epoch `0001-01-01`), its inverse `ord2ymd`, `weekday`, and
`validDate`. Behaviour is pinned by `Spec/Ordinal.lean`.
-/
