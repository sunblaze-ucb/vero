import ProlepticGregorian.Impl.Ordinal

/-!
# ProlepticGregorian.Bundle

Per-package implementation bundle for the `ProlepticGregorian` root
package. Collects all API signatures into one structure.

DO NOT MODIFY — benchmark infrastructure.
-/

structure ProlepticGregorianBundle where
  isLeap       : ProlepticGregorian.IsLeapSig
  daysInMonth  : ProlepticGregorian.DaysInMonthSig
  ymd2ord      : ProlepticGregorian.Ymd2ordSig
  weekday      : ProlepticGregorian.WeekdaySig
  validDate    : ProlepticGregorian.ValidDateSig
  ord2ymd      : ProlepticGregorian.Ord2ymdSig
