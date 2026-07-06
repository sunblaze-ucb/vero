import Croniter.Impl.Cron

/-!
# Croniter.Bundle

Per-package implementation bundle for the `Croniter` root package.
Collects all API signatures into one structure.

DO NOT MODIFY — benchmark infrastructure.
-/

structure CroniterBundle where
  cronMatches : Croniter.CronMatchesSig
  nextFire    : Croniter.NextFireSig
  prevFire    : Croniter.PrevFireSig
