import Croniter.Impl.Cron
import Croniter.Bundle
import Croniter.Harness
import Croniter.Spec.Cron
import Croniter.Test

/-!
# Croniter

Root import hub for the cron next-fire benchmark.

A 3-field cron scheduler — minute / hour / day-of-week — over `Nat`
absolute minutes. `nextFire s t` returns the smallest firing time
strictly after `t`; `prevFire s t` the largest strictly before `t`.
The calendar fields of a time are read off by the frozen extractors
`minOf` / `hourOf` / `dowOf`; a spec fires when every field is allowed.

Scope: each field is an explicit list of allowed values (no
cron-expression parser); no seconds / month / day-of-month fields, and
no timezone handling. Behaviour is pinned by `Spec/Cron.lean`.
-/
