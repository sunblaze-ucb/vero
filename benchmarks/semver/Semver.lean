import Semver.Impl.Version
import Semver.Bundle
import Semver.Harness
import Semver.Spec.Version
import Semver.Test

/-!
# Semver

Root import hub for the SemVer 2.0.0 precedence + constraint-selection
benchmark.

A version is its precedence-relevant axes: `major`, `minor`, `patch`, a
pre-release identifier list, and (precedence-irrelevant) build metadata. The API
is the comparator family (`compareV` / `versionLt` / `versionEq`), the
constraint predicate (`satisfies`), and `select` (the greatest matching version
in a candidate list). Behaviour is pinned by `Spec/Version.lean`.

Scope: this models already-PARSED versions — there is no version-string parser —
and constraints as desugared clause lists (`Op ⋄ Version`).
-/
