import Semver.Impl.Version

/-!
# Semver.Bundle

Per-package implementation bundle for the `Semver` root package.
Collects all API signatures into one structure.

DO NOT MODIFY — benchmark infrastructure.
-/

structure SemverBundle where
  compareV  : Semver.CompareVSig
  versionLt : Semver.VersionLtSig
  versionEq : Semver.VersionEqSig
  satisfies : Semver.SatisfiesSig
  select    : Semver.SelectSig
