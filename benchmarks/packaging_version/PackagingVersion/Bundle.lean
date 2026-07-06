import PackagingVersion.Impl.Version

/-!
# PackagingVersion.Bundle

Per-package implementation bundle for the `PackagingVersion` root package.
Collects all API signatures into one structure.

DO NOT MODIFY — benchmark infrastructure.
-/

structure PackagingVersionBundle where
  verLe    : PackagingVersion.VerLeSig
  verEq    : PackagingVersion.VerEqSig
  maxVer   : PackagingVersion.MaxVerSig
  sortVers : PackagingVersion.SortVersSig
  minVer   : PackagingVersion.MinVerSig
