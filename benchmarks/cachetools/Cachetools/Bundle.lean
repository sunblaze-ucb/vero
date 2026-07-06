import Cachetools.Impl.Lru

/-!
# Cachetools.Bundle

Per-package implementation bundle for the `Cachetools` root package.
Collects all API signatures into one structure.

DO NOT MODIFY — benchmark infrastructure.
-/

structure CachetoolsBundle where
  empty    : Cachetools.EmptySig
  contains : Cachetools.ContainsSig
  get      : Cachetools.GetSig
  put      : Cachetools.PutSig
  lruKey   : Cachetools.LruKeySig
