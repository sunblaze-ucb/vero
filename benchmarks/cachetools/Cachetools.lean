import Cachetools.Impl.Lru
import Cachetools.Bundle
import Cachetools.Harness
import Cachetools.Spec.Lru
import Cachetools.Test

/-!
# Cachetools

Root import hub for the LRU-cache benchmark.

Models a least-recently-used (LRU) cache eviction policy over KEYS
(values are erased). A cache carries a `capacity` and its present keys
ordered most-recently-used first. `get` / `put` are pure state-threading
(each returns a new cache); `lruKey` names the current eviction victim.
Behaviour is pinned by `Spec/Lru.lean`.
-/
