import Ipaddress.Impl.Cidr

/-!
# Ipaddress.Test

Executable conformance tests. `#guard` assertions run against the curator's
reference implementations inside the `code` markers in `Impl/Cidr.lean`.

A `/24` block has `blockSize = 2^8 = 256`; a `/25` block has `128`; a `/23`
block has `512`. Concrete values below use these.

DO NOT MODIFY — infrastructure.
-/

open Ipaddress

-- ── containsAddr ───────────────────────────────────────────────
-- /24 block based at 0 covers 0..255.
#guard containsAddr 100 ⟨0, 24⟩ == true
#guard containsAddr 255 ⟨0, 24⟩ == true
#guard containsAddr 256 ⟨0, 24⟩ == false        -- first address of the next /24
#guard containsAddr 256 ⟨256, 24⟩ == true        -- second /24 block

-- ── networkAddr ────────────────────────────────────────────────
#guard networkAddr ⟨0, 24⟩ == 0
#guard networkAddr ⟨300, 24⟩ == 256              -- aligns 300 down to its /24 base
#guard networkAddr ⟨5, 32⟩ == 5                  -- /32 is a single host

-- ── broadcast ──────────────────────────────────────────────────
#guard broadcast ⟨0, 24⟩ == 255
#guard broadcast ⟨256, 24⟩ == 511
#guard broadcast ⟨5, 32⟩ == 5                    -- single host: broadcast = network

-- ── supernet ───────────────────────────────────────────────────
#guard supernet ⟨0, 24⟩ == ⟨0, 23⟩
#guard supernet ⟨256, 24⟩ == ⟨0, 23⟩             -- sibling of 0/24 shares the /23 parent
#guard supernet ⟨512, 24⟩ == ⟨512, 23⟩

-- ── collapse: drop subsumed blocks, dedup, keep maximal set ────
-- 0/25 (0..127) is nested inside 0/24 (0..255), so it is dropped.
#guard collapse [⟨0, 24⟩, ⟨0, 25⟩] == [⟨0, 24⟩]
-- duplicates collapse to one.
#guard collapse [⟨0, 24⟩, ⟨0, 24⟩] == [⟨0, 24⟩]
-- two disjoint, non-nested /24 blocks both survive (no merging is performed).
#guard collapse [⟨0, 24⟩, ⟨256, 24⟩] == [⟨0, 24⟩, ⟨256, 24⟩]
-- empty input collapses to empty.
#guard collapse ([] : List Cidr) == []
