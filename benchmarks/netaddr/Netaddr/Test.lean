import Netaddr.Impl.Cidr

/-!
# Netaddr.Test

Executable conformance tests. `#guard` assertions run against the curator's
reference implementations inside the `code` markers in `Impl/Cidr.lean`.

A `/24` block has `blockSize = 2^8 = 256`; a `/25` block has `128`; a `/23`
block has `512`. Concrete values below use these.

DO NOT MODIFY — infrastructure.
-/

open Netaddr

-- ── containsAddr / networkAddr / broadcast ─────────────────────
#guard containsAddr 100 ⟨0, 24⟩ == true
#guard containsAddr 256 ⟨0, 24⟩ == false
#guard networkAddr ⟨300, 24⟩ == 256
#guard broadcast ⟨0, 24⟩ == 255

-- ── spanningCidr: smallest aligned block spanning the inputs ───
-- 0/25 (0..127) and 128/25 (128..255) span exactly the /24 0..255.
#guard spanningCidr [⟨0, 25⟩, ⟨128, 25⟩] == ⟨0, 24⟩
-- a single aligned block spans itself.
#guard spanningCidr [⟨0, 24⟩] == ⟨0, 24⟩
-- two disjoint /24s (0..255 and 256..511) span the /23 0..511.
#guard spanningCidr [⟨0, 24⟩, ⟨256, 24⟩] == ⟨0, 23⟩
-- empty input → /0.
#guard spanningCidr ([] : List Cidr) == ⟨0, 0⟩

-- ── iprangeToCidrs: minimal aligned cover of [lo, hi] ──────────
-- [0, 255] is exactly the /24 0/24.
#guard iprangeToCidrs 0 255 == [⟨0, 24⟩]
-- a single point is a /32 host.
#guard iprangeToCidrs 5 5 == [⟨5, 32⟩]
-- [0, 2] needs a /31 (0..1) then a /32 (2).
#guard iprangeToCidrs 0 2 == [⟨0, 31⟩, ⟨2, 32⟩]
-- empty when hi < lo.
#guard iprangeToCidrs 10 5 == []
-- a /23-sized range [0, 511] is a single /23 block.
#guard iprangeToCidrs 0 511 == [⟨0, 23⟩]
-- an unaligned range [1, 4] splits into /32(1), /31(2..3), /32(4).
#guard iprangeToCidrs 1 4 == [⟨1, 32⟩, ⟨2, 31⟩, ⟨4, 32⟩]
