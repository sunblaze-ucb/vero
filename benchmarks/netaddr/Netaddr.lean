import Netaddr.Impl.Cidr
import Netaddr.Bundle
import Netaddr.Harness
import Netaddr.Spec.Cidr
import Netaddr.Test

/-!
# Netaddr

Root import hub for the IPv4 CIDR bit-algebra benchmark. Addresses are `Nat`
(convention `0 ≤ a < 2^32`); a CIDR block is `{ network, prefixLen }`. The two
headline operations, each pinned to a unique answer:

* `spanningCidr xs` — the single *smallest* aligned CIDR block that covers every
  block in `xs`.
* `iprangeToCidrs lo hi` — the *minimal* list of aligned CIDR blocks covering
  exactly the inclusive range `[lo, hi]`.

Behaviour is pinned by `Spec/Cidr.lean`. The address width is fixed at 32 (IPv4).
-/
