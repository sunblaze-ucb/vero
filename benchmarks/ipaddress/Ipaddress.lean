import Ipaddress.Impl.Cidr
import Ipaddress.Bundle
import Ipaddress.Harness
import Ipaddress.Spec.Cidr
import Ipaddress.Test

/-!
# Ipaddress

Root import hub for the IPv4 CIDR-algebra benchmark.

The headline operation is `collapse`: reduce a list of CIDR blocks to the
canonical set of maximal blocks covering the same address set. Supporting APIs
pin `containsAddr` / `networkAddr` / `broadcast` / `supernet`. Behaviour is
pinned by `Spec/Cidr.lean`.

## Deliberate scope

`collapse` performs contained-block removal plus dedup: it drops every block
subsumed by a strictly less-specific block in the input and removes duplicates,
yielding the maximal-block (non-subsumed, deduped) set. It does NOT coalesce
adjacent siblings — it does NOT merge `0.0.0.0/25` + `0.0.0.128/25` into
`0.0.0.0/24`. `supernet` here is the one-level parent block (prefix length
`- 1`); it takes no prefix-difference argument.
-/
