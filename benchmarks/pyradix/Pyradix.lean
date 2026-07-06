import Pyradix.Impl.Radix
import Pyradix.Bundle
import Pyradix.Harness
import Pyradix.Spec.Radix
import Pyradix.Test

/-!
# Pyradix

Root import hub for the longest-prefix-match benchmark over a CIDR prefix
table. A `Table` is an association list of `(net, plen, value)` entries.
`searchBest t q` returns the stored prefix that is the most specific
(longest `plen`) prefix covering address `q`; `searchWorst` is the
least-specific dual; `searchExact` is exact-block lookup; `covered` is the
subset of entries contained in a query block; `add`/`delete` are the
update operations. Coverage means bit-prefix containment over `Nat`
addresses at a fixed width `W = 32`. Behaviour is pinned by
`Spec/Radix.lean`.
-/
