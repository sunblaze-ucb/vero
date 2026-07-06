-- !benchmark @start imports
-- !benchmark @end imports

/-!
# Pyradix.Impl.Radix

Longest-prefix-match operations over a CIDR prefix table (a `Table` is an
association list of `(net, plen, value)` entries). The headline operation
`searchBest t q` returns the most-specific stored prefix that covers the
query address `q`; `searchWorst` is the least-specific dual; `searchExact`,
`add`, `delete`, and `covered` round out the API. Addresses and networks are
`Nat`; prefix lengths satisfy `plen ≤ W` for a fixed width `W`. Behaviour is
pinned by `Spec/Radix.lean`.
-/

-- ── Core data types (DO NOT MODIFY) ──────────────────────────

namespace Pyradix

/-- The address bit width. Addresses are `Nat` values intended to lie in
    `[0, 2^W)`; prefix lengths satisfy `plen ≤ W`. Fixed at the IPv4
    width 32. This is curator-frozen vocabulary, not an API. -/
def W : Nat := 32

/-- A stored CIDR prefix entry: a network number `net`, a prefix length
    `plen` (number of leading significant bits, `plen ≤ W`), and an
    associated `value`. -/
structure Prefix where
  net   : Nat
  plen  : Nat
  value : Nat
deriving DecidableEq, Repr

end Pyradix

/-- A radix tree, modelled as an association list of prefix entries. The
    first matching entry wins on exact lookup; the most-specific or
    least-specific covering entry is selected by `searchBest` and
    `searchWorst`. -/
abbrev Table := List Pyradix.Prefix

namespace Pyradix

-- ── API signatures (DO NOT MODIFY) ───────────────────────────

/-- `searchBest t q`: the stored prefix that is the *most specific*
    (longest `plen`) prefix covering address `q`, or `none` if no stored
    prefix covers `q`. The longest-prefix match. -/
abbrev SearchBestSig  := Table → Nat → Option Prefix

/-- `searchWorst t q`: the stored prefix that is the *least specific*
    (shortest `plen`) prefix covering address `q`, or `none`. The dual of
    `searchBest`. -/
abbrev SearchWorstSig := Table → Nat → Option Prefix

/-- `searchExact t net plen`: the stored entry whose network and prefix
    length exactly equal `(net, plen)` (compared on the masked network),
    or `none`. -/
abbrev SearchExactSig := Table → Nat → Nat → Option Prefix

/-- `add t p`: insert prefix `p`, replacing any existing entry with the
    same masked network and prefix length. -/
abbrev AddSig         := Table → Prefix → Table

/-- `delete t net plen`: remove every entry with the given masked network
    and prefix length. -/
abbrev DeleteSig      := Table → Nat → Nat → Table

/-- `covered t net plen`: every stored entry whose prefix lies *inside*
    the query prefix `(net, plen)` — i.e. entries at least as specific
    (`plen' ≥ plen`) whose network is covered by `(net, plen)`. -/
abbrev CoveredSig     := Table → Nat → Nat → List Prefix

end Pyradix

-- !benchmark @start global_aux
-- !benchmark @end global_aux

-- !benchmark @start code_aux def=searchBest
/-- `maskTo p x`: the top `p` bits of `x`, read as a number. Two addresses
    share a `p`-bit prefix exactly when their `maskTo p` values are equal.
    Frozen helper. -/
def maskTo (p x : Nat) : Nat := x / 2 ^ (Pyradix.W - p)

/-- `covers net plen q`: does the CIDR prefix `(net, plen)` cover the
    address `q`? True when `net` and `q` agree on their top `plen` bits. -/
def covers (net plen q : Nat) : Bool := maskTo plen net == maskTo plen q

/-- `samePrefix net₁ plen₁ net₂ plen₂`: do two entries denote the same
    CIDR block? Same masked network and same length. -/
def samePrefix (net₁ plen₁ net₂ plen₂ : Nat) : Bool :=
  plen₁ == plen₂ && maskTo plen₁ net₁ == maskTo plen₂ net₂
-- !benchmark @end code_aux def=searchBest

def Pyradix.searchBest : Pyradix.SearchBestSig :=
-- !benchmark @start code def=searchBest
  fun t q =>
    (t.filter (fun p => covers p.net p.plen q)).foldl
      (fun acc p =>
        match acc with
        | none => some p
        | some best => if best.plen < p.plen then some p else some best)
      none
-- !benchmark @end code def=searchBest

-- !benchmark @start code_aux def=searchWorst
-- !benchmark @end code_aux def=searchWorst

def Pyradix.searchWorst : Pyradix.SearchWorstSig :=
-- !benchmark @start code def=searchWorst
  fun t q =>
    (t.filter (fun p => covers p.net p.plen q)).foldl
      (fun acc p =>
        match acc with
        | none => some p
        | some best => if p.plen < best.plen then some p else some best)
      none
-- !benchmark @end code def=searchWorst

-- !benchmark @start code_aux def=searchExact
-- !benchmark @end code_aux def=searchExact

def Pyradix.searchExact : Pyradix.SearchExactSig :=
-- !benchmark @start code def=searchExact
  fun t net plen => t.find? (fun p => samePrefix p.net p.plen net plen)
-- !benchmark @end code def=searchExact

-- !benchmark @start code_aux def=add
-- !benchmark @end code_aux def=add

def Pyradix.add : Pyradix.AddSig :=
-- !benchmark @start code def=add
  fun t p => p :: t.filter (fun q => !(samePrefix q.net q.plen p.net p.plen))
-- !benchmark @end code def=add

-- !benchmark @start code_aux def=delete
-- !benchmark @end code_aux def=delete

def Pyradix.delete : Pyradix.DeleteSig :=
-- !benchmark @start code def=delete
  fun t net plen => t.filter (fun q => !(samePrefix q.net q.plen net plen))
-- !benchmark @end code def=delete

-- !benchmark @start code_aux def=covered
-- !benchmark @end code_aux def=covered

def Pyradix.covered : Pyradix.CoveredSig :=
-- !benchmark @start code def=covered
  fun t net plen => t.filter (fun p => plen ≤ p.plen && covers net plen p.net)
-- !benchmark @end code def=covered
