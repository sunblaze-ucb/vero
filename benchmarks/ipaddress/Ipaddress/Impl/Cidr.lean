-- !benchmark @start imports
-- !benchmark @end imports

/-!
# Ipaddress.Impl.Cidr

IPv4 CIDR-block algebra. The headline operation is `collapse`: reduce a list of
CIDR blocks to the canonical set of *maximal* blocks covering the same address
set — every block subsumed by a less-specific block in the list is dropped and
duplicates are removed.

Addresses are `Nat` (by convention `0 ≤ a < 2^32`). A CIDR block is
`{ network, prefixLen }` with `prefixLen ≤ 32` by convention, covering the
`2^(32 - prefixLen)` addresses that share its top `prefixLen` bits. Mask
operations are expressed as frozen `Nat` arithmetic on `/`, `*`, `%`, `^`, `==`,
keeping the vocabulary decidable and Mathlib-free.

Types and signatures are fixed vocabulary (DO NOT MODIFY).
-/

-- ── Core data types (DO NOT MODIFY) ──────────────────────────

/-- An IPv4 address as a natural number; by convention `0 ≤ a < 2^32`. -/
abbrev Addr := Nat

/-- A CIDR block: a network base address plus a prefix length
    (`0 ≤ prefixLen ≤ 32` by convention). The block covers the
    `2^(32 - prefixLen)` addresses sharing its top `prefixLen` bits. -/
structure Cidr where
  network   : Nat
  prefixLen : Nat
deriving DecidableEq, Repr

/-- The number of addresses in a block of prefix length `p`:
    `2^(32 - p)` (frozen). -/
abbrev blockSize (p : Nat) : Nat := 2 ^ (32 - p)

/-- The "network key" of address `a` at prefix length `p`: its top `p` bits,
    computed as `a / 2^(32 - p)` (frozen). Two addresses lie in the same
    `/p` block iff they share this key. -/
abbrev keyAt (a : Nat) (p : Nat) : Nat := a / blockSize p

/-- Membership predicate (frozen): address `a` lies in block `c` iff their
    top `c.prefixLen` bits agree. -/
abbrev memNet (a : Nat) (c : Cidr) : Bool := keyAt a c.prefixLen == keyAt c.network c.prefixLen

/-- A nested chain of blocks all based at network `0` (frozen test vocabulary):
    `nestedChain n = [⟨0,n⟩, ⟨0,n-1⟩, …, ⟨0,1⟩, ⟨0,0⟩]`. -/
def nestedChain : Nat → List Cidr
  | 0     => [⟨0, 0⟩]
  | n + 1 => ⟨0, n + 1⟩ :: nestedChain n

namespace Ipaddress

-- ── API signatures (DO NOT MODIFY) ───────────────────────────

/-- `containsAddr a c`: whether address `a` lies in block `c`. -/
abbrev ContainsAddrSig := Addr → Cidr → Bool

/-- `networkAddr c`: the lowest (aligned) address of block `c`. -/
abbrev NetworkAddrSig := Cidr → Addr

/-- `broadcast c`: the highest address of block `c`. -/
abbrev BroadcastSig := Cidr → Addr

/-- `supernet c`: the parent block at prefix length `prefixLen - 1`
    (one bit less specific), aligned down. -/
abbrev SupernetSig := Cidr → Cidr

/-- `collapse xs`: the canonical set of maximal blocks covering the same
    address set as `xs` — every block subsumed by a strictly less-specific
    block in `xs` is dropped, and duplicates removed. -/
abbrev CollapseSig := List Cidr → List Cidr

end Ipaddress

-- !benchmark @start global_aux
-- !benchmark @end global_aux

-- !benchmark @start code_aux def=containsAddr
-- !benchmark @end code_aux def=containsAddr

def Ipaddress.containsAddr : Ipaddress.ContainsAddrSig :=
-- !benchmark @start code def=containsAddr
  fun a c => memNet a c
-- !benchmark @end code def=containsAddr

-- !benchmark @start code_aux def=networkAddr
-- !benchmark @end code_aux def=networkAddr

def Ipaddress.networkAddr : Ipaddress.NetworkAddrSig :=
-- !benchmark @start code def=networkAddr
  fun c => (c.network / blockSize c.prefixLen) * blockSize c.prefixLen
-- !benchmark @end code def=networkAddr

-- !benchmark @start code_aux def=broadcast
-- !benchmark @end code_aux def=broadcast

def Ipaddress.broadcast : Ipaddress.BroadcastSig :=
-- !benchmark @start code def=broadcast
  fun c => (c.network / blockSize c.prefixLen) * blockSize c.prefixLen + blockSize c.prefixLen - 1
-- !benchmark @end code def=broadcast

-- !benchmark @start code_aux def=supernet
-- !benchmark @end code_aux def=supernet

def Ipaddress.supernet : Ipaddress.SupernetSig :=
-- !benchmark @start code def=supernet
  fun c =>
    { network := (c.network / blockSize (c.prefixLen - 1)) * blockSize (c.prefixLen - 1),
      prefixLen := c.prefixLen - 1 }
-- !benchmark @end code def=supernet

-- !benchmark @start code_aux def=collapse
/-- `coveredBy c xs`: some block in `xs` is strictly less specific than `c`
    (`prefixLen` strictly smaller) and contains `c`'s network address. -/
def Ipaddress.coveredBy (c : Cidr) (xs : List Cidr) : Bool :=
  xs.any (fun d => (d.prefixLen < c.prefixLen) && memNet c.network d)
-- !benchmark @end code_aux def=collapse

def Ipaddress.collapse : Ipaddress.CollapseSig :=
-- !benchmark @start code def=collapse
  fun xs => (xs.filter (fun c => !Ipaddress.coveredBy c xs)).eraseDups
-- !benchmark @end code def=collapse
