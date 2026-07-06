-- !benchmark @start imports
-- !benchmark @end imports

/-!
# Netaddr.Impl.Cidr

IPv4 CIDR bit-algebra. The headline operations:

* `spanningCidr xs` — the single *smallest* aligned CIDR block that covers every
  block in `xs`.
* `iprangeToCidrs lo hi` — the minimal list of aligned CIDR blocks covering
  exactly the inclusive address range `[lo, hi]`.

Addresses are `Nat` (convention `0 ≤ a < 2^32`); a CIDR block is
`{ network, prefixLen }` with `prefixLen ≤ 32` by convention; the width is fixed
at 32. Mask operations are frozen `Nat` arithmetic on `/`, `*`, `%`, `^`, `==`
(decidable, Mathlib-free). Types and signatures are fixed vocabulary (DO NOT
MODIFY); function bodies are the reference implementations.
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
    top `c.prefixLen` bits agree. Anchored on `/`, `^`, `==`. -/
abbrev memNet (a : Nat) (c : Cidr) : Bool := keyAt a c.prefixLen == keyAt c.network c.prefixLen

/-- Block-aligned base of address `a` at prefix `p`: floor `a` to its block
    boundary, `a / 2^(32-p) * 2^(32-p)` (frozen). -/
abbrev alignBase (a : Nat) (p : Nat) : Nat := a / blockSize p * blockSize p

namespace Netaddr

-- ── API signatures (DO NOT MODIFY) ───────────────────────────

/-- `containsAddr a c`: whether address `a` lies in block `c`. -/
abbrev ContainsAddrSig := Addr → Cidr → Bool

/-- `networkAddr c`: the lowest (aligned) address of block `c`. -/
abbrev NetworkAddrSig := Cidr → Addr

/-- `broadcast c`: the highest address of block `c`. -/
abbrev BroadcastSig := Cidr → Addr

/-- `spanningCidr xs`: the single smallest aligned CIDR block that spans
    (covers) every block in `xs`. For `xs = []` returns the `/0` block. -/
abbrev SpanningCidrSig := List Cidr → Cidr

/-- `iprangeToCidrs lo hi`: the minimal list of aligned CIDR blocks covering
    exactly the inclusive address range `[lo, hi]`. Empty when `hi < lo`. -/
abbrev IprangeToCidrsSig := Addr → Addr → List Cidr

end Netaddr

-- !benchmark @start global_aux
-- !benchmark @end global_aux

-- !benchmark @start code_aux def=containsAddr
-- !benchmark @end code_aux def=containsAddr

def Netaddr.containsAddr : Netaddr.ContainsAddrSig :=
-- !benchmark @start code def=containsAddr
  fun a c => memNet a c
-- !benchmark @end code def=containsAddr

-- !benchmark @start code_aux def=networkAddr
-- !benchmark @end code_aux def=networkAddr

def Netaddr.networkAddr : Netaddr.NetworkAddrSig :=
-- !benchmark @start code def=networkAddr
  fun c => alignBase c.network c.prefixLen
-- !benchmark @end code def=networkAddr

-- !benchmark @start code_aux def=broadcast
-- !benchmark @end code_aux def=broadcast

def Netaddr.broadcast : Netaddr.BroadcastSig :=
-- !benchmark @start code def=broadcast
  fun c => alignBase c.network c.prefixLen + blockSize c.prefixLen - 1
-- !benchmark @end code def=broadcast

-- !benchmark @start code_aux def=spanningCidr
/-- Lowest network base over a list of blocks (their common floor); `0` for the
    empty list. The spanning lower endpoint. -/
def Netaddr.loBase : List Cidr → Nat
  | [] => 0
  | c :: cs => cs.foldr (fun d acc => Nat.min (alignBase d.network d.prefixLen) acc)
                        (alignBase c.network c.prefixLen)

/-- Highest broadcast over a list of blocks (their common ceiling); `0` for the
    empty list. The spanning upper endpoint. -/
def Netaddr.hiBcast : List Cidr → Nat
  | [] => 0
  | c :: cs => cs.foldr (fun d acc => Nat.max (alignBase d.network d.prefixLen + blockSize d.prefixLen - 1) acc)
                        (alignBase c.network c.prefixLen + blockSize c.prefixLen - 1)

/-- Longest common top-bit prefix length of `lo` and `hi`: the largest
    `p ∈ [0, 32]` whose top-`p`-bit keys of `lo` and `hi` agree. -/
def Netaddr.commonPrefix (lo hi : Nat) : Nat :=
  (List.range 33).foldr
    (fun p acc => if lo / blockSize p == hi / blockSize p then Nat.max p acc else acc) 0
-- !benchmark @end code_aux def=spanningCidr

def Netaddr.spanningCidr : Netaddr.SpanningCidrSig :=
-- !benchmark @start code def=spanningCidr
  fun xs =>
    match xs with
    | [] => ⟨0, 0⟩
    | _ =>
      let lo := Netaddr.loBase xs
      let hi := Netaddr.hiBcast xs
      let p := Netaddr.commonPrefix lo hi
      ⟨alignBase lo p, p⟩
-- !benchmark @end code def=spanningCidr

-- !benchmark @start code_aux def=iprangeToCidrs
/-- The prefix length of the largest aligned block based at `lo` that still fits
    inside `[lo, hi]`: the smallest `p ∈ [0, 32]` with `lo % blockSize p = 0` and
    `lo + blockSize p - 1 ≤ hi`. -/
def Netaddr.maxBlockAt (lo hi : Nat) : Nat :=
  (List.range 33).foldr
    (fun p acc =>
      if lo % blockSize p == 0 && decide (lo + blockSize p - 1 ≤ hi) then Nat.min p acc else acc)
    32

/-- Range decomposition with explicit fuel: the worker behind `iprangeToCidrs`. -/
def Netaddr.iprangeGo (lo hi : Nat) : Nat → List Cidr
  | 0 => []
  | fuel + 1 =>
    if hi < lo then []
    else
      let p := Netaddr.maxBlockAt lo hi
      let bs := blockSize p
      ⟨lo, p⟩ :: Netaddr.iprangeGo (lo + bs) hi fuel
-- !benchmark @end code_aux def=iprangeToCidrs

def Netaddr.iprangeToCidrs : Netaddr.IprangeToCidrsSig :=
-- !benchmark @start code def=iprangeToCidrs
  fun lo hi => Netaddr.iprangeGo lo hi (hi + 1 - lo)
-- !benchmark @end code def=iprangeToCidrs
