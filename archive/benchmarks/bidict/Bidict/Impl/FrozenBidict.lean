import Bidict.Impl.BidictBase

-- !benchmark @start imports
-- !benchmark @end imports

/-!
# Bidict.Impl.FrozenBidict

Hash utility for frozen bidictional mappings. `frozenBidictHash` computes an
order-independent hash of a `BidictBase` by combining per-pair hash values
commutatively, so that two bidicts with the same key-value pairs (regardless
of insertion order) yield equal hashes.

DO NOT MODIFY types or signatures — these are the fixed vocabulary.
Implement only the function bodies.
-/

variable {KT VT : Type} [BEq KT] [BEq VT] [Hashable KT] [Hashable VT]

namespace Bidict

-- ── API signatures (DO NOT MODIFY) ───────────────────────────

/-- Hash signature: order-independent integer hash of a bidict's contents. -/
abbrev FrozenBidictHashSig := BidictBase KT VT → Int

end Bidict

-- !benchmark @start global_aux
-- !benchmark @end global_aux

-- ── frozenBidictHash ──────────────────────────────────────────

-- !benchmark @start code_aux def=frozenBidictHash
-- !benchmark @end code_aux def=frozenBidictHash

def Bidict.frozenBidictHash (self : BidictBase KT VT) : Int :=
-- !benchmark @start code def=frozenBidictHash
  -- Sum of (hash k + hash v) per pair — commutative so order-independent.
  self.foldl (fun acc (k, v) =>
    acc + Int.ofNat (hash k).toNat + Int.ofNat (hash v).toNat) 0
-- !benchmark @end code def=frozenBidictHash
