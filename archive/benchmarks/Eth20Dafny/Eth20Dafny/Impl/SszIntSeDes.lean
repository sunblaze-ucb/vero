-- !benchmark @start imports
-- !benchmark @end imports

/-!
# Eth20Dafny.Impl.SszIntSeDes

Integer serialization and deserialization helpers translated from
`ssz/IntSeDes.dfy`.

DO NOT MODIFY types or signatures — these are the fixed vocabulary.
Implement only the function bodies.
-/

namespace Eth20Dafny

-- API signatures.
abbrev UintSeSig := Nat → Nat → List UInt8
abbrev UintDesSig := List UInt8 → Nat

end Eth20Dafny

-- !benchmark @start global_aux
-- !benchmark @end global_aux

-- ── Reference implementations (LLM task slots) ──────────

-- !benchmark @start code_aux def=uintSe
-- !benchmark @end code_aux def=uintSe

def Eth20Dafny.uintSe : Eth20Dafny.UintSeSig :=
-- !benchmark @start code def=uintSe
  let rec go (n k : Nat) : List UInt8 :=
    match k with
    | 0 => []
    | 1 => [UInt8.ofNat n]
    | k' + 2 => UInt8.ofNat (n % 256) :: go (n / 256) (k' + 1)
    termination_by k
  fun n k => go n k
-- !benchmark @end code def=uintSe

-- !benchmark @start code_aux def=uintDes
-- !benchmark @end code_aux def=uintDes

def Eth20Dafny.uintDes : Eth20Dafny.UintDesSig :=
-- !benchmark @start code def=uintDes
  fun bytes =>
    bytes.foldr (fun b acc => b.toNat + 256 * acc) 0
-- !benchmark @end code def=uintDes
