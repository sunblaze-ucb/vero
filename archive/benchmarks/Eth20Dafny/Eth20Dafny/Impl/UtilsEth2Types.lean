import Eth20Dafny.Impl.Utils.Nativetypes
-- !benchmark @start imports
-- !benchmark @end imports

/-!
# Eth20Dafny.Impl.UtilsEth2Types

Core foundation types for Eth2 serialisation helpers.
-/


-- !benchmark @start global_aux
-- !benchmark @end global_aux

namespace Eth20Dafny

abbrev bytes := List (UInt8)

abbrev Seq32Byte := List (UInt8)

abbrev chunk := Seq32Byte

abbrev hash32 := Seq32Byte

inductive Tipe where
  | Uint8_
  | Uint16_
  | Uint32_
  | Uint64_
  | Uint128_
  | Uint256_
  | Bool_
  | Bitlist_ (a0 : Nat)
  | Bitvector_ (a0 : Nat)
  | Bytes_ (a0 : Nat)
  | Container_
  | List_ (a0 : Tipe) (a1 : Nat)
  | Vector_ (a0 : Tipe) (a1 : Nat)

inductive RawSerialisable where
  | Uint8 (a0 : Nat)
  | Uint16 (a0 : Nat)
  | Uint32 (a0 : Nat)
  | Uint64 (a0 : Nat)
  | Uint128 (a0 : Nat)
  | Uint256 (a0 : Nat)
  | Bool (a0 : Bool)
  | Bitlist (a0 : List (Bool)) (a1 : Nat)
  | Bitvector (a0 : List (Bool))
  | Bytes (a0 : List (UInt8))
  | List (a0 : List (RawSerialisable)) (a1 : Tipe) (a2 : Nat)
  | Vector (a0 : List (RawSerialisable))
  | Container (a0 : List (RawSerialisable))

def wellTyped : RawSerialisable → Prop
  | RawSerialisable.Bool _ => True
  | RawSerialisable.Uint8 n => n < 256
  | RawSerialisable.Uint16 n => n < 65536
  | RawSerialisable.Uint32 n => n < 4294967296
  | RawSerialisable.Uint64 n => n < 18446744073709551616
  | RawSerialisable.Uint128 _ => True
  | RawSerialisable.Uint256 _ => True
  | RawSerialisable.Bitlist xs limit => xs.length ≤ limit
  | RawSerialisable.Bitvector xs => 0 < xs.length
  | RawSerialisable.Bytes xs => 0 < xs.length
  | RawSerialisable.Container xs => ∀ x, x ∈ xs → wellTyped x
  | RawSerialisable.List xs _ limit => xs.length ≤ limit ∧ ∀ x, x ∈ xs → wellTyped x
  | RawSerialisable.Vector xs => 0 < xs.length ∧ ∀ x, x ∈ xs → wellTyped x

abbrev Serialisable := RawSerialisable

abbrev Bytes4 := Serialisable

abbrev Bytes32 := Serialisable

abbrev Bytes48 := Serialisable

abbrev Bytes96 := Serialisable

abbrev Root := Bytes32

def isBasicTipe : Tipe → Prop
  | Tipe.Uint8_ => True
  | Tipe.Uint16_ => True
  | Tipe.Uint32_ => True
  | Tipe.Uint64_ => True
  | Tipe.Uint128_ => True
  | Tipe.Uint256_ => True
  | Tipe.Bool_ => True
  | _ => False

abbrev String := List (Char)

abbrev Hash := Bytes32

abbrev BLSPubkey := Bytes48

abbrev BLSSignature := String

abbrev Slot := uint64

abbrev Gwei := uint64

abbrev Epoch := uint64

abbrev CommitteeIndex := uint64

abbrev ValidatorIndex := uint64

abbrev DomainType := Bytes4

def typeOf : RawSerialisable → Tipe
  | RawSerialisable.Bool _ => Tipe.Bool_
  | RawSerialisable.Uint8 _ => Tipe.Uint8_
  | RawSerialisable.Uint16 _ => Tipe.Uint16_
  | RawSerialisable.Uint32 _ => Tipe.Uint32_
  | RawSerialisable.Uint64 _ => Tipe.Uint64_
  | RawSerialisable.Uint128 _ => Tipe.Uint128_
  | RawSerialisable.Uint256 _ => Tipe.Uint256_
  | RawSerialisable.Bitlist _ limit => Tipe.Bitlist_ limit
  | RawSerialisable.Bitvector xs => Tipe.Bitvector_ xs.length
  | RawSerialisable.Bytes xs => Tipe.Bytes_ xs.length
  | RawSerialisable.Container _ => Tipe.Container_
  | RawSerialisable.List _ tipe limit => Tipe.List_ tipe limit
  | RawSerialisable.Vector xs =>
    match xs with
    | [] => Tipe.Vector_ Tipe.Bool_ 0
    | x :: _ => Tipe.Vector_ (typeOf x) xs.length

end Eth20Dafny
