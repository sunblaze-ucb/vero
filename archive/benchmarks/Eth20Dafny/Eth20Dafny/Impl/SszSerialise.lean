import Eth20Dafny.Impl.UtilsEth2Types
import Eth20Dafny.Impl.UtilsHelpers
import Eth20Dafny.Impl.SszBytesAndBits
import Eth20Dafny.Impl.SszBoolSeDes
import Eth20Dafny.Impl.SszIntSeDes
import Eth20Dafny.Impl.SszBitListSeDes
import Eth20Dafny.Impl.SszBitVectorSeDes

-- !benchmark @start imports
-- !benchmark @end imports

/-!
# Eth20Dafny.Impl.SszSerialise

SSZ serialisation helpers translated from `ssz/Serialise.dfy`.

DO NOT MODIFY types or signatures — these are the fixed vocabulary.
Implement only the reference implementations.
-/

namespace Eth20Dafny

-- API signatures.
abbrev SizeOfSig := Serialisable → Nat
abbrev DefaultSig := Tipe → Serialisable
abbrev SerialiseSig := Serialisable → List UInt8
abbrev SerialiseSeqOfBasicsSig := List Serialisable → List UInt8
abbrev DeserialiseSig := List UInt8 → Tipe → Try Serialisable

end Eth20Dafny

-- !benchmark @start global_aux
-- !benchmark @end global_aux

-- ── Reference implementations (LLM task slots) ──────────

-- !benchmark @start code_aux def=sizeOf
-- !benchmark @end code_aux def=sizeOf

def Eth20Dafny.sizeOf : Eth20Dafny.SizeOfSig :=
-- !benchmark @start code def=sizeOf
  fun s =>
    match s with
    | RawSerialisable.Bool _ => 1
    | RawSerialisable.Uint8 _ => 1
    | RawSerialisable.Uint16 _ => 2
    | RawSerialisable.Uint32 _ => 4
    | RawSerialisable.Uint64 _ => 8
    | RawSerialisable.Uint128 _ => 16
    | RawSerialisable.Uint256 _ => 32
    | _ => 0
-- !benchmark @end code def=sizeOf

-- !benchmark @start code_aux def=default
-- !benchmark @end code_aux def=default

def Eth20Dafny.default : Eth20Dafny.DefaultSig :=
-- !benchmark @start code def=default
  fun t =>
    match t with
    | Tipe.Bool_ => RawSerialisable.Bool false
    | Tipe.Uint8_ => RawSerialisable.Uint8 0
    | Tipe.Uint16_ => RawSerialisable.Uint16 0
    | Tipe.Uint32_ => RawSerialisable.Uint32 0
    | Tipe.Uint64_ => RawSerialisable.Uint64 0
    | Tipe.Uint128_ => RawSerialisable.Uint128 0
    | Tipe.Uint256_ => RawSerialisable.Uint256 0
    | Tipe.Bitlist_ limit => RawSerialisable.Bitlist [] limit
    | Tipe.Bitvector_ len => RawSerialisable.Bitvector (timeSeq false len)
    | Tipe.Bytes_ len => RawSerialisable.Bytes (timeSeq 0 len)
    | _ => RawSerialisable.Bytes []
-- !benchmark @end code def=default

-- !benchmark @start code_aux def=serialise
-- !benchmark @end code_aux def=serialise

def Eth20Dafny.serialise : Eth20Dafny.SerialiseSig :=
-- !benchmark @start code def=serialise
  fun s =>
    match s with
    | RawSerialisable.Bool b => boolToBytes b
    | RawSerialisable.Uint8 n => uintSe n 1
    | RawSerialisable.Uint16 n => uintSe n 2
    | RawSerialisable.Uint32 n => uintSe n 4
    | RawSerialisable.Uint64 n => uintSe n 8
    | RawSerialisable.Uint128 n => uintSe n 16
    | RawSerialisable.Uint256 n => uintSe n 32
    | RawSerialisable.Bitlist bits _ => fromBitlistToBytes bits
    | RawSerialisable.Bitvector bits => fromBitvectorToBytes bits
    | RawSerialisable.Bytes bs => bs
    | RawSerialisable.List l _ _ =>
      let rec goList : List Serialisable → List UInt8
        | [] => []
        | RawSerialisable.Bool b :: xs => boolToBytes b ++ goList xs
        | RawSerialisable.Uint8 n :: xs => uintSe n 1 ++ goList xs
        | RawSerialisable.Uint16 n :: xs => uintSe n 2 ++ goList xs
        | RawSerialisable.Uint32 n :: xs => uintSe n 4 ++ goList xs
        | RawSerialisable.Uint64 n :: xs => uintSe n 8 ++ goList xs
        | RawSerialisable.Uint128 n :: xs => uintSe n 16 ++ goList xs
        | RawSerialisable.Uint256 n :: xs => uintSe n 32 ++ goList xs
        | _ :: xs => goList xs
      goList l
    | RawSerialisable.Vector v =>
      let rec goVector : List Serialisable → List UInt8
        | [] => []
        | RawSerialisable.Bool b :: xs => boolToBytes b ++ goVector xs
        | RawSerialisable.Uint8 n :: xs => uintSe n 1 ++ goVector xs
        | RawSerialisable.Uint16 n :: xs => uintSe n 2 ++ goVector xs
        | RawSerialisable.Uint32 n :: xs => uintSe n 4 ++ goVector xs
        | RawSerialisable.Uint64 n :: xs => uintSe n 8 ++ goVector xs
        | RawSerialisable.Uint128 n :: xs => uintSe n 16 ++ goVector xs
        | RawSerialisable.Uint256 n :: xs => uintSe n 32 ++ goVector xs
        | _ :: xs => goVector xs
      goVector v
    | RawSerialisable.Container _ => []
-- !benchmark @end code def=serialise

-- !benchmark @start code_aux def=serialiseSeqOfBasics
-- !benchmark @end code_aux def=serialiseSeqOfBasics

def Eth20Dafny.serialiseSeqOfBasics : Eth20Dafny.SerialiseSeqOfBasicsSig :=
-- !benchmark @start code def=serialiseSeqOfBasics
  let rec go : List Serialisable → List UInt8
    | [] => []
    | RawSerialisable.Bool b :: xs => boolToBytes b ++ go xs
    | RawSerialisable.Uint8 n :: xs => uintSe n 1 ++ go xs
    | RawSerialisable.Uint16 n :: xs => uintSe n 2 ++ go xs
    | RawSerialisable.Uint32 n :: xs => uintSe n 4 ++ go xs
    | RawSerialisable.Uint64 n :: xs => uintSe n 8 ++ go xs
    | RawSerialisable.Uint128 n :: xs => uintSe n 16 ++ go xs
    | RawSerialisable.Uint256 n :: xs => uintSe n 32 ++ go xs
    | _ :: xs => go xs
  fun s => go s
-- !benchmark @end code def=serialiseSeqOfBasics

-- !benchmark @start code_aux def=deserialise
-- !benchmark @end code_aux def=deserialise

def Eth20Dafny.deserialise : Eth20Dafny.DeserialiseSig :=
-- !benchmark @start code def=deserialise
  fun xs t =>
    match t with
    | Tipe.Bool_ =>
      if xs.length = 1 && xs[0]!.toNat ≤ 1 then
        Try.Success (RawSerialisable.Bool (boolSeDesByteToBool xs))
      else
        Try.Failure
    | Tipe.Uint8_ =>
      if xs.length = 1 then
        Try.Success (RawSerialisable.Uint8 (uintDes xs))
      else
        Try.Failure
    | Tipe.Uint16_ =>
      if xs.length = 2 then
        Try.Success (RawSerialisable.Uint16 (uintDes xs))
      else
        Try.Failure
    | Tipe.Uint32_ =>
      if xs.length = 4 then
        Try.Success (RawSerialisable.Uint32 (uintDes xs))
      else
        Try.Failure
    | Tipe.Uint64_ =>
      if xs.length = 8 then
        Try.Success (RawSerialisable.Uint64 (uintDes xs))
      else
        Try.Failure
    | Tipe.Uint128_ =>
      if xs.length = 16 then
        Try.Success (RawSerialisable.Uint128 (uintDes xs))
      else
        Try.Failure
    | Tipe.Uint256_ =>
      if xs.length = 32 then
        Try.Success (RawSerialisable.Uint256 (uintDes xs))
      else
        Try.Failure
    | Tipe.Bitlist_ limit =>
      if xs ≠ [] ∧ (xs.getD (xs.length - 1) (0 : UInt8)).toNat > 0 then
        let desBl := fromBytesToBitList xs
        if desBl.length ≤ limit then
          Try.Success (RawSerialisable.Bitlist desBl limit)
        else
          Try.Failure
      else
        Try.Failure
    | Tipe.Bitvector_ len =>
      if 0 < xs.length && xs.length = (len + 7) / 8 then
        Try.Success (RawSerialisable.Bitvector (fromBytesToBitVector xs len))
      else
        Try.Failure
    | Tipe.Bytes_ len =>
      if xs.length > 0 && xs.length = len then
        Try.Success (RawSerialisable.Bytes xs)
      else
        Try.Failure
    | Tipe.Container_ =>
      Try.Failure
    | Tipe.List_ _ _ =>
      Try.Failure
    | Tipe.Vector_ _ _ =>
      Try.Failure
-- !benchmark @end code def=deserialise
