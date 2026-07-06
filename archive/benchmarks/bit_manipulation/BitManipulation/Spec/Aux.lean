import BitManipulation.Harness

/-!
# BitManipulation.Spec.Aux

Reference helpers shared across spec modules. Mirror the upstream
`BitHelpers` reference implementation used by PR #75 spec theorems
(byte-exact-output obligations). Importing this module gives every
spec file access to a canonical reference for each API.

DO NOT MODIFY — frozen curator-given content.
-/

namespace BitHelpers

/-- `1 <<< position.toNat`, the single-bit mask at `position` (treated as `Nat`). -/
def bitMask (position : Int) : Nat :=
  Nat.shiftLeft 1 position.toNat

/-- Reference: `Nat.toDigits 2 n` — Python-style binary digit list (no leading zero, MSB first). -/
def binaryDigits (n : Nat) : List Char :=
  Nat.toDigits 2 n

/-- Pad `digits` with leading `'0'`s on the left until length `width`. -/
def padLeft (width : Nat) (digits : List Char) : List Char :=
  List.replicate (width - digits.length) '0' ++ digits

/-- Prepend `"0b"` to a digit list to form a Python-style binary literal. -/
def binaryStringFromDigits (digits : List Char) : String :=
  "0b" ++ String.ofList digits

/-- Convenience: `binaryStringFromDigits (binaryDigits n)`. -/
def binaryString (n : Nat) : String :=
  binaryStringFromDigits (binaryDigits n)

/-- Pad both operands to the common width and zip with `op`, then re-prefix `"0b"`. -/
def binaryZipString (op : Char → Char → Char) (a b : Nat) : String :=
  let aDigits := binaryDigits a
  let bDigits := binaryDigits b
  let width := Nat.max aDigits.length bDigits.length
  binaryStringFromDigits (List.zipWith op (padLeft width aDigits) (padLeft width bDigits))

/-- `'1'` if `b`, else `'0'`. -/
def boolDigit (b : Bool) : Char :=
  if b then '1' else '0'

/-- Reference for `binary_and`. -/
def binaryAndString (a b : Int) : String :=
  binaryZipString
    (fun x y => boolDigit (x == '1' && y == '1'))
    a.toNat
    b.toNat

/-- Reference for `binary_or`. -/
def binaryOrString (a b : Int) : String :=
  binaryZipString
    (fun x y => boolDigit (x == '1' || y == '1'))
    a.toNat
    b.toNat

/-- Reference for `binary_xor`. -/
def binaryXorString (a b : Int) : String :=
  binaryZipString
    (fun x y => boolDigit (x != y))
    a.toNat
    b.toNat

/-- Bit-list payload (after `"0b"`) for the two's complement of an integer. -/
def twosComplementPayload (number : Int) : List Char :=
  if number < 0 then
    let magnitude := number.natAbs
    let width := (binaryDigits magnitude).length
    let tail := binaryDigits ((2 ^ width) - magnitude)
    '1' :: padLeft width tail
  else
    ['0']

/-- Reference for `twos_complement`. -/
def twosComplementString (number : Int) : String :=
  binaryStringFromDigits (twosComplementPayload number)

/-- Reference for `logical_left_shift`. -/
def logicalLeftShiftString (number shiftAmount : Int) : String :=
  binaryStringFromDigits
    (binaryDigits number.toNat ++ List.replicate shiftAmount.toNat '0')

/-- Reference for `logical_right_shift`. -/
def logicalRightShiftString (number shiftAmount : Int) : String :=
  let digits := binaryDigits number.toNat
  let shift := shiftAmount.toNat
  if shift ≥ digits.length then
    "0b0"
  else
    binaryStringFromDigits (digits.take (digits.length - shift))

/-- Bit-list payload for arithmetic right shift. -/
def arithmeticRightShiftPayload (number shiftAmount : Int) : List Char :=
  let digits :=
    if number ≥ 0 then
      '0' :: binaryDigits number.toNat
    else
      twosComplementPayload number
  let shift := shiftAmount.toNat
  let sign := digits.head?.getD '0'
  if shift ≥ digits.length then
    List.replicate digits.length sign
  else
    List.replicate shift sign ++ digits.take (digits.length - shift)

/-- Reference for `arithmetic_right_shift`. -/
def arithmeticRightShiftString (number shiftAmount : Int) : String :=
  binaryStringFromDigits (arithmeticRightShiftPayload number shiftAmount)

/-- Reference for `set_bit`. -/
def setBitValue (number position : Int) : Int :=
  Int.ofNat (Nat.lor number.toNat (bitMask position))

/-- Reference for `clear_bit`. -/
def clearBitValue (number position : Int) : Int :=
  let n := number.toNat
  let mask := bitMask position
  if Nat.land n mask == 0 then
    Int.ofNat n
  else
    Int.ofNat (n - mask)

/-- Reference for `flip_bit`. -/
def flipBitValue (number position : Int) : Int :=
  Int.ofNat (Nat.xor number.toNat (bitMask position))

/-- Reference for `is_bit_set`. -/
def isBitSetValue (number position : Int) : Bool :=
  Nat.land number.toNat (bitMask position) != 0

/-- Reference for `get_bit`. -/
def getBitValue (number position : Int) : Int :=
  if isBitSetValue number position then 1 else 0

end BitHelpers
