-- !benchmark @start imports
-- !benchmark @end imports

/-!
# ArithmeticV2.Impl.Overflow

Checked unsigned integer wrappers translated from Verus `overflow.rs`.
Types, semantic helper definitions, and API signatures are fixed vocabulary.
Function bodies are the curator's reference implementations inside the
`code` markers.
-/

-- !benchmark @start global_aux
-- !benchmark @end global_aux

namespace ArithmeticV2

structure CheckedU8 where
  i : Nat
  v : Option Nat
  deriving Repr, BEq, DecidableEq

structure CheckedU16 where
  i : Nat
  v : Option Nat
  deriving Repr, BEq, DecidableEq

structure CheckedU32 where
  i : Nat
  v : Option Nat
  deriving Repr, BEq, DecidableEq

structure CheckedU64 where
  i : Nat
  v : Option Nat
  deriving Repr, BEq, DecidableEq

structure CheckedU128 where
  i : Nat
  v : Option Nat
  deriving Repr, BEq, DecidableEq

structure CheckedUsize where
  i : Nat
  v : Option Nat
  deriving Repr, BEq, DecidableEq

abbrev CheckedU128_V := Nat
abbrev CheckedU16_V := Nat
abbrev CheckedU32_V := Nat
abbrev CheckedU64_V := Nat
abbrev CheckedU8_V := Nat
abbrev CheckedUsize_V := Nat

def CheckedU128_view (x : CheckedU128) : Nat := x.i

def CheckedU16_view (x : CheckedU16) : Nat := x.i

def CheckedU32_view (x : CheckedU32) : Nat := x.i

def CheckedU64_view (x : CheckedU64) : Nat := x.i

def CheckedU8_view (x : CheckedU8) : Nat := x.i

def CheckedUsize_view (x : CheckedUsize) : Nat := x.i

def CheckedU128_spec_new (v : Nat) : CheckedU128 := { i := v, v := some v }

def CheckedU16_spec_new (v : Nat) : CheckedU16 := { i := v, v := some v }

def CheckedU32_spec_new (v : Nat) : CheckedU32 := { i := v, v := some v }

def CheckedU64_spec_new (v : Nat) : CheckedU64 := { i := v, v := some v }

def CheckedU8_spec_new (v : Nat) : CheckedU8 := { i := v, v := some v }

def CheckedUsize_spec_new (v : Nat) : CheckedUsize := { i := v, v := some v }

def CheckedU128_well_formed (x : CheckedU128) : Prop :=
  match x.v with
  | some v => x.i = v ∧ v ≤ 340282366920938463463374607431768211455
  | none => 340282366920938463463374607431768211455 < x.i

def CheckedU16_well_formed (x : CheckedU16) : Prop :=
  match x.v with
  | some v => x.i = v ∧ v ≤ 65535
  | none => 65535 < x.i

def CheckedU32_well_formed (x : CheckedU32) : Prop :=
  match x.v with
  | some v => x.i = v ∧ v ≤ 4294967295
  | none => 4294967295 < x.i

def CheckedU64_well_formed (x : CheckedU64) : Prop :=
  match x.v with
  | some v => x.i = v ∧ v ≤ 18446744073709551615
  | none => 18446744073709551615 < x.i

def CheckedU8_well_formed (x : CheckedU8) : Prop :=
  match x.v with
  | some v => x.i = v ∧ v ≤ 255
  | none => 255 < x.i

def CheckedUsize_well_formed (x : CheckedUsize) : Prop :=
  match x.v with
  | some v => x.i = v ∧ v ≤ 18446744073709551615
  | none => 18446744073709551615 < x.i

def CheckedU128_spec_is_overflowed (x : CheckedU128) : Bool := decide (340282366920938463463374607431768211455 < x.i)

def CheckedU16_spec_is_overflowed (x : CheckedU16) : Bool := decide (65535 < x.i)

def CheckedU32_spec_is_overflowed (x : CheckedU32) : Bool := decide (4294967295 < x.i)

def CheckedU64_spec_is_overflowed (x : CheckedU64) : Bool := decide (18446744073709551615 < x.i)

def CheckedU8_spec_is_overflowed (x : CheckedU8) : Bool := decide (255 < x.i)

def CheckedUsize_spec_is_overflowed (x : CheckedUsize) : Bool := decide (18446744073709551615 < x.i)

def CheckedU128_clone (x : CheckedU128) : CheckedU128 := x

def CheckedU16_clone (x : CheckedU16) : CheckedU16 := x

def CheckedU32_clone (x : CheckedU32) : CheckedU32 := x

def CheckedU64_clone (x : CheckedU64) : CheckedU64 := x

def CheckedU8_clone (x : CheckedU8) : CheckedU8 := x

def CheckedUsize_clone (x : CheckedUsize) : CheckedUsize := x

abbrev CheckedU128NewSig := Nat → CheckedU128
abbrev CheckedU16NewSig := Nat → CheckedU16
abbrev CheckedU32NewSig := Nat → CheckedU32
abbrev CheckedU64NewSig := Nat → CheckedU64
abbrev CheckedU8NewSig := Nat → CheckedU8
abbrev CheckedUsizeNewSig := Nat → CheckedUsize
abbrev CheckedU128NewOverflowedSig := Int → CheckedU128
abbrev CheckedU16NewOverflowedSig := Int → CheckedU16
abbrev CheckedU32NewOverflowedSig := Int → CheckedU32
abbrev CheckedU64NewOverflowedSig := Int → CheckedU64
abbrev CheckedU8NewOverflowedSig := Int → CheckedU8
abbrev CheckedUsizeNewOverflowedSig := Int → CheckedUsize
abbrev CheckedU128IsOverflowedSig := CheckedU128 → Bool
abbrev CheckedU16IsOverflowedSig := CheckedU16 → Bool
abbrev CheckedU32IsOverflowedSig := CheckedU32 → Bool
abbrev CheckedU64IsOverflowedSig := CheckedU64 → Bool
abbrev CheckedU8IsOverflowedSig := CheckedU8 → Bool
abbrev CheckedUsizeIsOverflowedSig := CheckedUsize → Bool
abbrev CheckedU128UnwrapSig := CheckedU128 → Nat
abbrev CheckedU16UnwrapSig := CheckedU16 → Nat
abbrev CheckedU32UnwrapSig := CheckedU32 → Nat
abbrev CheckedU64UnwrapSig := CheckedU64 → Nat
abbrev CheckedU8UnwrapSig := CheckedU8 → Nat
abbrev CheckedUsizeUnwrapSig := CheckedUsize → Nat
abbrev CheckedU128ToOptionSig := CheckedU128 → Option Nat
abbrev CheckedU16ToOptionSig := CheckedU16 → Option Nat
abbrev CheckedU32ToOptionSig := CheckedU32 → Option Nat
abbrev CheckedU64ToOptionSig := CheckedU64 → Option Nat
abbrev CheckedU8ToOptionSig := CheckedU8 → Option Nat
abbrev CheckedUsizeToOptionSig := CheckedUsize → Option Nat
abbrev CheckedU128AddValueSig := CheckedU128 → Nat → CheckedU128
abbrev CheckedU16AddValueSig := CheckedU16 → Nat → CheckedU16
abbrev CheckedU32AddValueSig := CheckedU32 → Nat → CheckedU32
abbrev CheckedU64AddValueSig := CheckedU64 → Nat → CheckedU64
abbrev CheckedU8AddValueSig := CheckedU8 → Nat → CheckedU8
abbrev CheckedUsizeAddValueSig := CheckedUsize → Nat → CheckedUsize
abbrev CheckedU128AddCheckedSig := CheckedU128 → CheckedU128 → CheckedU128
abbrev CheckedU16AddCheckedSig := CheckedU16 → CheckedU16 → CheckedU16
abbrev CheckedU32AddCheckedSig := CheckedU32 → CheckedU32 → CheckedU32
abbrev CheckedU64AddCheckedSig := CheckedU64 → CheckedU64 → CheckedU64
abbrev CheckedU8AddCheckedSig := CheckedU8 → CheckedU8 → CheckedU8
abbrev CheckedUsizeAddCheckedSig := CheckedUsize → CheckedUsize → CheckedUsize
abbrev CheckedU128MulValueSig := CheckedU128 → Nat → CheckedU128
abbrev CheckedU16MulValueSig := CheckedU16 → Nat → CheckedU16
abbrev CheckedU32MulValueSig := CheckedU32 → Nat → CheckedU32
abbrev CheckedU64MulValueSig := CheckedU64 → Nat → CheckedU64
abbrev CheckedU8MulValueSig := CheckedU8 → Nat → CheckedU8
abbrev CheckedUsizeMulValueSig := CheckedUsize → Nat → CheckedUsize
abbrev CheckedU128MulCheckedSig := CheckedU128 → CheckedU128 → CheckedU128
abbrev CheckedU16MulCheckedSig := CheckedU16 → CheckedU16 → CheckedU16
abbrev CheckedU32MulCheckedSig := CheckedU32 → CheckedU32 → CheckedU32
abbrev CheckedU64MulCheckedSig := CheckedU64 → CheckedU64 → CheckedU64
abbrev CheckedU8MulCheckedSig := CheckedU8 → CheckedU8 → CheckedU8
abbrev CheckedUsizeMulCheckedSig := CheckedUsize → CheckedUsize → CheckedUsize

-- !benchmark @start code_aux def=CheckedU128_new
-- !benchmark @end code_aux def=CheckedU128_new

def CheckedU128_new : CheckedU128NewSig :=
-- !benchmark @start code def=CheckedU128_new
  fun v => { i := v, v := some v }
-- !benchmark @end code def=CheckedU128_new

-- !benchmark @start code_aux def=CheckedU16_new
-- !benchmark @end code_aux def=CheckedU16_new

def CheckedU16_new : CheckedU16NewSig :=
-- !benchmark @start code def=CheckedU16_new
  fun v => { i := v, v := some v }
-- !benchmark @end code def=CheckedU16_new

-- !benchmark @start code_aux def=CheckedU32_new
-- !benchmark @end code_aux def=CheckedU32_new

def CheckedU32_new : CheckedU32NewSig :=
-- !benchmark @start code def=CheckedU32_new
  fun v => { i := v, v := some v }
-- !benchmark @end code def=CheckedU32_new

-- !benchmark @start code_aux def=CheckedU64_new
-- !benchmark @end code_aux def=CheckedU64_new

def CheckedU64_new : CheckedU64NewSig :=
-- !benchmark @start code def=CheckedU64_new
  fun v => { i := v, v := some v }
-- !benchmark @end code def=CheckedU64_new

-- !benchmark @start code_aux def=CheckedU8_new
-- !benchmark @end code_aux def=CheckedU8_new

def CheckedU8_new : CheckedU8NewSig :=
-- !benchmark @start code def=CheckedU8_new
  fun v => { i := v, v := some v }
-- !benchmark @end code def=CheckedU8_new

-- !benchmark @start code_aux def=CheckedUsize_new
-- !benchmark @end code_aux def=CheckedUsize_new

def CheckedUsize_new : CheckedUsizeNewSig :=
-- !benchmark @start code def=CheckedUsize_new
  fun v => { i := v, v := some v }
-- !benchmark @end code def=CheckedUsize_new

-- !benchmark @start code_aux def=CheckedU128_new_overflowed
-- !benchmark @end code_aux def=CheckedU128_new_overflowed

def CheckedU128_new_overflowed : CheckedU128NewOverflowedSig :=
-- !benchmark @start code def=CheckedU128_new_overflowed
  fun i => { i := i.toNat, v := none }
-- !benchmark @end code def=CheckedU128_new_overflowed

-- !benchmark @start code_aux def=CheckedU16_new_overflowed
-- !benchmark @end code_aux def=CheckedU16_new_overflowed

def CheckedU16_new_overflowed : CheckedU16NewOverflowedSig :=
-- !benchmark @start code def=CheckedU16_new_overflowed
  fun i => { i := i.toNat, v := none }
-- !benchmark @end code def=CheckedU16_new_overflowed

-- !benchmark @start code_aux def=CheckedU32_new_overflowed
-- !benchmark @end code_aux def=CheckedU32_new_overflowed

def CheckedU32_new_overflowed : CheckedU32NewOverflowedSig :=
-- !benchmark @start code def=CheckedU32_new_overflowed
  fun i => { i := i.toNat, v := none }
-- !benchmark @end code def=CheckedU32_new_overflowed

-- !benchmark @start code_aux def=CheckedU64_new_overflowed
-- !benchmark @end code_aux def=CheckedU64_new_overflowed

def CheckedU64_new_overflowed : CheckedU64NewOverflowedSig :=
-- !benchmark @start code def=CheckedU64_new_overflowed
  fun i => { i := i.toNat, v := none }
-- !benchmark @end code def=CheckedU64_new_overflowed

-- !benchmark @start code_aux def=CheckedU8_new_overflowed
-- !benchmark @end code_aux def=CheckedU8_new_overflowed

def CheckedU8_new_overflowed : CheckedU8NewOverflowedSig :=
-- !benchmark @start code def=CheckedU8_new_overflowed
  fun i => { i := i.toNat, v := none }
-- !benchmark @end code def=CheckedU8_new_overflowed

-- !benchmark @start code_aux def=CheckedUsize_new_overflowed
-- !benchmark @end code_aux def=CheckedUsize_new_overflowed

def CheckedUsize_new_overflowed : CheckedUsizeNewOverflowedSig :=
-- !benchmark @start code def=CheckedUsize_new_overflowed
  fun i => { i := i.toNat, v := none }
-- !benchmark @end code def=CheckedUsize_new_overflowed

-- !benchmark @start code_aux def=CheckedU128_is_overflowed
-- !benchmark @end code_aux def=CheckedU128_is_overflowed

def CheckedU128_is_overflowed : CheckedU128IsOverflowedSig :=
-- !benchmark @start code def=CheckedU128_is_overflowed
  fun x =>
    match x.v with
    | some _ => false
    | none => true
-- !benchmark @end code def=CheckedU128_is_overflowed

-- !benchmark @start code_aux def=CheckedU16_is_overflowed
-- !benchmark @end code_aux def=CheckedU16_is_overflowed

def CheckedU16_is_overflowed : CheckedU16IsOverflowedSig :=
-- !benchmark @start code def=CheckedU16_is_overflowed
  fun x =>
    match x.v with
    | some _ => false
    | none => true
-- !benchmark @end code def=CheckedU16_is_overflowed

-- !benchmark @start code_aux def=CheckedU32_is_overflowed
-- !benchmark @end code_aux def=CheckedU32_is_overflowed

def CheckedU32_is_overflowed : CheckedU32IsOverflowedSig :=
-- !benchmark @start code def=CheckedU32_is_overflowed
  fun x =>
    match x.v with
    | some _ => false
    | none => true
-- !benchmark @end code def=CheckedU32_is_overflowed

-- !benchmark @start code_aux def=CheckedU64_is_overflowed
-- !benchmark @end code_aux def=CheckedU64_is_overflowed

def CheckedU64_is_overflowed : CheckedU64IsOverflowedSig :=
-- !benchmark @start code def=CheckedU64_is_overflowed
  fun x =>
    match x.v with
    | some _ => false
    | none => true
-- !benchmark @end code def=CheckedU64_is_overflowed

-- !benchmark @start code_aux def=CheckedU8_is_overflowed
-- !benchmark @end code_aux def=CheckedU8_is_overflowed

def CheckedU8_is_overflowed : CheckedU8IsOverflowedSig :=
-- !benchmark @start code def=CheckedU8_is_overflowed
  fun x =>
    match x.v with
    | some _ => false
    | none => true
-- !benchmark @end code def=CheckedU8_is_overflowed

-- !benchmark @start code_aux def=CheckedUsize_is_overflowed
-- !benchmark @end code_aux def=CheckedUsize_is_overflowed

def CheckedUsize_is_overflowed : CheckedUsizeIsOverflowedSig :=
-- !benchmark @start code def=CheckedUsize_is_overflowed
  fun x =>
    match x.v with
    | some _ => false
    | none => true
-- !benchmark @end code def=CheckedUsize_is_overflowed

-- !benchmark @start code_aux def=CheckedU128_unwrap
-- !benchmark @end code_aux def=CheckedU128_unwrap

def CheckedU128_unwrap : CheckedU128UnwrapSig :=
-- !benchmark @start code def=CheckedU128_unwrap
  fun x =>
    match x.v with
    | some v => v
    | none => 0
-- !benchmark @end code def=CheckedU128_unwrap

-- !benchmark @start code_aux def=CheckedU16_unwrap
-- !benchmark @end code_aux def=CheckedU16_unwrap

def CheckedU16_unwrap : CheckedU16UnwrapSig :=
-- !benchmark @start code def=CheckedU16_unwrap
  fun x =>
    match x.v with
    | some v => v
    | none => 0
-- !benchmark @end code def=CheckedU16_unwrap

-- !benchmark @start code_aux def=CheckedU32_unwrap
-- !benchmark @end code_aux def=CheckedU32_unwrap

def CheckedU32_unwrap : CheckedU32UnwrapSig :=
-- !benchmark @start code def=CheckedU32_unwrap
  fun x =>
    match x.v with
    | some v => v
    | none => 0
-- !benchmark @end code def=CheckedU32_unwrap

-- !benchmark @start code_aux def=CheckedU64_unwrap
-- !benchmark @end code_aux def=CheckedU64_unwrap

def CheckedU64_unwrap : CheckedU64UnwrapSig :=
-- !benchmark @start code def=CheckedU64_unwrap
  fun x =>
    match x.v with
    | some v => v
    | none => 0
-- !benchmark @end code def=CheckedU64_unwrap

-- !benchmark @start code_aux def=CheckedU8_unwrap
-- !benchmark @end code_aux def=CheckedU8_unwrap

def CheckedU8_unwrap : CheckedU8UnwrapSig :=
-- !benchmark @start code def=CheckedU8_unwrap
  fun x =>
    match x.v with
    | some v => v
    | none => 0
-- !benchmark @end code def=CheckedU8_unwrap

-- !benchmark @start code_aux def=CheckedUsize_unwrap
-- !benchmark @end code_aux def=CheckedUsize_unwrap

def CheckedUsize_unwrap : CheckedUsizeUnwrapSig :=
-- !benchmark @start code def=CheckedUsize_unwrap
  fun x =>
    match x.v with
    | some v => v
    | none => 0
-- !benchmark @end code def=CheckedUsize_unwrap

-- !benchmark @start code_aux def=CheckedU128_to_option
-- !benchmark @end code_aux def=CheckedU128_to_option

def CheckedU128_to_option : CheckedU128ToOptionSig :=
-- !benchmark @start code def=CheckedU128_to_option
  fun x => x.v
-- !benchmark @end code def=CheckedU128_to_option

-- !benchmark @start code_aux def=CheckedU16_to_option
-- !benchmark @end code_aux def=CheckedU16_to_option

def CheckedU16_to_option : CheckedU16ToOptionSig :=
-- !benchmark @start code def=CheckedU16_to_option
  fun x => x.v
-- !benchmark @end code def=CheckedU16_to_option

-- !benchmark @start code_aux def=CheckedU32_to_option
-- !benchmark @end code_aux def=CheckedU32_to_option

def CheckedU32_to_option : CheckedU32ToOptionSig :=
-- !benchmark @start code def=CheckedU32_to_option
  fun x => x.v
-- !benchmark @end code def=CheckedU32_to_option

-- !benchmark @start code_aux def=CheckedU64_to_option
-- !benchmark @end code_aux def=CheckedU64_to_option

def CheckedU64_to_option : CheckedU64ToOptionSig :=
-- !benchmark @start code def=CheckedU64_to_option
  fun x => x.v
-- !benchmark @end code def=CheckedU64_to_option

-- !benchmark @start code_aux def=CheckedU8_to_option
-- !benchmark @end code_aux def=CheckedU8_to_option

def CheckedU8_to_option : CheckedU8ToOptionSig :=
-- !benchmark @start code def=CheckedU8_to_option
  fun x => x.v
-- !benchmark @end code def=CheckedU8_to_option

-- !benchmark @start code_aux def=CheckedUsize_to_option
-- !benchmark @end code_aux def=CheckedUsize_to_option

def CheckedUsize_to_option : CheckedUsizeToOptionSig :=
-- !benchmark @start code def=CheckedUsize_to_option
  fun x => x.v
-- !benchmark @end code def=CheckedUsize_to_option

-- !benchmark @start code_aux def=CheckedU128_add_value
-- !benchmark @end code_aux def=CheckedU128_add_value

def CheckedU128_add_value : CheckedU128AddValueSig :=
-- !benchmark @start code def=CheckedU128_add_value
  fun x v2 =>
    let i := x.i + v2
    let out :=
      match x.v with
      | some v1 =>
        let sum := v1 + v2
        if sum ≤ 340282366920938463463374607431768211455 then some sum else none
      | none => none
    { i := i, v := out }
-- !benchmark @end code def=CheckedU128_add_value

-- !benchmark @start code_aux def=CheckedU16_add_value
-- !benchmark @end code_aux def=CheckedU16_add_value

def CheckedU16_add_value : CheckedU16AddValueSig :=
-- !benchmark @start code def=CheckedU16_add_value
  fun x v2 =>
    let i := x.i + v2
    let out :=
      match x.v with
      | some v1 =>
        let sum := v1 + v2
        if sum ≤ 65535 then some sum else none
      | none => none
    { i := i, v := out }
-- !benchmark @end code def=CheckedU16_add_value

-- !benchmark @start code_aux def=CheckedU32_add_value
-- !benchmark @end code_aux def=CheckedU32_add_value

def CheckedU32_add_value : CheckedU32AddValueSig :=
-- !benchmark @start code def=CheckedU32_add_value
  fun x v2 =>
    let i := x.i + v2
    let out :=
      match x.v with
      | some v1 =>
        let sum := v1 + v2
        if sum ≤ 4294967295 then some sum else none
      | none => none
    { i := i, v := out }
-- !benchmark @end code def=CheckedU32_add_value

-- !benchmark @start code_aux def=CheckedU64_add_value
-- !benchmark @end code_aux def=CheckedU64_add_value

def CheckedU64_add_value : CheckedU64AddValueSig :=
-- !benchmark @start code def=CheckedU64_add_value
  fun x v2 =>
    let i := x.i + v2
    let out :=
      match x.v with
      | some v1 =>
        let sum := v1 + v2
        if sum ≤ 18446744073709551615 then some sum else none
      | none => none
    { i := i, v := out }
-- !benchmark @end code def=CheckedU64_add_value

-- !benchmark @start code_aux def=CheckedU8_add_value
-- !benchmark @end code_aux def=CheckedU8_add_value

def CheckedU8_add_value : CheckedU8AddValueSig :=
-- !benchmark @start code def=CheckedU8_add_value
  fun x v2 =>
    let i := x.i + v2
    let out :=
      match x.v with
      | some v1 =>
        let sum := v1 + v2
        if sum ≤ 255 then some sum else none
      | none => none
    { i := i, v := out }
-- !benchmark @end code def=CheckedU8_add_value

-- !benchmark @start code_aux def=CheckedUsize_add_value
-- !benchmark @end code_aux def=CheckedUsize_add_value

def CheckedUsize_add_value : CheckedUsizeAddValueSig :=
-- !benchmark @start code def=CheckedUsize_add_value
  fun x v2 =>
    let i := x.i + v2
    let out :=
      match x.v with
      | some v1 =>
        let sum := v1 + v2
        if sum ≤ 18446744073709551615 then some sum else none
      | none => none
    { i := i, v := out }
-- !benchmark @end code def=CheckedUsize_add_value

-- !benchmark @start code_aux def=CheckedU128_add_checked
-- !benchmark @end code_aux def=CheckedU128_add_checked

def CheckedU128_add_checked : CheckedU128AddCheckedSig :=
-- !benchmark @start code def=CheckedU128_add_checked
  fun x y =>
    match y.v with
    | some n => CheckedU128_add_value x n
    | none => { i := x.i + y.i, v := none }
-- !benchmark @end code def=CheckedU128_add_checked

-- !benchmark @start code_aux def=CheckedU16_add_checked
-- !benchmark @end code_aux def=CheckedU16_add_checked

def CheckedU16_add_checked : CheckedU16AddCheckedSig :=
-- !benchmark @start code def=CheckedU16_add_checked
  fun x y =>
    match y.v with
    | some n => CheckedU16_add_value x n
    | none => { i := x.i + y.i, v := none }
-- !benchmark @end code def=CheckedU16_add_checked

-- !benchmark @start code_aux def=CheckedU32_add_checked
-- !benchmark @end code_aux def=CheckedU32_add_checked

def CheckedU32_add_checked : CheckedU32AddCheckedSig :=
-- !benchmark @start code def=CheckedU32_add_checked
  fun x y =>
    match y.v with
    | some n => CheckedU32_add_value x n
    | none => { i := x.i + y.i, v := none }
-- !benchmark @end code def=CheckedU32_add_checked

-- !benchmark @start code_aux def=CheckedU64_add_checked
-- !benchmark @end code_aux def=CheckedU64_add_checked

def CheckedU64_add_checked : CheckedU64AddCheckedSig :=
-- !benchmark @start code def=CheckedU64_add_checked
  fun x y =>
    match y.v with
    | some n => CheckedU64_add_value x n
    | none => { i := x.i + y.i, v := none }
-- !benchmark @end code def=CheckedU64_add_checked

-- !benchmark @start code_aux def=CheckedU8_add_checked
-- !benchmark @end code_aux def=CheckedU8_add_checked

def CheckedU8_add_checked : CheckedU8AddCheckedSig :=
-- !benchmark @start code def=CheckedU8_add_checked
  fun x y =>
    match y.v with
    | some n => CheckedU8_add_value x n
    | none => { i := x.i + y.i, v := none }
-- !benchmark @end code def=CheckedU8_add_checked

-- !benchmark @start code_aux def=CheckedUsize_add_checked
-- !benchmark @end code_aux def=CheckedUsize_add_checked

def CheckedUsize_add_checked : CheckedUsizeAddCheckedSig :=
-- !benchmark @start code def=CheckedUsize_add_checked
  fun x y =>
    match y.v with
    | some n => CheckedUsize_add_value x n
    | none => { i := x.i + y.i, v := none }
-- !benchmark @end code def=CheckedUsize_add_checked

-- !benchmark @start code_aux def=CheckedU128_mul_value
-- !benchmark @end code_aux def=CheckedU128_mul_value

def CheckedU128_mul_value : CheckedU128MulValueSig :=
-- !benchmark @start code def=CheckedU128_mul_value
  fun x v2 =>
    let i := x.i * v2
    let out :=
      match x.v with
      | some v1 =>
        let product := v1 * v2
        if product ≤ 340282366920938463463374607431768211455 then some product else none
      | none =>
        if v2 = 0 then some 0 else none
    { i := i, v := out }
-- !benchmark @end code def=CheckedU128_mul_value

-- !benchmark @start code_aux def=CheckedU16_mul_value
-- !benchmark @end code_aux def=CheckedU16_mul_value

def CheckedU16_mul_value : CheckedU16MulValueSig :=
-- !benchmark @start code def=CheckedU16_mul_value
  fun x v2 =>
    let i := x.i * v2
    let out :=
      match x.v with
      | some v1 =>
        let product := v1 * v2
        if product ≤ 65535 then some product else none
      | none =>
        if v2 = 0 then some 0 else none
    { i := i, v := out }
-- !benchmark @end code def=CheckedU16_mul_value

-- !benchmark @start code_aux def=CheckedU32_mul_value
-- !benchmark @end code_aux def=CheckedU32_mul_value

def CheckedU32_mul_value : CheckedU32MulValueSig :=
-- !benchmark @start code def=CheckedU32_mul_value
  fun x v2 =>
    let i := x.i * v2
    let out :=
      match x.v with
      | some v1 =>
        let product := v1 * v2
        if product ≤ 4294967295 then some product else none
      | none =>
        if v2 = 0 then some 0 else none
    { i := i, v := out }
-- !benchmark @end code def=CheckedU32_mul_value

-- !benchmark @start code_aux def=CheckedU64_mul_value
-- !benchmark @end code_aux def=CheckedU64_mul_value

def CheckedU64_mul_value : CheckedU64MulValueSig :=
-- !benchmark @start code def=CheckedU64_mul_value
  fun x v2 =>
    let i := x.i * v2
    let out :=
      match x.v with
      | some v1 =>
        let product := v1 * v2
        if product ≤ 18446744073709551615 then some product else none
      | none =>
        if v2 = 0 then some 0 else none
    { i := i, v := out }
-- !benchmark @end code def=CheckedU64_mul_value

-- !benchmark @start code_aux def=CheckedU8_mul_value
-- !benchmark @end code_aux def=CheckedU8_mul_value

def CheckedU8_mul_value : CheckedU8MulValueSig :=
-- !benchmark @start code def=CheckedU8_mul_value
  fun x v2 =>
    let i := x.i * v2
    let out :=
      match x.v with
      | some v1 =>
        let product := v1 * v2
        if product ≤ 255 then some product else none
      | none =>
        if v2 = 0 then some 0 else none
    { i := i, v := out }
-- !benchmark @end code def=CheckedU8_mul_value

-- !benchmark @start code_aux def=CheckedUsize_mul_value
-- !benchmark @end code_aux def=CheckedUsize_mul_value

def CheckedUsize_mul_value : CheckedUsizeMulValueSig :=
-- !benchmark @start code def=CheckedUsize_mul_value
  fun x v2 =>
    let i := x.i * v2
    let out :=
      match x.v with
      | some v1 =>
        let product := v1 * v2
        if product ≤ 18446744073709551615 then some product else none
      | none =>
        if v2 = 0 then some 0 else none
    { i := i, v := out }
-- !benchmark @end code def=CheckedUsize_mul_value

-- !benchmark @start code_aux def=CheckedU128_mul_checked
-- !benchmark @end code_aux def=CheckedU128_mul_checked

def CheckedU128_mul_checked : CheckedU128MulCheckedSig :=
-- !benchmark @start code def=CheckedU128_mul_checked
  fun x y =>
    match y.v with
    | some n => CheckedU128_mul_value x n
    | none =>
      let i := x.i * y.i
      let out :=
        match x.v with
        | some n1 => if n1 = 0 then some 0 else none
        | none => none
      { i := i, v := out }
-- !benchmark @end code def=CheckedU128_mul_checked

-- !benchmark @start code_aux def=CheckedU16_mul_checked
-- !benchmark @end code_aux def=CheckedU16_mul_checked

def CheckedU16_mul_checked : CheckedU16MulCheckedSig :=
-- !benchmark @start code def=CheckedU16_mul_checked
  fun x y =>
    match y.v with
    | some n => CheckedU16_mul_value x n
    | none =>
      let i := x.i * y.i
      let out :=
        match x.v with
        | some n1 => if n1 = 0 then some 0 else none
        | none => none
      { i := i, v := out }
-- !benchmark @end code def=CheckedU16_mul_checked

-- !benchmark @start code_aux def=CheckedU32_mul_checked
-- !benchmark @end code_aux def=CheckedU32_mul_checked

def CheckedU32_mul_checked : CheckedU32MulCheckedSig :=
-- !benchmark @start code def=CheckedU32_mul_checked
  fun x y =>
    match y.v with
    | some n => CheckedU32_mul_value x n
    | none =>
      let i := x.i * y.i
      let out :=
        match x.v with
        | some n1 => if n1 = 0 then some 0 else none
        | none => none
      { i := i, v := out }
-- !benchmark @end code def=CheckedU32_mul_checked

-- !benchmark @start code_aux def=CheckedU64_mul_checked
-- !benchmark @end code_aux def=CheckedU64_mul_checked

def CheckedU64_mul_checked : CheckedU64MulCheckedSig :=
-- !benchmark @start code def=CheckedU64_mul_checked
  fun x y =>
    match y.v with
    | some n => CheckedU64_mul_value x n
    | none =>
      let i := x.i * y.i
      let out :=
        match x.v with
        | some n1 => if n1 = 0 then some 0 else none
        | none => none
      { i := i, v := out }
-- !benchmark @end code def=CheckedU64_mul_checked

-- !benchmark @start code_aux def=CheckedU8_mul_checked
-- !benchmark @end code_aux def=CheckedU8_mul_checked

def CheckedU8_mul_checked : CheckedU8MulCheckedSig :=
-- !benchmark @start code def=CheckedU8_mul_checked
  fun x y =>
    match y.v with
    | some n => CheckedU8_mul_value x n
    | none =>
      let i := x.i * y.i
      let out :=
        match x.v with
        | some n1 => if n1 = 0 then some 0 else none
        | none => none
      { i := i, v := out }
-- !benchmark @end code def=CheckedU8_mul_checked

-- !benchmark @start code_aux def=CheckedUsize_mul_checked
-- !benchmark @end code_aux def=CheckedUsize_mul_checked

def CheckedUsize_mul_checked : CheckedUsizeMulCheckedSig :=
-- !benchmark @start code def=CheckedUsize_mul_checked
  fun x y =>
    match y.v with
    | some n => CheckedUsize_mul_value x n
    | none =>
      let i := x.i * y.i
      let out :=
        match x.v with
        | some n1 => if n1 = 0 then some 0 else none
        | none => none
      { i := i, v := out }
-- !benchmark @end code def=CheckedUsize_mul_checked

end ArithmeticV2
