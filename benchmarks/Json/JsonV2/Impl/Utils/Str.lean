-- !benchmark @start imports
-- !benchmark @end imports

/-!
# Json.Impl.Utils.Str

String utility vocabulary and reference implementations translated from
`JSON.Utils.Str`.

DO NOT MODIFY types or signatures - these are the fixed vocabulary.
Implement only the function bodies.
-/

namespace JSON

-- Types (no markers - fixed vocabulary)

abbrev JsonStrChar := Char

abbrev JsonStrString := List Char

abbrev JsonStrChar_2 := Char

abbrev JsonStrString_2 := List Char

inductive UnescapeError where
  | escapeAtEOS
  deriving Repr, DecidableEq, BEq

abbrev JsonEscChar := Char

-- Spec helpers (no markers - fixed vocabulary)

def digitsOfNat (n base : Nat) : List Nat := if base ≤ 1 then [n] else [n % base]

def ofDigits (digits : List Nat) (chars : List Char) : List Char := digits.filterMap (fun d => chars[d]?)

def ofNat_any (n : Nat) (chars : List Char) : List Char := ofDigits [n % chars.length] chars

def numberStr (str : List Char) (minus : Char) (is_digit : Char → Bool) : Prop := str ≠ [] ∧ (∀ c ∈ str, c = minus ∨ is_digit c = true)

def ofInt_any (n : Int) (chars : List Char) (minus : Char) : List Char := if n < 0 then minus :: ofNat_any n.natAbs chars else ofNat_any n.natAbs chars

def hexDigits : List Char := "0123456789ABCDEF".toList

-- API signatures (no markers - fixed vocabulary)

abbrev ParametricConversion_ToNat_anySig := List Char → Nat → List (Char × Nat) → Nat

abbrev ParametricEscaping_EscapeSig := List Char → List Char → Char → List Char

abbrev ParametricEscaping_UnescapeSig := List Char → Char → Except UnescapeError (List Char)

abbrev JoinSig := String → List String → String

abbrev ConcatSig := List String → String

-- !benchmark @start global_aux
-- !benchmark @end global_aux

-- !benchmark @start code_aux def=parametricConversion_ToNat_any
-- !benchmark @end code_aux def=parametricConversion_ToNat_any

def parametricConversion_ToNat_any : ParametricConversion_ToNat_anySig :=
-- !benchmark @start code def=parametricConversion_ToNat_any
  fun str base digits =>
    str.foldl
      (fun acc c =>
        match digits.find? (fun p => p.1 == c) with
        | some p => acc * base + p.2
        | none => acc * base)
      0
-- !benchmark @end code def=parametricConversion_ToNat_any

-- !benchmark @start code_aux def=parametricEscaping_Escape
-- !benchmark @end code_aux def=parametricEscaping_Escape

def parametricEscaping_Escape : ParametricEscaping_EscapeSig :=
-- !benchmark @start code def=parametricEscaping_Escape
  fun str special esc =>
    str.flatMap (fun c => if c ∈ special then [esc, c] else [c])
-- !benchmark @end code def=parametricEscaping_Escape

-- !benchmark @start code_aux def=parametricEscaping_Unescape
-- !benchmark @end code_aux def=parametricEscaping_Unescape

def parametricEscaping_Unescape : ParametricEscaping_UnescapeSig :=
-- !benchmark @start code def=parametricEscaping_Unescape
  fun str esc =>
    let rec go : List Char → Except UnescapeError (List Char)
      | [] => .ok []
      | c :: rest =>
        if c == esc then
          match rest with
          | [] => .error .escapeAtEOS
          | d :: rest' =>
            match go rest' with
            | .ok tl => .ok (d :: tl)
            | .error e => .error e
        else
          match go rest with
          | .ok tl => .ok (c :: tl)
          | .error e => .error e
    go str
-- !benchmark @end code def=parametricEscaping_Unescape

-- !benchmark @start code_aux def=join
-- !benchmark @end code_aux def=join

def join : JoinSig :=
-- !benchmark @start code def=join
  fun sep strs =>
    let rec go : List String → String
      | [] => ""
      | s :: rest =>
        match rest with
        | [] => s
        | _ => s ++ sep ++ go rest
    go strs
-- !benchmark @end code def=join

-- !benchmark @start code_aux def=concat
-- !benchmark @end code_aux def=concat

def concat : ConcatSig :=
-- !benchmark @start code def=concat
  fun strs =>
    strs.foldr (fun s acc => s ++ acc) ""
-- !benchmark @end code def=concat

end JSON
