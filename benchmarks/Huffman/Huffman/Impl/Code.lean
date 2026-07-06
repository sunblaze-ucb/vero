import Huffman.Impl.UniqueKey
import Huffman.Impl.Frequency

-- !benchmark @start imports
-- !benchmark @end imports

/-!
# Huffman.Impl.Code

Codes as association lists, together with executable encoding and decoding
operations translated from Coq's `Code.v`. Types, helpers, and signatures are
fixed vocabulary; the API bodies are curator reference implementations.

DO NOT MODIFY types or signatures — these are the fixed vocabulary.
Implement only the function bodies.
-/

abbrev Code (A : Type) := List (A × List Bool)

def in_alphabet {A : Type} (m : List A) (c : Code A) : Prop :=
  ∀ a : A, a ∈ m → ∃ l : List Bool, (a, l) ∈ c

inductive is_prefix : List Bool → List Bool → Prop where
  | prefix_nil : ∀ l, is_prefix [] l
  | prefix_cons : ∀ b l1 l2, is_prefix l1 l2 → is_prefix (b :: l1) (b :: l2)

def not_null {A : Type} (c : Code A) : Prop :=
  ∀ a : A, (a, []) ∉ c

def unique_prefix {A : Type} (l : Code A) : Prop :=
  unique_key l ∧ ∀ a b c1 c2, (a, c1) ∈ l → (b, c2) ∈ l → is_prefix c1 c2 → a = b

namespace Huffman

abbrev DecodeSig := (A : Type) → [DecidableEq A] → Code A → List Bool → List A
abbrev EncodeSig := (A : Type) → [DecidableEq A] → Code A → List A → List Bool
abbrev FindCodeSig := (A : Type) → [DecidableEq A] → A → Code A → List Bool
abbrev FindValSig := (A : Type) → [DecidableEq A] → List Bool → Code A → Option A

end Huffman

-- !benchmark @start global_aux
-- !benchmark @end global_aux

-- !benchmark @start code_aux def=find_code
-- !benchmark @end code_aux def=find_code

def Huffman.find_code : Huffman.FindCodeSig :=
-- !benchmark @start code def=find_code
  fun A inst a l =>
    let _ := inst
    let rec go : Code A → List Bool
      | [] => []
      | (b, c) :: l1 =>
          if a = b then
            c
          else
            go l1
    go l
-- !benchmark @end code def=find_code

-- !benchmark @start code_aux def=find_val
-- !benchmark @end code_aux def=find_val

def Huffman.find_val : Huffman.FindValSig :=
-- !benchmark @start code def=find_val
  fun A _ a l =>
    let rec go : Code A → Option A
      | [] => none
      | (b, c) :: l1 =>
          if a = c then
            some b
          else
            go l1
    go l
-- !benchmark @end code def=find_val

def decode_aux {A : Type} [DecidableEq A] (c : Code A) (head : List Bool) : List Bool → List A
  | [] =>
      match Huffman.find_val A head c with
      | some a => [a]
      | none => []
  | b :: m =>
      match Huffman.find_val A head c with
      | some a => a :: decode_aux c [b] m
      | none => decode_aux c (head ++ [b]) m

-- !benchmark @start code_aux def=decode
-- !benchmark @end code_aux def=decode

def Huffman.decode : Huffman.DecodeSig :=
-- !benchmark @start code def=decode
  fun A inst c m =>
    let _ := inst
    decode_aux c [] m
-- !benchmark @end code def=decode

-- !benchmark @start code_aux def=encode
-- !benchmark @end code_aux def=encode

def Huffman.encode : Huffman.EncodeSig :=
-- !benchmark @start code def=encode
  fun A inst c m =>
    let _ := inst
    let rec go : List A → List Bool
      | [] => []
      | a :: b => Huffman.find_code A a c ++ go b
    go m
-- !benchmark @end code def=encode
