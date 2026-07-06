import JsonV2.Impl.Utils.Views

/-!
# Json.Impl.Grammar

Foundation concrete JSON grammar vocabulary translated from `JSON.Grammar`.

DO NOT MODIFY types or signatures - these are the fixed vocabulary.
-/

namespace JSON

-- Types (no markers - fixed vocabulary)

abbrev jquote := View_

abbrev jperiod := View_

abbrev je := View_

abbrev jcolon := View_

abbrev jcomma := View_

abbrev jlbrace := View_

abbrev jrbrace := View_

abbrev jlbracket := View_

abbrev jrbracket := View_

abbrev jminus := View_

abbrev jsign := View_

abbrev jblanks := View_

structure Structural (T : Type) where
  before : View_
  t : T
  after : View_

inductive Maybe (T : Type) where
  | empty : Maybe T
  | nonEmpty (t : T) : Maybe T

structure Suffixed (T S : Type) where
  t : T
  suffix : Maybe (Structural S)

abbrev SuffixedSequence (D S : Type) := List (Suffixed D S)

structure Bracketed (L D S R : Type) where
  l : Structural L
  data : List (Suffixed D S)
  r : Structural R

abbrev jnull := View_

abbrev jbool := View_

abbrev jdigits := View_

abbrev jnum := View_

abbrev jint := View_

abbrev jstr := View_

structure jstring where
  lq : View_
  contents : View_
  rq : View_

structure jfrac where
  period : View_
  num : View_

structure jexp where
  e : View_
  sign : View_
  num : View_

structure jnumber where
  minus : View_
  num : View_
  frac : Option jfrac
  exp : Option jexp

mutual
  inductive GrammarValue where
    | null (n : View_) : GrammarValue
    | bool (b : View_) : GrammarValue
    | string (str : jstring) : GrammarValue
    | number (num : jnumber) : GrammarValue
    | object (obj : GrammarObject) : GrammarValue
    | array (arr : GrammarArray) : GrammarValue

  structure GrammarObject where
    inner : Bracketed View_ jKeyValue View_ View_

  structure GrammarArray where
    inner : Bracketed View_ GrammarValue View_ View_

  structure jKeyValue where
    k : jstring
    colon : Structural View_
    v : GrammarValue
end

abbrev jobject := GrammarObject

abbrev jarray := GrammarArray

abbrev jmember := Suffixed jKeyValue jcomma

abbrev jitem := Suffixed GrammarValue jcomma

abbrev jSON := Structural GrammarValue

-- Executable counterparts of the Dafny refinement predicates erased by the
-- plain `View_` aliases above. They preserve the public benchmark signatures
-- while making the scoped grammar model reject malformed concrete tokens.

def bytesAll? (p : UInt8 → Bool) : List UInt8 → Bool
  | [] => true
  | b :: bs => p b && bytesAll? p bs

def bytesNonemptyAll? (p : UInt8 → Bool) : List UInt8 → Bool
  | [] => false
  | b :: bs => p b && bytesAll? p bs

def view__BytesEq? (v : View_) (bs : List UInt8) : Bool :=
  view__Valid? v && view__Bytes v == bs

def jsonBlankByte? (b : UInt8) : Bool :=
  b == (0x20 : UInt8) || b == (0x09 : UInt8) ||
  b == (0x0A : UInt8) || b == (0x0D : UInt8)

def jsonDigitByte? (b : UInt8) : Bool :=
  decide ((48 : Nat) ≤ b.toNat ∧ b.toNat ≤ (57 : Nat))

def jquote__Valid? (v : jquote) : Bool := view__BytesEq? v [(34 : UInt8)]

def jperiod__Valid? (v : jperiod) : Bool := view__BytesEq? v [(46 : UInt8)]

def je__Valid? (v : je) : Bool :=
  view__BytesEq? v [(101 : UInt8)] || view__BytesEq? v [(69 : UInt8)]

def jcolon__Valid? (v : jcolon) : Bool := view__BytesEq? v [(58 : UInt8)]

def jcomma__Valid? (v : jcomma) : Bool := view__BytesEq? v [(44 : UInt8)]

def jlbrace__Valid? (v : jlbrace) : Bool := view__BytesEq? v [(123 : UInt8)]

def jrbrace__Valid? (v : jrbrace) : Bool := view__BytesEq? v [(125 : UInt8)]

def jlbracket__Valid? (v : jlbracket) : Bool := view__BytesEq? v [(91 : UInt8)]

def jrbracket__Valid? (v : jrbracket) : Bool := view__BytesEq? v [(93 : UInt8)]

def jminus__Valid? (v : jminus) : Bool :=
  view__BytesEq? v [(45 : UInt8)] || view__BytesEq? v []

def jsign__Valid? (v : jsign) : Bool :=
  view__BytesEq? v [(45 : UInt8)] ||
  view__BytesEq? v [(43 : UInt8)] ||
  view__BytesEq? v []

def jblanks__Valid? (v : jblanks) : Bool :=
  view__Valid? v && bytesAll? jsonBlankByte? (view__Bytes v)

def jnull__Valid? (v : jnull) : Bool :=
  view__BytesEq? v [(110 : UInt8), 117, 108, 108]

def jbool__Valid? (v : jbool) : Bool :=
  view__BytesEq? v [(116 : UInt8), 114, 117, 101] ||
  view__BytesEq? v [(102 : UInt8), 97, 108, 115, 101]

def jdigits__Valid? (v : jdigits) : Bool :=
  view__Valid? v && bytesAll? jsonDigitByte? (view__Bytes v)

def jnum__Valid? (v : jnum) : Bool :=
  view__Valid? v && bytesNonemptyAll? jsonDigitByte? (view__Bytes v)

def jint__Valid? (v : jint) : Bool :=
  view__Valid? v &&
    (view__Bytes v == [(48 : UInt8)] ||
      match view__Bytes v with
      | [] => false
      | b :: bs => b != (48 : UInt8) && jsonDigitByte? b && bytesAll? jsonDigitByte? bs)

def jstr__Valid? (v : jstr) : Bool :=
  view__Valid? v

def maybeValid? {T : Type} (p : T → Bool) : Maybe T → Bool
  | .empty => true
  | .nonEmpty t => p t

def optionValid? {T : Type} (p : T → Bool) : Option T → Bool
  | none => true
  | some t => p t

def structuralValid? {T : Type} (p : T → Bool) (s : Structural T) : Bool :=
  jblanks__Valid? s.before && p s.t && jblanks__Valid? s.after

def suffixEmpty? {T S : Type} (s : Suffixed T S) : Bool :=
  match s.suffix with
  | .empty => true
  | .nonEmpty _ => false

def noTrailingSuffix? {D S : Type} : List (Suffixed D S) → Bool
  | [] => true
  | x :: [] => suffixEmpty? x
  | x :: y :: xs => !suffixEmpty? x && noTrailingSuffix? (y :: xs)

def suffixedValid? {D S : Type} (pd : D → Bool) (ps : S → Bool) (x : Suffixed D S) : Bool :=
  pd x.t && maybeValid? (structuralValid? ps) x.suffix

def suffixedSequenceValid? {D S : Type} (pd : D → Bool) (ps : S → Bool) (xs : List (Suffixed D S)) : Bool :=
  noTrailingSuffix? xs && xs.all (suffixedValid? pd ps)

def bracketedValid? {L D S R : Type}
    (pl : L → Bool) (pd : D → Bool) (ps : S → Bool) (pr : R → Bool)
    (b : Bracketed L D S R) : Bool :=
  structuralValid? pl b.l &&
  suffixedSequenceValid? pd ps b.data &&
  structuralValid? pr b.r

def jstring__Valid? (str : jstring) : Bool :=
  jquote__Valid? str.lq && jstr__Valid? str.contents && jquote__Valid? str.rq

def jfrac__Valid? (frac : jfrac) : Bool :=
  jperiod__Valid? frac.period && jnum__Valid? frac.num

def jexp__Valid? (exp : jexp) : Bool :=
  je__Valid? exp.e && jsign__Valid? exp.sign && jnum__Valid? exp.num

def jnumber__Valid? (num : jnumber) : Bool :=
  jminus__Valid? num.minus &&
  jint__Valid? num.num &&
  optionValid? jfrac__Valid? num.frac &&
  optionValid? jexp__Valid? num.exp

mutual
  def grammarValue__Valid? : GrammarValue → Bool
    | .null n => jnull__Valid? n
    | .bool b => jbool__Valid? b
    | .string str => jstring__Valid? str
    | .number num => jnumber__Valid? num
    | .object obj => grammarObject__Valid? obj
    | .array arr => grammarArray__Valid? arr

  def grammarObject__Valid? : GrammarObject → Bool
    | ⟨⟨l, data, r⟩⟩ =>
      structuralValid? jlbrace__Valid? l &&
      noTrailingSuffix? data &&
      grammarObjectItemsAllValid? data &&
      structuralValid? jrbrace__Valid? r

  def grammarArray__Valid? : GrammarArray → Bool
    | ⟨⟨l, data, r⟩⟩ =>
      structuralValid? jlbracket__Valid? l &&
      noTrailingSuffix? data &&
      grammarArrayItemsAllValid? data &&
      structuralValid? jrbracket__Valid? r

  def jKeyValue__Valid? : jKeyValue → Bool
    | ⟨k, colon, v⟩ =>
      jstring__Valid? k &&
      structuralValid? jcolon__Valid? colon &&
      grammarValue__Valid? v

  def grammarObjectItemsAllValid? : List (Suffixed jKeyValue View_) → Bool
    | [] => true
    | ⟨t, suffix⟩ :: rest =>
      jKeyValue__Valid? t &&
      maybeValid? (structuralValid? jcomma__Valid?) suffix &&
      grammarObjectItemsAllValid? rest

  def grammarArrayItemsAllValid? : List (Suffixed GrammarValue View_) → Bool
    | [] => true
    | ⟨t, suffix⟩ :: rest =>
      grammarValue__Valid? t &&
      maybeValid? (structuralValid? jcomma__Valid?) suffix &&
      grammarArrayItemsAllValid? rest
end

def jobject__Valid? (obj : jobject) : Bool := grammarObject__Valid? obj

def jarray__Valid? (arr : jarray) : Bool := grammarArray__Valid? arr

def jmember__Valid? (member : jmember) : Bool :=
  suffixedValid? jKeyValue__Valid? jcomma__Valid? member

def jitem__Valid? (item : jitem) : Bool :=
  suffixedValid? grammarValue__Valid? jcomma__Valid? item

def jSON__Valid? (js : jSON) : Bool :=
  structuralValid? grammarValue__Valid? js

end JSON
