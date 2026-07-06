import JsonV2.Impl.Utils.Views
import JsonV2.Impl.Grammar

/-!
# Json.Impl.ConcreteSyntax.Spec

Concrete-syntax serialization vocabulary translated from
`JSON.ConcreteSyntax.Spec`.

DO NOT MODIFY types or signatures - these are the fixed vocabulary.
-/

namespace JSON

-- Spec helpers (no markers - fixed vocabulary)

abbrev GrammarBytes := List UInt8

abbrev GrammarNumber := jnumber

abbrev CSObject := GrammarObject

abbrev CSArray := GrammarArray

abbrev CSValue := GrammarValue

def csView (v : View_) : List UInt8 := view__Bytes v

def csStructural {T : Type} (f : T → List UInt8) (s : Structural T) : List UInt8 :=
  view__Bytes s.before ++ f s.t ++ view__Bytes s.after

def csMaybe {T : Type} (f : T → List UInt8) : Maybe T → List UInt8
  | .empty => []
  | .nonEmpty t => f t

def csSuffixed {D S : Type} (fd : D → List UInt8) (fs : S → List UInt8) (d : Suffixed D S) : List UInt8 :=
  fd d.t ++ csMaybe (csStructural fs) d.suffix

def csBracketedLocal {L D S R : Type} (fl : L → List UInt8) (fd : D → List UInt8) (fs : S → List UInt8) (fr : R → List UInt8) (b : Bracketed L D S R) : List UInt8 :=
  csStructural fl b.l ++ (b.data.map (csSuffixed fd fs)).foldl (· ++ ·) [] ++ csStructural fr b.r

def csFrac (self : jfrac) : List UInt8 :=
  csView self.period ++ csView self.num

def csExp (self : jexp) : List UInt8 :=
  csView self.e ++ csView self.sign ++ csView self.num

def csNumber (self : jnumber) : List UInt8 :=
  csView self.minus ++ csView self.num ++
    (match self.frac with
    | none => []
    | some f => csFrac f) ++
    (match self.exp with
    | none => []
    | some e => csExp e)

def csString (self : jstring) : List UInt8 :=
  csView self.lq ++ csView self.contents ++ csView self.rq

def csCommaSuffix : Maybe (Structural jcomma) → List UInt8
  | .empty => []
  | .nonEmpty s => csStructural csView s

mutual
  def csValue : CSValue → List UInt8
    | .null n => csView n
    | .bool b => csView b
    | .string s => csString s
    | .number n => csNumber n
    | .object obj => csObject obj
    | .array arr => csArray arr

  def csKeyValue : jKeyValue → List UInt8
    | ⟨k, colon, v⟩ => csString k ++ csStructural csView colon ++ csValue v

  def csObject : CSObject → List UInt8
    | ⟨⟨l, data, r⟩⟩ =>
      csStructural csView l ++
        csObjectItems data ++
        csStructural csView r

  def csArray : CSArray → List UInt8
    | ⟨⟨l, data, r⟩⟩ =>
      csStructural csView l ++
        csArrayItems data ++
        csStructural csView r

  def csObjectItems : List (Suffixed jKeyValue View_) → List UInt8
    | [] => []
    | ⟨t, suffix⟩ :: rest =>
      csKeyValue t ++ csCommaSuffix suffix ++ csObjectItems rest

  def csArrayItems : List (Suffixed GrammarValue View_) → List UInt8
    | [] => []
    | ⟨t, suffix⟩ :: rest =>
      csValue t ++ csCommaSuffix suffix ++ csArrayItems rest
end

end JSON
