import Flocq.Core.Impl.Zaux

-- !benchmark @start imports
-- !benchmark @end imports

/-!
# Flocq.Pff.Impl.Pff

Curated Pff floating-point vocabulary and selected computable APIs, adapted
from the rerun's source-backed translation of `Pff/Pff.v`.
-/

/-- Source-backed Coq record: `Record float : Set := Float {Fnum : Z; Fexp : Z}.` -/
structure PffFloat where
  num : Int
  exp : Int
deriving Inhabited, Repr, DecidableEq

def PffFloat.fnum (f : PffFloat) : Int :=
  f.num

def PffFloat.fexp (f : PffFloat) : Int :=
  f.exp

def pffAbs (x : Int) : Int :=
  if x < 0 then -x else x

namespace Flocq

-- API signatures
abbrev PffFoppSig := PffFloat → PffFloat
abbrev PffFabsSig := PffFloat → PffFloat
abbrev PffFplusSig := PffFloat → PffFloat → PffFloat
abbrev PffFmultSig := PffFloat → PffFloat → PffFloat
abbrev PffMZlistAuxSig := Int → Nat → List Int
abbrev PffMZlistSig := Int → Int → List Int
abbrev PffMProdSig := (A B : Type) → List A → List B → List (A × B)

end Flocq

-- !benchmark @start global_aux
-- !benchmark @end global_aux

-- !benchmark @start code_aux def=pffFopp
-- !benchmark @end code_aux def=pffFopp

def Flocq.pffFopp : Flocq.PffFoppSig :=
-- !benchmark @start code def=pffFopp
  fun x => { num := -x.num, exp := x.exp }
-- !benchmark @end code def=pffFopp

-- !benchmark @start code_aux def=pffFabs
-- !benchmark @end code_aux def=pffFabs

def Flocq.pffFabs : Flocq.PffFabsSig :=
-- !benchmark @start code def=pffFabs
  fun x => { num := pffAbs x.num, exp := x.exp }
-- !benchmark @end code def=pffFabs

-- !benchmark @start code_aux def=pffFplus
-- !benchmark @end code_aux def=pffFplus

def Flocq.pffFplus : Flocq.PffFplusSig :=
-- !benchmark @start code def=pffFplus
  fun x y =>
    let e := min x.exp y.exp
    let sx := x.num * (2 : Int) ^ (x.exp - e).toNat
    let sy := y.num * (2 : Int) ^ (y.exp - e).toNat
    { num := sx + sy, exp := e }
-- !benchmark @end code def=pffFplus

-- !benchmark @start code_aux def=pffFmult
-- !benchmark @end code_aux def=pffFmult

def Flocq.pffFmult : Flocq.PffFmultSig :=
-- !benchmark @start code def=pffFmult
  fun x y => { num := x.num * y.num, exp := x.exp + y.exp }
-- !benchmark @end code def=pffFmult

-- !benchmark @start code_aux def=pffMZlistAux
-- !benchmark @end code_aux def=pffMZlistAux

def Flocq.pffMZlistAux : Flocq.PffMZlistAuxSig :=
-- !benchmark @start code def=pffMZlistAux
  fun start n => List.range (n + 1) |>.map (fun k => start + Int.ofNat k)
-- !benchmark @end code def=pffMZlistAux

-- !benchmark @start code_aux def=pffMZlist
-- !benchmark @end code_aux def=pffMZlist

def Flocq.pffMZlist : Flocq.PffMZlistSig :=
-- !benchmark @start code def=pffMZlist
  fun lo hi =>
    if lo <= hi then
      Flocq.pffMZlistAux lo (Int.toNat (hi - lo))
    else
      []
-- !benchmark @end code def=pffMZlist

-- !benchmark @start code_aux def=pffMProd
-- !benchmark @end code_aux def=pffMProd

def Flocq.pffMProd : Flocq.PffMProdSig :=
-- !benchmark @start code def=pffMProd
  fun _A _B xs ys =>
    let rec go : List _A → List (_A × _B)
      | [] => []
      | x :: rest => ys.map (fun y => (x, y)) ++ go rest
    go xs
-- !benchmark @end code def=pffMProd
