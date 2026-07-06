import VerifiedIronkv.Impl.EnvironmentT
-- !benchmark @start imports
-- !benchmark @end imports

/-!
# VerifiedIronkv.Impl.KeysT

Translated Verus vocabulary and reference implementations for `KeysT`.

DO NOT MODIFY types or signatures. Implement only the marked function bodies.
-/

inductive KeyOrdering where
  | Less
  | Equal
  | Greater
  deriving Repr, DecidableEq, BEq, Inhabited

class KeyTrait (K : Type) where
  zero_spec : K
  cmp_spec : K → K → KeyOrdering

structure KeyIterator (K : Type) where
  k : Option K
  deriving Repr, DecidableEq, BEq, Inhabited

structure SHTKey where
  ukey : Nat
  deriving Repr, DecidableEq, BEq, Inhabited

structure KeyRange (K : Type) where
  lo : KeyIterator K
  hi : KeyIterator K
  deriving Repr, DecidableEq, BEq, Inhabited

abbrev AbstractKey := SHTKey

abbrev CKey := SHTKey

instance : KeyTrait SHTKey where
  zero_spec := { ukey := 0 }
  cmp_spec := fun a b =>
    if a.ukey < b.ukey then KeyOrdering.Less
    else if a.ukey = b.ukey then KeyOrdering.Equal
    else KeyOrdering.Greater

namespace Bank

abbrev CloneL151Sig := SHTKey → SHTKey

end Bank

-- !benchmark @start global_aux
-- !benchmark @end global_aux

-- !benchmark @start code_aux def=clone_l151
-- !benchmark @end code_aux def=clone_l151

def Bank.clone_l151 : Bank.CloneL151Sig :=
-- !benchmark @start code def=clone_l151
  fun x => x
-- !benchmark @end code def=clone_l151
