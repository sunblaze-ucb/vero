import DedekindReals.Impl.Cut
import DedekindReals.Impl.Additive
import DedekindReals.Impl.Multiplication

-- !benchmark @start imports
-- !benchmark @end imports

/-!
# DedekindReals.Impl.Order

Frozen order-theoretic vocabulary for Dedekind cuts translated from the Coq
`Order` module.

DO NOT MODIFY types or signatures -- these are the fixed vocabulary.
This module has no assigned scored APIs.
-/

namespace DedekindReals

-- !benchmark @start global_aux
-- !benchmark @end global_aux

-- Pure spec helpers.

def Rlt_le_trans : Prop := ∀ (x y z : R), Rlt x y → Rle y z → Rlt x z

def Rle_lt_trans : Prop := ∀ (x y z : R), Rle x y → Rlt y z → Rlt x z

-- Pure API helpers.

axiom unfinishedOrder : ∀ (A : Type), A

end DedekindReals
