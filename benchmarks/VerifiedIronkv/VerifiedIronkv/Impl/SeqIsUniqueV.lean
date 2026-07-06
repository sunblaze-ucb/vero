import VerifiedIronkv.Impl.MarshalIronshtSpecificV
-- !benchmark @start imports
-- !benchmark @end imports

/-!
# VerifiedIronkv.Impl.SeqIsUniqueV

Translated Verus vocabulary and reference implementations for `SeqIsUniqueV`.

DO NOT MODIFY types or signatures. Implement only the marked function bodies.
-/

namespace Bank

abbrev TestUniqueSig := List EndPoint → Bool
abbrev EndpointsContainSig := List EndPoint → EndPoint → Bool

end Bank

-- !benchmark @start global_aux
-- !benchmark @end global_aux

-- !benchmark @start code_aux def=test_unique
-- !benchmark @end code_aux def=test_unique

def Bank.test_unique : Bank.TestUniqueSig :=
-- !benchmark @start code def=test_unique
  fun endpoints =>
    decide (List.Nodup (endpoints.map ioTView))
-- !benchmark @end code def=test_unique

-- !benchmark @start code_aux def=endpoints_contain
-- !benchmark @end code_aux def=endpoints_contain

def Bank.endpoints_contain : Bank.EndpointsContainSig :=
-- !benchmark @start code def=endpoints_contain
  fun endpoints endpoint =>
    endpoints.any (fun e => ioTView e == ioTView endpoint)
-- !benchmark @end code def=endpoints_contain
