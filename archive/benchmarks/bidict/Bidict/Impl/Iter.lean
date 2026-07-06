import Bidict.Impl.BidictBase

-- !benchmark @start imports
-- !benchmark @end imports

/-!
# Bidict.Impl.Iter

Iteration utilities for bidictional mappings: `iteritems` enumerates
key-value pairs from an association list, and `inverted` swaps each pair
to produce the inverse view.

DO NOT MODIFY types or signatures — these are the fixed vocabulary.
Implement only the function bodies.
-/

variable {KT VT : Type} [BEq KT] [BEq VT] [Hashable KT] [Hashable VT]

namespace Bidict

-- ── API signatures (DO NOT MODIFY) ───────────────────────────

abbrev IteritemsSig := HashMap KT VT → List (KT × VT)
abbrev InvertedSig  := HashMap KT VT → List (VT × KT)

end Bidict

-- !benchmark @start global_aux
-- !benchmark @end global_aux

-- ── iteritems ────────────────────────────────────────────────

-- !benchmark @start code_aux def=iteritems
-- !benchmark @end code_aux def=iteritems

def Bidict.iteritems (arg : HashMap KT VT) : List (KT × VT) :=
-- !benchmark @start code def=iteritems
  arg
-- !benchmark @end code def=iteritems

-- ── inverted ─────────────────────────────────────────────────

-- !benchmark @start code_aux def=inverted
-- !benchmark @end code_aux def=inverted

def Bidict.inverted (arg : HashMap KT VT) : List (VT × KT) :=
-- !benchmark @start code def=inverted
  arg.map (fun (k, v) => (v, k))
-- !benchmark @end code def=inverted
