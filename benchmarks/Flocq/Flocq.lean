-- Flocq root hub — imports all Impl, Bundle, Harness, Spec, and Test files.
--
-- Note: the benchmark now uses Mathlib's `ℝ` throughout the shared Flocq
-- real-number chain, so Raux, GenericFmt, and the Prop modules can be imported
-- by the root hub and checked by `lake build`.

-- ── Impl files (Core.FLT axiom chain — safe to import together) ───────────────
import Flocq.Core.Impl.Zaux
import Flocq.Core.Impl.Raux
import Flocq.Core.Impl.Defs
import Flocq.Core.Impl.Digits
import Flocq.Core.Impl.FLX
import Flocq.Core.Impl.GenericFmt
import Flocq.Core.Impl.FLT
import Flocq.Core.Impl.RoundPred
import Flocq.Core.Impl.Ulp
import Flocq.Calc.Impl.Bracket
import Flocq.Calc.Impl.Operations
import Flocq.Calc.Impl.Div
import Flocq.Calc.Impl.Plus
import Flocq.Calc.Impl.Round
import Flocq.Calc.Impl.Sqrt
import Flocq.IEEE754.Impl.BinaryDefs
import Flocq.IEEE754.Impl.Binary
import Flocq.IEEE754.Impl.Bits
import Flocq.IEEE754.Impl.PrimFloat
import Flocq.Pff.Impl.Pff
import Flocq.Prop.Impl.Sterbenz
import Flocq.Prop.Impl.Relative
import Flocq.Prop.Impl.PlusError
import Flocq.Prop.Impl.MultError
import Flocq.Prop.Impl.DivSqrtError

-- ── Bundle + Harness ──────────────────────────────────────────────────────────
import Flocq.Bundle
import Flocq.Harness

-- ── Spec files (Core.FLT chain — compatible with Bundle/Harness) ──────────────
import Flocq.Core.Spec.Zaux
import Flocq.Core.Spec.Defs
import Flocq.Core.Spec.Digits
import Flocq.Core.Spec.FLX
import Flocq.Core.Spec.FLT
import Flocq.Core.Spec.GenericFmt
import Flocq.Core.Spec.RoundPred
import Flocq.Core.Spec.Ulp
import Flocq.Core.Spec.Raux
import Flocq.Calc.Spec.Bracket
import Flocq.Calc.Spec.Operations
import Flocq.Calc.Spec.Div
import Flocq.Calc.Spec.Plus
import Flocq.Calc.Spec.Round
import Flocq.Calc.Spec.Sqrt
import Flocq.IEEE754.Spec.Binary
import Flocq.IEEE754.Spec.Bits
import Flocq.IEEE754.Spec.PrimFloat
import Flocq.Pff.Spec.Pff
import Flocq.Prop.Spec.Sterbenz
import Flocq.Prop.Spec.Relative
import Flocq.Prop.Spec.PlusError
import Flocq.Prop.Spec.MultError
import Flocq.Prop.Spec.DivSqrtError

-- ── Test ──────────────────────────────────────────────────────────────────────
import Flocq.Test
