-- Build hub for the benchmark project. This file imports both the live
-- benchmark surface and frozen support context so the package compiles
-- as one Lean project. The scored implementation surface is defined by
-- `VestV2.Bundle`, `VestV2.Harness`, and the manifest's obligation-spec
-- classification.

-- Layer 0
import VestV2.Impl.Errors
import VestV2.Impl.Properties
import VestV2.Impl.BufTraits
-- Layer 1
import VestV2.Impl.RegularLeb128
import VestV2.Impl.RegularLeb128Rec
import VestV2.Impl.RegularLeb128Unrolled
import VestV2.Impl.RegularRepetition
import VestV2.Impl.RegularModifier
import VestV2.Impl.RegularUints
import VestV2.Impl.RegularDisjoint
import VestV2.Impl.RegularSequence
import VestV2.Impl.RegularVariant
import VestV2.Impl.RegularTag
import VestV2.Impl.BitcoinVarint
-- Layer 2
import VestV2.Impl.Utils
import VestV2.Impl.RegularBytes
import VestV2.Impl.RegularEnd
import VestV2.Impl.RegularFail
import VestV2.Impl.RegularSuccess
import VestV2.Impl.RegularClone
-- Specs
import VestV2.Spec.Errors
import VestV2.Spec.Properties
import VestV2.Spec.BufTraits
import VestV2.Spec.RegularLeb128
import VestV2.Spec.RegularLeb128Rec
import VestV2.Spec.RegularLeb128Unrolled
import VestV2.Spec.RegularRepetition
import VestV2.Spec.RegularModifier
import VestV2.Spec.RegularUints
import VestV2.Spec.RegularDisjoint
import VestV2.Spec.RegularSequence
import VestV2.Spec.RegularVariant
import VestV2.Spec.RegularTag
import VestV2.Spec.BitcoinVarint
import VestV2.Spec.Utils
import VestV2.Spec.RegularBytes
import VestV2.Spec.RegularEnd
import VestV2.Spec.RegularFail
import VestV2.Spec.RegularSuccess
import VestV2.Spec.RegularClone
-- Glue
import VestV2.Bundle
import VestV2.Harness
import VestV2.Test
