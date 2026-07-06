import Verdict.Impl.Asn1
import Verdict.Impl.PolicyCommon

-- !benchmark @start imports
-- !benchmark @end imports

/-!
# Verdict.Impl.Convert

Conversion from the parser-layer `Verdict.Certificate` (mirror of
Verus's `SpecCertificateValue`) to the policy-layer
`Verdict.Policy.AbstractCertificate` (mirror of Verus's
`policy::Certificate`).

Upstream: `verdict/src/convert.rs` — `Certificate::spec_from`.

`certFromParsed` is `opaque` — it is NOT a benchmark task. The full
Rust conversion is ~1125 lines spanning ~30 extension-decoding
combinators (extension dispatch, time-format conversion, key-type
dispatch, subject-alt-name decoding, etc.). Policy predicates
reference `certFromParsed` without seeing inside; what we need from
it is captured in `Spec/Convert.lean` as preservation properties.
-/

namespace Verdict

/-- Convert parser-layer `Certificate` to policy-layer
    `AbstractCertificate`. Returns `none` on conversion failure
    (unrecognised time format, malformed extension, etc.).

    Verus: `Certificate::from(&CertificateValue)` in
    `verdict/src/convert.rs` (`rspec!`-generated `spec_from`). -/
opaque certFromParsed : Verdict.Certificate → Option Verdict.Policy.AbstractCertificate

end Verdict
