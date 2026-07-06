import Verdict.Harness
import Verdict.Impl.Hex

/-!
# Verdict.Spec.Parser

Specifications for the parser layer that are NOT already captured in
`Spec/Base64.lean`. Only three genuine properties remain from the old
`Verdict/Spec/Parser.lean`:

  1. `spec_decode_base64_all_padding` — a four-byte all-`=` block
     decodes to `none` (the no-padding variant of `decodeBase64`
     rejects it).
  2. `spec_parse_x509_der_deterministic` — `parseX509Der` is
     deterministic.
  3. `spec_hex_upper_agreement` — the exec hex encoder agrees with
     the spec hex encoder pointwise.

`parseX509Der` is `opaque` at the Impl layer, so it is referenced
directly as `Verdict.parseX509Der` rather than routed through
`impl.verdict.*` (hence `_impl`).

Upstream:
- `verdict-parser/src/common/base64.rs`  (`spec_parse_helper`)
- `verdict-parser/src/lib.rs`            (`spec_parse_x509_der`)
- `verdict/src/hash.rs`                  (`spec_to_hex_upper` /
                                          `to_hex_upper` agreement)

DO NOT MODIFY — curator-given spec.
-/

/-- A four-byte all-padding block (`"===="`) decodes to `none`.

    Verus: `spec_parse_helper` in `verdict-parser/src/common/base64.rs`.
    The no-padding variant of `decodeBase64` implemented here
    reaches `spec_char_to_bits '=' = some none` on the first byte
    and short-circuits to `none`. -/
def spec_decode_base64_all_padding (impl : RepoImpl) : Prop :=
  impl.verdict.decodeBase64 [0x3D, 0x3D, 0x3D, 0x3D] = none

/-- `parseX509Der` is deterministic: the same DER input always
    yields the same parsed result.

    `parseX509Der` is `opaque` at the Impl layer, so this follows
    purely from functional equality — stated here so dependent
    policies can assume it without pattern-matching into the
    opaque body. -/
def spec_parse_x509_der_deterministic (_impl : RepoImpl) : Prop :=
  ∀ (der : Verdict.Bytes) (c1 c2 : Verdict.Certificate),
    Verdict.parseX509Der der = some c1 →
    Verdict.parseX509Der der = some c2 →
    c1 = c2

/-- The exec hex encoder agrees with the curator-given `specToHexUpper`
    pointwise.

    Verus: `to_hex_upper` in `verdict/src/hash.rs:27` carries
    `ensures res@ == spec_to_hex_upper(data@)`. `specToHexUpper` is
    curator-given vocabulary (fully defined in `Impl/Hex.lean`, not a
    benchmark task), so the spec references it directly rather than
    via `impl.verdict.*`. -/
def spec_hex_upper_agreement (impl : RepoImpl) : Prop :=
  ∀ (data : Verdict.Bytes),
    impl.verdict.toHexUpper data = Verdict.specToHexUpper data
