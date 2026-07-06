import Bmpwriter.Impl.Image
import Bmpwriter.Bundle
import Bmpwriter.Harness
import Bmpwriter.Spec.Image
import Bmpwriter.Test

/-!
# Bmpwriter

Root import hub for the fixed-schema image writer/parser benchmark. The format
is a 7-byte header (three magic bytes, then a 16-bit big-endian width and a
16-bit big-endian height) followed by a raw pixel payload.

API: `build w h px` serializes a triple to a flat byte list; `parseWidth` /
`parseHeight` decode the two dimension fields; `parse` validates the magic and
recovers `(width, height, payload)`; `validMagic` is the leading-tag observer.
Dimensions are `Nat`, bytes are `UInt8`. Behaviour is pinned by
`Spec/Image.lean`.
-/
