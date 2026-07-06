import Reedsolo.Impl.Field
import Reedsolo.Bundle
import Reedsolo.Harness
import Reedsolo.Spec.Field
import Reedsolo.Test

/-!
# Reedsolo

Root import hub for the GF(2⁸) field + Reed–Solomon systematic-encode
benchmark: GF(2⁸) multiply / power / inverse, the generator polynomial, and the
systematic encoder. The obligations pin the field to the GF(2⁸) of primitive
polynomial `0x11d` and pin the encoder by a unique answer (systematic message
prefix + divisibility of the codeword by the generator).

All arithmetic is discrete over `Nat` (a byte is a `Nat < 256`); there is no
`Float`. Field subtraction is XOR (`^^^`); the primitive element is `α = 2`.
-/
