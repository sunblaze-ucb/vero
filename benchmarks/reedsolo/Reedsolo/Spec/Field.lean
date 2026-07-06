import Reedsolo.Harness

/-!
# Reedsolo.Spec.Field

Specifications for the GF(2⁸) field core and the Reed–Solomon systematic
encoder. Each `spec_*` is a property over an arbitrary `impl : RepoImpl`; an
API is always reached through `impl.reedsolo.<fn>`.

The field is pinned to the GF(2⁸) of primitive polynomial `0x11d` by anchoring
`gfMul` to the frozen reference `clmulModPrimRef` (`spec_gf_mul_carryless_anchored`);
the remaining field laws (commutativity, unit, distributivity over XOR, closure)
are the properties any GF(2⁸) multiply satisfies. The encoder is pinned by a
unique answer: the codeword carries the message as a prefix
(`spec_encode_systematic`) and is divisible by the generator
(`spec_encode_divisible`, against the frozen `polyModRef` / `genPolyRef`). The
generator is pinned to `∏(x − α^i)` (`spec_generator_poly_recurrence`) plus
concrete vectors.

The references below (`clmulBitsRef`, `clmulModPrimRef`, `gfPolyMulRef`,
`genPolyRef`, `polyModRef`) are the specification's ground truth: they never
refer to `impl`, and are written purely in terms of Lean's bit operations
(`Nat.testBit`, `<<<`, `^^^`) and list operations.

DO NOT MODIFY.
-/

namespace Reedsolo

-- ── Frozen GF(2⁸) field reference (DO NOT MODIFY) ───────────────

/-- The fixed primitive polynomial `x⁸ + x⁴ + x³ + x² + 1 = 0x11d`. -/
def primPolyRef : Nat := 0x11d

/-- The primitive element `α = 2 = x`. -/
def alphaRef : Nat := 2

/-- Frozen carry-less product of the low `n` bits of `a` against `b`. -/
def clmulBitsRef : Nat → Nat → Nat → Nat
  | 0, _, _ => 0
  | (n+1), a, b => (if a.testBit n then b <<< n else 0) ^^^ clmulBitsRef n a b

/-- Frozen carry-less product of two bytes. -/
def clmulRef (a b : Nat) : Nat := clmulBitsRef 8 a b

/-- Frozen reduction modulo the primitive polynomial. -/
def reduceRef : Nat → Nat → Nat
  | 0, x => x
  | (fuel+1), x =>
      let x := if x.testBit (8 + fuel) then x ^^^ (primPolyRef <<< fuel) else x
      reduceRef fuel x

/-- Frozen GF(2⁸) multiply of `0x11d`: the field's definition via bit shifts,
    XOR, and reduction. -/
def clmulModPrimRef (a b : Nat) : Nat := reduceRef 7 (clmulRef a b)

/-- Frozen GF(2⁸) power against the frozen multiply. -/
def gfPowRef (a : Nat) : Nat → Nat
  | 0 => 1
  | (e+1) => clmulModPrimRef (gfPowRef a e) a

/-- Frozen GF(2⁸) power against the frozen multiply; `gfPowSqRef 8 a 254 = a^254`
    is the field inverse of a nonzero `a`. -/
def gfPowSqRef : Nat → Nat → Nat → Nat
  | 0, _, _ => 1
  | (n+1), base, e =>
      let half := gfPowSqRef n (clmulModPrimRef base base) (e / 2)
      if e % 2 == 1 then clmulModPrimRef half base else half

-- ── Frozen polynomial reference (DO NOT MODIFY) ─────────────────

/-- Frozen GF(2⁸) polynomial multiply (highest-degree-first coefficient lists),
    against the frozen field multiply. -/
def gfPolyMulRef (p q : List Nat) : List Nat :=
  let lp := p.length; let lq := q.length
  if lp == 0 || lq == 0 then []
  else (List.range (lp + lq - 1)).map (fun k =>
    (List.range lp).foldl (fun acc i =>
      let j := k - i
      if i ≤ k && j < lq then acc ^^^ clmulModPrimRef (p.getD i 0) (q.getD j 0) else acc) 0)

/-- Frozen Reed–Solomon generator polynomial `∏_{i<nsym} (x − α^i)`. -/
def genPolyRef (nsym : Nat) : List Nat :=
  (List.range nsym).foldl (fun g i => gfPolyMulRef g [1, gfPowRef alphaRef i]) [1]

/-- One frozen synthetic-division elimination step at position `i`. -/
def polyDivStepRef (divisor : List Nat) (msgout : List Nat) (i : Nat) : List Nat :=
  let coef := msgout.getD i 0
  if coef == 0 then msgout
  else (List.range divisor.length).foldl (fun m j =>
    if j == 0 then m
    else m.set (i + j) ((m.getD (i+j) 0) ^^^ clmulModPrimRef (divisor.getD j 0) coef)) msgout

/-- Frozen polynomial remainder of `dividend` modulo a monic `divisor`. -/
def polyModRef (dividend divisor : List Nat) : List Nat :=
  let sep := divisor.length - 1
  let n := dividend.length - sep
  let final := (List.range n).foldl (fun m i => polyDivStepRef divisor m i) dividend
  final.drop (final.length - sep)

/-- Frozen Horner evaluation of a highest-degree-first polynomial `p` at a point
    `x` in the field of `0x11d` (using the frozen field multiply and XOR add). -/
def polyEvalRef (p : List Nat) (x : Nat) : Nat :=
  p.foldl (fun acc coeff => (clmulModPrimRef acc x) ^^^ coeff) 0

/-- Frozen pointwise XOR (field addition) of two coefficient lists, truncated to
    the shorter length. -/
def xorListRef : List Nat → List Nat → List Nat
  | [], _ => []
  | _, [] => []
  | x :: xs, y :: ys => (x ^^^ y) :: xorListRef xs ys

/-- Frozen XOR-sum of the first-`nsym` field powers `α^i`, `0 ≤ i < nsym`. -/
def rootXorSumRef (nsym : Nat) : Nat :=
  (List.range nsym).foldl (fun acc i => acc ^^^ gfPowRef alphaRef i) 0

-- ════════════════════════════════════════════════════════════════
-- gfMul: the carry-less anchor + the field laws
-- ════════════════════════════════════════════════════════════════

/-- Carry-less multiply anchor: `gfMul a b = clmulModPrimRef a b` for all byte
    pairs, pinning `gfMul` to the GF(2⁸) multiplication of the field of `0x11d`. -/
def spec_gf_mul_carryless_anchored (impl : RepoImpl) : Prop :=
  ∀ (a b : Nat), impl.reedsolo.gfMul a b = clmulModPrimRef a b

/-- Annihilation: `gfMul a 0 = 0` — the field zero absorbs. -/
def spec_gf_mul_zero (impl : RepoImpl) : Prop :=
  ∀ (a : Nat), impl.reedsolo.gfMul a 0 = 0

/-- Multiplicative identity: `1` is the unit of the field. For any byte
    `a < 256`, `gfMul a 1 = a`. -/
def spec_gf_mul_one (impl : RepoImpl) : Prop :=
  ∀ (a : Nat), a < 256 → impl.reedsolo.gfMul a 1 = a

/-- Commutativity: for bytes `a, b < 256`, `gfMul a b = gfMul b a`. -/
def spec_gf_mul_comm (impl : RepoImpl) : Prop :=
  ∀ (a b : Nat), a < 256 → b < 256 → impl.reedsolo.gfMul a b = impl.reedsolo.gfMul b a

/-- Distributivity over XOR (field addition): `gfMul a (b ⊕ c) = gfMul a b ⊕
    gfMul a c`. -/
def spec_gf_mul_distrib_xor (impl : RepoImpl) : Prop :=
  ∀ (a b c : Nat), impl.reedsolo.gfMul a (b ^^^ c)
    = (impl.reedsolo.gfMul a b) ^^^ (impl.reedsolo.gfMul a c)

/-- Closure: the field product of two bytes is again a byte. For bytes
    `a, b < 256`, `gfMul a b < 256`. -/
def spec_gf_mul_range (impl : RepoImpl) : Prop :=
  ∀ (a b : Nat), a < 256 → b < 256 → impl.reedsolo.gfMul a b < 256

-- ════════════════════════════════════════════════════════════════
-- gfPow / gfInverse: recurrence + the unique Fermat inverse
-- ════════════════════════════════════════════════════════════════

/-- Power base case: `gfPow a 0 = 1` (the empty product). -/
def spec_gf_pow_zero (impl : RepoImpl) : Prop :=
  ∀ (a : Nat), impl.reedsolo.gfPow a 0 = 1

/-- Power recurrence: `gfPow a (e+1) = gfMul (gfPow a e) a`, pinning `gfPow` to
    iterated field multiplication. -/
def spec_gf_pow_succ (impl : RepoImpl) : Prop :=
  ∀ (a e : Nat),
    impl.reedsolo.gfPow a (e + 1) = impl.reedsolo.gfMul (impl.reedsolo.gfPow a e) a

/-- Inverse anchor: `gfInverse a = gfPowSqRef 8 a 254 = a^254`. In GF(2⁸) the
    multiplicative group has order 255, so `a^254` is the unique inverse of a
    nonzero `a`. -/
def spec_gf_inverse_pow254_anchored (impl : RepoImpl) : Prop :=
  ∀ (a : Nat), impl.reedsolo.gfInverse a = gfPowSqRef 8 a 254

/-- Inverse correctness witness: for concrete nonzero bytes, the inverse
    multiplies back to the unit, `gfMul a (gfInverse a) = 1`. -/
def spec_gf_inverse_correct_witness (impl : RepoImpl) : Prop :=
  impl.reedsolo.gfMul 2 (impl.reedsolo.gfInverse 2) = 1
  ∧ impl.reedsolo.gfMul 7 (impl.reedsolo.gfInverse 7) = 1
  ∧ impl.reedsolo.gfMul 19 (impl.reedsolo.gfInverse 19) = 1
  ∧ impl.reedsolo.gfMul 255 (impl.reedsolo.gfInverse 255) = 1

/-- Power byte closure: for every byte `a < 256` and every exponent `e`,
    `gfPow a e < 256`. Holds over all exponents, not a finite table. -/
def spec_gf_pow_range (impl : RepoImpl) : Prop :=
  ∀ (a e : Nat), a < 256 → impl.reedsolo.gfPow a e < 256

/-- Inverse byte closure: for `a < 256`, `gfInverse a < 256`. -/
def spec_gf_inverse_range (impl : RepoImpl) : Prop :=
  ∀ (a : Nat), a < 256 → impl.reedsolo.gfInverse a < 256

-- ════════════════════════════════════════════════════════════════
-- rsGeneratorPoly: frozen product recurrence + concrete vectors + shape
-- ════════════════════════════════════════════════════════════════

/-- Generator base case: the empty product is the constant polynomial `[1]`. -/
def spec_generator_poly_base (impl : RepoImpl) : Prop :=
  impl.reedsolo.rsGeneratorPoly 0 = [1]

/-- Generator recurrence: `rsGeneratorPoly (n+1) = gfPolyMulRef (rsGeneratorPoly n)
    [1, α^n]` (against the frozen multiply and `α^n`), pinning the generator to
    `∏_{i<nsym}(x − α^i)`. -/
def spec_generator_poly_recurrence (impl : RepoImpl) : Prop :=
  ∀ (n : Nat),
    impl.reedsolo.rsGeneratorPoly (n + 1)
      = gfPolyMulRef (impl.reedsolo.rsGeneratorPoly n) [1, gfPowRef alphaRef n]

/-- Concrete generator vectors, fixing the absolute coefficients:
    `rsGeneratorPoly 1 = [1,1]`, `2 = [1,3,2]`, `3 = [1,7,14,8]`. -/
def spec_generator_poly_concrete (impl : RepoImpl) : Prop :=
  impl.reedsolo.rsGeneratorPoly 1 = [1, 1]
  ∧ impl.reedsolo.rsGeneratorPoly 2 = [1, 3, 2]
  ∧ impl.reedsolo.rsGeneratorPoly 3 = [1, 7, 14, 8]

/-- Generator shape: the degree-`nsym` generator has length `nsym + 1`. -/
def spec_generator_poly_length (impl : RepoImpl) : Prop :=
  ∀ (nsym : Nat), (impl.reedsolo.rsGeneratorPoly nsym).length = nsym + 1

/-- Generator is monic: for every `nsym`, the highest-degree coefficient is `1`,
    `(rsGeneratorPoly nsym).head? = some 1`. -/
def spec_generator_poly_monic (impl : RepoImpl) : Prop :=
  ∀ (nsym : Nat), (impl.reedsolo.rsGeneratorPoly nsym).head? = some 1

/-- Generator byte closure: every coefficient of the generator is a byte, for
    all `nsym`, `∀ x ∈ rsGeneratorPoly nsym, x < 256`. -/
def spec_generator_poly_coeffs_byte (impl : RepoImpl) : Prop :=
  ∀ (nsym : Nat), ∀ x ∈ impl.reedsolo.rsGeneratorPoly nsym, x < 256

-- ════════════════════════════════════════════════════════════════
-- rsEncodeMsg: systematic + divisible
-- ════════════════════════════════════════════════════════════════

/-- Systematic prefix: the first `msg.length` symbols of the codeword are the
    message verbatim, `(rsEncodeMsg msg nsym).take msg.length = msg`. -/
def spec_encode_systematic (impl : RepoImpl) : Prop :=
  ∀ (msg : List Nat) (nsym : Nat),
    (impl.reedsolo.rsEncodeMsg msg nsym).take msg.length = msg

/-- Codeword length: a `k`-symbol message with `nsym` parity symbols yields a
    codeword of length `k + nsym`. -/
def spec_encode_length (impl : RepoImpl) : Prop :=
  ∀ (msg : List Nat) (nsym : Nat),
    (impl.reedsolo.rsEncodeMsg msg nsym).length = msg.length + nsym

/-- Divisibility: the codeword is divisible by the generator — the frozen
    remainder of `rsEncodeMsg msg nsym` modulo `genPolyRef nsym` is the all-zero
    parity block `List.replicate nsym 0`. The defining Reed–Solomon property. -/
def spec_encode_divisible (impl : RepoImpl) : Prop :=
  ∀ (msg : List Nat) (nsym : Nat),
    polyModRef (impl.reedsolo.rsEncodeMsg msg nsym) (impl.reedsolo.rsGeneratorPoly nsym)
      = List.replicate nsym 0

/-- Systematic ∧ divisible: the codeword carries the message as a prefix AND is
    divisible by the generator — the full systematic-encode contract. -/
def spec_encode_systematic_and_divisible (impl : RepoImpl) : Prop :=
  ∀ (msg : List Nat) (nsym : Nat),
    (impl.reedsolo.rsEncodeMsg msg nsym).take msg.length = msg
    ∧ polyModRef (impl.reedsolo.rsEncodeMsg msg nsym) (impl.reedsolo.rsGeneratorPoly nsym)
        = List.replicate nsym 0

/-- Empty-message codeword: `rsEncodeMsg [] nsym = List.replicate nsym 0` for
    every `nsym`. -/
def spec_encode_empty_zero (impl : RepoImpl) : Prop :=
  ∀ (nsym : Nat), impl.reedsolo.rsEncodeMsg [] nsym = List.replicate nsym 0

-- ════════════════════════════════════════════════════════════════
-- Deeper field + encoder laws
-- ════════════════════════════════════════════════════════════════

/-- Associativity of byte multiplication: for bytes `a, b, c < 256`,
    `gfMul (gfMul a b) c = gfMul a (gfMul b c)`. -/
def spec_gf_mul_assoc (impl : RepoImpl) : Prop :=
  ∀ (a b c : Nat), a < 256 → b < 256 → c < 256 →
    impl.reedsolo.gfMul (impl.reedsolo.gfMul a b) c
      = impl.reedsolo.gfMul a (impl.reedsolo.gfMul b c)

/-- Exponent-addition law: `gfPow a (e + f) = gfMul (gfPow a e) (gfPow a f)`
    for every byte `a < 256` and all exponents. -/
def spec_gf_pow_add (impl : RepoImpl) : Prop :=
  ∀ (a e f : Nat), a < 256 →
    impl.reedsolo.gfPow a (e + f)
      = impl.reedsolo.gfMul (impl.reedsolo.gfPow a e) (impl.reedsolo.gfPow a f)

/-- Iterated-product closure: the running GF product of a list of bytes,
    starting from the unit, is again a byte. -/
def spec_gf_mul_fold_range (impl : RepoImpl) : Prop :=
  ∀ (xs : List Nat),
    (∀ x ∈ xs, x < 256) →
    xs.foldl (fun acc x => impl.reedsolo.gfMul acc x) 1 < 256

/-- Generator trailing coefficient: the last coefficient of the degree-`nsym`
    generator is `α` raised to `nsym·(nsym−1)/2`. -/
def spec_generator_poly_tail_power (impl : RepoImpl) : Prop :=
  ∀ (nsym : Nat),
    (impl.reedsolo.rsGeneratorPoly nsym).getLast?
      = some (impl.reedsolo.gfPow alphaRef ((nsym * (nsym - 1)) / 2))

/-- Codeword byte closure: encoding a byte message produces a codeword whose
    every symbol is a byte. -/
def spec_encode_codeword_coeffs_byte (impl : RepoImpl) : Prop :=
  ∀ (msg : List Nat) (nsym : Nat),
    (∀ x ∈ msg, x < 256) →
    ∀ x ∈ impl.reedsolo.rsEncodeMsg msg nsym, x < 256

/-- Systematic-parity uniqueness: if appending a length-`nsym` block `parity`
    to `msg` yields a word divisible by the generator, then `parity` is exactly
    the parity block the encoder emits (the tail of the codeword). -/
def spec_encode_parity_unique (impl : RepoImpl) : Prop :=
  ∀ (msg parity : List Nat) (nsym : Nat),
    parity.length = nsym →
    polyModRef (msg ++ parity) (impl.reedsolo.rsGeneratorPoly nsym)
      = List.replicate nsym 0 →
    parity = (impl.reedsolo.rsEncodeMsg msg nsym).drop msg.length

-- ════════════════════════════════════════════════════════════════
-- Field-algebra tower: bilinearity, Frobenius, group order, inverses
-- ════════════════════════════════════════════════════════════════

/-- Bilinearity and squaring additivity: `gfMul` distributes over XOR in the
    first argument and in the second, and `gfMul (a ⊕ b) (a ⊕ b) = gfMul a a ⊕
    gfMul b b`, for bytes `a, b, c < 256`. -/
def spec_gf_mul_xor_linear_square_additive (impl : RepoImpl) : Prop :=
  ∀ (a b c : Nat), a < 256 → b < 256 → c < 256 →
    impl.reedsolo.gfMul (a ^^^ b) c
        = ((impl.reedsolo.gfMul a c) ^^^ (impl.reedsolo.gfMul b c))
    ∧ impl.reedsolo.gfMul c (a ^^^ b)
        = ((impl.reedsolo.gfMul c a) ^^^ (impl.reedsolo.gfMul c b))
    ∧ impl.reedsolo.gfMul (a ^^^ b) (a ^^^ b)
        = ((impl.reedsolo.gfMul a a) ^^^ (impl.reedsolo.gfMul b b))

/-- Frobenius additivity: for every `k`, the map `x ↦ gfPow x (2^k)` distributes
    over XOR — `gfPow (a ⊕ b) (2^k) = gfPow a (2^k) ⊕ gfPow b (2^k)` for bytes
    `a, b < 256`. -/
def spec_gf_frobenius_additive (impl : RepoImpl) : Prop :=
  ∀ (a b k : Nat), a < 256 → b < 256 →
    impl.reedsolo.gfPow (a ^^^ b) (2 ^ k)
      = ((impl.reedsolo.gfPow a (2 ^ k)) ^^^ (impl.reedsolo.gfPow b (2 ^ k)))

/-- Multiplicative order: for every nonzero byte `a < 256`, `gfPow a 255 = 1`,
    and powers are periodic with period 255, `gfPow a (e + 255) = gfPow a e`. -/
def spec_gf_pow_period_255 (impl : RepoImpl) : Prop :=
  ∀ (a e : Nat), a < 256 → a ≠ 0 →
    impl.reedsolo.gfPow a 255 = 1
    ∧ impl.reedsolo.gfPow a (e + 255) = impl.reedsolo.gfPow a e

/-- Left cancellation: for nonzero `a < 256` and bytes `b, c < 256`, if
    `gfMul a b = gfMul a c` then `b = c`. -/
def spec_gf_mul_cancel (impl : RepoImpl) : Prop :=
  ∀ (a b c : Nat), a < 256 → a ≠ 0 → b < 256 → c < 256 →
    impl.reedsolo.gfMul a b = impl.reedsolo.gfMul a c → b = c

/-- Inverse correctness and uniqueness: for every nonzero byte `a < 256`,
    `gfInverse a` is a byte, `gfMul a (gfInverse a) = 1`, and it is the only byte
    `b < 256` with `gfMul a b = 1`. -/
def spec_gf_inverse_unique_nonzero (impl : RepoImpl) : Prop :=
  ∀ (a : Nat), a < 256 → a ≠ 0 →
    impl.reedsolo.gfInverse a < 256
    ∧ impl.reedsolo.gfMul a (impl.reedsolo.gfInverse a) = 1
    ∧ ∀ (b : Nat), b < 256 → impl.reedsolo.gfMul a b = 1 → b = impl.reedsolo.gfInverse a

/-- Inverse is involutive and reverses products: for nonzero bytes `a, b < 256`,
    `gfInverse (gfInverse a) = a` and
    `gfInverse (gfMul a b) = gfMul (gfInverse a) (gfInverse b)`. -/
def spec_gf_inverse_involutive_and_product (impl : RepoImpl) : Prop :=
  ∀ (a b : Nat), a < 256 → b < 256 → a ≠ 0 → b ≠ 0 →
    impl.reedsolo.gfInverse (impl.reedsolo.gfInverse a) = a
    ∧ impl.reedsolo.gfInverse (impl.reedsolo.gfMul a b)
        = impl.reedsolo.gfMul (impl.reedsolo.gfInverse a) (impl.reedsolo.gfInverse b)

/-- Primitivity of `α`: the first 255 powers `α^0, …, α^254` are pairwise
    distinct — `gfPow α i = gfPow α j` with `i, j < 255` forces `i = j`. -/
def spec_alpha_powers_distinct_before_255 (impl : RepoImpl) : Prop :=
  ∀ (i j : Nat), i < 255 → j < 255 →
    impl.reedsolo.gfPow alphaRef i = impl.reedsolo.gfPow alphaRef j → i = j

-- ════════════════════════════════════════════════════════════════
-- Generator structure + encoder syndrome/linearity
-- ════════════════════════════════════════════════════════════════

/-- Generator roots: every `α^i` with `i < nsym` is a root of the degree-`nsym`
    generator — the frozen Horner evaluation of `rsGeneratorPoly nsym` at
    `gfPow α i` is `0`. -/
def spec_generator_roots_vanish (impl : RepoImpl) : Prop :=
  ∀ (nsym i : Nat), i < nsym →
    polyEvalRef (impl.reedsolo.rsGeneratorPoly nsym) (impl.reedsolo.gfPow alphaRef i) = 0

/-- Generator next-to-leading coefficient: for `nsym > 0`, the second coefficient
    of `rsGeneratorPoly nsym` equals the frozen XOR-sum of the roots
    `rootXorSumRef nsym`. -/
def spec_generator_second_coeff_xor_roots (impl : RepoImpl) : Prop :=
  ∀ (nsym : Nat), nsym > 0 →
    (impl.reedsolo.rsGeneratorPoly nsym).getD 1 0 = rootXorSumRef nsym

/-- Encoder XOR-linearity: for equal-length byte messages, encoding their
    pointwise XOR equals the pointwise XOR of their codewords —
    `rsEncodeMsg (xorListRef m₁ m₂) nsym = xorListRef (rsEncodeMsg m₁ nsym)
    (rsEncodeMsg m₂ nsym)`. -/
def spec_encode_xor_linear (impl : RepoImpl) : Prop :=
  ∀ (msg1 msg2 : List Nat) (nsym : Nat),
    msg1.length = msg2.length →
    (∀ x ∈ msg1, x < 256) →
    (∀ x ∈ msg2, x < 256) →
    impl.reedsolo.rsEncodeMsg (xorListRef msg1 msg2) nsym
      = xorListRef (impl.reedsolo.rsEncodeMsg msg1 nsym) (impl.reedsolo.rsEncodeMsg msg2 nsym)

/-- Codeword syndromes vanish: for a byte message and every `i < nsym`, the
    frozen Horner evaluation of the codeword at `gfPow α i` is `0`. -/
def spec_encode_syndromes_vanish (impl : RepoImpl) : Prop :=
  ∀ (msg : List Nat) (nsym i : Nat),
    (∀ x ∈ msg, x < 256) → i < nsym →
    polyEvalRef (impl.reedsolo.rsEncodeMsg msg nsym) (impl.reedsolo.gfPow alphaRef i) = 0

-- ── Frozen list references for the code-geometry laws (DO NOT MODIFY) ──

/-- Frozen single-symbol perturbation: XOR `mag` into position `pos` of `xs`. -/
def xorAtRef (xs : List Nat) (pos mag : Nat) : List Nat :=
  xs.set pos ((xs.getD pos 0) ^^^ mag)

/-- Frozen Hamming distance: the number of positions at which two coefficient
    lists differ (an extra tail symbol counts as a difference). -/
def countDiffRef : List Nat → List Nat → Nat
  | [], [] => 0
  | [], _ :: ys => 1 + countDiffRef [] ys
  | _ :: xs, [] => 1 + countDiffRef xs []
  | x :: xs, y :: ys => (if x = y then 0 else 1) + countDiffRef xs ys

/-- Frozen Hamming weight: the number of nonzero coefficients of a list. -/
def hammingWeightRef : List Nat → Nat
  | [] => 0
  | x :: xs => (if x = 0 then 0 else 1) + hammingWeightRef xs

-- ════════════════════════════════════════════════════════════════
-- Primitivity, subfields, trace, code geometry
-- ════════════════════════════════════════════════════════════════

/-- Primitive-element order and discrete logarithm: `α` has exact
    multiplicative order 255 (`gfPow α 255 = 1`, and no `0 < d < 255` returns
    `1`), and every nonzero byte is `α^i` for a unique `i < 255`. -/
def spec_alpha_order_and_log_complete (impl : RepoImpl) : Prop :=
  impl.reedsolo.gfPow alphaRef 255 = 1
  ∧ (∀ (d : Nat), d < 255 → impl.reedsolo.gfPow alphaRef d = 1 → d = 0)
  ∧ (∀ (a : Nat), a < 256 → a ≠ 0 →
      ∃ i : Nat,
        i < 255 ∧ impl.reedsolo.gfPow alphaRef i = a
        ∧ ∀ (j : Nat), j < 255 → impl.reedsolo.gfPow alphaRef j = a → j = i)

/-- Generator uniqueness: the degree-`nsym` generator is the only monic byte
    polynomial of length `nsym + 1` whose frozen Horner evaluation vanishes at
    every `α^i`, `i < nsym`. Any such `p` equals `rsGeneratorPoly nsym`. -/
def spec_generator_monic_roots_unique (impl : RepoImpl) : Prop :=
  ∀ (nsym : Nat) (p : List Nat),
    nsym ≤ 255 →
    p.length = nsym + 1 →
    p.head? = some 1 →
    (∀ c ∈ p, c < 256) →
    (∀ i : Nat, i < nsym → polyEvalRef p (impl.reedsolo.gfPow alphaRef i) = 0) →
    p = impl.reedsolo.rsGeneratorPoly nsym

/-- Single-error syndromes: after XOR-ing a nonzero magnitude `mag` into one
    codeword position `pos`, the zeroth frozen syndrome recovers `mag`, the
    ratio of the first two syndromes is `α^(n−1−pos)`, and that ratio is a root
    of the frozen locator `[loc, 1]` at its inverse. -/
def spec_single_error_syndrome_ratio_locator (impl : RepoImpl) : Prop :=
  ∀ (msg : List Nat) (nsym pos mag : Nat),
    (∀ x ∈ msg, x < 256) →
    2 ≤ nsym →
    mag < 256 → mag ≠ 0 →
    pos < (impl.reedsolo.rsEncodeMsg msg nsym).length →
    let cw := impl.reedsolo.rsEncodeMsg msg nsym
    let err := xorAtRef cw pos mag
    let s0 := polyEvalRef err (impl.reedsolo.gfPow alphaRef 0)
    let s1 := polyEvalRef err (impl.reedsolo.gfPow alphaRef 1)
    let loc := impl.reedsolo.gfMul s1 (impl.reedsolo.gfInverse s0)
    s0 = mag
    ∧ loc = impl.reedsolo.gfPow alphaRef (cw.length - 1 - pos)
    ∧ polyEvalRef [loc, 1] (impl.reedsolo.gfInverse loc) = 0

/-- Minimum distance: the codewords of two distinct equal-length byte messages
    (with total length at most 255) differ in at least `nsym + 1` positions,
    measured by the frozen `countDiffRef`. -/
def spec_encode_mds_distance_bound (impl : RepoImpl) : Prop :=
  ∀ (msg1 msg2 : List Nat) (nsym : Nat),
    msg1.length = msg2.length →
    (∀ x ∈ msg1, x < 256) →
    (∀ x ∈ msg2, x < 256) →
    msg1 ≠ msg2 →
    msg1.length + nsym ≤ 255 →
    nsym + 1 ≤ countDiffRef (impl.reedsolo.rsEncodeMsg msg1 nsym)
                            (impl.reedsolo.rsEncodeMsg msg2 nsym)

/-- Nonzero-codeword weight: a byte message with at least one nonzero symbol
    (and total length at most 255) has a codeword of frozen Hamming weight at
    least `nsym + 1`. -/
def spec_encode_nonzero_weight_bound (impl : RepoImpl) : Prop :=
  ∀ (msg : List Nat) (nsym : Nat),
    (∀ x ∈ msg, x < 256) →
    (∃ x, x ∈ msg ∧ x ≠ 0) →
    msg.length + nsym ≤ 255 →
    nsym + 1 ≤ hammingWeightRef (impl.reedsolo.rsEncodeMsg msg nsym)

/-- Group-orbit sum and product: for every nonzero byte `a`, XOR-summing
    `a · α^i` over `i < 255` gives `0`, and the running `gfMul` product of the
    same 255 terms from the unit gives `1` (the scaled orbit is the whole
    nonzero group). -/
def spec_multiplicative_group_scaled_sum_product (impl : RepoImpl) : Prop :=
  ∀ (a : Nat), a < 256 → a ≠ 0 →
    (List.range 255).foldl
        (fun acc i => acc ^^^ impl.reedsolo.gfMul a (impl.reedsolo.gfPow alphaRef i)) 0 = 0
    ∧ (List.range 255).foldl
        (fun acc i => impl.reedsolo.gfMul acc (impl.reedsolo.gfMul a (impl.reedsolo.gfPow alphaRef i))) 1 = 1

/-- Absolute trace: `Tr x = ⊕_{k<8} gfPow x (2^k)` takes values in `{0,1}`, is
    additive over XOR, and is fixed by squaring, for all bytes `a, b`. -/
def spec_trace_binary_linear_frobenius (impl : RepoImpl) : Prop :=
  ∀ (a b : Nat), a < 256 → b < 256 →
    let trace := fun x =>
      (List.range 8).foldl (fun acc k => acc ^^^ impl.reedsolo.gfPow x (2 ^ k)) 0
    (trace a = 0 ∨ trace a = 1)
    ∧ trace (a ^^^ b) = (trace a ^^^ trace b)
    ∧ trace (impl.reedsolo.gfPow a 2) = trace a

/-- Subfield fixed points: for `k ∈ {1,2,4}` and `j < 255`, the power `α^j` is
    fixed by `x ↦ gfPow x (2^k)` exactly when `255 / (2^k − 1)` divides `j`
    (the fixed points of the `2^k`-power map are the `GF(2^k)` subgroup). -/
def spec_subfield_alpha_exponent_characterization (impl : RepoImpl) : Prop :=
  ∀ (k j : Nat),
    (k = 1 ∨ k = 2 ∨ k = 4) →
    j < 255 →
    (impl.reedsolo.gfPow (impl.reedsolo.gfPow alphaRef j) (2 ^ k)
        = impl.reedsolo.gfPow alphaRef j
      ↔ (255 / (2 ^ k - 1)) ∣ j)

end Reedsolo
