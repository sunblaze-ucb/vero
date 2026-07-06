import Ecdsa.Harness

/-!
# Ecdsa.Spec.Curve

Specifications for the elliptic-curve group law in affine coordinates. Each
`spec_*` is a property over an arbitrary `impl : RepoImpl`, reached through
`impl.ecdsa.<fn>`. The group law is pinned in four layers:

* **On-curve characterization** — `containsPoint` is an `iff` against the curve
  residue `y² ≡ x³ + a·x + b (mod p)` (`spec_contains_point_iff`).
* **Coordinate formulas** — `pointAdd` and `pointDouble` are pinned to their
  explicit slope arithmetic (`spec_point_add_affine_formula`,
  `spec_point_double_affine_formula`), plus the degenerate-branch laws.
* **On-curve closure + group correctness** — anchored by golden vectors on the
  curve `y² = x³ + 2x + 2 (mod 17)` with generator `(5, 1)`: the small multiples
  `2G`, `3G`, `4G`, `−G`, and `scalarMult` agree with the standard values and
  stay on-curve. (General algebraic closure and group associativity are out of
  scope.)
* **Structural laws** — identity, negation, commutativity, and the `scalarMult`
  recurrence tying scalar multiplication to `pointAdd`.

The curve `y² = x³ + 2x + 2 (mod 17)` and generator `(5, 1)` are the
specification's own ground truth; they never refer to `impl`.

DO NOT MODIFY.
-/

-- ════════════════════════════════════════════════════════════════
-- On-curve characterization (frozen iff)
-- ════════════════════════════════════════════════════════════════

/-- On-curve characterization: an affine point `(x, y)` is on the curve exactly
    when `y² ≡ x³ + a·x + b (mod p)`. -/
def spec_contains_point_iff (impl : RepoImpl) : Prop :=
  ∀ (c : Curve) (x y : Nat),
    impl.ecdsa.containsPoint c (.affine x y) = true ↔
      (y * y) % c.p = (((x * x) % c.p * x) % c.p + c.a * x + c.b) % c.p

/-- Infinity is always on the curve (the group identity lies on every curve).
    Grounds the infinity case of `containsPoint`. -/
def spec_contains_point_infinity (impl : RepoImpl) : Prop :=
  ∀ (c : Curve), impl.ecdsa.containsPoint c .infinity = true

-- ════════════════════════════════════════════════════════════════
-- Coordinate formulas (frozen slope arithmetic — force the group law)
-- ════════════════════════════════════════════════════════════════

/-- Point-doubling coordinate formula: for an affine `(x, y)` with `2y ≢ 0
    (mod p)`, `pointDouble` equals the affine point built from the tangent slope
    `λ = (3x² + a)·inv(2y)` and `x₃ = λ² − 2x`, `y₃ = λ(x − x₃) − y`, over `%`,
    `*`, `+`, `−` and `inverseMod`. -/
def spec_point_double_affine_formula (impl : RepoImpl) : Prop :=
  ∀ (c : Curve) (x y : Nat), (2 * y) % c.p ≠ 0 →
    impl.ecdsa.pointDouble c (.affine x y) =
      (let lam := ((3 * x * x + c.a) * impl.ecdsa.inverseMod ((2 * y) % c.p) c.p) % c.p
       let x3 := ((lam * lam) % c.p + c.p + c.p - 2 * (x % c.p)) % c.p
       let y3 := ((lam * ((x + c.p - x3 % c.p) % c.p)) % c.p + c.p - y % c.p) % c.p
       Point.affine x3 y3)

/-- Point-doubling vertical-tangent law: when `2y ≡ 0 (mod p)`, doubling an
    affine `(x, y)` gives the point at infinity. -/
def spec_point_double_infinity (impl : RepoImpl) : Prop :=
  ∀ (c : Curve) (x y : Nat), (2 * y) % c.p = 0 →
    impl.ecdsa.pointDouble c (.affine x y) = .infinity

/-- Identity-doubling law: doubling the group identity `O` is `O` on every
    curve — `2·O = O`. The `.infinity`-input case of `pointDouble`, distinct from
    the affine vertical-tangent clause `spec_point_double_infinity`. -/
def spec_point_double_at_infinity (impl : RepoImpl) : Prop :=
  ∀ (c : Curve), impl.ecdsa.pointDouble c .infinity = .infinity

/-- Point-addition coordinate formula: for affine `P, Q` with distinct reduced
    `x`-coordinates, `pointAdd` equals the affine point built from the chord
    slope `λ = (y₂ − y₁)·inv(x₂ − x₁)` and `x₃ = λ² − (x₁ + x₂)`,
    `y₃ = λ(x₁ − x₃) − y₁`, over `%`, `*`, `+`, `−` and `inverseMod`. -/
def spec_point_add_affine_formula (impl : RepoImpl) : Prop :=
  ∀ (c : Curve) (x1 y1 x2 y2 : Nat), x1 % c.p ≠ x2 % c.p →
    impl.ecdsa.pointAdd c (.affine x1 y1) (.affine x2 y2) =
      (let lam := (((y2 + c.p - y1 % c.p) % c.p) *
                   impl.ecdsa.inverseMod ((x2 + c.p - x1 % c.p) % c.p) c.p) % c.p
       let x3 := ((lam * lam) % c.p + c.p + c.p - (x1 % c.p + x2 % c.p) % c.p) % c.p
       let y3 := ((lam * ((x1 + c.p - x3 % c.p) % c.p)) % c.p + c.p - y1 % c.p) % c.p
       Point.affine x3 y3)

/-- Addition delegates to doubling on equal points: for affine `P, Q` with equal
    reduced `x` and `y₁ + y₂ ≢ 0 (mod p)` — i.e. `P = Q` and not a vertical
    pair — `pointAdd P Q = pointDouble P`. -/
def spec_point_add_eq_double (impl : RepoImpl) : Prop :=
  ∀ (c : Curve) (x1 y1 x2 y2 : Nat),
    x1 % c.p = x2 % c.p → (y1 + y2) % c.p ≠ 0 →
    impl.ecdsa.pointAdd c (.affine x1 y1) (.affine x2 y2) =
      impl.ecdsa.pointDouble c (.affine x1 y1)

/-- Vertical-chord law: for affine `P, Q` with equal reduced `x` and
    `y₁ + y₂ ≡ 0 (mod p)` (so `Q = −P`), the sum is the point at infinity.
    Pins the `P + (−P) = O` branch of the adder. -/
def spec_point_add_vertical (impl : RepoImpl) : Prop :=
  ∀ (c : Curve) (x1 y1 x2 y2 : Nat),
    x1 % c.p = x2 % c.p → (y1 + y2) % c.p = 0 →
    impl.ecdsa.pointAdd c (.affine x1 y1) (.affine x2 y2) = .infinity

-- ════════════════════════════════════════════════════════════════
-- Structural group laws (identity, negation, commutativity)
-- ════════════════════════════════════════════════════════════════

/-- Left identity: `O + P = P` for every point `P`. The point at infinity is the
    group identity on the left. -/
def spec_point_add_left_identity (impl : RepoImpl) : Prop :=
  ∀ (c : Curve) (P : Point), impl.ecdsa.pointAdd c .infinity P = P

/-- Right identity: `P + O = P` for every point `P`. The point at infinity is
    the group identity on the right. -/
def spec_point_add_right_identity (impl : RepoImpl) : Prop :=
  ∀ (c : Curve) (P : Point), impl.ecdsa.pointAdd c P .infinity = P

/-- Negation formula: `−(x, y) = (x, (p − y mod p) mod p)` and `−O = O`. -/
def spec_neg_point_formula (impl : RepoImpl) : Prop :=
  (∀ (c : Curve), impl.ecdsa.negPoint c .infinity = .infinity) ∧
  (∀ (c : Curve) (x y : Nat),
    impl.ecdsa.negPoint c (.affine x y) = .affine x ((c.p - y % c.p) % c.p))

/-- Negation keeps the abscissa: `−(x, y)` has the same `x`-coordinate. -/
def spec_neg_point_same_x (impl : RepoImpl) : Prop :=
  ∀ (c : Curve) (x y : Nat),
    ∃ y', impl.ecdsa.negPoint c (.affine x y) = .affine x y'

-- ════════════════════════════════════════════════════════════════
-- scalarMult recurrence (ties the scalar to pointAdd → doubler)
-- ════════════════════════════════════════════════════════════════

/-- Scalar-multiplication zero law: `0 · P = O`. The base case grounding the
    double-and-add recurrence. -/
def spec_scalar_mult_zero (impl : RepoImpl) : Prop :=
  ∀ (c : Curve) (P : Point), impl.ecdsa.scalarMult c 0 P = .infinity

/-- Scalar-multiplication recurrence: `(k+1) · P = (k · P) + P`, tying
    `scalarMult` to iterated `pointAdd`. -/
def spec_scalar_mult_succ (impl : RepoImpl) : Prop :=
  ∀ (c : Curve) (k : Nat) (P : Point),
    impl.ecdsa.scalarMult c (k + 1) P =
      impl.ecdsa.pointAdd c (impl.ecdsa.scalarMult c k P) P

/-- Scalar-multiplication one law: `1 · P = P`. The first rung of the ladder,
    pinning `scalarMult c 1` to the identity on points (combined with the
    recurrence and `O + P = P`). -/
def spec_scalar_mult_one (impl : RepoImpl) : Prop :=
  ∀ (c : Curve) (P : Point), impl.ecdsa.scalarMult c 1 P = impl.ecdsa.pointAdd c .infinity P

-- ════════════════════════════════════════════════════════════════
-- On-curve closure + group correctness, anchored by golden vectors
--
-- Curve  y² = x³ + 2x + 2  (mod 17),  generator G = (5, 1).
-- ════════════════════════════════════════════════════════════════

/-- Golden generator: `G = (5, 1)` and its small multiples `2G`, `3G`, `4G` all
    lie on `y² = x³ + 2x + 2 (mod 17)`. Anchors on-curve closure of
    `pointDouble` and `pointAdd` at concrete points. -/
def spec_curve_golden_on_curve (impl : RepoImpl) : Prop :=
  let c : Curve := { p := 17, a := 2, b := 2 }
  let G : Point := .affine 5 1
  impl.ecdsa.containsPoint c G = true ∧
  impl.ecdsa.containsPoint c (impl.ecdsa.pointDouble c G) = true ∧
  impl.ecdsa.containsPoint c (impl.ecdsa.pointAdd c G (impl.ecdsa.pointDouble c G)) = true ∧
  impl.ecdsa.containsPoint c (impl.ecdsa.pointDouble c (impl.ecdsa.pointDouble c G)) = true

/-- Golden group values: the small multiples of `G = (5, 1)` on
    `y² = x³ + 2x + 2 (mod 17)` equal the standard points — `2G = (6, 3)`,
    `3G = (10, 6)`, `4G = (3, 1)` — and `G + (−G) = O`. -/
def spec_curve_golden_values (impl : RepoImpl) : Prop :=
  let c : Curve := { p := 17, a := 2, b := 2 }
  let G : Point := .affine 5 1
  impl.ecdsa.pointDouble c G = .affine 6 3 ∧
  impl.ecdsa.pointAdd c G (impl.ecdsa.pointDouble c G) = .affine 10 6 ∧
  impl.ecdsa.pointDouble c (impl.ecdsa.pointDouble c G) = .affine 3 1 ∧
  impl.ecdsa.pointAdd c G (impl.ecdsa.negPoint c G) = .infinity

/-- Golden scalar ladder: `scalarMult` on `G = (5, 1)` reproduces the standard
    multiples — `0·G = O`, `1·G = G`, `2·G = (6, 3)`, `3·G = (10, 6)` — and
    `5·G` lands on the curve. -/
def spec_curve_golden_scalar (impl : RepoImpl) : Prop :=
  let c : Curve := { p := 17, a := 2, b := 2 }
  let G : Point := .affine 5 1
  impl.ecdsa.scalarMult c 0 G = .infinity ∧
  impl.ecdsa.scalarMult c 1 G = G ∧
  impl.ecdsa.scalarMult c 2 G = .affine 6 3 ∧
  impl.ecdsa.scalarMult c 3 G = .affine 10 6 ∧
  impl.ecdsa.containsPoint c (impl.ecdsa.scalarMult c 5 G) = true

-- ════════════════════════════════════════════════════════════════
-- Identity-absorption + negation/modulus structural laws
-- ════════════════════════════════════════════════════════════════

/-- Identity absorption: scaling the group identity leaves it fixed —
    `scalarMult c k O = O` for every scalar `k` and every curve. -/
def spec_scalar_mult_infinity_absorbs (impl : RepoImpl) : Prop :=
  ∀ (c : Curve) (k : Nat), impl.ecdsa.scalarMult c k .infinity = .infinity

/-- Negation on the reduced ordinate: for `p > 0`, negating twice returns the
    abscissa unchanged and the ordinate reduced modulo `p` —
    `negPoint c (negPoint c (x, y)) = (x, y % p)`. -/
def spec_neg_point_double_reduces_y (impl : RepoImpl) : Prop :=
  ∀ (c : Curve) (x y : Nat), 0 < c.p →
    impl.ecdsa.negPoint c (impl.ecdsa.negPoint c (.affine x y)) =
      .affine x (y % c.p)

/-- Modular ordinate cancellation: for `p > 0`, `negPoint c (x, y)` is an affine
    point `(x, y')` whose ordinate cancels the input modulo `p` —
    `(y + y') % p = 0` and `(y' + y) % p = 0`. -/
def spec_neg_point_y_sum_zero (impl : RepoImpl) : Prop :=
  ∀ (c : Curve) (x y : Nat), 0 < c.p →
    ∃ y', impl.ecdsa.negPoint c (.affine x y) = .affine x y' ∧
      (y + y') % c.p = 0 ∧ (y' + y) % c.p = 0

/-- Inverse-sum law: for `p > 0`, a point added to its negation is the identity
    on both sides — `pointAdd c P (negPoint c P) = O` and
    `pointAdd c (negPoint c P) P = O`. -/
def spec_point_add_neg_point_inverse (impl : RepoImpl) : Prop :=
  ∀ (c : Curve) (P : Point), 0 < c.p →
    impl.ecdsa.pointAdd c P (impl.ecdsa.negPoint c P) = .infinity ∧
    impl.ecdsa.pointAdd c (impl.ecdsa.negPoint c P) P = .infinity

/-- Negation preserves membership: for `p > 0`, `−P` lies on the curve exactly
    when `P` does — `containsPoint c (negPoint c P) = containsPoint c P`. -/
def spec_contains_point_neg_point (impl : RepoImpl) : Prop :=
  ∀ (c : Curve) (P : Point), 0 < c.p →
    impl.ecdsa.containsPoint c (impl.ecdsa.negPoint c P) =
      impl.ecdsa.containsPoint c P

/-- Vertical-tangent by reduced ordinate: a zero reduced ordinate `y % p = 0`
    makes doubling vertical — `pointDouble c (x, y) = O`. -/
def spec_point_double_zero_ordinate (impl : RepoImpl) : Prop :=
  ∀ (c : Curve) (x y : Nat), y % c.p = 0 →
    impl.ecdsa.pointDouble c (.affine x y) = .infinity

/-- Scaled inverse-sum: for `p > 0`, every scalar multiple of `P + (−P)` is the
    identity — `scalarMult c k (pointAdd c P (negPoint c P)) = O`. -/
def spec_scalar_mult_inverse_sum_absorbs (impl : RepoImpl) : Prop :=
  ∀ (c : Curve) (k : Nat) (P : Point), 0 < c.p →
    impl.ecdsa.scalarMult c k
      (impl.ecdsa.pointAdd c P (impl.ecdsa.negPoint c P)) = .infinity
