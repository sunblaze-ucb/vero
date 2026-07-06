import Flocq.Harness
import Flocq.Calc.Impl.Round

/-!
# Flocq.Calc.Spec.Round

Specifications for the `truncateAux`, `truncate`, and `truncateFIX`
rounding-helper functions. Each `spec_*` is a property over an arbitrary
`impl : RepoImpl`.

These specs correspond to the computational content of the Coq definitions
`truncate_aux`, `truncate`, and `truncate_FIX` from `src/Calc/Round.v`.

DO NOT MODIFY — this file is frozen curator-given content.
-/

-- ── rounding-choice predicate specs ──────────────────────────────────────────

/-- `condIncr true` increments its input. -/
def spec_condIncr_true (impl : RepoImpl) : Prop :=
  ∀ (m : Int), impl.flocq.condIncr true m = m + 1

/-- `condIncr false` leaves its input unchanged. -/
def spec_condIncr_false (impl : RepoImpl) : Prop :=
  ∀ (m : Int), impl.flocq.condIncr false m = m

/-- Directed-down never increments an exact value. -/
def spec_roundSignDN_exact (impl : RepoImpl) : Prop :=
  ∀ (s : Bool), impl.flocq.roundSignDN s Location.Exact = false

/-- Directed-down increments an inexact negative value exactly when the sign
    flag is true. -/
def spec_roundSignDN_inexact (impl : RepoImpl) : Prop :=
  ∀ (s : Bool) (o : Ordering), impl.flocq.roundSignDN s (Location.Inexact o) = s

/-- Directed-up never increments an exact value. -/
def spec_roundUP_exact (impl : RepoImpl) : Prop :=
  impl.flocq.roundUP Location.Exact = false

/-- Directed-up increments every inexact value. -/
def spec_roundUP_inexact (impl : RepoImpl) : Prop :=
  ∀ (o : Ordering), impl.flocq.roundUP (Location.Inexact o) = true

/-- Directed-up under a sign increments inexact values exactly when the sign
    flag is false. -/
def spec_roundSignUP_inexact (impl : RepoImpl) : Prop :=
  ∀ (s : Bool) (o : Ordering), impl.flocq.roundSignUP s (Location.Inexact o) = !s

/-- Round-toward-zero increments inexact values exactly when the sign flag is
    true. -/
def spec_roundZR_inexact (impl : RepoImpl) : Prop :=
  ∀ (s : Bool) (o : Ordering), impl.flocq.roundZR s (Location.Inexact o) = s

/-- Nearest rounding does not increment values below the midpoint. -/
def spec_roundN_lt (impl : RepoImpl) : Prop :=
  ∀ (p : Bool), impl.flocq.roundN p (Location.Inexact Ordering.lt) = false

/-- Nearest rounding uses the parity/tie flag exactly at the midpoint. -/
def spec_roundN_eq (impl : RepoImpl) : Prop :=
  ∀ (p : Bool), impl.flocq.roundN p (Location.Inexact Ordering.eq) = p

/-- Nearest rounding increments values above the midpoint. -/
def spec_roundN_gt (impl : RepoImpl) : Prop :=
  ∀ (p : Bool), impl.flocq.roundN p (Location.Inexact Ordering.gt) = true

-- ── truncateAux specs ─────────────────────────────────────────────────────────

/-- The mantissa component of `truncateAux β (m, e, l) k` equals `m / β^k`.
    Corresponds directly to the `Z.div m p` component of `truncate_aux`. -/
def spec_truncateAux_mantissa (impl : RepoImpl) : Prop :=
  ∀ (β : Radix) (m e k : Int) (l : Location),
    (impl.flocq.truncateAux β (m, e, l) k).1 = m / β.val ^ k.natAbs

/-- The exponent component of `truncateAux β (m, e, l) k` equals `e + k`.
    Corresponds to the `(e + k)` component of `truncate_aux`. -/
def spec_truncateAux_exponent (impl : RepoImpl) : Prop :=
  ∀ (β : Radix) (m e k : Int) (l : Location),
    (impl.flocq.truncateAux β (m, e, l) k).2.1 = e + k

/-- The location component of `truncateAux β (m, e, l) k` is obtained by
    calling `newLocation (β^k) (m % β^k) l`.
    Corresponds to `new_location p (Z.modulo m p) l` in `truncate_aux`. -/
def spec_truncateAux_location (impl : RepoImpl) : Prop :=
  ∀ (β : Radix) (m e k : Int) (l : Location),
    (impl.flocq.truncateAux β (m, e, l) k).2.2 =
      impl.flocq.newLocation (β.val ^ k.natAbs) (m % (β.val ^ k.natAbs)) l

-- ── truncate specs ────────────────────────────────────────────────────────────

/-- When `fexp(zdigits(β, m) + e) ≤ e`, `truncate` is the identity: the
    shift amount `k = fexp(zdigits(β,m)+e) − e` is non-positive so no
    truncation is needed. -/
def spec_truncate_passthrough (impl : RepoImpl) : Prop :=
  ∀ (β : Radix) (fexp : Int → Int) (m e : Int) (l : Location),
    fexp (impl.flocq.zdigits β m + e) ≤ e →
    impl.flocq.truncate β fexp (m, e, l) = (m, e, l)

/-- When `fexp(zdigits(β, m) + e) > e`, `truncate` delegates to `truncateAux`
    with shift `k = fexp(zdigits(β,m)+e) − e`. -/
def spec_truncate_shifts (impl : RepoImpl) : Prop :=
  ∀ (β : Radix) (fexp : Int → Int) (m e : Int) (l : Location),
    fexp (impl.flocq.zdigits β m + e) > e →
    impl.flocq.truncate β fexp (m, e, l) =
      impl.flocq.truncateAux β (m, e, l) (fexp (impl.flocq.zdigits β m + e) - e)

-- ── truncateFIX specs ─────────────────────────────────────────────────────────

/-- When `emin ≤ e`, `truncateFIX` is the identity: the exponent is already
    at or above the minimum, so no shift is needed. -/
def spec_truncateFIX_passthrough (impl : RepoImpl) : Prop :=
  ∀ (β : Radix) (emin m e : Int) (l : Location),
    emin ≤ e →
    impl.flocq.truncateFIX β emin (m, e, l) = (m, e, l)

/-- When `emin > e`, the mantissa after `truncateFIX β emin (m, e, l)` is
    `m / β^(emin − e)`. -/
def spec_truncateFIX_mantissa (impl : RepoImpl) : Prop :=
  ∀ (β : Radix) (emin m e : Int) (l : Location),
    emin > e →
    (impl.flocq.truncateFIX β emin (m, e, l)).1 =
      m / β.val ^ (emin - e).natAbs

/-- When `emin > e`, the exponent after `truncateFIX β emin (m, e, l)` is
    `emin` (i.e., `e + (emin − e)`). -/
def spec_truncateFIX_exponent (impl : RepoImpl) : Prop :=
  ∀ (β : Radix) (emin m e : Int) (l : Location),
    emin > e →
    (impl.flocq.truncateFIX β emin (m, e, l)).2.1 = emin

/-- When `emin > e`, the location after `truncateFIX β emin (m, e, l)` is
    `newLocation (β^(emin−e)) (m % β^(emin−e)) l`. -/
def spec_truncateFIX_location (impl : RepoImpl) : Prop :=
  ∀ (β : Radix) (emin m e : Int) (l : Location),
    emin > e →
    (impl.flocq.truncateFIX β emin (m, e, l)).2.2 =
      impl.flocq.newLocation
        (β.val ^ (emin - e).natAbs)
        (m % β.val ^ (emin - e).natAbs)
        l
