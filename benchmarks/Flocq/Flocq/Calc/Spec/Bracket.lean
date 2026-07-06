import Flocq.Harness
import Flocq.Calc.Impl.Bracket

/-!
# Flocq.Calc.Spec.Bracket

Specifications for the `newLocationEven`, `newLocationOdd`, and
`newLocation` bracket-location functions. Each `spec_*` is a property
over an arbitrary `impl : RepoImpl`.

These specs correspond to the case analysis underlying the Coq theorems
`new_location_even_correct`, `new_location_odd_correct`, and
`new_location_correct` from `src/Calc/Bracket.v`.

DO NOT MODIFY — this file is frozen curator-given content.
-/

-- ── newLocationEven specs ─────────────────────────────────────────────────────

/-- When `k = 0` and the location is `Exact`, `newLocationEven` returns `Exact`.
    Corresponds to the `k = 0, loc_Exact` branch of `new_location_even`. -/
def spec_newLocationEven_k0_exact (impl : RepoImpl) : Prop :=
  ∀ (nb_steps : Int),
    impl.flocq.newLocationEven nb_steps 0 Location.Exact = Location.Exact

/-- When `k = 0` and the location is `Inexact`, `newLocationEven` returns
    `Inexact lt` (the real is in the lower half of the whole interval).
    Corresponds to the `k = 0, loc_Inexact` branch of `new_location_even`. -/
def spec_newLocationEven_k0_inexact (impl : RepoImpl) : Prop :=
  ∀ (nb_steps : Int) (o : Ordering),
    impl.flocq.newLocationEven nb_steps 0 (Location.Inexact o) =
      Location.Inexact Ordering.lt

/-- When `k ≠ 0` and `2 * k < nb_steps`, `newLocationEven` returns
    `Inexact lt` for any input location (the real is below the midpoint).
    Corresponds to the `2 * k < nb_steps` branch of `new_location_even`. -/
def spec_newLocationEven_lo (impl : RepoImpl) : Prop :=
  ∀ (nb_steps k : Int) (l : Location),
    k ≠ 0 → 2 * k < nb_steps →
    impl.flocq.newLocationEven nb_steps k l = Location.Inexact Ordering.lt

/-- When `k ≠ 0`, `2 * k = nb_steps`, and the location is `Exact`,
    `newLocationEven` returns `Inexact eq` (the real is at the midpoint).
    Corresponds to the `2 * k = nb_steps, loc_Exact` branch. -/
def spec_newLocationEven_mid_exact (impl : RepoImpl) : Prop :=
  ∀ (nb_steps k : Int),
    k ≠ 0 → 2 * k = nb_steps →
    impl.flocq.newLocationEven nb_steps k Location.Exact =
      Location.Inexact Ordering.eq

/-- When `k ≠ 0`, `2 * k = nb_steps`, and the location is `Inexact`,
    `newLocationEven` returns `Inexact gt` (the real is above the midpoint).
    Corresponds to the `2 * k = nb_steps, loc_Inexact` branch. -/
def spec_newLocationEven_mid_inexact (impl : RepoImpl) : Prop :=
  ∀ (nb_steps k : Int) (o : Ordering),
    k ≠ 0 → 2 * k = nb_steps →
    impl.flocq.newLocationEven nb_steps k (Location.Inexact o) =
      Location.Inexact Ordering.gt

/-- When `k ≠ 0` and `2 * k > nb_steps`, `newLocationEven` returns
    `Inexact gt` for any input location (the real is above the midpoint).
    Corresponds to the `2 * k > nb_steps` branch of `new_location_even`. -/
def spec_newLocationEven_hi (impl : RepoImpl) : Prop :=
  ∀ (nb_steps k : Int) (l : Location),
    k ≠ 0 → 2 * k > nb_steps →
    impl.flocq.newLocationEven nb_steps k l = Location.Inexact Ordering.gt

-- ── newLocationOdd specs ──────────────────────────────────────────────────────

/-- When `k = 0` and the location is `Exact`, `newLocationOdd` returns `Exact`. -/
def spec_newLocationOdd_k0_exact (impl : RepoImpl) : Prop :=
  ∀ (nb_steps : Int),
    impl.flocq.newLocationOdd nb_steps 0 Location.Exact = Location.Exact

/-- When `k = 0` and the location is `Inexact`, `newLocationOdd` returns
    `Inexact lt`. -/
def spec_newLocationOdd_k0_inexact (impl : RepoImpl) : Prop :=
  ∀ (nb_steps : Int) (o : Ordering),
    impl.flocq.newLocationOdd nb_steps 0 (Location.Inexact o) =
      Location.Inexact Ordering.lt

/-- When `k ≠ 0` and `2 * k + 1 < nb_steps`, `newLocationOdd` returns
    `Inexact lt` for any input location.
    Corresponds to the `2 * k + 1 < nb_steps` branch of `new_location_odd`. -/
def spec_newLocationOdd_lo (impl : RepoImpl) : Prop :=
  ∀ (nb_steps k : Int) (l : Location),
    k ≠ 0 → 2 * k + 1 < nb_steps →
    impl.flocq.newLocationOdd nb_steps k l = Location.Inexact Ordering.lt

/-- When `k ≠ 0`, `2 * k + 1 = nb_steps`, and the location is `Exact`,
    `newLocationOdd` returns `Inexact lt`.
    Corresponds to the `inbetween_step_Lo_Mi_Eq_odd` case. -/
def spec_newLocationOdd_mid_exact (impl : RepoImpl) : Prop :=
  ∀ (nb_steps k : Int),
    k ≠ 0 → 2 * k + 1 = nb_steps →
    impl.flocq.newLocationOdd nb_steps k Location.Exact =
      Location.Inexact Ordering.lt

/-- When `k ≠ 0`, `2 * k + 1 = nb_steps`, and the location is `Inexact o`,
    `newLocationOdd` returns `Inexact o` (preserves the sub-ordering).
    Corresponds to the `inbetween_step_any_Mi_odd` case. -/
def spec_newLocationOdd_mid_inexact (impl : RepoImpl) : Prop :=
  ∀ (nb_steps k : Int) (o : Ordering),
    k ≠ 0 → 2 * k + 1 = nb_steps →
    impl.flocq.newLocationOdd nb_steps k (Location.Inexact o) =
      Location.Inexact o

/-- When `k ≠ 0` and `2 * k + 1 > nb_steps`, `newLocationOdd` returns
    `Inexact gt` for any input location.
    Corresponds to the `2 * k + 1 > nb_steps` branch of `new_location_odd`. -/
def spec_newLocationOdd_hi (impl : RepoImpl) : Prop :=
  ∀ (nb_steps k : Int) (l : Location),
    k ≠ 0 → 2 * k + 1 > nb_steps →
    impl.flocq.newLocationOdd nb_steps k l = Location.Inexact Ordering.gt

-- ── newLocation specs ─────────────────────────────────────────────────────────

/-- When `nb_steps` is even, `newLocation` agrees with `newLocationEven`. -/
def spec_newLocation_even (impl : RepoImpl) : Prop :=
  ∀ (nb_steps k : Int) (l : Location),
    nb_steps % 2 = 0 →
    impl.flocq.newLocation nb_steps k l =
      impl.flocq.newLocationEven nb_steps k l

/-- When `nb_steps` is odd, `newLocation` agrees with `newLocationOdd`. -/
def spec_newLocation_odd (impl : RepoImpl) : Prop :=
  ∀ (nb_steps k : Int) (l : Location),
    nb_steps % 2 ≠ 0 →
    impl.flocq.newLocation nb_steps k l =
      impl.flocq.newLocationOdd nb_steps k l
