-- !benchmark @start imports
-- !benchmark @end imports

/-!
# Flocq.Calc.Impl.Bracket

Location tracking for floating-point bracket computation, translated from
the Coq source `src/Calc/Bracket.v`.

`Location` records where a real number sits relative to the midpoint of a
bracketing interval: `Exact` means the number coincides with the lower
bound, while `Inexact o` encodes whether it is below (`lt`), at (`eq`), or
above (`gt`) the midpoint. The three API functions compute the new location
when an interval is subdivided into `nb_steps` equal steps and the real
lies in the `k`-th sub-interval.

Types and signatures are fixed vocabulary (DO NOT MODIFY). Implement only
the function bodies inside the `!benchmark code` markers.
-/

-- ── Core data types (DO NOT MODIFY) ──────────────────────────────────────────

/-- Records the position of a real number within a bracketing interval.
    - `Exact`: the number coincides with the lower bound of the interval.
    - `Inexact o`: the number is strictly inside; `o` encodes its position
      relative to the midpoint (`lt` = below midpoint, `eq` = at midpoint,
      `gt` = above midpoint). -/
inductive Location where
  | Exact   : Location
  | Inexact : Ordering → Location
  deriving Repr, DecidableEq, BEq, Inhabited

namespace Flocq

-- ── API signatures (DO NOT MODIFY) ───────────────────────────────────────────

/-- Signature for `newLocationEven`: given `nb_steps`, step index `k`, and
    current location `l`, compute the combined location (even-radix variant).
    The two `Int` arguments are `nb_steps` and `k` respectively. -/
abbrev NewLocationEvenSig := Int → Int → Location → Location

/-- Signature for `newLocationOdd`: given `nb_steps`, step index `k`, and
    current location `l`, compute the combined location (odd-radix variant).
    The two `Int` arguments are `nb_steps` and `k` respectively. -/
abbrev NewLocationOddSig := Int → Int → Location → Location

/-- Signature for `newLocation`: dispatch to `newLocationEven` or
    `newLocationOdd` based on the parity of `nb_steps`.
    The two `Int` arguments are `nb_steps` and `k` respectively. -/
abbrev NewLocationSig := Int → Int → Location → Location

end Flocq

-- !benchmark @start global_aux
-- !benchmark @end global_aux

-- !benchmark @start code_aux def=newLocationEven
-- !benchmark @end code_aux def=newLocationEven

def Flocq.newLocationEven : Flocq.NewLocationEvenSig :=
-- !benchmark @start code def=newLocationEven
  fun nb_steps k l =>
    if k == 0 then
      match l with
      | Location.Exact   => l
      | _                => Location.Inexact Ordering.lt
    else
      Location.Inexact
        (match compare (2 * k) nb_steps with
         | Ordering.lt => Ordering.lt
         | Ordering.eq =>
           match l with
           | Location.Exact => Ordering.eq
           | _              => Ordering.gt
         | Ordering.gt => Ordering.gt)
-- !benchmark @end code def=newLocationEven

-- !benchmark @start code_aux def=newLocationOdd
-- !benchmark @end code_aux def=newLocationOdd

def Flocq.newLocationOdd : Flocq.NewLocationOddSig :=
-- !benchmark @start code def=newLocationOdd
  fun nb_steps k l =>
    if k == 0 then
      match l with
      | Location.Exact   => l
      | _                => Location.Inexact Ordering.lt
    else
      Location.Inexact
        (match compare (2 * k + 1) nb_steps with
         | Ordering.lt => Ordering.lt
         | Ordering.eq =>
           match l with
           | Location.Inexact o => o
           | Location.Exact     => Ordering.lt
         | Ordering.gt => Ordering.gt)
-- !benchmark @end code def=newLocationOdd

-- !benchmark @start code_aux def=newLocation
-- !benchmark @end code_aux def=newLocation

def Flocq.newLocation : Flocq.NewLocationSig :=
-- !benchmark @start code def=newLocation
  fun nb_steps k l =>
    if nb_steps % 2 == 0 then
      Flocq.newLocationEven nb_steps k l
    else
      Flocq.newLocationOdd nb_steps k l
-- !benchmark @end code def=newLocation
