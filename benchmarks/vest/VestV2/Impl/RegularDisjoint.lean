import VestV2.Impl.Properties

/-!
# VestV2.Impl.RegularDisjoint

Disjointness trait for VestV2 parser combinators. Two combinators are
disjoint if at most one can successfully parse any given byte buffer.
This is used as a precondition for the `Choice` combinator.

Types are fixed vocabulary (DO NOT MODIFY).
-/

-- ── Types (DO NOT MODIFY) ─────────────────────────────────

/-- Trait for combinators that are disjoint: if `disjoint_from s o`
    is true, then at most one of `s` and `o` can successfully parse
    any given byte buffer. -/
class DisjointFrom (Self Other : Type) where
  disjoint_from : Self → Other → Bool
