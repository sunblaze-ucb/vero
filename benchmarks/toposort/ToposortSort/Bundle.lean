import ToposortSort.Impl.Toposort

/-!
# ToposortSort.Bundle

Per-package implementation bundle for the `ToposortSort` root package.
Collects all 2 API signatures into one structure.  Polymorphic APIs expand
their binders inline since the structure itself takes no type parameters.

DO NOT MODIFY — benchmark infrastructure.
-/

structure ToposortSortBundle where
  toposort : ∀ {α : Type _} [BEq α] [Hashable α],
    Std.HashMap α (Std.HashSet α) → Option (List (Std.HashSet α))
  toposort_flatten : ∀ {α : Type _} [BEq α] [Hashable α] [Ord α],
    Std.HashMap α (Std.HashSet α) → Bool → Option (List α)
