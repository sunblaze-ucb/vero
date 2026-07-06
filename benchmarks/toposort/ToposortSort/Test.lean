import ToposortSort.Impl.Toposort
import ToposortSort.Bundle
import ToposortSort.Harness

/-!
# ToposortSort.Test

`#guard` conformance tests. Every guard invokes the API via the
bundle-qualified form `canonical.toposortSort.<field>` so that the same
tests evaluate the LLM's filled-in implementations during grading.

Guards are kept minimal/total and use `Nat` element types so
elaboration stays fast. Each API gets at least three guards covering:
the empty graph, a linear chain (a → b → c), a branching DAG
(a → b, a → c), and a cycle (which must be rejected with `none`).

DO NOT MODIFY — infrastructure.
-/

-- ── toposort ─────────────────────────────────────────────────────
-- API: Std.HashMap α (Std.HashSet α) → Option (List (Std.HashSet α))
-- Returns `Option` of layers (HashSets) in dependency order:
-- earliest layer = items with no remaining dependencies.

-- empty graph: returns the empty layer list
#guard canonical.toposortSort.toposort
         (Std.HashMap.ofList ([] : List (Nat × Std.HashSet Nat)))
         == some ([] : List (Std.HashSet Nat))

-- linear chain 1 → 2 → 3 (1 depends on 2, 2 depends on 3):
-- layers must be [{3}, {2}, {1}]
#guard canonical.toposortSort.toposort
         (Std.HashMap.ofList
           [ (1, Std.HashSet.ofList [2])
           , (2, Std.HashSet.ofList [3])
           , (3, Std.HashSet.ofList ([] : List Nat)) ])
         == some [Std.HashSet.ofList [3], Std.HashSet.ofList [2], Std.HashSet.ofList [1]]

-- branching DAG 1 → {2, 3}, 2 and 3 leaf:
-- layers must be [{2, 3}, {1}]  (HashSet equality is content-based)
#guard canonical.toposortSort.toposort
         (Std.HashMap.ofList
           [ (1, Std.HashSet.ofList [2, 3])
           , (2, Std.HashSet.ofList ([] : List Nat))
           , (3, Std.HashSet.ofList ([] : List Nat)) ])
         == some [Std.HashSet.ofList [2, 3], Std.HashSet.ofList [1]]

-- cycle 1 ↔ 2 → must be rejected
#guard canonical.toposortSort.toposort
         (Std.HashMap.ofList
           [ (1, Std.HashSet.ofList [2])
           , (2, Std.HashSet.ofList [1]) ])
         == (none : Option (List (Std.HashSet Nat)))

-- dependency-only vertex: 2 appears only as a dependency and must be
-- materialised before its dependent 1
#guard canonical.toposortSort.toposort
         (Std.HashMap.ofList
           [ (1, Std.HashSet.ofList [2]) ])
         == some [Std.HashSet.ofList [2], Std.HashSet.ofList [1]]

-- longer cycle should be rejected, preventing implementations that only
-- special-case the two-node cycle guard above
#guard canonical.toposortSort.toposort
         (Std.HashMap.ofList
           [ (1, Std.HashSet.ofList [2])
           , (2, Std.HashSet.ofList [3])
           , (3, Std.HashSet.ofList [1]) ])
         == (none : Option (List (Std.HashSet Nat)))

-- ── toposort_flatten ─────────────────────────────────────────────
-- API: [Ord α] → Std.HashMap α (Std.HashSet α) → Bool → Option (List α)
-- Collapses layers into a single list; `sort = true` sorts each layer
-- ascending, so output is fully deterministic.

-- empty graph: flattened result is the empty list
#guard canonical.toposortSort.toposort_flatten
         (Std.HashMap.ofList ([] : List (Nat × Std.HashSet Nat))) true
         == some ([] : List Nat)

-- linear chain 1 → 2 → 3, sorted: [3, 2, 1]
#guard canonical.toposortSort.toposort_flatten
         (Std.HashMap.ofList
           [ (1, Std.HashSet.ofList [2])
           , (2, Std.HashSet.ofList [3])
           , (3, Std.HashSet.ofList ([] : List Nat)) ]) true
         == some [3, 2, 1]

-- branching DAG 1 → {2, 3}, sorted: leaves first then root → [2, 3, 1]
#guard canonical.toposortSort.toposort_flatten
         (Std.HashMap.ofList
           [ (1, Std.HashSet.ofList [2, 3])
           , (2, Std.HashSet.ofList ([] : List Nat))
           , (3, Std.HashSet.ofList ([] : List Nat)) ]) true
         == some [2, 3, 1]

-- cycle 1 ↔ 2 → none
#guard canonical.toposortSort.toposort_flatten
         (Std.HashMap.ofList
           [ (1, Std.HashSet.ofList [2])
           , (2, Std.HashSet.ofList [1]) ]) true
         == (none : Option (List Nat))

-- implicit dependency-only vertex also flattens in dependency order
#guard canonical.toposortSort.toposort_flatten
         (Std.HashMap.ofList
           [ (1, Std.HashSet.ofList [2]) ]) true
         == some [2, 1]
