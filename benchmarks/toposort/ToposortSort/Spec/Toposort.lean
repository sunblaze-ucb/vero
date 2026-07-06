import ToposortSort.Spec.Aux

/-!
# ToposortSort.Spec.Toposort

Structural specifications for topological sorting over
`Std.HashMap α (Std.HashSet α)`. `toposort` returns dependency layers
or `none` on a true cycle; `toposort_flatten` must be exactly the flat
view of those layers.

DO NOT MODIFY — frozen curator-given content.
-/

/-- Ported from PR #35 `EmptyInputLaw`: the empty graph has no layers. -/
def spec_toposort_empty (impl : RepoImpl) : Prop :=
  impl.toposortSort.toposort (∅ : Std.HashMap Nat (Std.HashSet Nat)) = some []

/-- Empty input flattens to an empty list for either value of the sort flag. -/
def spec_toposort_flatten_empty (impl : RepoImpl) : Prop :=
  impl.toposortSort.toposort_flatten (∅ : Std.HashMap Nat (Std.HashSet Nat)) true = some [] ∧
  impl.toposortSort.toposort_flatten (∅ : Std.HashMap Nat (Std.HashSet Nat)) false = some []

/-- Self-dependencies are ignored rather than treated as true cycles. -/
def spec_toposort_self_loop_not_cycle (impl : RepoImpl) : Prop :=
  impl.toposortSort.toposort
    (Std.HashMap.ofList [(0, Std.HashSet.ofList [0])])
    = some [Std.HashSet.ofList [0]]

/-- Dependency-only vertices are materialised as graph items with no deps. -/
def spec_toposort_implicit_vertex (impl : RepoImpl) : Prop :=
  impl.toposortSort.toposort
    (Std.HashMap.ofList [(1, Std.HashSet.ofList [2])])
    = some [Std.HashSet.ofList [2], Std.HashSet.ofList [1]]

/-- A two-node mutual dependency is a true cycle. -/
def spec_toposort_cycle_returns_none (impl : RepoImpl) : Prop :=
  impl.toposortSort.toposort
    (Std.HashMap.ofList [(1, Std.HashSet.ofList [2]), (2, Std.HashSet.ofList [1])])
    = (none : Option (List (Std.HashSet Nat)))

/-- Ported from PR #35 `LayersMentionKnownItems`, adjusted for implicit
    dependency-only vertices. Output layers cannot invent graph items. -/
def spec_layers_mention_graph_items (impl : RepoImpl) : Prop :=
  ∀ (data : Std.HashMap Nat (Std.HashSet Nat)) layers,
    impl.toposortSort.toposort data = some layers →
    ∀ layer, layer ∈ layers →
      ∀ x, x ∈ layer → isGraphItem data x

/-- Successful topological sorting covers every explicit or dependency-only graph item. -/
def spec_layers_cover_graph_items (impl : RepoImpl) : Prop :=
  ∀ (data : Std.HashMap Nat (Std.HashSet Nat)) layers x,
    impl.toposortSort.toposort data = some layers →
    isGraphItem data x →
    ∃ layer, layer ∈ layers ∧ x ∈ layer

/-- Ported from PR #35 `LayersAreDependencyFreeInternally`: items in the same
    layer have no non-self dependency edge between them. -/
def spec_layers_are_dependency_free_internally (impl : RepoImpl) : Prop :=
  ∀ (data : Std.HashMap Nat (Std.HashSet Nat)) layers,
    impl.toposortSort.toposort data = some layers →
    ∀ layer, layer ∈ layers →
      layerHasNoInternalDependencies data layer

/-- Ported from PR #35 `FailureConsistency`, strengthened to both sort flags. -/
def spec_flatten_failure_consistency (impl : RepoImpl) : Prop :=
  ∀ (data : Std.HashMap Nat (Std.HashSet Nat)) (sort : Bool),
    impl.toposortSort.toposort data = none ↔
      impl.toposortSort.toposort_flatten data sort = none

/-- Ported from PR #35 `FlattenMatchesLayeredOutput`: sorted flattening is the
    sorted concatenation of the layers returned by `toposort`. -/
def spec_flatten_matches_layered_output_sorted (impl : RepoImpl) : Prop :=
  ∀ (data : Std.HashMap Nat (Std.HashSet Nat)) layers,
    impl.toposortSort.toposort data = some layers →
    impl.toposortSort.toposort_flatten data true =
      some (flattenLayersSorted layers)

/-- Unsorted flattening is the direct concatenation of each produced layer. -/
def spec_flatten_matches_layered_output_unsorted (impl : RepoImpl) : Prop :=
  ∀ (data : Std.HashMap Nat (Std.HashSet Nat)) layers,
    impl.toposortSort.toposort data = some layers →
    impl.toposortSort.toposort_flatten data false =
      some (flattenLayersUnsorted layers)

/-- Flattened output contains each graph item at most once. -/
def spec_flatten_output_has_no_duplicates (impl : RepoImpl) : Prop :=
  ∀ (data : Std.HashMap Nat (Std.HashSet Nat)) (sort : Bool) flat,
    impl.toposortSort.toposort_flatten data sort = some flat →
    flat.Nodup

/-- Flattened output is a genuine topological order for every non-self edge. -/
def spec_flatten_respects_dependency_order (impl : RepoImpl) : Prop :=
  ∀ (data : Std.HashMap Nat (Std.HashSet Nat)) flat,
    impl.toposortSort.toposort_flatten data true = some flat →
    dependenciesPrecedeDependents data flat

/-- Totality on acyclic input: if some ranking of the keys sends every non-self
    dependency edge strictly downward — a witness that the graph is acyclic —
    then `toposort` must SUCCEED (return `some`), never `none`. Every success
    obligation above is guarded by `toposort data = some layers`, so an
    implementation that returns `none` discharges all of them vacuously; this law
    is the one that forbids that dodge over the UNBOUNDED space of acyclic graphs.
    Because acyclicity is certified by an arbitrary rank witness rather than a
    named graph shape, no finite table of hard-coded inputs can satisfy it — an
    impl that only answers a handful of concrete graphs and returns `none`
    elsewhere fails here on every acyclic graph it did not enumerate. -/
def spec_toposort_total_on_acyclic (impl : RepoImpl) : Prop :=
  ∀ (data : Std.HashMap Nat (Std.HashSet Nat)) (rank : Nat → Nat),
    (∀ k deps y, data[k]? = some deps → y ∈ deps → y ≠ k → rank y < rank k) →
    impl.toposortSort.toposort data ≠ none

/-- Maximal-antichain layering: whenever `toposort` succeeds, every source (a
    graph item with no non-self dependency) lands in the FIRST layer, not spread
    across later ones. This pins the layered (Kahn-level) semantics of the Python
    source — layers are maximal sets of mutually-independent, currently-ready
    items — and rejects a degenerate linearizer that emits an otherwise-valid
    topological order as one-item-per-layer, which would still satisfy every
    ordering/coverage law above. -/
def spec_toposort_sources_in_first_layer (impl : RepoImpl) : Prop :=
  ∀ (data : Std.HashMap Nat (Std.HashSet Nat)) l rest,
    impl.toposortSort.toposort data = some (l :: rest) →
    ∀ x, isGraphItem data x →
      (∀ deps y, data[x]? = some deps → y ∈ deps → y = x) →
      x ∈ l
