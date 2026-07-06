import ToposortSort.Harness

/-!
# ToposortSort.Spec.Aux

Auxiliary predicates and projections shared by the topological-sort specs.
-/

universe u

/-- An item belongs to the input graph if it is either an explicit key or
    appears in an explicit dependency set. -/
def isGraphItem
    {α : Type u} [BEq α] [Hashable α]
    (data : Std.HashMap α (Std.HashSet α)) (x : α) : Prop :=
  data.contains x = true ∨
    ∃ (k : α) (deps : Std.HashSet α), data[k]? = some deps ∧ x ∈ deps

/-- No layer may contain a non-self dependency edge between two of its items. -/
def layerHasNoInternalDependencies
    {α : Type u} [BEq α] [Hashable α]
    (data : Std.HashMap α (Std.HashSet α)) (layer : Std.HashSet α) : Prop :=
  ∀ x, x ∈ layer →
    match data[x]? with
    | some deps => ∀ y, y ∈ layer → y ∈ deps → y = x
    | none => True

/-- The exact list produced by flattening layers with `sort = true`. -/
def flattenLayersSorted (layers : List (Std.HashSet Nat)) : List Nat :=
  Toposort.flattenLayers true layers

/-- The exact list produced by flattening layers with `sort = false`. -/
def flattenLayersUnsorted (layers : List (Std.HashSet Nat)) : List Nat :=
  Toposort.flattenLayers false layers

/-- Every non-self dependency edge appears before its dependent in a flat output. -/
def dependenciesPrecedeDependents
    (data : Std.HashMap Nat (Std.HashSet Nat)) (flat : List Nat) : Prop :=
  ∀ x deps y,
    data[x]? = some deps →
    y ∈ deps →
    y ≠ x →
    match flat.idxOf? y, flat.idxOf? x with
    | some depIx, some itemIx => depIx < itemIx
    | _, _ => False
