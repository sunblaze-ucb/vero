import Std

-- !benchmark @start imports
-- !benchmark @end imports

/-!
# ToposortSort.Impl.Toposort

Types, signatures, and implementations for topological sorting of
dependency graphs. `toposort` applies a layered Kahn's algorithm,
returning layers of independent items as `Std.HashSet`s in dependency
order, or `none` on a circular dependency. `toposort_flatten` collapses
the layers into a single list, optionally sorted within each layer.

Types and signatures are fixed vocabulary (DO NOT MODIFY). Function
bodies are the curator's reference implementations; the pipeline
replaces them with `sorry` inside the `code` markers before presenting
the benchmark to the LLM.
-/

variable {α : Type _} [BEq α] [Hashable α]

namespace Toposort

-- ── API signatures (DO NOT MODIFY) ────────────────────────────────

/-- Topological sort: returns layers of mutually-independent items in
    dependency order, or `none` if the graph contains a cycle. -/
abbrev ToposortSig :=
  Std.HashMap α (Std.HashSet α) → Option (List (Std.HashSet α))

/-- Flatten topological sort into a single list, optionally sorting each
    layer. Returns `none` if the graph contains a cycle. -/
abbrev ToposortFlattenSig :=
  [Ord α] → Std.HashMap α (Std.HashSet α) → Bool → Option (List α)

end Toposort

-- !benchmark @start global_aux
-- ── Transparent source-shaped helpers ──────────────────────────────

/-- Remove self-dependencies: for each key `k`, filter `k` out of its
    own dependency set so that items that depend only on themselves are
    treated as having no dependencies. -/
def Toposort.removeSelfDeps
    (data : Std.HashMap α (Std.HashSet α)) : Std.HashMap α (Std.HashSet α) :=
  data.fold (fun m k deps =>
    let deps' : Std.HashSet α :=
      deps.fold (fun s e => if e == k then s else s.insert e) {}
    m.insert k deps'
  ) {}

/-- Collect every value that appears in any dependency set. -/
def Toposort.allDepValues
    (data : Std.HashMap α (Std.HashSet α)) : Std.HashSet α :=
  data.fold (fun s _ deps =>
    deps.fold (fun s' e => s'.insert e) s
  ) {}

/-- Collect every explicit key in the dependency map. -/
def Toposort.allKeys
    (data : Std.HashMap α (Std.HashSet α)) : Std.HashSet α :=
  data.fold (fun s k _ => s.insert k) {}

/-- Add dependency-only vertices with empty dependency sets, matching
    Python's `extra_items_in_deps` update before the Kahn loop. -/
def Toposort.addImplicitVertices
    (data : Std.HashMap α (Std.HashSet α)) : Std.HashMap α (Std.HashSet α) :=
  let keys := Toposort.allKeys data
  (Toposort.allDepValues data).fold (fun m e =>
    if keys.contains e then m else m.insert e ({} : Std.HashSet α)
  ) data

/-- Python-source normalization before the loop: discard self-deps, then
    add dependency-only vertices as empty-dependency items. -/
def Toposort.normalizedGraph
    (data : Std.HashMap α (Std.HashSet α)) : Std.HashMap α (Std.HashSet α) :=
  Toposort.addImplicitVertices (Toposort.removeSelfDeps data)

/-- Current zero-dependency layer in a Kahn loop state. -/
def Toposort.readyLayer
    (data : Std.HashMap α (Std.HashSet α)) : Std.HashSet α :=
  data.fold (fun s k deps => if deps.isEmpty then s.insert k else s) {}

/-- Remove one ready layer from a Kahn loop state and strip those items
    from the remaining dependency sets. -/
def Toposort.removeReadyLayer
    (ordered : Std.HashSet α)
    (data : Std.HashMap α (Std.HashSet α)) : Std.HashMap α (Std.HashSet α) :=
  data.fold (fun m k deps =>
    if ordered.contains k then m
    else
      let newDeps : Std.HashSet α :=
        deps.fold (fun s e =>
          if ordered.contains e then s else s.insert e) {}
      m.insert k newDeps
  ) {}

/-- Kahn's algorithm loop.  `fuel` is initialised to `data.size`; each
    iteration removes at least one item (the non-empty `ordered` set),
    so the loop terminates in at most `data.size` steps.  Returns `none`
    on circular dependency. -/
def Toposort.kahnLoop
    (data : Std.HashMap α (Std.HashSet α))
    (acc  : List (Std.HashSet α))
    (fuel : Nat) : Option (List (Std.HashSet α)) :=
  match fuel with
  | 0 =>
    -- Fuel exhausted: success if map is now empty, else circular dep.
    if data.isEmpty then some acc.reverse else none
  | fuel' + 1 =>
    -- Collect items whose dependency set is currently empty.
    let ordered : Std.HashSet α := Toposort.readyLayer data
    if ordered.isEmpty then
      -- No progress this round.
      if data.isEmpty then some acc.reverse else none
    else
      -- Remove ordered items; strip them from remaining dependency sets.
      let newData := Toposort.removeReadyLayer ordered data
      Toposort.kahnLoop newData (ordered :: acc) fuel'

/-- Convert a layer set to the list used by `toposort_flatten`.  Python's
    `sort=True` uses `sorted(d)`, while `sort=False` uses the set's
    iteration order. -/
def Toposort.layerElems [Ord α] (sort : Bool) (s : Std.HashSet α) : List α :=
  let lst : List α := s.fold (fun l e => e :: l) []
  if sort then lst.mergeSort (fun a b => compare a b == .lt) else lst

/-- Flatten a list of layers using the same per-layer conversion as the
    public `toposort_flatten` API. -/
def Toposort.flattenLayers [Ord α] (sort : Bool) (levels : List (Std.HashSet α)) : List α :=
  levels.flatMap (Toposort.layerElems sort)
-- !benchmark @end global_aux

-- ── API implementations (LLM task inside code markers) ────────────
--
-- Note: `def Toposort.X : Toposort.XSig` would trigger a stuck metavar
-- for the polymorphic `α`; we use the expanded type form instead, which
-- is elaboration-equivalent and matches the abbrev exactly.

-- !benchmark @start code_aux def=toposort
-- !benchmark @end code_aux def=toposort

def Toposort.toposort :
    Std.HashMap α (Std.HashSet α) → Option (List (Std.HashSet α)) :=
-- !benchmark @start code def=toposort
  fun data =>
    if data.isEmpty then
      some []
    else
      -- Step 1/2: source normalization: strip self-deps and add
      -- dependency-only vertices as empty-dependency items.
      let data2 := Toposort.normalizedGraph data
      -- Step 3: Kahn's algorithm, fuel = map size (upper bound on iterations).
      Toposort.kahnLoop data2 [] data2.size
-- !benchmark @end code def=toposort

-- !benchmark @start code_aux def=toposort_flatten
-- !benchmark @end code_aux def=toposort_flatten

def Toposort.toposort_flatten :
    [Ord α] → Std.HashMap α (Std.HashSet α) → Bool → Option (List α) :=
-- !benchmark @start code def=toposort_flatten
  fun [Ord α] data sort =>
    match Toposort.toposort data with
    | none => none
    | some levels => some (Toposort.flattenLayers sort levels)
-- !benchmark @end code def=toposort_flatten
