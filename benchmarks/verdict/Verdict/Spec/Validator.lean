import Verdict.Harness

/-!
# Verdict.Spec.Validator

Specifications for the validator layer. Each `spec_*` takes an
arbitrary `impl : RepoImpl`.

DO NOT MODIFY — this file is frozen curator-given content.
-/

/-- The empty path is simple. -/
def spec_is_simple_path_nil (impl : RepoImpl) : Prop :=
  impl.verdict.isSimplePath [] = true

/-- A singleton path is simple. -/
def spec_is_simple_path_singleton (impl : RepoImpl) : Prop :=
  ∀ (i : Nat), impl.verdict.isSimplePath [i] = true

/-- A path with a repeated index is not simple. -/
def spec_is_simple_path_not_if_dup (impl : RepoImpl) : Prop :=
  ∀ (path : Verdict.BundlePath) (i : Nat),
    path.count i ≥ 2 →
    impl.verdict.isSimplePath path = false

/-- Every index in a `pathInBounds`-accepted path is strictly less
    than `bundleLen`. -/
def spec_path_in_bounds_forall (impl : RepoImpl) : Prop :=
  ∀ (path : Verdict.BundlePath) (bundleLen : Nat),
    impl.verdict.pathInBounds path bundleLen = true →
    ∀ i, i ∈ path → i < bundleLen

/-- `chainFromPath` has length `|path| + 1` when all indices are in
    bounds, and its last element is always `root`. -/
def spec_chain_from_path_shape (impl : RepoImpl) : Prop :=
  ∀ (bundle : List Verdict.Certificate)
    (path : Verdict.BundlePath)
    (root : Verdict.Certificate),
    impl.verdict.pathInBounds path bundle.length = true →
    let chain := impl.verdict.chainFromPath bundle path root
    chain.length = path.length + 1 ∧ chain.getLast? = some root

/-- `validateX509Base64` rejects an empty bundle. -/
def spec_validator_empty_bundle (impl : RepoImpl) : Prop :=
  ∀ (rootsB64 : List Verdict.Bytes) (task : Verdict.Task),
    (impl.verdict.validateX509Base64 rootsB64 [] task).isOk = false

/-- A `BundlePath + rootIdx` witnesses `Query.valid()` against a
    (bundle, roots) pair iff it is a simple, in-bounds path that
    starts at the leaf (index 0), whose consecutive pairs all pass
    `issuedByRaw`, and whose last element is issued by
    `roots[rootIdx]`. Mirrors Verus's
    `is_simple_path_to_root(path, root_idx)` at
    `verdict/src/validator.rs:110-128`. Bare definition (not an API
    obligation) so both soundness and completeness specs can share
    it. -/
def chainWitnesses
    (impl : RepoImpl)
    (bundle : List Verdict.Certificate)
    (roots  : List Verdict.Certificate)
    (path   : Verdict.BundlePath)
    (rootIdx : Nat) : Prop :=
  path ≠ [] ∧
  path.head? = some 0 ∧
  impl.verdict.isSimplePath path = true ∧
  impl.verdict.pathInBounds path bundle.length = true ∧
  rootIdx < roots.length ∧
  (∀ i, i + 1 < path.length →
    impl.verdict.issuedByRaw
      bundle[path[i+1]!]! bundle[path[i]!]! = true) ∧
  (match path.getLast? with
   | some lastIdx =>
       impl.verdict.issuedByRaw roots[rootIdx]! bundle[lastIdx]! = true
   | none => False)

/-- Soundness: if the validator accepts, then a witnessing path
    exists. Mirrors Verus `Validator::validate`'s ensures
    `res matches Ok(true) ⇒ Query.valid()`
    (`verdict/src/validator.rs:60-65`, `:137-143`). -/
def spec_validator_sound (impl : RepoImpl) : Prop :=
  ∀ (rootsB64 bundleB64 : List Verdict.Bytes) (task : Verdict.Task),
    impl.verdict.validateX509Base64 rootsB64 bundleB64 task = .ok true →
    let roots  := rootsB64.filterMap impl.verdict.parseX509Base64
    let bundle := bundleB64.filterMap impl.verdict.parseX509Base64
    bundle ≠ [] ∧
    ∃ (path : Verdict.BundlePath) (rootIdx : Nat),
      chainWitnesses impl bundle roots path rootIdx

/-- Completeness: if a witnessing path exists, the validator
    accepts. Mirrors the `⇐` direction of Verus
    `Validator::validate`'s ensures. Without this spec, a
    validator that unconditionally returns `.ok false` would still
    pass `spec_validator_sound` vacuously. -/
def spec_validator_complete (impl : RepoImpl) : Prop :=
  ∀ (rootsB64 bundleB64 : List Verdict.Bytes) (task : Verdict.Task),
    let roots  := rootsB64.filterMap impl.verdict.parseX509Base64
    let bundle := bundleB64.filterMap impl.verdict.parseX509Base64
    (∃ (path : Verdict.BundlePath) (rootIdx : Nat),
        chainWitnesses impl bundle roots path rootIdx) →
    impl.verdict.validateX509Base64 rootsB64 bundleB64 task = .ok true

/-- Tail-closure of `isSimplePath`: uniqueness at the head extends
    to uniqueness over the tail. Mirrors the inductive structure of
    Verus `Query::is_simple_path` at
    `verdict/src/validator.rs:94-108`. -/
def spec_is_simple_path_tail (impl : RepoImpl) : Prop :=
  ∀ (i : Nat) (path : Verdict.BundlePath),
    impl.verdict.isSimplePath (i :: path) = true →
    impl.verdict.isSimplePath path = true

/-- `chainFromPath` starts at the first bundle cert indexed by the
    path. Mirrors the shape of `check_simple_path` at
    `verdict/src/validator.rs:368-440`, which assumes `path[0]` is
    the leaf cert. -/
def spec_chain_from_path_head (impl : RepoImpl) : Prop :=
  ∀ (bundle : List Verdict.Certificate)
    (i : Nat) (path : Verdict.BundlePath)
    (root : Verdict.Certificate),
    impl.verdict.pathInBounds (i :: path) bundle.length = true →
    (impl.verdict.chainFromPath bundle (i :: path) root).head?
      = bundle[i]?
