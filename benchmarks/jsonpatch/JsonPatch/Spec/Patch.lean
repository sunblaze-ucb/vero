import JsonPatch.Harness
import JsonPatch.Spec.Pointer

/-!
# JsonPatch.Spec.Patch

Specifications for the JSON Patch core: `applyOp` (one RFC 6902 operation) and
`apply` (an operation list). These are the complex, structural heart of the
benchmark. The curated target is the **patch-apply semantics**, never `diff` /
`make_patch` (a `diff` would be reward-hackable by emitting a whole-document
replace); here every law pins how a *given* patch transforms a *given*
document.

The laws, all stated as general `∀`-laws over arbitrary `Json` / `Op` / paths
against the frozen Spec-local reference helpers:

- **Per-op structural laws.** `add` inserts-or-overwrites at an object member
  (`spec_add_obj_sets`); `remove` deletes an existing member and preserves the
  siblings (`spec_remove_obj_deletes`); `replace` overwrites an existing member
  and *fails* on an absent one (`spec_replace_obj_requires_present`); `test` is
  the identity when the pointed value matches and a conflict otherwise
  (`spec_test_identity_or_fail`).
- **move vs copy (the distinguishing laws).** `move` is exactly remove-from
  then add-at-target (`spec_move_is_remove_then_add`); `copy` leaves the source
  in place — after a copy the source still resolves to its original value
  (`spec_copy_preserves_source`). Together these force a candidate to implement
  the two operations *differently* (a `move := copy` fails
  `spec_move_is_remove_then_add`; a `copy := move` fails
  `spec_copy_preserves_source`).
- **Op-list monoid action.** `apply []` is the identity
  (`spec_apply_nil`); `apply (op :: rest)` is `applyOp op` then `apply rest`
  (`spec_apply_cons`); and the crown composition homomorphism
  `apply (p₁ ++ p₂) = applyList p₁ then applyList p₂` with monadic
  short-circuit (`spec_apply_append_hom`).
- **applyOp pinned to the reference** (`spec_applyOp_ref`): the single-op action
  equals the frozen reference `refApplyOp`, ruling out any op whose behaviour
  drifts from RFC 6902 on the cases the semantic laws do not separately name.

## Self-contained frozen reference helpers

Everything the specs reference is a byte-for-byte frozen copy living in this
Spec file (or the imported `Spec/Pointer.lean`): `refObjSet`, `refObjRemove`,
`refObjHas`, `refArrInsert`, `refArrRemove`, `refArrSet`, `refAddLast`,
`refRemoveLast`, `refReplaceLast`, `refModifyAt`, `refApplyOp`, `refApplyList`
(and, via the import, `refObjGet`, `refArrIndex`, `refResolveParts`). The
implementation helpers of the same shape live in the agent-editable
`!benchmark global_aux` slot, which `codeproof` mode empties and lets the
candidate re-supply. Anchoring every reference semantic to these Spec-local
frozen copies makes the obligations non-hackable: a candidate that redefines
`modifyAt`/`addLast` degenerately cannot also bend the reference the specs
compare against. **No spec references an editable-slot helper.**

DO NOT MODIFY.
-/

namespace JsonPatch

-- ── Frozen Spec-local copies of the Impl/Patch helpers ───────

/-- Frozen Spec-local copy of `Impl/Pointer.objSet`. -/
def refObjSet (kvs : List (String × Json)) (k : String) (v : Json) : List (String × Json) :=
  match kvs with
  | [] => [(k, v)]
  | (k', v') :: rest =>
    if k' = k then (k, v) :: rest else (k', v') :: refObjSet rest k v

/-- Frozen Spec-local copy of `Impl/Pointer.objRemove`. -/
def refObjRemove (kvs : List (String × Json)) (k : String) : List (String × Json) :=
  match kvs with
  | [] => []
  | (k', v') :: rest =>
    if k' = k then rest else (k', v') :: refObjRemove rest k

/-- Frozen Spec-local copy of `Impl/Pointer.objHas`. -/
def refObjHas (kvs : List (String × Json)) (k : String) : Bool :=
  (refObjGet kvs k).isSome

/-- Frozen Spec-local copy of `Impl/Patch.arrInsert`. -/
def refArrInsert (xs : List Json) (i : Nat) (v : Json) : List Json :=
  match i, xs with
  | 0, xs => v :: xs
  | _+1, [] => [v]
  | i+1, x :: rest => x :: refArrInsert rest i v

/-- Frozen Spec-local copy of `Impl/Patch.arrRemove`. -/
def refArrRemove (xs : List Json) (i : Nat) : List Json :=
  match i, xs with
  | _, [] => []
  | 0, _ :: rest => rest
  | i+1, x :: rest => x :: refArrRemove rest i

/-- Frozen Spec-local copy of `Impl/Patch.arrSet`. -/
def refArrSet (xs : List Json) (i : Nat) (v : Json) : List Json :=
  match i, xs with
  | _, [] => []
  | 0, _ :: rest => v :: rest
  | i+1, x :: rest => x :: refArrSet rest i v

/-- Frozen Spec-local copy of `Impl/Patch.addLast`. -/
def refAddLast (doc : Json) (part : String) (v : Json) : Option Json :=
  match doc with
  | .obj kvs => some (.obj (refObjSet kvs part v))
  | .arr xs =>
    if part = "-" then some (.arr (xs ++ [v]))
    else match refArrIndex part with
      | some i => if i ≤ xs.length then some (.arr (refArrInsert xs i v)) else none
      | none => none
  | _ => none

/-- Frozen Spec-local copy of `Impl/Patch.removeLast`. -/
def refRemoveLast (doc : Json) (part : String) : Option Json :=
  match doc with
  | .obj kvs => if refObjHas kvs part then some (.obj (refObjRemove kvs part)) else none
  | .arr xs =>
    match refArrIndex part with
    | some i => if i < xs.length then some (.arr (refArrRemove xs i)) else none
    | none => none
  | _ => none

/-- Frozen Spec-local copy of `Impl/Patch.replaceLast`. -/
def refReplaceLast (doc : Json) (part : String) (v : Json) : Option Json :=
  match doc with
  | .obj kvs => if refObjHas kvs part then some (.obj (refObjSet kvs part v)) else none
  | .arr xs =>
    match refArrIndex part with
    | some i => if i < xs.length then some (.arr (refArrSet xs i v)) else none
    | none => none
  | _ => none

/-- Frozen Spec-local copy of `Impl/Patch.addRoot`. -/
def refAddRoot (doc : Json) (v : Json) : Option Json :=
  match doc with
  | .obj _ => some v
  | _ => none

/-- Frozen Spec-local copy of `Impl/Patch.modifyAt`. -/
def refModifyAt (doc : Json) (parts : List String)
    (f : Json → String → Option Json) : Option Json :=
  match parts with
  | [] => none
  | [last] => f doc last
  | p :: ps =>
    match doc with
    | .obj kvs =>
      match refObjGet kvs p with
      | some child =>
        match refModifyAt child ps f with
        | some child' => some (.obj (refObjSet kvs p child'))
        | none => none
      | none => none
    | .arr xs =>
      match refArrIndex p with
      | some i =>
        match xs[i]? with
        | some child =>
          match refModifyAt child ps f with
          | some child' => some (.arr (refArrSet xs i child'))
          | none => none
        | none => none
      | none => none
    | _ => none

/-- Frozen Spec-local copy of `Impl/Patch.applyOp` — the reference single-op
    action. -/
def refApplyOp (op : Op) (doc : Json) : Option Json :=
  match op with
  | .add path v =>
      match path with
      | [] => refAddRoot doc v
      | _ => refModifyAt doc path (fun d part => refAddLast d part v)
  | .remove path =>
      match path with
      | [] => none
      | _ => refModifyAt doc path (fun d part => refRemoveLast d part)
  | .replace path v =>
      match path with
      | [] => some v
      | _ => refModifyAt doc path (fun d part => refReplaceLast d part v)
  | .test path v =>
      match refResolveParts doc path with
      | some val => if val = v then some doc else none
      | none => none
  | .move from_ path =>
      match from_ with
      | [] => none
      | _ =>
        match refResolveParts doc from_ with
        | some val =>
          if from_ = path then some doc
          else
            match refModifyAt doc from_ (fun d part => refRemoveLast d part) with
            | some doc' =>
              match path with
              | [] => refAddRoot doc' val
              | _ => refModifyAt doc' path (fun d part => refAddLast d part val)
            | none => none
        | none => none
  | .copy from_ path =>
      match from_ with
      | [] => none
      | _ =>
        match refResolveParts doc from_ with
        | some val =>
          match path with
          | [] => refAddRoot doc val
          | _ => refModifyAt doc path (fun d part => refAddLast d part val)
        | none => none

/-- Frozen Spec-local copy of `Impl/Patch.apply` — the reference op-list fold. -/
def refApplyList (ops : List Op) (doc : Json) : Option Json :=
  match ops with
  | [] => some doc
  | op :: rest =>
    match refApplyOp op doc with
    | some doc' => refApplyList rest doc'
    | none => none

end JsonPatch

open JsonPatch

-- ════════════════════════════════════════════════════════════════
-- applyOp pinned to the reference single-op action
-- ════════════════════════════════════════════════════════════════

/-- `applyOp` is exactly the reference single-op action: for every operation and
    document, `applyOp op doc = refApplyOp op doc`, where `refApplyOp` is the
    frozen Spec-local RFC 6902 reference. This pins the whole single-op behaviour
    (add/remove/replace/move/copy/test, including the `none`-on-conflict
    semantics) to the reference, on every case the semantic laws below do not
    separately name. Stated against the frozen reference (not the editable
    implementation helper). Over `impl.jsonPatch.applyOp`, `refApplyOp`. -/
def spec_applyOp_ref (impl : RepoImpl) : Prop :=
  ∀ (op : Op) (doc : Json), impl.jsonPatch.applyOp op doc = refApplyOp op doc

-- ════════════════════════════════════════════════════════════════
-- Per-op structural laws
-- ════════════════════════════════════════════════════════════════

/-- `add` at a top-level object member inserts-or-overwrites: applying
    `add [k] v` to an object rebuilds it with `refObjSet kvs k v` (which
    overwrites in place if `k` is present, else appends). Pins `add`'s object
    semantics to Python `dict[k] = v`. Over `impl.jsonPatch.applyOp`,
    `refObjSet`. -/
def spec_add_obj_sets (impl : RepoImpl) : Prop :=
  ∀ (kvs : List (String × Json)) (k : String) (v : Json),
    impl.jsonPatch.applyOp (.add [k] v) (.obj kvs) = some (.obj (refObjSet kvs k v))

/-- `remove` at a top-level object member deletes it when present and conflicts
    when absent: applying `remove [k]` to an object is `some (obj (refObjRemove
    kvs k))` if `k ∈ kvs`, else `none`. Pins the delete-or-conflict semantics of
    Python `del dict[k]`. Over `impl.jsonPatch.applyOp`, `refObjHas`,
    `refObjRemove`. -/
def spec_remove_obj_deletes (impl : RepoImpl) : Prop :=
  ∀ (kvs : List (String × Json)) (k : String),
    impl.jsonPatch.applyOp (.remove [k]) (.obj kvs) =
      (if refObjHas kvs k then some (.obj (refObjRemove kvs k)) else none)

/-- `replace` requires the member to exist: applying `replace [k] v` to an
    object overwrites `k` when present and **conflicts** (`none`) when absent —
    unlike `add`, `replace` never creates a new member. Pins the
    overwrite-existing-only semantics and, together with `spec_add_obj_sets`,
    distinguishes `replace` from `add`. Over `impl.jsonPatch.applyOp`,
    `refObjHas`, `refObjSet`. -/
def spec_replace_obj_requires_present (impl : RepoImpl) : Prop :=
  ∀ (kvs : List (String × Json)) (k : String) (v : Json),
    impl.jsonPatch.applyOp (.replace [k] v) (.obj kvs) =
      (if refObjHas kvs k then some (.obj (refObjSet kvs k v)) else none)

/-- `test` is the identity-or-fail operation: `test path v` returns the document
    **unchanged** exactly when the pointed value equals `v` (via the frozen
    reference walk), and conflicts (`none`) otherwise. It never mutates the
    document. Pins the assertion semantics of RFC 6902 `test`. Over
    `impl.jsonPatch.applyOp`, `refResolveParts`. -/
def spec_test_identity_or_fail (impl : RepoImpl) : Prop :=
  ∀ (doc : Json) (path : List String) (v : Json),
    impl.jsonPatch.applyOp (.test path v) doc =
      (match refResolveParts doc path with
       | some val => if val = v then some doc else none
       | none => none)

-- ════════════════════════════════════════════════════════════════
-- move vs copy (the distinguishing laws)
-- ════════════════════════════════════════════════════════════════

/-- `move` is exactly remove-from then add-at-target (the RFC 6902 definition),
    for the common case of *non-root* source and target (`from_` and `path` both
    nonempty). When the source resolves to `val`: if `from_ = path` it is a no-op;
    otherwise `move` removes `from_` and then adds `val` at `path`; an
    unresolvable source conflicts. This forces `move` to *delete* the source (a
    `move := copy` leaves the source behind and fails here). Stated entirely
    against frozen reference helpers, with the root cases (empty `from_`/`path`)
    deliberately excluded — their conflict / whole-document-replace behaviour is
    covered by `spec_applyOp_ref`. Over `impl.jsonPatch.applyOp`,
    `refResolveParts`, `refRemoveLast`, `refAddLast`, `refModifyAt`. -/
def spec_move_is_remove_then_add (impl : RepoImpl) : Prop :=
  ∀ (doc : Json) (fp pp : String) (from_ path : List String),
    let f := fp :: from_
    let p := pp :: path
    impl.jsonPatch.applyOp (.move f p) doc =
      (match refResolveParts doc f with
       | some val =>
         if f = p then some doc
         else
           match refModifyAt doc f (fun d part => refRemoveLast d part) with
           | some doc' => refModifyAt doc' p (fun d part => refAddLast d part val)
           | none => none
       | none => none)

/-- `copy` preserves the source: after copying a top-level object member `f` to a
    fresh target key `t` (with `f ≠ t` and `t` absent), the source `f` still
    resolves to its original value. This forces `copy` to *not* delete the source
    (a `copy := move` removes it and fails here), distinguishing `copy` from
    `move`. Over `impl.jsonPatch.applyOp`, `impl.jsonPatch.resolve`, `refObjGet`,
    `refObjHas`. -/
def spec_copy_preserves_source (impl : RepoImpl) : Prop :=
  ∀ (kvs : List (String × Json)) (f t : String) (val : Json),
    f ≠ t → refObjGet kvs f = some val → refObjHas kvs t = false →
    (match impl.jsonPatch.applyOp (.copy [f] [t]) (.obj kvs) with
     | some doc' => impl.jsonPatch.resolve doc' [f] = some val
     | none => False)

-- ════════════════════════════════════════════════════════════════
-- Op-list monoid action
-- ════════════════════════════════════════════════════════════════

/-- `apply []` is the identity of the op-list action: applying the empty patch
    returns the document unchanged. Over `impl.jsonPatch.apply`. -/
def spec_apply_nil (impl : RepoImpl) : Prop :=
  ∀ (doc : Json), impl.jsonPatch.apply [] doc = some doc

/-- `apply (op :: rest)` folds `applyOp op` then `apply rest` with monadic
    short-circuit: a conflict on the head aborts the whole patch. Pins the
    left-to-right fold that underlies `apply`. Over `impl.jsonPatch.apply`,
    `impl.jsonPatch.applyOp`. -/
def spec_apply_cons (impl : RepoImpl) : Prop :=
  ∀ (op : Op) (rest : List Op) (doc : Json),
    impl.jsonPatch.apply (op :: rest) doc =
      (match impl.jsonPatch.applyOp op doc with
       | some doc' => impl.jsonPatch.apply rest doc'
       | none => none)

/-- Composition homomorphism (the crown patch law): applying the concatenation
    of two patches equals applying the first and then, on success, the second —
    `apply (p₁ ++ p₂) doc = (apply p₁ doc) >>= apply p₂`, with a conflict
    anywhere aborting the whole result. This is the op-list monoid acting on
    documents. The candidate's `apply` (on the concatenation, left side) is
    equated against the frozen reference fold `refApplyList` on the two pieces
    (right side): pinning the right side to the fixed fold means the law cannot
    be gamed by a candidate whose `apply` folds inconsistently — it must agree
    with the reference fold. Over `impl.jsonPatch.apply`, `refApplyList`. -/
def spec_apply_append_hom (impl : RepoImpl) : Prop :=
  ∀ (p1 p2 : List Op) (doc : Json),
    impl.jsonPatch.apply (p1 ++ p2) doc =
      (match refApplyList p1 doc with
       | some doc' => refApplyList p2 doc'
       | none => none)

-- ════════════════════════════════════════════════════════════════
-- Deeper op-list algebra + patch round-trips
-- ════════════════════════════════════════════════════════════════

/-- Applying a one-element patch is the single-op action: `apply [op] doc =
    applyOp op doc`. Pins the length-one fold to `applyOp`. Over
    `impl.jsonPatch.apply`, `impl.jsonPatch.applyOp`. -/
def spec_apply_singleton_eq_applyOp (impl : RepoImpl) : Prop :=
  ∀ (op : Op) (doc : Json),
    impl.jsonPatch.apply [op] doc = impl.jsonPatch.applyOp op doc

/-- Three-patch composition: `apply (p₁ ++ (p₂ ++ p₃)) doc` equals running the
    reference fold on `p₁`, then `p₂`, then `p₃`, with a conflict at any phase
    aborting the whole result. Extends the two-patch composition law to a triple,
    pinning the associative monoid action of op-lists on documents. The candidate's
    `apply` on the full concatenation (left) is equated against the frozen fold
    `refApplyList` on the three pieces (right). Over `impl.jsonPatch.apply`,
    `refApplyList`. -/
def spec_apply_three_way_composition (impl : RepoImpl) : Prop :=
  ∀ (p1 p2 p3 : List Op) (doc : Json),
    impl.jsonPatch.apply (p1 ++ (p2 ++ p3)) doc =
      (match refApplyList p1 doc with
       | some d1 =>
         match refApplyList p2 d1 with
         | some d2 => refApplyList p3 d2
         | none => none
       | none => none)

/-- Conflict is absorbing under suffix append: if a patch `p₁` already conflicts on
    `doc`, then `p₁ ++ p₂` conflicts on `doc` too, for every suffix `p₂`. Pins the
    monadic short-circuit — a failed prefix cannot be resurrected by later
    operations. Over `impl.jsonPatch.apply`. -/
def spec_apply_prefix_conflict_absorbing (impl : RepoImpl) : Prop :=
  ∀ (p1 p2 : List Op) (doc : Json),
    impl.jsonPatch.apply p1 doc = none →
      impl.jsonPatch.apply (p1 ++ p2) doc = none

/-- `add` then read-back at an object location: if the parent path resolves to an
    object, then adding `v` at `parent ++ [k]` succeeds and resolving that same
    path afterwards yields exactly `v`. Pins the RFC 6902 guarantee that a
    successful object `add` makes the added value readable at its own path — the
    add-then-read round-trip through the rebuilt document spine. Over
    `impl.jsonPatch.applyOp`, `impl.jsonPatch.resolve`, `refResolveParts`. -/
def spec_add_obj_path_reads_back (impl : RepoImpl) : Prop :=
  ∀ (doc : Json) (parent : List String) (k : String) (v : Json) (kvs : List (String × Json)),
    refResolveParts doc parent = some (.obj kvs) →
    match impl.jsonPatch.applyOp (.add (parent ++ [k]) v) doc with
    | some doc' => impl.jsonPatch.resolve doc' (parent ++ [k]) = some v
    | none => False

/-- `add` then `remove` on a fresh object member is the identity: if the parent
    path resolves to an object not already containing key `k`, then the two-op
    patch `[add (parent ++ [k]) v, remove (parent ++ [k])]` returns the document
    unchanged. Pins the RFC 6902 inverse relationship between `add` (of a new
    member) and `remove` at an arbitrary-depth object location. Over
    `impl.jsonPatch.apply`, `refResolveParts`, `refObjHas`. -/
def spec_add_remove_fresh_obj_path_inverse (impl : RepoImpl) : Prop :=
  ∀ (doc : Json) (parent : List String) (k : String) (v : Json) (kvs : List (String × Json)),
    refResolveParts doc parent = some (.obj kvs) →
    refObjHas kvs k = false →
    impl.jsonPatch.apply [(.add (parent ++ [k]) v), (.remove (parent ++ [k]))] doc = some doc

/-- `replace` with the value already present is the identity: if a path resolves to
    `v`, then `replace path v` returns the document unchanged. Pins the RFC 6902
    guarantee that replacing a location with its current value is a no-op, at
    arbitrary depth (including the root pointer). Over `impl.jsonPatch.applyOp`,
    `refResolveParts`. -/
def spec_replace_resolved_value_identity (impl : RepoImpl) : Prop :=
  ∀ (doc : Json) (path : List String) (v : Json),
    refResolveParts doc path = some v →
    impl.jsonPatch.applyOp (.replace path v) doc = some doc

/-- A `test` operation anywhere inside a patch is a pure guard on the running
    document: `apply (p₁ ++ (test path v :: p₂)) doc` equals running `p₁`, then —
    if the pointed value at `path` equals `v` — running `p₂` on the *unchanged*
    intermediate document, and conflicting (`none`) otherwise (or if `p₁` or the
    lookup fails). The intermediate document is passed to the suffix byte-for-byte;
    `test` never mutates it. Over `impl.jsonPatch.apply`, `refApplyList`,
    `refResolveParts`. -/
def spec_test_in_patch_pure_guard (impl : RepoImpl) : Prop :=
  ∀ (p1 p2 : List Op) (doc : Json) (path : List String) (v : Json),
    impl.jsonPatch.apply (p1 ++ (.test path v :: p2)) doc =
      (match refApplyList p1 doc with
       | some mid =>
         match refResolveParts mid path with
         | some got => if got = v then refApplyList p2 mid else none
         | none => none
       | none => none)

/-- `move` decomposes into a remove-then-add patch, for a non-root, non-no-op
    move: when `f` and `p` are both nonempty, `f ≠ p`, and `f` resolves to `val`,
    then `applyOp (move f p) doc = apply [remove f, add p val] doc`. Pins the RFC
    6902 definition of `move` as "remove from the source, then add the removed
    value at the target" — including the index-shifting behaviour when the source
    and target lie in the same array, since both sides add onto the post-remove
    document. Over `impl.jsonPatch.applyOp`, `impl.jsonPatch.apply`,
    `refResolveParts`. -/
def spec_move_equals_remove_add_patch (impl : RepoImpl) : Prop :=
  ∀ (doc : Json) (f p : List String) (val : Json),
    (f = [] → False) →
    (p = [] → False) →
    (f = p → False) →
    refResolveParts doc f = some val →
    impl.jsonPatch.applyOp (.move f p) doc =
      impl.jsonPatch.apply [(.remove f), (.add p val)] doc

/-- `copy` makes the target read back the source value: for a non-root source that
    resolves to `val` and an object-valued target parent, `copy from_ (parent ++
    [k])` succeeds and resolving the target path afterwards yields exactly `val`.
    Pins the RFC 6902 guarantee that a copy deposits the source value (read before
    the write) at the target, readable there. Over `impl.jsonPatch.applyOp`,
    `impl.jsonPatch.resolve`, `refResolveParts`. -/
def spec_copy_obj_target_reads_source (impl : RepoImpl) : Prop :=
  ∀ (doc : Json) (from_ parent : List String) (k : String) (val : Json) (kvs : List (String × Json)),
    (from_ = [] → False) →
    refResolveParts doc from_ = some val →
    refResolveParts doc parent = some (.obj kvs) →
    match impl.jsonPatch.applyOp (.copy from_ (parent ++ [k])) doc with
    | some doc' => impl.jsonPatch.resolve doc' (parent ++ [k]) = some val
    | none => False
