import JsonPatch.Harness

/-!
# JsonPatch.Spec.Pointer

Specifications for the JSON Pointer core: `escape` / `unescape` (the asymmetric
RFC 6901 `~0`/`~1` token escaping) and `resolve` (the reference-token walk).

The crown pointer law is the escape/unescape round-trip
`spec_unescape_escape_roundtrip`: `unescape (escape s) = s` for **every** string
`s`. This is exactly where the RFC's asymmetric replacement order matters —
`escape` rewrites `~` first then `/`, while `unescape` rewrites `~1` first then
`~0`. Getting either order wrong (e.g. an `unescape` that expands `~0` before
`~1`) breaks the round-trip on strings such as `"~1"` or `"/~"`, so the law pins
the correct ordering rather than merely "some pair of string substitutions".

`resolve` is pinned structurally to the frozen reference walk `refResolveParts`
(a byte-for-byte copy of the implementation walk), and characterised by its
per-step behaviour on objects and arrays.

## Self-contained frozen reference helpers

`refObjGet`, `refArrIndex`, `refWalk`, `refResolveParts` below are byte-for-byte
copies of the corresponding frozen `Impl/Pointer.lean` helpers, defined
**entirely within this Spec file**. They are duplicated deliberately: the
implementation helpers live inside the agent-editable `!benchmark global_aux`
slot, which `codeproof` mode empties and lets the candidate re-supply. Were the
specs to depend on them, a candidate could redefine `walk`/`objGet` degenerately
(e.g. `resolveParts := fun d _ => some d`) and satisfy `spec_resolve_walk`
vacuously while shipping a nonsense `resolve`. Anchoring every reference
semantic to these Spec-local frozen copies makes the obligations non-hackable:
the reference meaning is fixed no matter what the candidate supplies.

DO NOT MODIFY.
-/

namespace JsonPatch

/-- Frozen Spec-local copy of `Impl/Pointer.objGet`. -/
def refObjGet (kvs : List (String × Json)) (k : String) : Option Json :=
  match kvs with
  | [] => none
  | (k', v) :: rest => if k' = k then some v else refObjGet rest k

/-- Frozen Spec-local copy of `Impl/Pointer.isDigits`. -/
def refIsDigits (s : String) : Bool :=
  !s.isEmpty && s.all (fun c => '0' ≤ c && c ≤ '9')

/-- Frozen Spec-local copy of `Impl/Pointer.arrIndex`. -/
def refArrIndex (part : String) : Option Nat :=
  if part = "0" then some 0
  else if refIsDigits part && part.front ≠ '0' then some part.toNat!
  else none

/-- Frozen Spec-local copy of `Impl/Pointer.walk`. -/
def refWalk (doc : Json) (part : String) : Option Json :=
  match doc with
  | .obj kvs => refObjGet kvs part
  | .arr xs =>
    match refArrIndex part with
    | some i => xs[i]?
    | none => none
  | _ => none

/-- Frozen Spec-local copy of `Impl/Pointer.resolveParts` — the reference
    pointer walk. -/
def refResolveParts (doc : Json) : List String → Option Json
  | [] => some doc
  | p :: ps =>
    match refWalk doc p with
    | some d => refResolveParts d ps
    | none => none

/-- Frozen Spec-local copy of `Impl/Pointer.escapeChars` — the reference
    per-character escape scanner. -/
def refEscapeChars : List Char → List Char
  | [] => []
  | c :: rest =>
    if c = '~' then '~' :: '0' :: refEscapeChars rest
    else if c = '/' then '~' :: '1' :: refEscapeChars rest
    else c :: refEscapeChars rest

/-- Frozen Spec-local copy of `Impl/Pointer.unescapeChars` — the reference
    unescape scanner. -/
def refUnescapeChars : List Char → List Char
  | [] => []
  | '~' :: '1' :: rest => '/' :: refUnescapeChars rest
  | '~' :: '0' :: rest => '~' :: refUnescapeChars rest
  | c :: rest => c :: refUnescapeChars rest

end JsonPatch

open JsonPatch

-- ════════════════════════════════════════════════════════════════
-- escape / unescape: the asymmetric RFC 6901 round-trip
-- ════════════════════════════════════════════════════════════════

/-- Round-trip (the crown pointer law): `unescape` inverts `escape` on **every**
    string — `unescape (escape s) = s` for all `s`. Escaping rewrites `~ ↦ ~0`
    then `/ ↦ ~1`; unescaping must rewrite `~1 ↦ /` then `~0 ↦ ~` (the reverse
    order). Any wrong ordering (e.g. expanding `~0` before `~1`) fails on inputs
    like `"~1"` or `"/~"`, so this pins the RFC's exact asymmetric escaping —
    not merely "some inverse pair of substitutions". Over `impl.jsonPatch.escape`,
    `impl.jsonPatch.unescape`. -/
def spec_unescape_escape_roundtrip (impl : RepoImpl) : Prop :=
  ∀ (s : String), impl.jsonPatch.unescape (impl.jsonPatch.escape s) = s

/-- `escape` is exactly the reference per-character scanner: for every string,
    `escape s` equals `String.ofList (refEscapeChars s.toList)`, where
    `refEscapeChars` is the frozen Spec-local scanner (`~ ↦ ~0`, `/ ↦ ~1`, every
    other char fixed). Pins `escape` to touch only the two special characters in
    a single left-to-right pass (a wrong replacement order, or one that mangles
    ordinary text, fails). Stated against the frozen reference (not the editable
    implementation helper). Over `impl.jsonPatch.escape`, `refEscapeChars`. -/
def spec_escape_chars (impl : RepoImpl) : Prop :=
  ∀ (s : String), impl.jsonPatch.escape s = String.ofList (refEscapeChars s.toList)

-- ════════════════════════════════════════════════════════════════
-- resolve: the reference-token walk
-- ════════════════════════════════════════════════════════════════

/-- `resolve` is exactly the reference walk: for every document and token list,
    `resolve doc parts = refResolveParts doc parts`, where `refResolveParts` is
    the frozen Spec-local left-to-right `walk` fold. This pins `resolve` to the
    genuine step-by-step pointer walk (a resolver that ignores later tokens, or
    that reads arrays right-to-left, fails). Stated against the frozen reference
    walk (not the editable implementation helper), so it cannot be gamed by
    co-degenerating a candidate-supplied `resolveParts`. Over
    `impl.jsonPatch.resolve`, `refResolveParts`. -/
def spec_resolve_walk (impl : RepoImpl) : Prop :=
  ∀ (doc : Json) (parts : List String),
    impl.jsonPatch.resolve doc parts = refResolveParts doc parts

/-- `resolve` on the empty token list is the identity: the empty pointer `""`
    references the whole document. Pins the base case. Over
    `impl.jsonPatch.resolve`. -/
def spec_resolve_nil (impl : RepoImpl) : Prop :=
  ∀ (doc : Json), impl.jsonPatch.resolve doc [] = some doc

/-- `resolve` steps through one object member correctly: resolving `k :: rest`
    against an object first looks `k` up (via the frozen `refObjGet`) and then
    resolves `rest` against the found child; a missing key yields `none`. Pins the
    object-member walk step. Over `impl.jsonPatch.resolve`, `refObjGet`,
    `refResolveParts`. -/
def spec_resolve_obj_step (impl : RepoImpl) : Prop :=
  ∀ (kvs : List (String × Json)) (k : String) (rest : List String),
    impl.jsonPatch.resolve (.obj kvs) (k :: rest) =
      (match refObjGet kvs k with
       | some child => refResolveParts child rest
       | none => none)

/-- `resolve` decomposes over pointer concatenation: resolving `p₁ ++ p₂` against
    a document equals resolving `p₁`, then (on success) resolving `p₂` against the
    intermediate value, with a lookup failure anywhere yielding `none`. This pins
    `resolve` as a genuine left-to-right walk composing over token-list append —
    the pointer-walk homomorphism. Over `impl.jsonPatch.resolve`. -/
def spec_resolve_append_bind (impl : RepoImpl) : Prop :=
  ∀ (doc : Json) (p1 p2 : List String),
    impl.jsonPatch.resolve doc (p1 ++ p2) =
      (match impl.jsonPatch.resolve doc p1 with
       | some d => impl.jsonPatch.resolve d p2
       | none => none)

/-- `escape` distributes over string concatenation: `escape (a ++ b) = escape a ++
    escape b` for all strings. Pins the RFC 6901 token escaping as a per-character
    pass that is a monoid homomorphism from string concatenation — escaping a
    concatenation cannot differ from concatenating the two escapes. Over
    `impl.jsonPatch.escape`. -/
def spec_escape_append_hom (impl : RepoImpl) : Prop :=
  ∀ (a b : String),
    impl.jsonPatch.escape (a ++ b) = impl.jsonPatch.escape a ++ impl.jsonPatch.escape b

/-- `escape` never leaves a raw `/` in its output: for every string, the escaped
    form contains no `/` character (every `/` becomes `~1`). Pins the RFC 6901
    invariant that an escaped reference token is `/`-free, so a token can be safely
    joined into a `/`-delimited pointer string. Over `impl.jsonPatch.escape`. -/
def spec_escape_no_raw_slash (impl : RepoImpl) : Prop :=
  ∀ (s : String), ¬ (impl.jsonPatch.escape s).toList.contains '/'
