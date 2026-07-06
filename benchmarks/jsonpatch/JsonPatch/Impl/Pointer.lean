-- !benchmark @start imports
-- !benchmark @end imports

/-!
# JsonPatch.Impl.Pointer

JSON Pointer core (RFC 6901), ported from the `jsonpointer` library
(`jsonpointer.py`, v3.0.0, stefankoegl, Modified BSD). This module also
defines the shared, mathlib-free JSON model used by the whole benchmark.

Representation (all core `Int`/`String`/`List`, no `Float`):
```
inductive Json | null | bool Bool | num Int | str String
              | arr (List Json) | obj (List (String × Json))
```
An `obj` is an association list `key ↦ value`. It models a Python `dict`: keys
are unique and carried in insertion order; an in-place overwrite keeps a key's
position, a fresh key is appended, and a removal drops it. `num` is an `Int`
(JSON numbers restricted to integers — enough for the structural patch/pointer
semantics and keeps everything decidable and `Float`-free).

Because `Json` recurses through `List (String × Json)`, the automatic
`deriving DecidableEq` handler does not apply; the instance is supplied by hand
below (a structural boolean equality `Json.beq` proven sound and reflexive).
This is frozen type-level vocabulary, not an implementation slot.

A **reference token list** (`List String`) is a JSON Pointer whose parts have
already been unescaped — the RFC calls these the "reference tokens". The string
form (`"/foo/a~1b"`) is turned into a token list by `parsePointer`, which does
the `/`-split, per-token `unescape`, the leading-`/` check, and the `~`-escape
validation exactly as `jsonpointer.JsonPointer.__init__` does.

APIs in this module: `escape` / `unescape` (RFC6901 `~0`/`~1` token escaping —
note the deliberately *asymmetric* replacement order, implemented as total
structural char scanners `escapeChars` / `unescapeChars`), and `resolve` (walk a
token list through a document, `none` on a missing object member, an
out-of-bounds or malformed array index).

Types and signatures are fixed vocabulary (DO NOT MODIFY).
-/

namespace JsonPatch

/-- A JSON value, modelled mathlib-free. `num` is an `Int` (integer JSON
    numbers); `obj` is an association list `key ↦ value` modelling a Python
    `dict` (unique keys, insertion order). Mirrors the JSON documents that
    `jsonpatch`/`jsonpointer` operate on. -/
inductive Json where
  | null
  | bool (b : Bool)
  | num (n : Int)
  | str (s : String)
  | arr (xs : List Json)
  | obj (kvs : List (String × Json))
deriving Repr, Inhabited

namespace Json

/-!
`Json.beq` is a structural boolean equality on `Json`. Frozen; used only to
supply the hand-written `DecidableEq` instance (the auto-deriver cannot handle
the `List (String × Json)` recursion).
-/
mutual
def beq : Json → Json → Bool
  | .null, .null => true
  | .bool a, .bool b => a == b
  | .num a, .num b => a == b
  | .str a, .str b => a == b
  | .arr a, .arr b => beqArr a b
  | .obj a, .obj b => beqObj a b
  | _, _ => false
def beqArr : List Json → List Json → Bool
  | [], [] => true
  | x :: xs, y :: ys => beq x y && beqArr xs ys
  | _, _ => false
def beqObj : List (String × Json) → List (String × Json) → Bool
  | [], [] => true
  | (k1, v1) :: xs, (k2, v2) :: ys => (k1 == k2) && beq v1 v2 && beqObj xs ys
  | _, _ => false
end

mutual
theorem beq_eq : ∀ (a b : Json), beq a b = true → a = b
  | .null, b, h => by cases b <;> simp_all [beq]
  | .bool _, b, h => by cases b <;> simp_all [beq]
  | .num _, b, h => by cases b <;> simp_all [beq]
  | .str _, b, h => by cases b <;> simp_all [beq]
  | .arr xs, b, h => by
      cases b <;> simp_all [beq]
      exact beqArr_eq xs _ h
  | .obj kvs, b, h => by
      cases b <;> simp_all [beq]
      exact beqObj_eq kvs _ h
theorem beqArr_eq : ∀ (a b : List Json), beqArr a b = true → a = b
  | [], b, h => by cases b <;> simp_all [beqArr]
  | x :: xs, b, h => by
      cases b with
      | nil => simp [beqArr] at h
      | cons y ys =>
        simp [beqArr] at h
        have := beq_eq x y h.1
        have := beqArr_eq xs ys h.2
        simp_all
theorem beqObj_eq : ∀ (a b : List (String × Json)), beqObj a b = true → a = b
  | [], b, h => by cases b <;> simp_all [beqObj]
  | (k1, v1) :: xs, b, h => by
      cases b with
      | nil => simp [beqObj] at h
      | cons hd ys =>
        obtain ⟨k2, v2⟩ := hd
        simp [beqObj] at h
        have := beq_eq v1 v2 h.1.2
        have := beqObj_eq xs ys h.2
        simp_all
end

mutual
theorem beq_refl : ∀ (a : Json), beq a a = true
  | .null => by simp [beq]
  | .bool _ => by simp [beq]
  | .num _ => by simp [beq]
  | .str _ => by simp [beq]
  | .arr xs => by simp [beq]; exact beqArr_refl xs
  | .obj kvs => by simp [beq]; exact beqObj_refl kvs
theorem beqArr_refl : ∀ (a : List Json), beqArr a a = true
  | [] => by simp [beqArr]
  | x :: xs => by simp [beqArr]; exact ⟨beq_refl x, beqArr_refl xs⟩
theorem beqObj_refl : ∀ (a : List (String × Json)), beqObj a a = true
  | [] => by simp [beqObj]
  | (_, v) :: xs => by simp [beqObj]; exact ⟨beq_refl v, beqObj_refl xs⟩
end

end Json

instance : DecidableEq Json := fun a b =>
  if h : Json.beq a b = true then isTrue (Json.beq_eq a b h)
  else isFalse (fun heq => h (heq ▸ Json.beq_refl a))

/-- A single RFC 6902 patch operation. Paths (`path`, `from_`) are carried as
    *reference-token lists* (already-unescaped parts). Mirrors the six
    `PatchOperation` subclasses of `jsonpatch.py`. -/
inductive Op where
  | add     (path : List String) (value : Json)
  | remove  (path : List String)
  | replace (path : List String) (value : Json)
  | move    (from_ : List String) (path : List String)
  | copy    (from_ : List String) (path : List String)
  | test    (path : List String) (value : Json)
deriving Repr, DecidableEq, Inhabited

-- ── API signatures (DO NOT MODIFY) ───────────────────────────

/-- `escape s`: RFC 6901 reference-token escape — `~` ↦ `~0`, then `/` ↦ `~1`. -/
abbrev EscapeSig := String → String

/-- `unescape s`: RFC 6901 reference-token unescape — `~1` ↦ `/`, then `~0` ↦ `~`. -/
abbrev UnescapeSig := String → String

/-- `resolve doc parts`: resolve a reference-token list against `doc`, returning
    the referenced sub-value or `none` on a lookup failure. -/
abbrev ResolveSig := Json → List String → Option Json

end JsonPatch

-- !benchmark @start global_aux
namespace JsonPatch

/-- `objGet kvs k`: first value bound to key `k` in the object assoc-list `kvs`,
    or `none`. Mirrors Python `dict.__getitem__` / `KeyError`. Frozen helper. -/
def objGet (kvs : List (String × Json)) (k : String) : Option Json :=
  match kvs with
  | [] => none
  | (k', v) :: rest => if k' = k then some v else objGet rest k

/-- `objSet kvs k v`: bind key `k` to `v` in `kvs`, overwriting **in place** if
    `k` is already present (keeping its position) and otherwise appending at the
    end. Mirrors Python `dict[k] = v` (insertion-order preserving). Frozen
    helper. -/
def objSet (kvs : List (String × Json)) (k : String) (v : Json) : List (String × Json) :=
  match kvs with
  | [] => [(k, v)]
  | (k', v') :: rest =>
    if k' = k then (k, v) :: rest else (k', v') :: objSet rest k v

/-- `objRemove kvs k`: drop the binding for key `k` (the first match) from `kvs`.
    Mirrors Python `del dict[k]`. Frozen helper. -/
def objRemove (kvs : List (String × Json)) (k : String) : List (String × Json) :=
  match kvs with
  | [] => []
  | (k', v') :: rest =>
    if k' = k then rest else (k', v') :: objRemove rest k

/-- `objHas kvs k`: whether key `k` occurs in `kvs`. Frozen helper. -/
def objHas (kvs : List (String × Json)) (k : String) : Bool :=
  (objGet kvs k).isSome

/-- `isDigits s`: whether `s` is a nonempty run of ASCII digits. Frozen helper. -/
def isDigits (s : String) : Bool :=
  !s.isEmpty && s.all (fun c => '0' ≤ c && c ≤ '9')

/-- `arrIndex part`: parse an RFC 6901 array index — a token is a valid index
    iff it has no leading zeros, no sign, no spaces (`"0"` or `[1-9][0-9]*`).
    Returns the `Nat` index or `none`. Mirrors `jsonpointer`'s
    `_RE_ARRAY_INDEX = 0|[1-9][0-9]*`. Frozen helper. -/
def arrIndex (part : String) : Option Nat :=
  if part = "0" then some 0
  else if isDigits part && part.front ≠ '0' then some part.toNat!
  else none

/-- `walk doc part`: take a single reference-token step. On an object, `part` is
    a member key (`none` if absent). On an array, `part` must be a valid index in
    range (`none` on a bad or out-of-bounds index; the `"-"` end-of-list token is
    *not* resolvable and yields `none`). Any other document type yields `none`.
    Frozen helper mirroring `JsonPointer.walk`. -/
def walk (doc : Json) (part : String) : Option Json :=
  match doc with
  | .obj kvs => objGet kvs part
  | .arr xs =>
    match arrIndex part with
    | some i => xs[i]?
    | none => none
  | _ => none

/-- `resolveParts doc parts`: fold `walk` left-to-right over the token list.
    Frozen helper — the deterministic pointer walk underlying `resolve`. -/
def resolveParts (doc : Json) : List String → Option Json
  | [] => some doc
  | p :: ps =>
    match walk doc p with
    | some d => resolveParts d ps
    | none => none

/-- `escapeChars cs`: per-character RFC 6901 escape over a char list — `~ ↦ ~0`,
    `/ ↦ ~1`, every other char unchanged. Structurally recursive (total), so it
    carries equation lemmas the round-trip law can reason about. This exactly
    reproduces Python `s.replace('~', '~0').replace('/', '~1')`: the first
    replacement introduces only `~0` (never a bare `/`), so a single left-to-right
    per-character pass agrees with the two sequential passes. Frozen helper. -/
def escapeChars : List Char → List Char
  | [] => []
  | c :: rest =>
    if c = '~' then '~' :: '0' :: escapeChars rest
    else if c = '/' then '~' :: '1' :: escapeChars rest
    else c :: escapeChars rest

/-- `unescapeChars cs`: left-to-right RFC 6901 unescape scanner — `~1 ↦ /`,
    `~0 ↦ ~` (checked in that order, consuming two chars), every other char
    unchanged. Structurally recursive (total). This exactly reproduces Python
    `s.replace('~1', '/').replace('~0', '~')` (the first pass introduces only `/`,
    never a fresh `~0`, so the single scanner pass agrees with the two passes).
    Frozen helper. -/
def unescapeChars : List Char → List Char
  | [] => []
  | '~' :: '1' :: rest => '/' :: unescapeChars rest
  | '~' :: '0' :: rest => '~' :: unescapeChars rest
  | c :: rest => c :: unescapeChars rest

end JsonPatch
-- !benchmark @end global_aux

namespace JsonPatch

-- !benchmark @start code_aux def=escape
-- !benchmark @end code_aux def=escape

def escape : EscapeSig :=
-- !benchmark @start code def=escape
  fun s => String.ofList (escapeChars s.toList)
-- !benchmark @end code def=escape

-- !benchmark @start code_aux def=unescape
-- !benchmark @end code_aux def=unescape

def unescape : UnescapeSig :=
-- !benchmark @start code def=unescape
  fun s => String.ofList (unescapeChars s.toList)
-- !benchmark @end code def=unescape

-- !benchmark @start code_aux def=resolve
-- !benchmark @end code_aux def=resolve

def resolve : ResolveSig :=
-- !benchmark @start code def=resolve
  fun doc parts => resolveParts doc parts
-- !benchmark @end code def=resolve

end JsonPatch
