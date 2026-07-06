import JsonPatch.Impl.Pointer
-- !benchmark @start imports
-- !benchmark @end imports

/-!
# JsonPatch.Impl.Patch

JSON Patch core (RFC 6902), ported from the `jsonpatch` library
(`jsonpatch.py`, v1.33, stefankoegl, Modified BSD). Applies the six patch
operations — `add`, `remove`, `replace`, `move`, `copy`, `test` — over the
shared `Json` model from `Impl/Pointer`.

Every operation is a *pure, total* function returning `Option Json`: `some d'`
for the patched document, `none` for a conflict / test failure (mirroring
`jsonpatch`'s `JsonPatchConflict` / `JsonPatchTestFailed` exceptions). The
per-op semantics match `jsonpatch.py` exactly:

- **add** at an object member inserts-or-overwrites; at an array index inserts
  (shifting), the `"-"` token appends, an out-of-range index conflicts.
- **remove** deletes an existing member/element, conflicts when absent.
- **replace** overwrites an existing member/element, conflicts when absent.
- **move** = remove-from + add-at-target (a no-op when source = target, checked
  only after the source is successfully read).
- **copy** = add-at-target with the source value, leaving the source in place.
- **test** returns the document unchanged iff the pointed value structurally
  equals the operation value, else conflicts.

Root (empty-pointer) semantics match `jsonpatch.py` exactly: a root `replace`
returns the operation value; a root `add` returns the value only when the
document is an object (an array/scalar root `add` conflicts); a root `remove`
conflicts; and a root `move`/`copy` *source* conflicts (the root cannot be read
as a member), while a root *target* replaces the whole document with the moved
/copied value (again only when the post-edit document is an object).

`apply` folds the operation list left-to-right with monadic short-circuit
(`Option.bind`): a conflict anywhere aborts the whole patch, exactly like
`JsonPatch.apply`.

APIs in this module: `applyOp` (one operation) and `apply` (an operation list).

All functions are total, terminating `def`s (structural recursion on `Json` /
the path / the op list); no `Float`.

Types and signatures are fixed vocabulary (DO NOT MODIFY).
-/

namespace JsonPatch

-- ── API signatures (DO NOT MODIFY) ───────────────────────────

/-- `applyOp op doc`: apply a single RFC 6902 operation, `none` on conflict. -/
abbrev ApplyOpSig := Op → Json → Option Json

/-- `apply ops doc`: apply an operation list left-to-right, `none` on any
    conflict. -/
abbrev ApplySig := List Op → Json → Option Json

end JsonPatch

-- !benchmark @start global_aux
namespace JsonPatch

/-- `arrInsert xs i v`: insert `v` at index `i` of `xs`, shifting the tail
    right. Requires `i ≤ xs.length` (checked by callers). Frozen helper mirroring
    `list.insert(i, v)`. -/
def arrInsert (xs : List Json) (i : Nat) (v : Json) : List Json :=
  match i, xs with
  | 0, xs => v :: xs
  | _+1, [] => [v]           -- unreachable when i+1 ≤ length; benign
  | i+1, x :: rest => x :: arrInsert rest i v

/-- `arrRemove xs i`: drop the element at index `i` (requires `i < length`).
    Frozen helper mirroring `del list[i]`. -/
def arrRemove (xs : List Json) (i : Nat) : List Json :=
  match i, xs with
  | _, [] => []
  | 0, _ :: rest => rest
  | i+1, x :: rest => x :: arrRemove rest i

/-- `arrSet xs i v`: overwrite the element at index `i` with `v` (requires
    `i < length`). Frozen helper mirroring `list[i] = v`. -/
def arrSet (xs : List Json) (i : Nat) (v : Json) : List Json :=
  match i, xs with
  | _, [] => []
  | 0, _ :: rest => v :: rest
  | i+1, x :: rest => x :: arrSet rest i v

/-- `addLast doc part v`: perform an `add` at the *final* reference token `part`
    of a parent document `doc`. On an object: insert-or-overwrite the member.
    On an array: `"-"` appends, otherwise `part` must be a valid index with
    `0 ≤ i ≤ length` (else `none`). Frozen helper mirroring `AddOperation.apply`
    at the last step. -/
def addLast (doc : Json) (part : String) (v : Json) : Option Json :=
  match doc with
  | .obj kvs => some (.obj (objSet kvs part v))
  | .arr xs =>
    if part = "-" then some (.arr (xs ++ [v]))
    else match arrIndex part with
      | some i => if i ≤ xs.length then some (.arr (arrInsert xs i v)) else none
      | none => none
  | _ => none

/-- `removeLast doc part`: perform a `remove` at the final token `part`. On an
    object the member must exist; on an array the index must be valid and in
    range; else `none`. Frozen helper mirroring `RemoveOperation.apply`. -/
def removeLast (doc : Json) (part : String) : Option Json :=
  match doc with
  | .obj kvs => if objHas kvs part then some (.obj (objRemove kvs part)) else none
  | .arr xs =>
    match arrIndex part with
    | some i => if i < xs.length then some (.arr (arrRemove xs i)) else none
    | none => none
  | _ => none

/-- `replaceLast doc part v`: perform a `replace` at the final token `part`. On
    an object the member must already exist; on an array the index must be in
    range; else `none`. Frozen helper mirroring `ReplaceOperation.apply`. -/
def replaceLast (doc : Json) (part : String) (v : Json) : Option Json :=
  match doc with
  | .obj kvs => if objHas kvs part then some (.obj (objSet kvs part v)) else none
  | .arr xs =>
    match arrIndex part with
    | some i => if i < xs.length then some (.arr (arrSet xs i v)) else none
    | none => none
  | _ => none

/-- `addRoot doc v`: the RFC 6902 `add` (and `move`/`copy` target) at the *root*
    (empty pointer). Python replaces the whole document by `v` only when the
    document is an object (`isinstance(subobj, MutableMapping)`); a root `add` to
    an array or scalar raises (`TypeError` / conflict). Frozen helper. -/
def addRoot (doc : Json) (v : Json) : Option Json :=
  match doc with
  | .obj _ => some v
  | _ => none

/-- `modifyAt doc parts f`: navigate `doc` down the parent path `parts`, then
    apply the last-step editor `f` to the (parent, last-token) pair. The empty
    path has no last step and is handled by the callers' root-specific logic
    (`addRoot` for `add`; a direct value for root `replace`; a conflict for root
    `remove`/`move`/`copy`-source), so `modifyAt` treats `[]` as a conflict
    (`none`). Rebuilds the spine on the way back up, preserving object member
    positions and array indices. Frozen helper mirroring `pointer.to_last` + the
    last-step edit. -/
def modifyAt (doc : Json) (parts : List String)
    (f : Json → String → Option Json) : Option Json :=
  match parts with
  | [] => none
  | [last] => f doc last
  | p :: ps =>
    match doc with
    | .obj kvs =>
      match objGet kvs p with
      | some child =>
        match modifyAt child ps f with
        | some child' => some (.obj (objSet kvs p child'))
        | none => none
      | none => none
    | .arr xs =>
      match arrIndex p with
      | some i =>
        match xs[i]? with
        | some child =>
          match modifyAt child ps f with
          | some child' => some (.arr (arrSet xs i child'))
          | none => none
        | none => none
      | none => none
    | _ => none

end JsonPatch
-- !benchmark @end global_aux

namespace JsonPatch

-- !benchmark @start code_aux def=applyOp
-- !benchmark @end code_aux def=applyOp

def applyOp : ApplyOpSig :=
-- !benchmark @start code def=applyOp
  fun op doc =>
    match op with
    | .add path v =>
        match path with
        | [] => addRoot doc v                                    -- root add: replace whole doc (obj only)
        | _ => modifyAt doc path (fun d part => addLast d part v)
    | .remove path =>
        match path with
        | [] => none                                            -- root remove is a conflict
        | _ => modifyAt doc path (fun d part => removeLast d part)
    | .replace path v =>
        match path with
        | [] => some v                                          -- root replace: replace whole doc
        | _ => modifyAt doc path (fun d part => replaceLast d part v)
    | .test path v =>
        match resolveParts doc path with
        | some val => if val = v then some doc else none
        | none => none
    | .move from_ path =>
        match from_ with
        | [] => none                                            -- can't read the root as a source member
        | _ =>
          match resolveParts doc from_ with
          | some val =>
            -- the from = path no-op is checked only AFTER a successful source read
            if from_ = path then some doc
            else
              match modifyAt doc from_ (fun d part => removeLast d part) with
              | some doc' =>
                match path with
                | [] => addRoot doc' val                        -- target root: replace whole doc
                | _ => modifyAt doc' path (fun d part => addLast d part val)
              | none => none
          | none => none
    | .copy from_ path =>
        match from_ with
        | [] => none                                            -- can't read the root as a source member
        | _ =>
          match resolveParts doc from_ with
          | some val =>
            match path with
            | [] => addRoot doc val                             -- target root: replace whole doc
            | _ => modifyAt doc path (fun d part => addLast d part val)
          | none => none
-- !benchmark @end code def=applyOp

-- !benchmark @start code_aux def=apply
-- !benchmark @end code_aux def=apply

def apply : ApplySig :=
-- !benchmark @start code def=apply
  fun ops doc =>
    match ops with
    | [] => some doc
    | op :: rest =>
      match applyOp op doc with
      | some doc' => apply rest doc'
      | none => none
-- !benchmark @end code def=apply

end JsonPatch
