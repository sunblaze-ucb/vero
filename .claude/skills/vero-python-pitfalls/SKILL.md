---
name: vero-python-pitfalls
description: Load BEFORE translating any Python item to Lean 4 to avoid known Python→Lean pitfalls. Pair with vero-source-python and vero-lean-pitfalls.
---

# Python → Lean 4 — Known Pitfalls

## Benchmark-quality baseline

The Lean benchmark is allowed to be smaller than the Python repo, but it
must not silently change the selected APIs' observable semantics. Before
compressing scaffold/context, confirm that the LLM still has enough
information to reconstruct:

- success and failure paths;
- mutation/aliasing effects that become input-output relations in Lean;
- boundary behavior for empty inputs, malformed inputs, overflow, and
  exceptional cases;
- cross-API laws such as encode/decode or push/pop round trips.

If a source behavior is intentionally omitted, record it as a curation
decision instead of leaving a weak spec that makes the omission invisible.

## Integer division

Python `a // b` is **floor** division (rounds toward −∞). Lean's `Int.div`/`/` is **truncated** (rounds toward 0). They differ for negatives.

| Python | Lean (preserve floor) |
|---|---|
| `a // b` | `Int.fdiv a b` |
| `a % b` | `Int.fmod a b` |

If the Python source only ever uses non-negative operands, `Int.div` is fine — but document the assumption.

## `range(...)` semantics

Python `range(a, b)` is `[a, a+1, ..., b-1]`. Use `List.range'` (start, length) — *not* `List.range` (which is `[0, ..., n-1]`).

```python
range(2, 5)   # [2, 3, 4]
```

→

```lean
List.range' 2 3   -- [2, 3, 4]; length = b - a
```

For descending or step-N ranges, write a recursive helper.

## Mutability + aliasing

Python lists / dicts are mutable. Lean has no in-place mutation in the pure subset. The curator-given translation:
- `lst.append(x)` → `lst ++ [x]` (new list)
- `dct[k] = v` → `dct.insert k v` returning a new map
- Python's reliance on identity (`lst is other_lst`) cannot be expressed; flag with `@review human`.

If the Python code relies on mutating a parameter and reading the mutation in the caller, the spec almost certainly needs reformulation as input → output. Discuss with the curator.

For buffer-writing APIs, do not replace "writes prefix and preserves
suffix" with "returns some new list" unless the spec explicitly captures
the old buffer, written length, prefix, suffix, and failure unchanged
behavior. This is the same failure mode as Json's `SerializeInto`
contract drift.

## `None` vs `Option`

Python's `None` is the only inhabitant of `NoneType`. Lean's `none : Option α` requires the type `α` to be inferred or annotated. Translation:

```python
def lookup(k: int) -> int | None:
    return self.dict.get(k)
```

→

```lean
def lookup (k : Int) (s : State) : Option Int := s.dict.find? k
```

Avoid `Option Unit` for "side-effect succeeded?" — use `Bool` or a dedicated `Result` enum.

## Float

Lean's `Float` is IEEE 754 double, same as Python's. **But**: `Float` does not have decidable equality and arithmetic isn't pure (NaN, ±0). Heavily prefer `Int` if the Python contract allows integer reasoning.

If a spec must talk about `Float`, name the floating-point assumption explicitly in `spec_helper_*` and flag with `@review human`.

## String iteration

Python `for c in s` iterates Unicode code points. Lean's `String` API has `String.toList : String → List Char` — use that, not `String.length` for character counts (which counts UTF-8 bytes in some configurations).

## `dict` ordering

Python 3.7+ guarantees insertion order on `dict`. Lean's `Std.HashMap` does not. If insertion order is observable in the spec, translate to `AssocList Key Value` (preserves order, less efficient — but specs care more).

## Recursion depth

Python tolerates moderate recursion via tail-call-stack tricks; Lean prefers `partial def` or a structurally-decreasing recursive definition. Long-running iterative algorithms in Python often need refactoring as `Nat.rec` / `List.foldl` in Lean.

## `print` / `input` / file I/O

These APIs have no place in the benchmark. Skip them and add an `@review human` annotation in the manifest noting the omission. If a spec actually depends on a side effect (rare in benchmark code), discuss with the curator.

## Exceptions

Python `raise ValueError(...)` becomes one of:
- `Option α` returning `none` on the error path,
- `Except String α` returning `Except.error msg`,
- `if not_valid then panic! "msg" else …` (avoid — `panic!` is unsafe),

Always prefer `Option` / `Except` for total functions. If the function signature already has a clear "failure" value (e.g., negative for "not found"), reuse that rather than introducing a new wrapper.

Specs must constrain both sides when the source distinguishes success
and failure. A success-only postcondition can be vacuous for an
implementation that rejects too often.

## Built-in `len`

Python `len(lst)` is `lst.length` in Lean for `List` / `String`. For `dict`, the equivalent depends on the chosen Lean type:

| Python | `AssocList` | `Std.HashMap` |
|---|---|---|
| `len(d)` | `d.keys.length` | `d.size` |

## Mutable defaults

Python's `def f(x=[])` mutable-default pitfall does not exist in Lean (default args are re-evaluated). Don't translate guard logic that exists *only* to defend against this.

## Class methods + `self`

Python `class Foo: def bar(self, x): …` translates to a free function `def Foo.bar (self : Foo) (x : T) : U`, with `self` as the first parameter. Manifest API name is `Foo.bar` (or `bar` if the class is the package's primary type).

## `__init__` / construction

Python `__init__` is the constructor. Lean's `structure Foo` already gives you `Foo.mk` (anonymous constructor). Translate `__init__` body that does work beyond field-assignment as a separate `def Foo.init (...) : Foo`.

## Decorators

Most decorators (`@property`, `@cached_property`, `@staticmethod`, `@classmethod`) lose meaning in Lean. Translate the underlying function and document with `@review human` if the decorator semantics matter.

## Generators

`def gen(): yield x; yield y` translates to `def gen : List T := [x, y]` for finite generators. Infinite generators need a different model (lazy list, stream) — flag with `@review human`.

## Typing module

`typing.List`, `typing.Dict`, etc. are erased — use the Lean equivalent of the parameterized type. `typing.Any` is a curator-level red flag — usually means the function body has multiple shapes; translate each shape as a separate Lean function or use a tagged union.

## `*args` / `**kwargs`

Variadic args translate to a `List T` parameter. Keyword args translate to explicit named parameters in Lean. If the Python signature is genuinely dynamic, flag as `@review human` — the spec probably needs a different shape.
