---
name: vero-source-python
description: Load BEFORE translating Python source to Lean 4. Provides Python-specific classification rules, type mappings, stdlib-opaque modeling guidance, and patterns for mapping Python constructs into the ratified bundle paradigm (Impl/ + Spec/ + Bundle + Harness). Pair with vero-discover, vero-plan, vero-translate, vero-spec-write, and vero-python-pitfalls.
---

# VCG Source — Python

Python source has no built-in spec language. The `python_spec` workflow translates Python to Lean (this skill + vero-translate), then `spec_write` (separate skill) authors the specifications. This skill covers the discover → plan → translate stages.

**Reference the canonical shape** at `reference/BankLedger/`. Every emitted file mirrors that layout.

## Classification (vero-discover)

Python items map to:

| Python construct | Lean classification |
|---|---|
| top-level `def` or `class` method, no leading underscore | API (kind=`api`) |
| `def _foo` or `def __foo` | API helper (kind=`api_helper`); not exposed in apis[] sig list |
| `class Foo:` (data) | Type (`structure` in Lean) |
| `class Foo:` (mixin / pure-method) | Type + companion API methods |
| module-level constant | curator decides — usually inlined in Impl, occasionally a `def` |
| docstring with `>>>` doctests | Test candidate — emit as `#guard` in Test.lean |
| `import math`, `import sys`, ... | External lib — model as `opaque` (see below) |

If the source repo has typing annotations, prefer them as ground truth. Without annotations, infer from usage and flag with `@review human`.

## Type mappings

| Python type | Lean target |
|---|---|
| `int` | `Int` (or `Nat` if always non-negative — verify and annotate) |
| `bool` | `Bool` |
| `float` | `Float` (with `@review human: floating-point semantics differ`) |
| `str` | `String` |
| `bytes` | `ByteArray` |
| `list[T]` | `List T` |
| `tuple[T, U]` | `T × U` |
| `dict[K, V]` | `AssocList K V` (or `Std.HashMap K V` if order doesn't matter and `[Hashable K]` is available) |
| `set[T]` | `List T` (with curator-given `nodup`-style invariant in spec_helper) — there's no canonical `Set T` in core Lean 4 |
| `Optional[T]` / `T | None` | `Option T` |
| `Iterable[T]` | `List T` (eager); flag if streaming semantics matter |
| user `class Foo` | `structure Foo where` |

## External-library handling

Python's standard library and ecosystem have no Lean equivalents in many cases. Pattern:

```lean
-- !benchmark @start global_aux
/-- Opaque model of `math.sqrt`. The benchmark does not constrain the
    return value beyond non-negativity; downstream specs encode the
    minimum needed (e.g., square root of n is ≤ n).

    @review human: confirm this opaque model is sufficient for the
    intended specs. -/
opaque sqrt : Int → Int

axiom sqrt_nonneg : ∀ n, 0 ≤ sqrt n  -- only if a spec actually needs it
-- !benchmark @end global_aux
```

Rules:
- **Always model with `opaque`.** Never rely on Mathlib's `Real.sqrt` etc. — the benchmark must be self-contained on a Mathlib-free toolchain unless the curator decides otherwise.
- **`axiom` only when a spec demands it.** Prefer `opaque` alone. Each axiom must be added to `manifest.json::trusted_axioms` (the grader's allowlist).
- **`@review human` annotation** every external-lib model, naming the lib + the assumption being made.
- **Preferred replacements** (use these *only* when the curator confirms they're available on the target toolchain):
  - `collections.Counter` → custom `AssocList Key Nat`-backed structure
  - `functools.reduce` → `List.foldl`
  - `itertools.combinations` → custom recursive helper, flag complexity
  - `re` (regex) → `lean-regex` library OR opaque + axiom; usually opaque

## Module / file mapping

One Python file → one Impl module + one Spec module + one manifest entry:

```
src/foo.py
  ↓
<Project>/Impl/Foo.lean    -- types + APIs, with translated reference impls in code markers
<Project>/Spec/Foo.lean    -- empty until spec_write fills
manifest.json -> packages[0].modules[?] = { name=Foo, impl=..., spec=..., apis=[...] }
```

Multi-file Python packages (`pkg/__init__.py`, `pkg/sub.py`) flatten by moduling: `<Project>/Impl/Pkg.lean`, `<Project>/Impl/PkgSub.lean`. Document the flattening in `curation/notes.md`.

## Translate stage shape (per file)

```lean
-- File header / imports
-- !benchmark @start imports
import <Project>.Bundle
-- !benchmark @end imports

-- Module docstring (curator-written, frozen)
/-! # <Project>.Impl.<ModuleName>

<one-paragraph summary of the module's purpose, ported from the
Python module docstring + reading the source>
-/

namespace <Project>

-- Types (curator-given, frozen — no markers around individual types)
structure Foo where ...
deriving Repr, BEq

-- Sig abbrevs (one per API, listed in manifest)
abbrev BarSig := Int → Foo → Foo
abbrev BazSig := Foo → Bool

-- Opaque external models + their axioms (if needed)
-- !benchmark @start global_aux
opaque sqrt : Int → Int
-- !benchmark @end global_aux

-- APIs — one !benchmark code pair per api; body is the translated reference implementation
-- !benchmark @start code_aux def=bar
-- !benchmark @end code_aux def=bar
-- !benchmark @start code def=bar
def <Project>.bar : <Project>.BarSig :=
  -- translated Python body, not `sorry`
  ...
-- !benchmark @end code def=bar

end <Project>
```

API helpers (Python `_foo`) get the same `code` + `code_aux` marker pair but without an `abbrev <Foo>Sig` — manifest lists them under `api_helpers[]` (kind=`api_helper`), and validator skips the sig-abbrev requirement.

## Tests (`Test.lean`)

For every doctest in the Python source, emit a `#guard`:

```python
def factor(n: int) -> int:
    """
    >>> factor(9)
    3
    """
    ...
```

→

```lean
/-- doctest: factor(9) -> 3 -/
#guard <Project>.factor 9 == 3
```

If the Python source has no doctests, ask the curator (via `@review human`) what `#guard`s to add. Do not invent expected outputs that are not grounded in the Python source, documentation, or a curator-approved oracle.

## Plan stage shape

The plan emitted by `vero-plan` has the same shape as for Dafny/Verus/Coq — `api_namespace`, `packages`, `modules`, `types`, `apis` with `lean_name` + `sig_abbrev` + `lean_type`. The difference: `specs[]` may be empty (you're not mining them from source) and the `ref_impls[]` come from the Python translation, not a verified reference.

## Verify before declaring translate done

1. `lake build` succeeds.
2. Every `apis[]` entry in `manifest.json` has its `abbrev <Sig>` + `def <Project>.<name>` with a real translated reference body inside the `code` marker in the right Impl file.
3. Every external lib used by the source has an `opaque` (and optional `axiom`) in `global_aux`, with a `@review human` annotation.
4. `Spec/<Module>.lean` files exist as scaffolds — `import <Project>.Harness` + module docstring + `DO NOT MODIFY` notice; they will be filled by `spec_write`.
5. `Test.lean` has `#guard`s for every doctest found in source (or `@review human` notes for the curator if absent).

## What NOT to do

- Don't leave API bodies as `sorry` in the curated benchmark. The body inside the `code` marker is the curator's translated reference implementation; pre-agent generation replaces it with `sorry` before the benchmark is shown to the solving agent.
- Don't write specs in this stage. That's `spec_write`.
- Don't emit `Mathlib` imports unless the curator's `human_guidance.md` explicitly authorizes it.
- Don't introduce `instance` blocks for `DecidableEq`/`BEq`/`Hashable` on opaque types — the `opaque` declaration deliberately blocks decidable equality.
- Don't translate Python `print` / `input` / file I/O. Skip those APIs and add a `@review human` note explaining the omission.
