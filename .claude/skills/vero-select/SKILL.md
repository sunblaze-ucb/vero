---
name: vero-select
description: Use after human review of vero-discover output to compute dependency closure of selected items, plan Lean file layout, and determine translation order. Produces curation/selection.md and curation/selection_plan.json.
allowed-tools: Read, Write, Bash, Grep, Glob
---

# VCG Selection: Dependency Closure and Translation Planning

Read human-annotated discovery markdowns, compute the dependency closure
of selected items, plan the Lean file layout, and determine the
layer-by-layer translation order.

## When to use

- After human review of `curation/discovery/*.md` (items checked/unchecked)
- To compute what must be translated based on selections + dependencies
- To plan the Lean output directory structure and translation order

## Input

Human-annotated discovery files at `curation/discovery/*.md` where each item line reads:

- `- [x] category=<api|api_helper|spec|spec_helper|type|test> <item>` — included, with curator-confirmed category
- `- [ ] category=<…> <item>` — excluded from the benchmark

The category was suggested by `vero-discover` and confirmed (or overridden) by the curator during review.

## Step 1: Parse selections

For each discovery file (prefer `discovery_report.json` — same data, structured):

1. Extract every checked item as `(item, category)`.
2. Extract the dependency list attached to each item.
3. Build a dependency graph: `item → [dependency names]`.

## Step 2: Compute dependency closure

Starting from the set of checked items, close under dependencies:

```
closure = dict((item, category) for (item, category) in checked)
worklist = list(checked)
while worklist:
    item = worklist.pop()
    for dep in dependencies(item):
        if dep not in closure:
            # Inherit a default category for auto-pulled items:
            #   - A type dependency  → category=type
            #   - A spec's bare-name  → category=spec_helper
            #   - An API's call-dep   → category=api_helper  (flagged — see below)
            closure[dep] = infer_category(item, dep)
            worklist.append(dep)
```

### Closure warnings — two kinds

**Kind 1: auto-included items.** The closure pulled in an item the curator didn't check.

```markdown
- `funcA` (checked, category=api) depends on `TypeB` (NOT checked) — **pulled in as category=type**
  - From: `src--module1.dfy.md`
  - Reason: type dependency in `funcA`'s signature
```

**Kind 2: category mismatch (hard error).** A spec references a bare-name item that isn't marked as a spec helper (or type, or API via `impl.<…>`). A spec cannot typecheck against a name that won't be curated.

```markdown
- Spec `push_pop_roundtrip` (category=spec) references bare name `toSeq` — **mismatch**
  - Problem: `toSeq` is marked category=api_helper, which by default is not curated.
  - Fix one of:
    - (a) Promote `toSeq` to category=spec_helper (curator provides the body).
    - (b) Rewrite the spec to reference `impl.<pkg>.toSeq` and promote `toSeq` to category=api.
    - (c) Drop the spec.
```

Spec-helper **auto-promotion**. If `closure` would pull a bare-name spec dependency in with a weaker category (api_helper, or missing), silently bump it to `category=spec_helper` and emit a Kind-1 warning. This is the mechanism that prevents a spec from being under-scoped into an un-typechecking state.

The curator can then either:
- Accept the auto-promotion (leave as-is).
- Override by explicitly categorizing the dependency differently.
- Uncheck the spec to drop the whole chain.

## Step 2b: Scope-warning check against old curation

If a sibling `benchmarks/<name>_old/` exists, compute two counts from the *current* closure and two from the old tree:

| Metric | Current closure | Old tree |
|---|---|---|
| API count | count of `category=api` in closure | count old implementation tasks / code slots in the old tree |
| Spec count | count of `category=spec` in closure | count old proof/spec obligations in the old tree |

If either current count is lower than the old count, emit a **scope warning** as the first paragraph of `selection.md`:

```markdown
> ⚠ **Scope warning.** Current closure has N APIs and M specs. The pre-existing
> `benchmarks/<name>_old/` has N' APIs and M' specs. If N < N' or M < M', the
> curator is probably under-scoping. Review and widen the checkboxes before
> proceeding.
```

Do not silently proceed — surface the discrepancy by kind so the curator knows whether APIs, Specs, or both are short.

## Step 3: Layer assignment

Assign each item in the closure to a translation layer:

| Layer | Contents | Rule |
|-------|----------|------|
| 0 | Types with no type dependencies | Foundation types |
| 1 | Types depending on Layer 0 types | Compound types |
| 2 | Spec helpers + API helpers depending only on Layer 0–1 types | Curator-given vocabulary |
| 3 | APIs depending only on earlier layers | Implementation obligations |
| 4+ | APIs depending on earlier APIs | Composition |
| S | Specs (reference items in any earlier layer; Spec files are independent of each other) | Proof obligations |
| T | Tests | `#guard` blocks |

**Rules:**
- Types → Spec/API helpers → APIs → Specs → Tests.
- Within the same layer, items are independent and can be translated in parallel.
- A `category=spec` item always lands in Layer S, regardless of dep depth.
- A `category=spec_helper` item lands in Layer 2 alongside other spec-helpers even if it depends on a type — the goal is that `Spec/<Module>.lean` can import the helpers directly via `Impl/<Module>.lean` without pulling in the full API chain.

## Step 4: Plan Lean File Layout

Map source files to Lean files, mirroring the source directory structure:

| Source file | Lean file | Namespace |
|-------------|-----------|-----------|
| `src/tree.dfy` | `ProjectName/Tree.lean` | `ProjectName.Tree` |
| `src/merkle.dfy` | `ProjectName/Merkle.lean` | `ProjectName.Merkle` |
| ... | ... | ... |

Add spec and test files:

| Purpose | Lean file | Depends on |
|---------|-----------|------------|
| Spec for Tree | `ProjectName/Spec/Tree.lean` | `ProjectName/Tree.lean` |
| Tests | `ProjectName/Test.lean` | All API files |

## Step 5: Estimate Metrics

For each planned Lean file, estimate:

| File | Items | code slots (est.) | spec obligations (est.) | opaque (est.) | axiom (est.) | Notes |
|------|------:|-----------------:|-----------------------:|-------------:|------------:|-------|
| `Tree.lean` | 5 types | 0 | 0 | 0 | 0 | All types, fully defined |
| `Merkle.lean` | 5 fns | 5 | 0 | 0 | 0 | Complex bodies become API slots |
| `Spec/Tree.lean` | 11 thms | 0 | 11 | 0 | 0 | Frozen spec obligations |
| ... | ... | ... | ... | ... | ... |

Estimation rules:
- Types → 0 code slots (types are always fully defined)
- `body: given` → 0 code slots
- `category=api` with non-opaque body → 1 code slot per function
- `body: opaque` → 1 opaque per function, + N axioms for proved properties
- Each selected theorem/lemma → 1 spec obligation
- Each function with `ensures` → 1 companion spec def (spec task)

### Companion Def Pairs

Identify functions that need companion spec definitions. A companion pair
consists of:
1. **Function** — `def f := <translated reference impl>` inside a `code` marker (implementation task after pre-agent materialization)
2. **Spec def** — `def f_spec : Prop := <property>` (body given — IS the specification)
3. **Downstream proof task** — generated later from the spec def; translate does not emit `Proof/`

These arise from:
- Dafny functions with `ensures` clauses
- Verus `fn` with `ensures` (generates companion theorem)
- Any function whose correctness is stated as a separate lemma

Mark companion pairs in the metrics — they generate one code slot and
one spec obligation in curation; proof tasks are materialized
downstream from the spec obligation.

## Output: `curation/selection.md`

```markdown
# Selection Report: {project_name}

## Selection Summary

| Category | Selected | Closure-added | Total | Skipped |
|----------|--------:|-------------:|------:|--------:|
| Types | N | N | N | N |
| Spec functions | N | N | N | N |
| Exec functions | N | N | N | N |
| Predicates | N | N | N | N |
| Theorems | N | N | N | N |
| Axioms | N | N | N | N |
| Tests | N | N | N | N |
| **Total** | **N** | **N** | **N** | **N** |

## Closure Warnings

- `itemA` depends on `itemB` (not selected) — pulled into closure
  - Source: `path/to/file`
  - Reason: {type dep | call dep | proof dep}

## Translation Layers

### Layer 0: Foundation Types
| Item | Source | Lean file | Notes |
|------|--------|-----------|-------|
| `Tree` | `tree.dfy` | `Project/Tree.lean` | 2 constructors |
| ... | ... | ... | ... |

### Layer 1: Compound Types
...

### Layer 2: Core Functions
...

### Layer S: Specifications
| Item | Source | Lean file | Depends on |
|------|--------|-----------|------------|
| `height_leavesIn` | `tree.dfy` | `Project/Spec/Tree.lean` | `Tree.leavesIn` |
| ... | ... | ... | ... |

### Layer T: Tests
| Item | Source | Lean file | Tests |
|------|--------|-----------|-------|
| `test_deposit` | `RunDeposit.dfy` | `Project/Test.lean` | `deposit`, `getDepositRoot` |

## Lean File Layout

```
{ProjectName}/
├── {ProjectName}.lean          (root import hub)
├── {ProjectName}/
│   ├── Tree.lean               (Layer 0)
│   ├── Merkle.lean             (Layer 2)
│   ├── Contract.lean           (Layer 3)
│   ├── Spec/
│   │   ├── Tree.lean           (Layer S)
│   │   ├── Merkle.lean         (Layer S)
│   │   └── Contract.lean       (Layer S)
│   └── Test.lean               (Layer T)
├── lakefile.toml
└── lean-toolchain
```

## Estimated Metrics

| File | Items | sorry (est.) | opaque | axiom | Lines (est.) |
|------|------:|------------:|-------:|------:|------------:|
| ... | ... | ... | ... | ... | ... |
| **Total** | **N** | **N** | **N** | **N** | **N** |

## Human Review Notes

[Reviewer adds notes, adjustments, approval here]
```

## Machine-Readable Output: `curation/selection_plan.json`

Also write a JSON file with the structured selection plan:

```json
{
  "selected_items": [
    {
      "name": "Stack",
      "qualified_name": "Stack",
      "category": "type",
      "visibility": "public",
      "source_file": "Stack.dfy",
      "source_line": 3,
      "checked": true,
      "closure_added": false,
      "lean_file": "DummyDafny/Impl/Stack.lean",
      "lean_name": "Stack",
      "layer": 0
    },
    {
      "name": "push",
      "qualified_name": "push",
      "category": "api",
      "visibility": "public",
      "source_file": "Stack.dfy",
      "source_line": 8,
      "checked": true,
      "closure_added": false,
      "lean_file": "DummyDafny/Impl/Stack.lean",
      "lean_name": "push",
      "layer": 3
    },
    {
      "name": "toSeq",
      "qualified_name": "toSeq",
      "category": "spec_helper",
      "visibility": "internal",
      "source_file": "Stack.dfy",
      "source_line": 22,
      "checked": false,
      "closure_added": true,
      "closure_promoted_from": "api_helper",
      "lean_file": "DummyDafny/Impl/Stack.lean",
      "lean_name": "toSeq",
      "layer": 2
    },
    {
      "name": "push_pop_roundtrip",
      "qualified_name": "push_pop_roundtrip",
      "category": "spec",
      "visibility": "public",
      "source_file": "StackSpec.dfy",
      "source_line": 5,
      "checked": true,
      "closure_added": false,
      "lean_file": "DummyDafny/Spec/Stack.lean",
      "lean_name": "spec_push_pop_roundtrip",
      "layer": 100
    }
  ],
  "layers": {
    "0": ["Stack"],
    "2": ["toSeq"],
    "3": ["push", "pop", "peek", "size"],
    "100": ["push_pop_roundtrip", "push_increases_size"],
    "200": ["test_main"]
  },
  "lean_files": {
    "DummyDafny/Impl/Stack.lean": ["Stack", "toSeq", "push", "pop", "peek", "size"],
    "DummyDafny/Spec/Stack.lean": ["push_pop_roundtrip", "push_increases_size"],
    "DummyDafny/Test.lean": ["test_main"]
  },
  "closure_warnings": [
    {
      "kind": "auto_included",
      "item": "toSeq",
      "reason": "spec `push_pop_roundtrip` references bare name; promoted to spec_helper"
    }
  ],
  "category_counts": {
    "api": 4,
    "api_helper": 0,
    "spec": 2,
    "spec_helper": 1,
    "type": 1,
    "test": 1
  },
  "old_benchmark_counts": {
    "present": false,
    "api": null,
    "spec": null
  }
}
```

Layer convention: 0–99 for types / helpers / APIs, 100+ for specs (Layer S), 200+ for tests (Layer T). `lean_name` is the destination Lean identifier (for spec items, prefix with `spec_` per paradigm).

## Workflow (incremental — avoid one giant Write at the end)

Read inputs and emit outputs one chunk at a time. A monolithic
"digest-everything-then-write-selection.md" plan tends to hit long
thinking stalls on repos with 15+ discovery files. Instead:

**Step 1 — Prefer `discovery_report.json` over the markdowns.**
Read `curation/discovery_report.json` first. It has the full
dependency graph in ~1/10th the tokens of the markdown set. Only read
a specific `discovery/<file>.md` when you need human-added review
notes for a borderline item. Do NOT read all 19 markdowns up-front.

**Step 2 — Parse checkboxes cheaply.**
Use a single `Bash` call with `grep "^- \[x\]" curation/discovery/*.md`
to pull out the selected-item lines (and their file-of-origin). Do
NOT Read every markdown just to find the `[x]`s.

**Step 3 — Compute closure deterministically.**
Walk the dependency graph from the selected set. This is a pure graph
computation; no thinking required.

**Step 4 — Write `selection.md` section by section.**
Do NOT compose the whole report in a single Write. Emit it in this
order, each as its own Write / Edit call:

  1. `Write` the header + `## Selection Summary` table.
  2. `Edit` to append `## Closure Warnings`.
  3. `Edit` to append `## Translation Layers` — and within it, one
     Edit per layer (Layer 0, then Layer 1, …, then Layer S, then
     Layer T). Each layer Edit keeps `selection.md` valid markdown.
  4. `Edit` to append `## Lean File Layout` (tree diagram).
  5. `Edit` to append `## Estimated Metrics`.
  6. `Edit` to append `## Human Review Notes` (empty — reviewer
     fills in).

Between edits, pause for the closure computation — emit any
surprising closure additions as a Write to the file before continuing,
so partial progress is observable to the curator even if the session
is interrupted.

**Step 5 — Emit `selection_plan.json` last.**
Only after `selection.md` is complete and self-consistent. One Write.

**Check-in rule:** before each Write/Edit, in one sentence name which
section you are about to emit. This makes stalled-in-thinking episodes
obvious to a watching human (they see "I will now emit Layer 2" and
then the next log line in ≤ 30s).

(See Step 2b above for the scope-warning rule against an existing `benchmarks/<name>_old/`.)
