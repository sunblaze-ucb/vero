---
name: vero-discover
description: Use when scanning a verified source repo (Dafny, Verus, or Coq) to classify every item and produce per-file discovery markdown for human curation. Produces curation/discovery/*.md, curation/api.md, and curation/discovery_report.json.
allowed-tools: Read, Write, Bash, Grep, Glob, Agent
---

# VCG Discovery: Source Repo Scan and Classification

Scan a verified source repository, classify every item (type, function,
predicate, theorem, test, boundary), and produce per-file discovery
markdown for human review plus a machine-readable JSON report.

## When to use

- Starting a new VCG (Verified Code Generation) translation project
- Cataloging a verified codebase before translation to Lean 4
- Producing an api.md coverage map from a Dafny, Verus, or Coq repo

## Language Detection

Detect the source language from file extensions:

| Extension | Language | Notes |
|-----------|----------|-------|
| `.dfy` | Dafny | |
| `.rs` | Verus | Confirm by checking for `verus!` macro blocks |
| `.v` | Coq | |
| `.vy` | Coq (Vernacular) | Less common |

For Rust files, grep for `verus!` or `use vstd::` to confirm Verus.
Plain Rust files without Verus annotations should be classified as
`skip` (not verified code).

## Classification Rules

Classify every top-level item into exactly one category:

| Category | Description | Lean mapping |
|----------|-------------|--------------|
| `type` | Data type, struct, enum, record | `inductive` or `structure` |
| `spec-fn` | Ghost/specification function | `def` (body given) |
| `exec-fn` | Executable function (API) | `def` with translated reference body inside a `code` marker |
| `predicate` | Boolean/propositional predicate | `def ... : Bool` or `def ... : Prop` |
| `theorem` | Lemma, theorem, proof function | `def spec_* (impl : RepoImpl) : Prop` |
| `axiom` | Axiom, assumed property, external_body property | `axiom` |
| `test` | Test function, assertion block | `#guard` block |
| `skip` | Non-verified boilerplate, build config, imports | (not translated) |

### Classification heuristics per language

**Dafny:**
- `datatype` / `class` / `newtype` / `type` → `type`
- `function` (ghost) → `spec-fn`
- `function method` → `exec-fn`
- `method` → `exec-fn`
- `predicate` → `predicate`
- `lemma` → `theorem`
- `{:axiom}` annotation → `axiom`
- `method Main()` with assertions → `test`

**Verus:**
- `struct` / `enum` (including `rspec!` wrappers) → `type`
- `spec fn` / `open spec fn` / `closed spec fn` → `spec-fn`
- `fn` with `ensures` → `exec-fn`
- `proof fn` → `theorem`
- `#[verifier::external_body]` → `axiom` (mark as boundary)
- `#[test]` / `assert!` blocks → `test`

**Coq:**
- `Inductive` / `Record` / `Structure` / `Class` → `type`
- `Definition` / `Fixpoint` / `Function` → `spec-fn`
- `Lemma` / `Theorem` / `Fact` / `Corollary` / `Remark` → `theorem`
- `Axiom` / `Parameter` / `Conjecture` → `axiom`
- `Example` / `Goal` → `test`
- `Instance` → `spec-fn` (with typeclass annotation)

## Visibility Classification

For each item, classify its visibility:

| Visibility | Meaning | Heuristic |
|-----------|---------|-----------|
| `public` | Exported, part of module API | `pub`, no underscore prefix, used by other modules |
| `internal` | Used internally, not exported | Not `pub`, but used by other items in the project |
| `private` | Helper, underscore-prefixed | `_` prefix, or only used locally within one function |

Public APIs are higher-value benchmark tasks because they define the
module's contract.

## Spec Quality Classification

For each theorem/lemma, classify its spec quality:

| Kind | Description | Example |
|------|-------------|---------|
| `functional` | Describes functional behavior (input→output relationship) | `push_pop_roundtrip` |
| `characterizing` | Independent mathematical property | `sameDN_refl`, `size_nonneg` |
| `helper` | Facilitates loop invariant or SMT proof only | Internal induction step lemma |
| `tautological` | Restates the implementation | `f_returns_what_it_returns` |

Functional and characterizing specs are high-value benchmark tasks.
Helper and tautological specs are lower-value (may still be included).

## Dependency Extraction

For each item, record its dependencies:
1. **Imports**: module/file imports that bring names into scope
2. **Type references**: types used in signatures or bodies
3. **Function calls**: functions called in the body
4. **Proof dependencies**: theorems/lemmas invoked in proofs (Coq tactics, Dafny `reveal`, Verus `proof fn` calls)

Dependencies determine translation order: items with no dependencies are
Layer 0; items depending only on Layer 0 are Layer 1; etc.

## Category (the curator's central decision)

Every item is classified into one of four categories. The category
determines how the item lands in the Lean benchmark:

| Category | What it becomes | Role |
|---|---|---|
| **API** | sig abbrev + reference implementation in `!benchmark code` marker + Bundle field + wired into `canonical` | Implementation obligation — pre-agent generation hides the curated body with `sorry` before the LLM writes its solution |
| **API helper** | (by default) nothing — the LLM invents it locally inside `code_aux`. Curator *may* opt-in: fully-defined `def` in `Impl/` with no marker, not in Bundle | A tool API implementations share; curator-given only when the curator wants to hand it to the LLM |
| **Spec** | `def spec_<name> (impl : RepoImpl) : Prop` in `Spec/<Module>.lean` | Proof obligation — the LLM must prove (or refute) this downstream |
| **Spec helper** | Fully-defined function / predicate in `Impl/` (or framework file), no marker, not in Bundle | Vocabulary referenced by bare name inside spec bodies; must be curated or the Spec file won't typecheck |

Plus the supporting roles that aren't in the four-way split: `type` (always curator-given, no marker), `test` (becomes `#guard` in `Test.lean`), `skip` (not translated).

**The source language doesn't tell you.** Dafny `function method`, Verus `spec fn` / `fn`, Coq `Definition` can each land in any of the four categories — the syntactic keyword is a weak hint, not the answer. Use these heuristics instead, in priority order:

1. **Would a library user call this by name?** Yes → API. Internal traversal the curator exposes only because the source has no private keyword → not API.
2. **Does the function appear bare (not under `impl.<…>`) in any spec body?** Yes → spec helper, it *must* be curator-given.
3. **Is the body algorithmically substantive, with multiple reasonable implementations?** Yes → good API candidate. One-line projection → not worth stubbing.
4. **Does the source declare `ensures` clauses on the function?** Yes → author expected the body to be pinned by a spec → API. No `ensures`, only called from other proofs → spec helper.
5. **Is it called only from inside other API bodies (not from specs)?** Yes → API helper; default to leaving the LLM to invent it.

When two heuristics conflict, note it in the per-item discovery markdown as a suggestion that the curator review.

**Predicates**, **types**, and **facts stated as theorems** always land as spec helpers (predicates) / types / specs respectively. A predicate can't be an API obligation unless it is intentionally selected as executable code.

## Per-File Discovery Markdown Format

Produce one file per source file at `curation/discovery/{source_path}.md`.
Replace path separators with `--` (e.g., `src/policy/chrome.rs` → `src--policy--chrome.rs.md`).

Every item line carries the **suggested category** (the curator overrides during review). Format: `- [ ] category=<api|api_helper|spec|spec_helper|type|test|skip> <item>`.

```markdown
# discovery: {source_path}

Source: `{source_path}` ({N} lines)
Language: {Dafny | Verus | Coq}
Module: {module_name}

## Types
- [ ] category=type `TypeName` — {kind}, {N constructors/fields} — maps to: `{inductive|structure|abbrev}`
  - Visibility: {public|internal|private}
  - Dependencies: {list or "none"}
  - Notes: {considerations, deriving suggestions}

## Functions
- [ ] category={api|api_helper|spec_helper} `funcName(args)` → {ReturnType} — maps to: `def`
  - Visibility: {public|internal|private}
  - Dependencies: [{list}]
  - Reason: {one line — which heuristics drove the category suggestion}
  - Notes: {annotations, ensures clauses, requires clauses}

## Predicates
- [ ] category=spec_helper `predName(args)` — maps to: `def ... : {Bool|Prop}`
  - Visibility: {public|internal|private}
  - Dependencies: [{list}]
  - Notes: {what it checks}

## Theorems / Lemmas
- [ ] category={spec|spec_helper|skip} `theoremName` — maps to: `def spec_<…> (impl : RepoImpl) : Prop`
  - Visibility: {public|internal|private}
  - Dependencies: [{list}]
  - Hypothesis: {preconditions / requires}
  - Conclusion: {postcondition / ensures}
  - Reason: {one line — why this category}

## Tests
- [ ] category=test `testName` — maps to: `#guard` block
  - Values: {input/output pairs or assertion checks}

## External Boundaries
- [ ] category=api_helper `boundaryName` — maps to: `opaque`
  - Properties proved in source: {list → become axioms in Lean}

## Notes
[Human adds review notes here]
```

### Rules for the discovery markdown

1. Every top-level item appears exactly once.
2. The suggested category is the agent's best guess; the curator overrides during `vero-select` review.
3. `skip` items are omitted entirely (don't clutter the review).
4. Include line numbers or ranges where practical for cross-reference.
5. Group by source kind (Types / Functions / Predicates / …), not by category — the category is a per-item annotation.
6. Note any `TODO`, `FIXME`, `assume`, or `admit` in the source.

## Machine-Readable Output: `curation/discovery_report.json`

After producing the markdown files, also write a JSON report at
`curation/discovery_report.json` with this structure. The key field is
`suggested_category` — one of the four benchmark categories plus the
supporting roles (`type`, `test`, `skip`).

```json
{
  "source_language": "dafny",
  "source_dir": "/path/to/source",
  "commit_hash": "abc123",
  "repo_url": "https://github.com/...",
  "items": [
    {
      "name": "Stack",
      "qualified_name": "Stack",
      "suggested_category": "type",
      "visibility": "public",
      "source_file": "Stack.dfy",
      "source_line": 3,
      "signature_summary": "datatype Stack<T> = Empty | Cons(top: T, rest: Stack<T>)",
      "dependencies": [],
      "reason": "datatype declaration; always curator-given",
      "notes": "Generic binary stack, 2 constructors"
    },
    {
      "name": "push",
      "qualified_name": "push",
      "suggested_category": "api",
      "visibility": "public",
      "source_file": "Stack.dfy",
      "source_line": 8,
      "signature_summary": "function method push<T>(s: Stack<T>, v: T) : Stack<T>",
      "dependencies": ["Stack"],
      "reason": "user-facing library entry; has ensures clauses in source",
      "notes": ""
    },
    {
      "name": "toSeq",
      "qualified_name": "toSeq",
      "suggested_category": "spec_helper",
      "visibility": "internal",
      "source_file": "Stack.dfy",
      "source_line": 22,
      "signature_summary": "ghost function toSeq<T>(s: Stack<T>) : seq<T>",
      "dependencies": ["Stack"],
      "reason": "ghost function used only in ensures clauses of other fns; referenced by bare name in specs",
      "notes": ""
    },
    {
      "name": "push_pop_roundtrip",
      "qualified_name": "push_pop_roundtrip",
      "suggested_category": "spec",
      "visibility": "public",
      "source_file": "StackSpec.dfy",
      "source_line": 5,
      "signature_summary": "lemma push_pop_roundtrip<T>(s: Stack<T>, v: T) ensures pop(push(s, v)) == s",
      "dependencies": ["Stack", "push", "pop"],
      "reason": "characterizing lemma about push/pop; becomes def spec_* proof obligation",
      "notes": "Round-trip property"
    }
  ],
  "file_summaries": {
    "Stack.dfy": {"lines": 50, "types": 1, "functions": 5, "theorems": 0},
    "StackSpec.dfy": {"lines": 40, "types": 0, "functions": 0, "theorems": 4}
  }
}
```

The `suggested_category` is the agent's best call per the heuristic rubric; the curator overrides it in `vero-select` review. The `reason` field (one sentence) is mandatory and must cite at least one heuristic — it's how the curator audits the suggestion.

This JSON is consumed by `vero-select` and `vero-plan`; both expect the four-category vocabulary.

## Assembled Catalog: `curation/api.md`

After producing per-file discovery markdowns, assemble `curation/api.md`:

```markdown
# API Catalog: {project_name}

Source: {repo_url} ({commit_hash})
Language: {language}
Total lines: {N}

## Architecture

{ASCII dependency graph of modules}

## Summary

| File | Types | Spec Fns | Exec Fns | Predicates | Theorems | Axioms | Tests |
|------|------:|--------:|---------:|----------:|---------:|-------:|------:|
| ... | ... | ... | ... | ... | ... | ... | ... |
| **Total** | **N** | **N** | **N** | **N** | **N** | **N** | **N** |

## Per-File Catalogs

[Links to each curation/discovery/{path}.md]
```

## Sub-Agent Strategy (Large Repos)

For repos with more than ~20 source files, use parallel sub-agents:

1. **Group files by directory** — max 10 source files per group
2. **Launch one sub-agent per group** — each produces discovery markdowns
   for its files
3. **Coordinator** merges results into `curation/api.md`

Each sub-agent receives:
- The language-specific classification skill (vero-source-{lang})
- Its assigned file list
- The output directory path

## Workflow (incremental — one file at a time)

**Do not** read all source files up front and then write all markdowns
at the end. A "read 19 files, think, then Write 19 times" flow is
what causes multi-minute thinking stalls and loses everything on
interrupt. Instead, close each file's loop before opening the next
one:

```
1. Detect language (scan extensions + grep for markers)
2. List all source files (exclude tests/, build/, vendor/)
3. FOR EACH source file, one at a time (NOT in parallel):
   a. Read the source file
   b. Classify its top-level items (category, visibility, spec_kind,
      body_disposition)
   c. Extract dependencies
   d. Write curation/discovery/<path>.md IMMEDIATELY — do not batch
      writes across files
   e. If discovery_report.json exists, Edit to append this file's
      items; otherwise Write it fresh with just these items. Either
      way the JSON stays valid after each file so the run is
      restartable.
4. After the per-file loop, assemble curation/api.md with the summary
   table (this is a small synthesis pass, one Write).
5. Report: total items found, items per category.
```

**Idempotency.** If `curation/discovery/<path>.md` already exists and
the source file's mtime is older than the markdown, skip the Read +
Write pair unless `--force`. Do NOT blindly re-read all 19
already-analyzed files because of the Write guard — that's wasted
turns.

**Check-in rule.** Before each file's Write, announce in one
sentence: "Now processing `src/foo.dfy` — 3 types, 5 fns." Keeps
progress observable.

**Batch size.** If you must batch (for Agent sub-agents), group at
most 5 files per sub-agent. Never dispatch a single 19-file batch.

## Output Directory Structure

```
curation/
├── discovery/
│   ├── src--module1.dfy.md
│   ├── src--module2.dfy.md
│   └── ...
├── api.md
└── discovery_report.json
```
