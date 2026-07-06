# Curation Pipeline Artifact Schemas

Each stage of the curation pipeline consumes and produces named JSON
artifacts on disk. This document pins down their shapes so the
pipeline code, the curation skills, the validator, and downstream
consumers share one contract.

Status: in progress. The `validate` artifact is proposed, the others
are in use today (`init`, `discover`, `select`, `plan`) but had informal
schemas. This doc is the authoritative shape going forward.

## Artifact index

| File | Producer | Consumers | Purpose |
|---|---|---|---|
| `.vero/config.json` | `init` | all stages | Workflow + language + project identity + source commit pin |
| `.vero/stage_state.json` | all stages | all stages + CLI | Which stages are pending / in-progress / done |
| `.vero/source_index.json` | `source_index` | `discover`, `select`, `plan`, `validate`, humans | No-LLM source-wide entity registry |
| `.vero/discover.json` | `discover` | `select`, humans | Catalog of upstream entities |
| `.vero/select.json` | `select` | `plan`, humans | Chosen entities + proposed module grouping |
| `.vero/plan.json` | `plan` | `translate`, `validate`, humans | Authoritative translation plan (API / spec / module naming, types, ref impls, tests) |
| `benchmark/<Project>/manifest.json` | `translate` | `validate`, `pre_agent_gen`, downstream tooling | Canonical benchmark metadata (packages, modules, APIs, specs) |
| `.vero/validate.json` | `validate` | CLI + humans | Rule-based + LLM findings |

All `.vero/*.json` files are under the workspace directory
(`<output_dir>/.vero/`). `manifest.json` lives inside the curated
Lean tree at `<output_dir>/benchmark/<Project>/manifest.json`.

All artifacts are UTF-8 JSON, pretty-printed (two-space indent).
Extraction code must tolerate added fields (forward-compat).

## Conventions

- Paths are relative to the repo root where the consuming tool
  considers "the benchmark" (e.g. paths in `manifest.json` are
  relative to `benchmark/<Project>/`).
- Timestamps are ISO-8601 UTC strings (e.g. `"2026-04-19T02:15:00Z"`).
- Any string field may be `null` if the pipeline does not yet know the
  value. Consumers should not treat `null` as absent; they should
  treat it as "known unknown".
- Missing optional fields are absent (not `null`); consumers default
  them.

## `config.json`

### Purpose

Per-workspace configuration pinned at `init`. Identifies the upstream
source + the chosen Lean target + the workflow variant.

### Location

`<output_dir>/.vero/config.json`

### Producer

`init` stage.

### Consumers

Every later stage reads this. CLI commands (`status`, `extract`) also
consume it.

### Schema

```json
{
  "version": 1,
  "workflow": "verified_to_lean | python_spec",
  "source": {
    "language": "dafny | verus | coq | python",
    "path": "<absolute path to upstream source>",
    "repo_url": "<upstream git URL or null>",
    "commit_hash": "<upstream commit SHA or null>",
    "repo_relpath": "<subpath within upstream repo or null>"
  },
  "project_name": "BankLedger",
  "benchmark_id": "bank_ledger_reference",
  "lean_version": "4.29.1",
  "curation": {
    "curator": null,
    "started_at": "2026-04-19T02:15:00Z"
  }
}
```

### Notes

- `workflow` is the only axis that changes which stages run. `python_spec` adds a `spec_write` stage after `translate`.
- `source.repo_url` + `source.commit_hash` + `source.repo_relpath` are forwarded to `manifest.json` at `translate` time.
- `project_name` is the Lean project name (`<Project>.lean` root hub) AND the root package name per Convention #1.
- `benchmark_id` is a snake_case identifier used as a primary key across the benchmark registry.

## `stage_state.json`

### Purpose

Tracks the per-stage status so the CLI can report progress, resume
from a given stage, and enforce stage ordering.

### Location

`<output_dir>/.vero/stage_state.json`

### Producer

Written by every stage as it transitions state. Also read back by every stage (to check prerequisites).

### Consumers

CLI (`run`, `status`), all stage runners.

### Schema

```json
{
  "version": 1,
  "stages": {
    "init": {
      "status": "done",
      "started_at": "2026-04-19T02:15:00Z",
      "finished_at": "2026-04-19T02:15:03Z",
      "artifact": ".vero/config.json",
      "human_review_required": false,
      "human_review_done": null
    },
    "discover": {
      "status": "done",
      "started_at": "2026-04-19T02:15:05Z",
      "finished_at": "2026-04-19T02:22:11Z",
      "artifact": ".vero/discover.json",
      "human_review_required": true,
      "human_review_done": "2026-04-19T02:30:00Z"
    },
    "select":    { "status": "in_progress", "started_at": "...", "finished_at": null, "artifact": ".vero/select.json", "human_review_required": true, "human_review_done": null },
    "plan":      { "status": "pending", ... },
    "translate": { "status": "pending", ... },
    "validate":  { "status": "pending", ... },
    "spec_write": { "status": "not_applicable", ... }
  }
}
```

### Notes

- `status` is one of: `pending`, `in_progress`, `done`, `failed`, `not_applicable`.
- `not_applicable` is used for workflow-gated stages that this config does not run (e.g. `spec_write` under `verified_to_lean`).
- `artifact` is the primary output the stage writes. Used for "did this stage actually produce its output?" checks.
- Human-review gates: `human_review_required` is read from the stage definition; `human_review_done` flips to a timestamp when the human confirms (via CLI flag or by re-running).

## `discover.json`

### Purpose

A catalog of upstream entities (types, functions, specs, theorems,
tests) extracted from the source repo. This is the universe from
which `select` picks.

### Location

`<output_dir>/.vero/discover.json`

### Producer

`discover` stage (LLM agent). Human may edit per-entity checkmarks in
sibling Markdown files `<output_dir>/discovery/*.md`; the agent
re-reads these on resume.

### Consumers

`select` stage.

### Schema

```json
{
  "version": 1,
  "source_path": "<absolute path>",
  "source_language": "verus",
  "entities": [
    {
      "id": "createAccount",
      "kind": "fn | type | spec | proof | test | axiom | opaque",
      "upstream_name": "create_account",
      "file": "src/account.rs",
      "line_start": 42,
      "line_end": 58,
      "signature": "<verus form or lean-like shape>",
      "doc": "Natural-language description from source comments.",
      "deps": ["AccountId", "Ledger"],
      "complexity": 12,
      "has_spec": true,
      "has_proof": true,
      "flags": []
    },
    {
      "id": "spec_create_zero_balance",
      "kind": "spec",
      "upstream_name": "spec_create_zero_balance",
      "file": "src/account.rs",
      "line_start": 80,
      "line_end": 95,
      "signature": "<forall ...>",
      "doc": "Creating a new account gives it zero balance.",
      "deps": ["createAccount", "accountExists", "getBalance"],
      "flags": []
    }
  ]
}
```

## `source_index.json`

### Purpose

A no-LLM, best-effort registry of top-level source entities. It is not
the final selection, but it gives later stages a stable universe of
names so the pipeline can detect silent drops, inconsistent API
references, and unreviewed axiomization.

### Location

`<output_dir>/.vero/source_index.json`

### Producer

`source_index` stage.

### Consumers

`discover`, `select`, `plan`, `validate`.

### Schema

```json
{
  "version": 1,
  "source_language": "lean | coq | dafny | verus | python",
  "source_path": "<absolute path>",
  "entities": [
    {
      "id": "FloatSpec/src/Core/Defs.lean:F2R:1234",
      "name": "F2R",
      "qualified_name": "F2R",
      "kind": "def | theorem | lemma | axiom | opaque | structure | ...",
      "source_file": "FloatSpec/src/Core/Defs.lean",
      "source_line": 65,
      "signature": "def F2R ...",
      "default_role": "unclassified",
      "disposition": "unclassified",
      "selected": true,
      "dependencies": [],
      "notes": "best-effort no-LLM extraction; confirm in discover/select"
    }
  ]
}
```

### Role/disposition vocabulary

`role` / `default_role` values:

- `scored_api`: model-facing implementation task.
- `scored_spec`: evaluated benchmark proof obligation/spec, not a Bundle API.
- `api_helper`: implementation helper, not scored.
- `semantic_model`: interpretation function such as `F2R`.
- `spec_helper`: helper predicate/theorem used by specs.
- `trusted_theory`: provided theorem from upstream proof infrastructure.
- `trusted_external`: real opaque/external boundary.
- `proof_helper_task`: theorem/lemma proof obligation selected as an
  unscored helper task.
- `trusted_theorem`: source theorem with a real proof or explicit human-review
  justification for trusting it.
- `reference_api`: frozen reference API intentionally used for comparison.
- `dropped_with_reason`: excluded, with `drop_reason` or `reason`.
- `requires_human_review`: unsafe or ambiguous classification.
- `unclassified`: source-index inventory only; later LLM stages must assign a
  concrete role before using the item.

`disposition` values:

- `unclassified`, `provided`, `scored`, `hidden`, `dropped`, `axiomatized`,
  `opaque`.

Upstream definitions/theorems should not become Lean `axiom`s unless
the role is `trusted_external` or `requires_human_review` with a
recorded reason.

### Notes

- `kind` values: `fn`, `type`, `spec` (a property / ensures clause elevated to a spec), `proof` (a lemma / proof obligation), `test`, `axiom`, `opaque` (external fn sig).
- `deps` are `id`s of other entities (must be present in the same file unless `flags` contains `"cross_module"`).
- `complexity` is language-dependent (e.g. line count, cyclomatic, Verus proof-obligation count). Used by `select` for size filtering.
- `flags` is a free-form tag set (e.g. `"cross_module"`, `"ffi"`, `"large"`, `"private"`). Extractor may add tags to hint the selector.

### Validate rules

The `source_index` rule check is layered:

Error-level:

- `source_index.json` must be a JSON object with `version: 1` and an `entities` or `items` list.
- Each entity must be an object with `id`, `name`, `kind`, `source_file`, and positive integer `source_line`.
- Entity `id` values must be unique.
- `source_file` must be a relative path contained in the source tree.
- `role` / `default_role` and `disposition` must use the supported vocabularies.
- `dropped_with_reason` entries require `drop_reason` or `reason`; `axiomatized` entries require `trusted_external` or `requires_human_review`.
- `dependencies`, when present, must be a list.

Warning-level:

- Missing `source_index.json`, empty entity lists, missing `source_path`, missing `source_language`, or missing `generated_at`.
- `source_path` or entity `source_file` paths that are not accessible from the validation environment.
- Dependency ids that are not present in the same source index, since they may indicate incomplete extraction.

## `select.json`

### Purpose

The subset of `discover.json` entities chosen for the benchmark,
grouped into proposed modules, with dependency-closure warnings.

### Location

`<output_dir>/.vero/select.json`

### Producer

`select` stage.

### Consumers

`plan` stage.

### Schema

```json
{
  "version": 1,
  "selected_entity_ids": ["createAccount", "closeAccount", ..., "spec_create_zero_balance", ...],
  "dependency_closure_warnings": [
    {
      "entity_id": "transfer",
      "depends_on": ["deposit", "withdraw"],
      "missing_deps": [],
      "resolution": "auto_included"
    }
  ],
  "proposed_packages": [
    {
      "name": "BankLedger",
      "is_root": true,
      "modules": [
        {
          "name": "Account",
          "entity_ids": ["AccountId", "Balance", "Account", "Ledger", "createAccount", "closeAccount", "accountExists", "getBalance",
                         "spec_create_zero_balance", "spec_create_exists", "spec_close_removes", "spec_close_preserves_others"]
        },
        {
          "name": "Transaction",
          "entity_ids": ["deposit", "withdraw", "spec_deposit_increases", "spec_withdraw_decreases", "spec_withdraw_insufficient"]
        }
      ]
    }
  ]
}
```

### Notes

- `selected_entity_ids` is the canonical "in the benchmark" list. Anything not in here is excluded.
- `dependency_closure_warnings[].resolution`: `auto_included` | `flagged` | `skipped`. Auto-included deps are added to the selection; flagged deps block progress.
- `proposed_packages` honors the uniform-bundle paradigm: exactly one `is_root: true` entry whose `name` matches `config.project_name`. Additional packages (multi-package benchmarks) have `is_root: false`.

## `plan.json`

### Purpose

The authoritative translation plan: for each module, the exact Lean
names, signature abbrevs, types, spec text, reference implementations,
and test cases that `translate` should emit. This is the contract
between the agent that wrote the plan and the agent/code that writes
the Lean files.

### Location

`<output_dir>/.vero/plan.json`

### Producer

`plan` stage (LLM agent). Human answers are interleaved via
`<output_dir>/plan/questions.md`.

### Consumers

`translate` stage, `validate` stage.

### Schema

```json
{
  "version": 1,
  "api_namespace": "Bank",
  "packages": [
    {
      "name": "BankLedger",
      "is_root": true,
      "bundle_type": "BankLedgerBundle",
      "repo_impl_field": "bankLedger",
      "modules": [
        {
          "name": "Account",
          "upstream_files": ["src/account.rs"],
          "types": [
            {
              "name": "AccountId",
              "lean_form": "abbrev AccountId := Nat",
              "is_foundation": true
            },
            {
              "name": "Account",
              "lean_form": "structure Account where\n  id : AccountId\n  balance : Balance\n  deriving Repr, DecidableEq, BEq",
              "is_foundation": true
            }
          ],
          "apis": [
            {
              "upstream_name": "create_account",
              "lean_name": "createAccount",
              "sig_abbrev": "CreateAccountSig",
              "lean_type": "AccountId → Ledger → Ledger",
              "opaque": false,
              "role": "scored_api",
              "disposition": "scored",
              "source_id": "src/account.rs:create_account:1234",
              "nl_description": "Add a new account with the given id to the ledger."
            }
          ],
          "specs": [
            {
              "name": "spec_create_zero_balance",
              "nl_description": "Creating a new account gives it zero balance.",
              "lean_form": "∀ (id : AccountId) (ledger : Ledger), impl.bankLedger.accountExists id ledger = false → impl.bankLedger.getBalance id (impl.bankLedger.createAccount id ledger) = some 0",
              "apis_referenced": ["createAccount", "accountExists", "getBalance"],
              "source_theorem": "spec_create_zero_balance",
              "equivalence_status": "equivalent",
              "semantic_bridge_required": [],
              "curator_intended_truth": "prove | disprove | unsat | sat | unknown"
            }
          ],
          /* No ref_impls field. Reference implementations are written
             directly inside each API's `code` marker in Impl/*.lean.
             Pre-agent-gen replaces marker content with `sorry` before
             the LLM sees the benchmark. */
        }
      ]
    }
  ],
  "test_cases": [
    {
      "name": "guard_create_account_zero_balance",
      "nl_description": "After creating an account it has balance 0.",
      "lean_form": "#guard getBalance 1 (createAccount 1 []) == some 0"
    }
  ]
}
```

### Notes

- `api_namespace` is project-wide (not per-package) since all APIs share one Lean namespace prefix. Soft convention, and may be absent for some future projects.
- `packages[].is_root` must be exactly one `true`.
- `types[].is_foundation` flags types that must live in the foundation module (the one every other Impl imports, e.g. `Impl/Account.lean` holding `Ledger` shared with Transaction + Ledger modules). Translate stage uses this to co-locate types.
- `apis[].opaque = true` means the function is FFI / external; `translate` emits `opaque` + axiomatized behavior instead of a `sorry` body.
- `apis[].role`, `apis[].disposition`, and `apis[].source_id` preserve
  the role classification from `source_index.json` / discovery. Semantic
  models such as `F2R` should be `semantic_model` or `spec_helper`, not
  silently dropped.
- `specs[].source_theorem`, `equivalence_status`, and
  `semantic_bridge_required` record whether the translated spec is
  equivalent to the source theorem. If a source theorem is decomposed into
  structural specs, list the bridge lemmas needed to recover the original
  theorem.
- `specs[].curator_intended_truth` is the curator's ground-truth label for coverage evaluation. May be `unknown` if the curator hasn't decided; evaluator treats `unknown` as non-scoring.
- **No `ref_impls[]` field** (retired 2026-04-20). The reference
  implementation lives inside each API's `code` marker in
  `Impl/<Module>.lean` directly. Pre-agent-gen replaces marker
  content with `sorry` before the LLM sees the benchmark; `#guard`
  tests in `Test.lean` call `Bank.*` directly, so they hit the real
  reference at build time.
- `test_cases[]` become `#guard` statements in `Test.lean` (against
  `Bank.*`).

## `manifest.json`

### Purpose

The canonical benchmark metadata. Pinned in the curated Lean tree.
Consumed by the pre-agent-gen stage (which reads `packages[].modules[].specs` to emit `Proof/<Module>.lean`), the evaluator, and downstream tooling.

### Location

`<output_dir>/benchmark/<Project>/manifest.json`

### Producer

`translate` stage (derived from the translated files; not a free-form
write. The translate stage parses the emitted Lean files and builds
this).

### Consumers

- `validate` stage (manifest-vs-code consistency checks).
- `pre_agent_gen` stage (to materialize `Proof/<Module>.lean`).
- Evaluator (to know what APIs / specs are in scope).
- Human readers.

### Schema

See the canonical example at `reference/BankLedger/manifest.json`.

Key fields:

```json
{
  "benchmark_id": "<snake_case id>",
  "description": "<one-line purpose or null>",
  "lean_version": "4.29.1",
  "modes_supported": ["proof", "codeproof"],
  "source": {
    "name": null,
    "language": null,
    "repo_url": null,
    "commit_hash": null,
    "path": null
  },
  "curation": {
    "date": null
  },
  "root_package": "<PackageName>",
  "trusted_axioms": ["<FullyQualified.AxiomName>", "..."],
  "files": {
    "root_hub": "<Project>.lean",
    "harness": "<RootPackage>/Harness.lean",
    "test": "<RootPackage>/Test.lean",
    "lakefile": "lakefile.toml"
  },
  "packages": [
    {
      "name": "<PackageName>",
      "bundle": "<Package>/Bundle.lean",
      "bundle_type": "<PackageName>Bundle",
      "repo_impl_field": "<lowerCamelCase(PackageName)>",
      "modules": [
        {
          "name": "Account",
          "impl": "<Package>/Impl/Account.lean",
          "spec": "<Package>/Spec/Account.lean",
          "apis": [
            {"name": "createAccount",  "sig": "CreateAccountSig",  "type": "AccountId → Ledger → Ledger", "kind": "api", "role": "scored_api", "source_id": "..."}
          ],
          "api_helpers": [
            {"name": "internalCompact"}
          ],
          "specs": ["spec_create_zero_balance", "..."],
          "spec_helpers": ["canonicalBalance"]
        }
      ]
    }
  ]
}
```

### Notes

- Exactly one package entry has `name == root_package`; by convention its directory is named after the benchmark (`BankLedger/` here).
- `source.*` fields are placeholder-nullable for hand-crafted references. Curated benchmarks populate them from upstream.
- `files` block lists benchmark-singleton paths (not per-package). Paths are relative to the Lean project directory (same dir as `lakefile.toml`).
- `packages[].modules[].apis[]` entries carry `name` (fn name as `Bank.<name>`), `sig` (sig abbrev), `type` (the abbrev's body), and an optional `kind` which is `"api"` (default) or `"api_helper"`. An `api_helper` entry has no sig abbrev requirement and no `!benchmark code` slot requirement, and the LLM writes its body free-form.
- `packages[].modules[].api_helpers[]` (optional, default `[]`) is an alternative home for `api_helper` entries when you want them clearly separated from the signature-constrained `apis`. Each entry is `{"name": "<fn>"}`; no sig or type required.
- `packages[].modules[].specs[]` lists proof-obligation names (strings). Entries may also be `{"name": "<spec>", "kind": "spec"}`; helpers referenced by specs go in `spec_helpers`.
- `packages[].modules[].spec_helpers[]` (optional, default `[]`) lists predicate/property definitions used inside specs or APIs. Strings or `{"name": ..., "kind": "spec_helper"}` objects. These are not proof obligations; the validator skips them.
- `packages[].modules[].apis[]` and `specs[]` may carry the same
  role/disposition/source metadata as `plan.json`. The validator uses
  it to reject unreviewed axiomization and weakened source-theorem
  translations.
- Files with zero `apis[]` entries (no fillable APIs) are treated as frozen context. The validator will not require `!benchmark` markers on such files and will warn if any markers are present (the agent cannot modify a marker-free file by convention).
- `packages[].bundle_type` and `repo_impl_field` let generators know the Lean identifiers without inferring from filenames.
- `trusted_axioms` (optional; default `[]`) lists fully-qualified axiom names declared anywhere in the benchmark (e.g. in `Impl/Core.lean`) that the evaluator should treat as trusted. Proofs depending on these axioms grade as `passed` alongside the standard Lean trio (`Classical.choice`, `propext`, `Quot.sound`). The axiom check still rejects `sorryAx` and any axiom not in the allowlist.

## `validate.json`

### Purpose

Structured validation report from the `validate` stage. Consumed by
the CLI to decide whether to halt the pipeline.

### Location

`<output_dir>/.vero/validate.json`, with a human-readable summary
at `<output_dir>/validate/report.md`.

### Producer

`validate` stage.

### Consumers

CLI, humans, CI.

### Schema

```json
{
  "version": 1,
  "ran_at": "2026-04-19T03:10:00Z",
  "overall": "pass | warn | fail",
  "blockers": [
    "markers.positioning: imports marker at <file>:<line> is not immediately after the last import statement"
  ],
  "rule_checks": {
    "manifest_schema": {
      "status": "pass | warn | fail",
      "details": []
    },
    "manifest_vs_code": {
      "status": "pass",
      "details": [
        {"severity": "info", "location": "BankLedger/Impl/Account.lean", "message": "..."}
      ]
    },
    "markers_grammar":      {"status": "pass", "details": []},
    "markers_positioning":  {"status": "pass", "details": []},
    "file_roles":           {"status": "pass", "details": []},
    "build":                {"status": "pass", "details": [{"severity": "info", "message": "14 jobs built"}]},
    "guards":               {"status": "pass", "details": [{"severity": "info", "message": "15 guards"}]},
    "toolchain":            {"status": "pass", "details": []}
  },
  "llm_review": {
    "spec_intent_alignment": {"status": "pass", "details": []},
    "idiom":                 {"status": "warn", "details": [...]},
    "test_meaningfulness":   {"status": "pass", "details": []},
    "review_annotations":    {"status": "pass", "details": []},
    "spec_completeness":     {"status": "pass", "details": []}
  }
}
```

### Notes

- `overall` rolls up as: any `rule_checks.*` = `fail` → `fail`; otherwise any `llm_review.*` = `fail` under `--strict` → `fail`; otherwise any `warn` → `warn`; else `pass`.
- `blockers[]` is a flattened list of `fail`-status messages that halt the pipeline.
- Each rule check has a defined purpose; see the plan at `plan/20260419-013604-pipeline-rewrite.md` for the full rule-book.
- `details[].severity` is `info | warn | error`; must match the parent `status`.

## Schema evolution

- Bump the top-level `"version": N` when a breaking change is introduced.
- Add new optional fields freely (version bump not required).
- Removing or repurposing a field requires a version bump + a migration note here.
- Consumers should read the version and reject if unknown.

## Cross-references

- Pipeline plan: `plan/20260419-013604-pipeline-rewrite.md`
- Reference benchmark: `reference/BankLedger/` (canonical shape, see `manifest.json` there for a populated example).
- Reference paradigm: `reference/README.md` + `reference/BankLedger/ARCHITECTURE.md`.
- Marker + positioning conventions: `plan/20260418-131540-reference-repo-curation.md` (Convention #2).
