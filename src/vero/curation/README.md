# Curation Pipeline — Source to Lean 4 Benchmarks

Translates source code into compilable Lean 4 projects where `sorry` stubs define benchmark tasks for LLM evaluation. Supports four input shapes: verified code (Dafny/Verus/Coq), un-curated Python repos, pre-curated Python repos with a `benchmark.json`, and Lean 4 source.

> **Artifact schemas:** see [`docs/pipeline-schema.md`](../../../docs/pipeline-schema.md) for the authoritative shape of every JSON artifact the pipeline reads or writes.

## Quick Start

```bash
# Verified code (default workflow)
python -m vero.curation run /path/to/source output/project --lang dafny

# Python — un-curated repo (specs authored after translation)
python -m vero.curation run /path/to/source output/project --workflow python_spec

# Python — pre-curated benchmark.json (one-shot scaffolding)
python -m vero.curation python-from-json datasets/<repo>/task/benchmark.json output/project

# Lean source — extract specs from existing theorems
python -m vero.curation run /path/to/lean-src output/project --workflow lean_spec

# Resume / re-run a specific stage
python -m vero.curation run output/project --stage select
python -m vero.curation run output/project --stage translate --force
python -m vero.curation run output/project --stage translate --continue

# Status / task index
python -m vero.curation status output/project
python -m vero.curation extract output/project/lean_output/ProjectName/
```

## Workflows

| Workflow | Stages | Use case |
|---|---|---|
| `verified_to_lean` (default) | init → discover → select → plan → translate → validate | Dafny / Verus / Coq repos with existing proofs |
| `python_spec` | init → discover → select → plan → translate → spec_write → validate | Un-curated Python repos — agent authors specs after translation |
| `python_from_benchmark_json` | python_from_json → python_adjust_bodies → spec_write → validate | Pre-curated Python repos (`datasets/<r>/task/benchmark.json` paired with `original_python/`). Two-phase: scaffold sigs+sorry, then translate Python bodies into Impls, then author specs. |
| `lean_spec` | init → discover → select → plan → translate → spec_write → validate | Lean 4 source — extract specs from existing theorems, optionally extend |

Select via `--workflow`. Auto-detection by source extension is the default; pass `--lang` to override.

## Pipeline Stages

| Stage | What it does | Human reviews |
|---|---|---|
| **init** | Detect language, gather git metadata, scaffold workspace + Lean project | — |
| **discover** | Agent scans source, classifies items (types / functions / theorems / tests) | Check/uncheck items in `discovery/*.md` |
| **select** | Agent computes dependency closure, assigns layers, plans file layout | Verify closure warnings + layout |
| **plan** | Agent writes translation plan with exact Lean signatures + architecture sketch | Answer questions, adjust mappings |
| **translate** (or **orchestrated_translate**) | Agent emits the Lean project — Impl/Spec/Bundle/Harness/Test, `!benchmark` markers, `!curation @review` annotations. Orchestrator dispatches per-module executors in parallel. | Review code, give feedback via `@review` / `@human:` comments |
| **spec_write** | Two-substep agent flow: (1) reason about specs, write `spec_plan.md`; (2) human approves with `# APPROVED` marker; (3) agent formalizes into `Spec/<Module>.lean` | Edit + approve `spec_plan.md` |
| **python_from_json** | One-shot: read `benchmark.json`, emit Lean project + manifest with sigs + `sorry` Impl bodies + empty Spec scaffolds | Inspect emitted scaffold + `@review human` annotations |
| **python_adjust_bodies** | Single-agent translate of Python `def` bodies (under `<source_dir>/<python_context_path>/`, default `original_python`) into the matching `!benchmark code def=<name>` markers. Lake-build clean before exit. Idempotent (no-op if no `sorry` remains in code blocks). | Inspect filled Impls; `--stage python_adjust_bodies --force` to retry, `--continue` to resume the session |
| **validate** | Rule-based + (optional) LLM-review checks: marker grammar, manifest consistency, spec shape, source coverage, lake build | Inspect `validate/report.md` |

Stages with `human_review = True` pause the pipeline; resume with `--stage <next>`.

## CLI Reference

### `run` — Execute the pipeline

```bash
python -m vero.curation run <source_dir> <output_dir> [options]   # new run
python -m vero.curation run <output_dir> --stage <stage> [options] # resume
```

| Flag | Description | Default |
|---|---|---|
| `--lang {dafny,verus,coq,python,lean}` | Source language (auto-detected if omitted) | auto |
| `--workflow <name>` | Pipeline workflow | `verified_to_lean` |
| `--source-subdir <path>` | Subdirectory within repo where source code lives | `""` |
| `--stage <name>` | Start from this stage (by name) | first stage |
| `--force` | Re-run the stage even if already completed | off |
| `--continue` | Resume the agent session from where it stopped | off |
| `--model <model>` | Claude model to use | `CurationConfig` default |
| `--max-turns <N>` | Override max turns for the target stage | per-stage default |
| `--no-orchestrator` | Disable the orchestrator/executor architecture (single-agent fallback) | orchestrator on |
| `--max-concurrent <N>` | Max concurrent executor agents | 4 |

### `python-from-json` — Mode A scaffolder (phase 1 only)

```bash
python -m vero.curation python-from-json <benchmark.json> <out_dir> [--lean-version <v>]
```

Reads a pre-curated `benchmark.json` (the output of an older Python curation pipeline) and emits a Lean 4 project in the canonical paradigm with `sorry` Impl bodies + empty Spec scaffolds. Idempotent — re-running overwrites.

**This subcommand only runs phase 1.** For the full Mode A pipeline (scaffold → fill bodies → author specs → validate) use:

```bash
python -m vero.curation run <source_dir> <out_dir> --workflow python_from_benchmark_json
```

where `<source_dir>` is the dir containing `benchmark.json` *and* the python source (typically `datasets/<repo>/task/`).

### `status`, `extract`

```bash
python -m vero.curation status <output_dir>
python -m vero.curation extract <lean_project_dir>
```

`status` shows per-stage completion + active config. `extract` enumerates `!benchmark` slots with their file locations and sorry status.

## Configuration

Pipeline config is stored in `<output_dir>/config.yaml`:

```yaml
source_dir: /path/to/source
output_dir: /path/to/output
source_language: dafny
workflow: verified_to_lean
model: claude-sonnet-4-6
lean_version: "4.29.1"
permission_mode: acceptEdits

# Per-stage turn limits
max_turns_discover: 50
max_turns_select: 30
max_turns_plan: 30
max_turns_translate: 100
max_turns_spec_write: 50
max_turns_orchestrator: 200
max_turns_per_module: 40

# Orchestrator
use_orchestrator: true
max_concurrent_executors: 4
max_executor_retries: 2

# Optional: external LLM endpoint
api_key: null
api_base_url: null
```

Override model and per-stage turns via CLI flags. Edit `config.yaml` directly for persistent changes.

## Human Feedback System

After translation, each definition has a `-- !curation @review v<N>` comment:

```lean
-- !curation @review v1 [ ] push — Stack.dfy:5, exec-fn, body: sorry
def Stack.push (s : Stack α) (v : α) : Stack α := sorry
```

**Human actions:**

- `[x]` — approve (agent won't change it on the next `--force` round).
- Edit text after `—` — give feedback (agent addresses it on next `--force` run, archives the comment as `@v<N-1>... [RESOLVED]` and writes a fresh `@review v<N>` if more changes are needed).
- `-- !curation @human: <note>` — author a free-form note to the agent; archived as `@v<N-1>-human: ... [NOTED]` after the agent applies it.
- `-- !curation @answer: <text>` near a prior `@question` — answer the agent's question; archived as `@v<N-1>-answer: ... [ANSWERED]`.

The translate stage's `_render_review_markdown` writes a `curation/review.md` summary listing the build status, marker metrics, and every benchmark task; humans use that as the starting point for the review loop.

## Validator

Run rule-based + LLM checks via `--stage validate` (or as part of any workflow that includes the stage). Rule-based checks live in `validation/checks.py`:

| Check | What it verifies |
|---|---|
| `manifest_schema` | `manifest.json` has all required top-level + `files` + per-package keys |
| `manifest_vs_code` | Each manifest API has its `abbrev <Sig>` + `def <Pkg>.<name>` in the right Impl file; structure RepoImpl in Harness; `def canonical` exists |
| `markers_grammar` | Every `!benchmark` marker has valid key/fields; `!solution` grammar OK |
| `markers_positioning` | `imports` marker adjacent to last `import` line; `proof_aux` never between `by` and proof body |
| `file_roles` | Impl files with APIs have `imports` + `global_aux` + per-API `code` + `code_aux` markers; Spec files marker-free; Harness/Test/root non-editable |
| `spec_shape` | Every manifest-listed spec is `def spec_<name> (impl : RepoImpl) : Prop`; no theorems in Spec files |
| `source_index` | `.vero/source_index.json` is a valid source-wide inventory: versioned object, entity ids/locations, safe relative source paths, role/disposition vocabulary, dependency shape; missing/incomplete producer metadata is warning-level |
| `source_coverage` | (When `discover.json` exists) every source item marked `selected: true` round-trips to a manifest entry |
| `guards` | `Test.lean` has at least one `#guard` |
| `toolchain` | `lean-toolchain` matches `manifest.lean_version` |
| `build` | `lake build` succeeds |

LLM-review checks (opt-in, file-by-file dispatch via the `vero-validate` skill) cover semantic concerns: spec intent capture, code idiom, test meaningfulness, review-annotation sanity, spec completeness, trusted-boundary sanity, and repo issue taxonomy.

## Skills

The agent loads workflow-appropriate skills via the built-in `Skill` tool. The `_skill_preamble.py` module maps each `(stage, language)` pair to the right set:

| Skill | Loaded by |
|---|---|
| `vero-discover` / `vero-select` / `vero-plan` / `vero-translate` / `vero-validate` / `vero-spec-write` | corresponding stage |
| `vero-source-{dafny,verus,coq,python,lean}` | discover, plan, translate (when `source_language` matches) |
| `vero-{dafny,verus,coq,python}-pitfalls` | translate (when source is one of those) |
| `vero-lean-pitfalls` | translate (always — Lean is the target language) |

Skill content lives under `.claude/skills/<name>/SKILL.md`.

## Architecture

- `pipeline.py` — `Pipeline` base + per-workflow subclasses + `WORKFLOWS` registry + `get_pipeline` factory.
- `stages/` — one file per stage; each defines a `StageRunner` subclass with a class-level `name` + `human_review` and an async `run(ctx) -> StageResult` method. `_skill_preamble.py` is the only inter-stage helper.
- `agent.py` — thin wrapper around `claude_agent_sdk.query` with MCP server registration for the Lean LSP.
- `validation/` — `checks.py` rule-based + `llm_review.py` subagent dispatcher + `markers.py` parser.
- `marker.py` / `lean_project.py` / `feedback.py` — pure helpers used by translate / validate.
- `models.py` — Pydantic dataclasses shared across stages (DiscoveredItem, SelectionPlan, TaskEntry, ...).
- `config.py` — `CurationConfig` (the workspace config.yaml shape).

The orchestrator-executor architecture (under `orchestrator/`) is the default for `translate`. It splits the project into per-module units, dispatches executors in parallel, and falls back to a single-agent path when `use_orchestrator=False`.
