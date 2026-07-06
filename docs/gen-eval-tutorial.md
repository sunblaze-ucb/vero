# Gen / Eval Tutorial

A start-to-finish guide to running LLM generation + evaluation on a curated Lean 4 benchmark.

If you want the background on *why* the pipeline is shaped this way, see [`src/vero/generation/README.md`](../src/vero/generation/README.md) and [`src/vero/evaluation/README.md`](../src/vero/evaluation/README.md). This doc is the hands-on reference.

## TL;DR

```bash
# One-time setup
uv sync && source .venv/bin/activate
cp .env.example .env   # then edit to add your API keys

# Fresh run: gen + eval
vero run benchmark=bankledger agent=claude mode=proof

# Re-eval an existing run
vero run run=bankledger-claude-proof-20260420-143022 eval.name=retry eval.timeout=1200
```

## 1. Concepts at a glance

A **benchmark** is a curated Lean 4 project (`manifest.json` + frozen `Bundle.lean` / `Harness.lean` / `Spec/*.lean` + reference `Impl/*.lean`). It has one or more `!benchmark`-marked slots the LLM is expected to fill, and one or more specs (`def spec_<S> : Prop`) a correct filling must satisfy.

A **run** is one end-to-end attempt at a benchmark: copy benchmark → materialize `Proof/` stubs → invoke an LLM agent to edit → extract the results into an `artifact.json` → grade.

Each run writes everything to `agent_runs/<name>/`:

```
agent_runs/<name>/
    run.yaml                     # frozen, fully-resolved config
    manifest.json                # run metadata (benchmark, agent, git sha, env fingerprint)
    source/                      # the agent's working sandbox
        <Project>/...
        INSTRUCTION.md
        agent_events.jsonl       # full-fidelity agent event stream
        agent.log                # human-readable agent log
        artifact.json            # extracted slot schedule + bodies
    eval/<eval-name>/            # one dir per eval attempt
        sandbox/                 # re-rendered clean sandbox (anti-cheat)
        report.json
        report.md
        eval.log                 # evaluator's own event trace
        eval.manifest.json       # per-eval metadata (timings, git sha, summary)
```

By default `agent_runs/` is git-ignored (runtime output). Archive-worthy reference runs live in `saved_agent_runs/` (tracked).

## 2. Setup

```bash
uv sync && source .venv/bin/activate
```

Credentials live in a `.env` at the repo root. Run `cp .env.example .env` and fill in the key(s) for the agent you're running. Which variables are read depends on the credentials profile (`credentials=<profile>`, default `litellm`). The `codex` and `gemini` agents also need their CLI binary on `$PATH`.

See [`agents.md`](agents.md) for the full credentials matrix, the built-in agents, and how to plug in your own.

## 3. The two modes

### `proof` mode

The reference `Impl/*` is given. The agent writes proofs about it. For each spec `S` the pipeline materializes a pair:

- `prove_<S> : spec_<S> canonical := sorry`
- `disprove_<S> : ¬ spec_<S> canonical := sorry`

The agent fills exactly one. Filling `prove_` is the common case; `disprove_` exists so the benchmark can catch a curator bug (the spec is actually wrong for the reference impl).

### `codeproof` mode

The reference `Impl/*` bodies are `sorry`-d. The agent writes an implementation **and** a proof stub per spec:

- `prove_<S> : spec_<S> canonical := sorry` (their impl satisfies the spec)
- `unsat_<S> : ¬ ∃ impl, spec_<S> impl := sorry` (no impl can)
- `sat_<S> : ∃ impl, spec_<S> impl := sorry` (some impl can, use with care)
- One `Proof/Joint.lean` slot with a `!solution specs=[...]` joint-unsat claim.

The agent fills exactly one of `{prove_, unsat_, sat_}` per spec. `sat_<S>` alone is trivially satisfiable by an ad-hoc bundle and is **rejected as `unpaired_sat`** unless paired with a verified `joint_unsat` claim naming `<S>` in `Proof/Joint.lean`. Then the combination asserts "S is individually satisfiable, but not jointly with the other named specs".

## 4. The command

Everything is one command: `vero run [overrides]`. Overrides use Hydra syntax (`key=value`).

```bash
# Fresh gen + eval, all defaults (bankledger + claude + proof)
vero run

# Pick a different benchmark / agent / mode
vero run benchmark=tiny_unsat mode=codeproof
vero run benchmark=bankledger agent=codex agent.model=gpt-5-codex-v1
vero run mode=codeproof agent.max_turns=80

# Materialize the sandbox only (no LLM); useful for inspecting the layout
vero run benchmark=bankledger skip_agent=true skip_eval=true

# Run gen only, inspect artifact manually, eval later
vero run benchmark=bankledger skip_eval=true

# Re-eval an existing run (run= implies skip_gen=true)
vero run run=<prior-run-name> eval.name=retry-longer eval.timeout=1200

# Override a leaf under a group preset
vero run agent=claude agent.model=claude-opus-4-7 agent.max_turns=60
```

Discover available groups and all overridable leaves:

```bash
vero run --help
```

### Naming

If you don't pass `name=`, the run name is auto-generated as `${benchmark.id}-${agent.kind}-${mode}-YYYYMMDD-HHMMSS`. Pin it with `name=<explicit>` to get a reproducible path (then `overwrite=true` is required to replace an existing run dir).

### Flag interactions

- `run=<name>` with no stage flags implies `skip_gen=true`, the common re-eval case.
- `skip_gen=true` requires `run=<name>` set (so the evaluator knows which artifact to grade).
- `skip_agent=true` materializes the sandbox but never invokes an LLM, so the artifact is extracted from the un-filled sandbox and eval reports every spec as `unfilled`.
- `eval.name` defaults to `default`; reuse a name only with `eval.overwrite=true` (else pick a fresh name).
- `iterate=<profile>` enables the iteration harness (see below). Incompatible with `skip_gen=true`.

### Iteration harness (`iterate=default` / `iterate=self`)

Agents sometimes give up after a single turn even when there's budget left. The iteration harness re-invokes the agent against a fresh sandbox up to `iterate.max` additional times (total passes = `max + 1`), optionally feeding the prior eval report back as structured feedback.

```bash
# Default: 5 retries, run eval between iterations, feed report.md back.
vero run benchmark=bankledger iterate=default

# Self-assess: 5 retries, no eval between iterations; agent must judge
# its own done condition.
vero run benchmark=bankledger iterate=self

# Custom knobs inline.
vero run iterate=default iterate.max=3 iterate.budget_usd=2.50 iterate.stop_on_done=false
```

Config profiles live under `conf/iterate/`:

| Profile   | max | mode | stop_on_done | budget_usd |
|-----------|-----|------|--------------|------------|
| `off`     | 0   | n/a  | n/a          | n/a        |
| `default` | 5   | eval | true         | null       |
| `eval`    | 5   | eval | true         | null       |
| `self`    | 5   | self | true         | null       |

Per-iteration output lands at `agent_runs/<name>/iter-N/source/` + `iter-N/eval/<eval.name>/` (for `mode=eval`). A top-level `iterations.json` summarises all iterations, and the best iteration's `source/` + `eval/<eval.name>/` are copied to the run root for aggregator back-compat.

Stop conditions, first hit wins:

1. `done`. Build ok, every spec passed, and (codeproof) joint passed. Only when `stop_on_done=true`.
2. `budget_exceeded`. Cumulative `total_cost_usd` across iterations meets or exceeds `budget_usd`. Only enforced when agents report a dollar figure (Claude SDK does, while codex, gemini, and gauss do not today).
3. `max_iterations`. Exhausted `max + 1` passes.

When `mode=eval`, iteration N+1 receives the prior iteration's `report.md` verbatim at `source/FEEDBACK.md`, and the rendered `INSTRUCTION.md` embeds the same content under a "Previous iteration feedback" section that tells the agent never to bulk-revert prior passes.

When `mode=self`, no eval runs between iterations; the agent gets a short nudge in the INSTRUCTION telling it which iteration it is on and to re-assess the done condition and keep working.

## 5. Adding a benchmark to the registry

The registry is just `conf/benchmark/*.yaml`. One file per benchmark:

```yaml
# conf/benchmark/my_lib.yaml
path: benchmarks/my_lib     # relative to repo root
id: my_lib                  # appears in auto-generated run names
default_mode: proof         # informational; the CLI's run.mode overrides
```

Hydra picks it up automatically. `vero run benchmark=my_lib ...` is enough.

For authoring new benchmarks, see `src/vero/curation/`. That pipeline emits the `manifest.json` and frozen tree that a registry YAML then points at.

## 6. Adding an agent

A **profile** for an existing backend is just a file under `conf/agent/`:

```yaml
# conf/agent/claude-opus.yaml
kind: claude              # claude | codex | gemini | gauss
model: claude-opus-4-8
max_turns: 60
timeout_seconds: 0
```

Then `vero run agent=claude-opus ...`. The `kind` field selects the backend; everything else passes through to the agent constructor.

To integrate a **new** agent (your own model or harness), see [`agents.md`](agents.md). It covers the one-method adapter and the fully-decoupled sandbox path.

## 7. Re-evaluation deep dive

Re-eval exists because the evaluator's rule set evolves. You may want to re-grade a run from weeks ago under a tighter axiom allowlist, a longer Lake timeout, or a fixed grader bug.

The CLI supports this with zero ceremony:

```bash
vero run run=bankledger-claude-proof-20260420-143022
```

What happens:

1. The frozen `run.yaml` at that run's root is loaded as the base config.
2. Your CLI overrides (e.g. `eval.timeout=1200`) are layered on top; benchmark / agent / mode come straight from the frozen config so you never restate them.
3. Since no stage flag is set, the CLI infers `skip_gen=true`.
4. `run.yaml` and `manifest.json` at the run root are **not** overwritten, since they describe the original gen invocation.
5. A new `eval/<eval.name>/` subtree is created (default `eval/default/`; pick a different `eval.name=` if `default` already exists, or pass `eval.overwrite=true`).

To re-eval a run that's been archived into `saved_agent_runs/`, the CLI searches `<root>/<name>/` first then falls back to `saved_agent_runs/<name>/` automatically. Same command.

## 8. Reading the output

### `eval/<name>/report.md`

Top-level counts, then per-spec rows with status + theorem-level axiom breakdown. This is the primary human-facing summary.

### `eval/<name>/report.json`

Structured version; downstream analysis scripts live here.

### `eval/<name>/eval.manifest.json`

Per-eval metadata: start time, elapsed seconds, git sha at eval time, summary counts, paths. Useful for comparing two evals on the same run.

### `source/artifact.json`

The canonical slot-by-slot record of what the agent produced. Shape is schema-driven, with one entry per expected slot, `found=True|False`, a body hash, and token-taint flags. Re-eval reads this, and any third-party analysis should too.

### `source/agent_events.jsonl`

Full-fidelity agent event stream (one JSON event per line). Turn-by-turn LLM text, thinking blocks, tool-use + tool-result payloads, errors. This is the authoritative replay format.

### `source/agent.log`

Human-readable mirror of the JSONL. Useful for `tail -f` during a live run.

## 9. Common workflows

### "Did my prompt change land?"

```bash
# Same benchmark, same agent, same model, different prompt
vero run benchmark=bankledger mode=proof name=bankledger-proof-v2
# Compare with the prior run
diff saved_agent_runs/<prior>/eval/default/report.md \
     agent_runs/bankledger-proof-v2/eval/default/report.md
```

### "Sweep across models / benchmarks / modes"

Hydra multirun (`-m`) spawns one `vero run` per cell of the cross-product. Each run still writes to `agent_runs/<name>/` (so the existing re-eval workflow keeps working), and the sweep lands under `agent_runs_sweep/<timestamp>/`:

```bash
# 2 × 2 × 2 = 8 cells, one per (benchmark, agent, mode)
vero run -m \
    benchmark=bankledger,deposit_sc \
    agent=claude,codex \
    mode=proof,codeproof

# Aggregate the 8 runs into results.csv + results.json + results.md
vero-sweep-aggregate agent_runs_sweep/<timestamp>/
```

The aggregator walks every run dir under the sweep root (identified by a top-level `manifest.json`), reads each `eval/<name>/report.json`, and emits one row per (benchmark, agent, model, mode, eval) cell. Use `--out-dir` to land the tables elsewhere.

### "I updated the grader, regrade everything"

```bash
for dir in agent_runs/*/; do
    name=$(basename "$dir")
    vero run run="$name" eval.name=regrade-$(date +%s)
done
```

## 10. Troubleshooting

- **`claude_agent_sdk` refuses to launch.** You're running under Claude Code with `CLAUDECODE=1` set. The CLI auto-scrubs the `CLAUDE_CODE_*` env vars before invoking the agent; if you're still seeing the error, make sure you're on current `main` (post-PR #55).
- **Codex returns 401 from a LiteLLM proxy.** Check `conf/agent/codex.yaml` and the per-run `.codex_home/config.toml` that gets generated under your sandbox. The `[model_providers.openai_http]` block needs `env_key = "OPENAI_API_KEY"` so codex attaches the Authorization header.
- **Every spec in one module grades `build_error`.** The module's proof file didn't compile. Intra-module cascade is inherent to Lean (no `.olean` emitted on failure). Per-module axiom checks isolate healthy modules elsewhere.
- **Every spec grades `build_error` with `impl_broken=true`.** Stage 1 (the Harness compile) failed, so the agent's `Impl/*` doesn't type-check. No partial credit; fix the impl.
- **`passed_specs=0, unpaired_sat_specs=N`.** The agent took the `sat_<S>` shortcut. The prompt forbids it and the grader rejects it; read `agent.log` to confirm the agent saw the current `INSTRUCTION.md`.

## 11. Exit codes

`vero run` exits 0 on success, non-zero on failure (config errors, agent crash, build failure). The detailed grade report lives in `eval/<name>/report.{json,md}`.
