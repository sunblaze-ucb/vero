# `vero.generation` — LLM generation pipeline

Drives an LLM agent to fill the `!benchmark` marker slots in a benchmark built in the **ratified bundle paradigm** (see `reference/BankLedger/` for the canonical exemplar).

For how to *run* the pipeline, see [`docs/gen-eval-tutorial.md`](../../../docs/gen-eval-tutorial.md). This README covers what the module does and why, not how to invoke it.

Two backends land today, pluggable under a shared protocol:

| Agent | Transport | Usage field |
|---|---|---|
| `claude` | `claude_agent_sdk.query()` (async iterator) | `total_cost_usd` (client estimate) |
| `codex` | `codex exec --json` subprocess (JSONL stream) | `{input_tokens, cached_input_tokens, output_tokens}` |

## Pipeline

```
benchmark dir         sandbox dir (copy + materialize)    agent run       artifact
────────────          ─────────────────────────────       ──────────      ────────
manifest.json   ──►   Bundle.lean / Harness.lean ──┐                    ┌─► slots[] (one per expected
Bundle.lean           Impl/*.lean  (code → sorry    ├──► Agent         │    schedule entry, with
Harness.lean            in codeproof mode)          │    (Claude /      │    found=T/F, body_lines,
Impl/*.lean           Spec/*.lean   (frozen)         │    Codex)        │    actual_fields, error)
Spec/*.lean           Proof/*.lean (materialized   ──┘                  ├─► extras[]  (agent-added
Test/*.lean             per mode)                                       │    markers outside the schedule)
                      INSTRUCTION.md                                    └─► file_errors{}  (unparseable
                      agent_events.jsonl                                     files)
                      agent.log                                              │
                                                                             ▼
                                                                  vero.evaluation
```

The artifact shape is **schema-driven**: the expected-slot schedule is computed from `manifest.json` + mode before the agent runs, and the extractor matches parsed slots against that schedule by `(prefix, key, def_name)`. Agent-added or renamed markers land in `extras`; missing markers become `ExtractedSlot(found=False)`. This keeps the artifact deterministic regardless of agent behaviour, and is exactly what the evaluator's re-render step expects.

## Modes

| Mode | `Impl/*` code slots | `Proof/` materialized | Agent fills |
|---|---|---|---|
| `proof` | reference impl | per spec: `prove_<S>`, `disprove_<S>` | one of each pair; other stays `sorry` |
| `codeproof` | `sorry` | per spec: `prove_<S>`, `unsat_<S>`, `sat_<S>` + `Proof/Joint.lean` | implementations **and** one proof stub per spec (+ optional joint) |

`sat_<S>` only scores when paired with a verified joint-unsat claim — see `vero.evaluation`'s grader. Lone `sat_<S>` is treated as `unpaired_sat` (not passed).

## Modules

| File | Responsibility |
|---|---|
| `benchmark.py` | Typed loader for `manifest.json`; enumerates modules, APIs, specs, expected paths. |
| `proof_materialize.py` | Pure-Python emitter for `<Project>/Proof/<Module>.lean` per mode (+ `Proof/Joint.lean`). |
| `sandbox.py` | `create_sandbox`: copy + materialize + sorry-out Impl (codeproof) + strip `!curation` + write INSTRUCTION.md. |
| `render.py` | `render_sandbox`: rebuild a fresh sandbox from a source benchmark + artifact. Used by the evaluator; also useful for reproducing a run from JSON. |
| `prompt.py` | Per-mode INSTRUCTION.md Jinja2 template renderer. |
| `extractor.py` | Expected-slot schedule + `extract()`. Produces `Artifact` with `slots`, `extras`, `file_errors`. |
| `agents/base.py` | `Agent` protocol, `BaseAgent` (lifecycle + timeout + `run_start`/`run_end` + error wrap), `AgentResult`, `create_agent` factory. |
| `agents/event_log.py` | `EventLogger` — canonical JSONL stream + readable mirror. Shared by every backend. |
| `agents/claude.py` | `ClaudeAgent` — drives `claude_agent_sdk.query()`. Routes thinking / text / tool_use / tool_result through the logger. |
| `agents/codex.py` | `CodexAgent` — spawns `codex exec --json`. Per-run `$sandbox/.codex_home/` so user's `~/.codex/` is untouched. Maps `item.{started,completed}` event kinds onto the shared logger. |
| `runner.py` | `run_generation(...)`: sandbox → agent → extract. Called by `vero.cli_dispatch`. |

The CLI lives at `src/vero/{cli,cli_dispatch}.py`; config defaults in `conf/{run,benchmark,agent}/*.yaml`. See the tutorial.

## Credentials

All credential env vars live in `.env` at the repo root; the CLI loads them via `python-dotenv` before the agent runs.

- **Claude** — `CLAUDE_AGENT_API_KEY` (used in place of `ANTHROPIC_API_KEY` for the subprocess), optionally `CLAUDE_AGENT_API_BASE` for a proxy.
- **Codex** — resolves creds from the environment with a fallback chain so `.env` (loaded by the CLI via `python-dotenv`) just works without caller-side exports:
  - `api_key`: `CODEX_AGENT_API_KEY` → `LLM_API_KEY` → `OPENAI_API_KEY`
  - `base_url`: `CODEX_AGENT_BASE_URL` → `LLM_API_BASE`

  The resolved key is written into per-run `$sandbox/.codex_home/auth.json` **and** injected into the codex subprocess env as `CODEX_API_KEY` + `OPENAI_API_KEY` (the latter matches the `env_key` our `config.toml` points at for the custom LiteLLM provider). If a `base_url` is resolved, `config.toml` gets an `openai_base_url` + `[model_providers.openai_http]` block. The user's `~/.codex/` is never modified. `CODEX_AGENT_*` remain available as explicit overrides when codex should use different creds than the rest of the pipeline.

The CLI itself scrubs `CLAUDE_CODE_*` env vars from `os.environ` before invoking a claude agent so the CLI can be called from inside an active Claude Code session.

## Troubleshooting

- Agent ran but eval shows `build_error` for every spec in a module: that module's proof file didn't compile; the cascade is expected within a module. Per-module axiom checks isolate healthy modules elsewhere.
- Agent ran but `passed_specs=0, unpaired_sat_specs=N`: the agent took the `sat_<S>` shortcut. The prompt forbids this and the grader rejects it. Inspect the agent's `agent.log` to confirm it saw the current INSTRUCTION.md.
- Codex auth returns 401 from a LiteLLM proxy: check that `config.toml` includes `env_key = "OPENAI_API_KEY"` in the `[model_providers.openai_http]` block. Without it codex never attaches an Authorization header.
