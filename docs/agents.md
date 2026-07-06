# Agents and credentials

This explains how to give vero an agent, wire up API credentials, and plug in your own agent. To run an existing agent you only need [section 1, Credentials](#1-credentials) and [section 2, Built-in agents](#2-built-in-agents). [Section 3](#3-bring-your-own-agent) covers integrating a new one.

## How an agent fits in (read this first)

vero owns the whole harness, and an agent is a small, replaceable part. For each run, vero does four things.

1. **Renders a sandbox.** vero writes a fresh, self-contained Lean 4 project to `agent_runs/<run>/source/`, with the frozen files in place, the slots you must fill marked by `!benchmark @start … @end`, and an `INSTRUCTION.md` describing the task.
2. **Hands the sandbox to the agent.** The agent's entire job is to edit the marked slot bodies inside that directory, using whatever Lean tooling it likes (`lake build`, an LSP, search).
3. **Extracts an artifact.** vero parses the edited sandbox back into a deterministic `artifact.json`, one entry per expected slot.
4. **Re-renders a clean sandbox and grades.** The grader rebuilds a fresh project from the source benchmark, overlays only the agent's slot bodies, compiles it with Lake, and checks each spec's axioms.

The agent never parses the benchmark format and never calls render, extract, or grade. vero does all of that. Because grading re-renders from the source benchmark and keeps only your slot bodies, editing a frozen file, injecting a custom axiom, or adding a trivializing typeclass instance cannot change your score, since it is discarded or flagged. An agent is therefore safe to let loose inside the sandbox, and the worst it can do is fail to fill a slot.

## 1. Credentials

Credentials live in a `.env` file at the repo root. Copy `.env.example` to `.env` and edit it. vero loads the file with `python-dotenv` before launching the agent, so no shell exports are needed.

Which variables are read depends on the credentials profile, selected with `credentials=<profile>` on the command line (the default is `litellm`). Profiles are Hydra configs under `conf/credentials/`.

| Profile (`credentials=`) | Reads from `.env` | Use when |
|---|---|---|
| `litellm` *(default)* | `LLM_API_KEY`, `LLM_API_BASE` (feed both agents), plus optional per-agent `CLAUDE_AGENT_*` and `CODEX_AGENT_*` overrides | You route everything through one LiteLLM-style proxy. |
| `anthropic` | `ANTHROPIC_API_KEY` | You talk to `api.anthropic.com` directly (pair with `agent=claude`). |
| `openai` | `OPENAI_API_KEY` | You talk to `api.openai.com` directly (pair with `agent=codex`). |
| `openrouter` | `OPENROUTER_API_KEY`, `OPENROUTER_API_BASE` | You route both agents through OpenRouter. |
| `none` | *(nothing)* | You have hand-configured `~/.claude/` and `~/.codex/` and just want vero to drive the run. |

The profile only injects environment and config into the sandboxed agent process, and never touches your global `~/.claude/` or `~/.codex/`. For example,

```bash
# default (litellm proxy)
vero run benchmark=bankledger agent=codex mode=codeproof

# Anthropic-direct
vero run benchmark=bankledger agent=claude credentials=anthropic
```

## 2. Built-in agents

Select one with `agent=<kind>`. Profiles live in `conf/agent/*.yaml`.

| `agent=` | Backend and transport | Notes |
|---|---|---|
| `claude` | Claude Agent SDK (`claude_agent_sdk.query()`) | Reports `total_cost_usd`, and supports `effort` (reasoning) and `strict_budget_usd`. |
| `codex`  | `codex exec --json` subprocess | Needs the `codex` binary on `$PATH`, and uses a per-run scoped `.codex_home/`. |
| `gemini` | Gemini CLI | Needs the `gemini` CLI on `$PATH`. |
| `gauss`  | Gauss agent (delegates Lean work to a `claude-code` or `codex` backend) | Multi-provider. See `conf/agent/gauss.yaml`. |

Any leaf in the profile is overridable inline.

```bash
vero run agent=claude agent.model=claude-opus-4-8 agent.max_turns=60
vero run agent=codex  agent.model=gpt-5-codex     agent.timeout_seconds=1800
```

To add a profile for an existing backend, drop a file in `conf/agent/`.

```yaml
# conf/agent/claude-opus.yaml
kind: claude          # selects the backend
model: claude-opus-4-8
max_turns: 60
```

Then run `vero run agent=claude-opus …`. The `kind` field picks the backend class, and everything else passes to its constructor.

## 3. Bring your own agent

An agent only needs to edit slot bodies in a sandbox directory. There are two ways to wire that in.

### Option A. A thin adapter (recommended)

Implement one method, and vero runs render, your agent, extract, and grade in a single `vero run agent=<yours>`. Your agent stays completely unaware of the benchmark format.

The contract lives in `src/vero/generation/agents/base.py`.

```python
from pathlib import Path
from vero.generation.agents.base import BaseAgent, RunOutcome
from vero.generation.agents.event_log import EventLogger

class MyAgent(BaseAgent):
    name = "myagent"

    def __init__(self, model=None, timeout_seconds=1800, **kw):
        self.model = model
        self.timeout_seconds = timeout_seconds

    def _run_inner(self, *, event_log: EventLogger,
                   sandbox_dir: Path, instruction_file: Path) -> RunOutcome:
        # Launch YOUR agent against the sandbox. It should read
        # `instruction_file` and edit the `!benchmark @start … @end`
        # slot bodies under `sandbox_dir` in place. Lean tools (lake, LSP)
        # work out of the box inside the sandbox.
        import subprocess
        proc = subprocess.run(
            ["my-agent-cli", "--workdir", str(sandbox_dir),
             "--instructions", str(instruction_file), "--model", self.model or ""],
            capture_output=True, text=True, timeout=self.timeout_seconds,
        )
        # Optionally stream your agent's steps into event_log for replayable logs.
        return RunOutcome(ok=proc.returncode == 0, stderr_tail=proc.stderr[-2000:])
```

Register the backend in `create_agent()` (same file) with a new `kind` branch, add a `conf/agent/myagent.yaml` with `kind: myagent`, and run.

```bash
vero run benchmark=bankledger agent=myagent mode=codeproof
```

`BaseAgent` gives you the lifecycle for free. It validates the instruction file, opens the `agent_events.jsonl` and `agent.log` event stream, emits `run_start` and `run_end`, wraps crashes as `run_error`, and enforces `timeout_seconds`. You return a `RunOutcome`, which is just `ok` plus optional `usage`, `total_cost_usd`, and `error`.

### Option B. Fully decoupled (no vero code)

If your agent cannot be driven from Python, run it against a pre-rendered sandbox, then use `vero-extract` and `vero run` to score it.

```bash
# 1. Render the sandbox only (no agent, no eval).
vero run benchmark=bankledger mode=codeproof skip_agent=true skip_eval=true name=myrun
#    creates agent_runs/myrun/source/  (Lean project + INSTRUCTION.md)

# 2. Point your agent at agent_runs/myrun/source/ and let it edit the
#    !benchmark slot bodies (read source/INSTRUCTION.md for the contract).

# 3. Re-extract what your agent wrote into artifact.json, then grade.
vero-extract --run myrun      # reads the benchmark and mode from the run's run.yaml
vero run run=myrun            # grades the freshly-extracted artifact
```

The `vero-extract` step is required because `vero run run=<name>` grades the stored `source/artifact.json`, which step 1 wrote before your agent edited anything. Option A avoids this, since vero extracts automatically right after your agent finishes. `vero-extract` also accepts an explicit target, as in `vero-extract --sandbox <dir> --benchmark benchmarks/bankledger --mode codeproof`.

## See also

- [`gen-eval-tutorial.md`](gen-eval-tutorial.md) for running gen/eval, modes, output, re-eval, sweeps, and the iteration harness.
- [`../src/vero/generation/README.md`](../src/vero/generation/README.md) for how sandbox rendering, extraction, and the agent protocol work internally.
- [`pipeline-schema.md`](pipeline-schema.md) for the `artifact.json` and `manifest.json` schemas.
