# vero

Benchmark for library-level formal code generation. Three phases: **Curation** (upstream Dafny/Verus/Coq → Lean 4 projects with `!benchmark` slots) · **Generation** (LLM fills the slots in a sandbox, emits `artifact.json`) · **Evaluation** (grader re-renders a fresh sandbox from the artifact and scores it).

Entry points:
- `python -m vero.curation …` — curation pipeline (`src/vero/curation/README.md`).
- `vero run …` — unified gen/eval CLI (`docs/gen-eval-tutorial.md`).

Ongoing history and decisions belong in `WORKLOG.md`, active tasks in `TODO.md`, and per-feature plans in `plan/` (all start empty in the public release and are filled as work proceeds). The content below is the prescriptive *how-to-work-here* ruleset.

## Working Conventions

> **These conventions are mandatory.** Before starting any non-trivial task: (1) read `TODO.md` and `WORKLOG.md`, (2) confirm the target branch with the user, (3) write a `plan/` file. Skip a step only when the user explicitly says so.

### Branch Discipline

**Do not commit directly to `main` unless the user explicitly asks.** Always work on a feature branch.

Before touching code:
1. Propose a branch name to the user (e.g. `<user>/<short-desc>` or `feat/<short-desc>`) and wait for confirmation.
2. `git switch -c <branch-name>`.
3. Do the work there. Land on `main` via PR / merge after explicit user approval.

Exceptions (direct work on `main` is OK only when the user says so): trivial cleanups the user has greenlit, hotfixes they've requested, or explicit "work on main" instructions.

### Push Discipline

**Never push to a remote without the user's explicit confirmation.** This covers the initial `git push -u` of a new branch, subsequent normal pushes, and any form of force-push (`--force`, `--force-with-lease`). Commits can be amended, branches rewritten, or commits reverted cheaply while everything stays local; once pushed, options shrink (teammates pull, CI triggers, history rewrites require coordination).

- Prepare the push locally and show the user what you're about to push.
- Wait for explicit "push it" / "yes push" before running `git push`.
- For force-push to `main`/`master`, confirm twice: once that a force-push is acceptable, once that the blast radius is understood.

### Working Memory

Three files act as shared memory across sessions and subagents:

| File | Purpose |
|---|---|
| `TODO.md` | Active tasks and issues — **consult before and update after any work** |
| `plan/YYYYMMDD-HHMMSS-<desc>.md` | Timestamped plan — **required before touching code on any non-trivial task** |
| `WORKLOG.md` | Shared dated worklog — descriptive history (decisions, things tried, breaking changes). **Read at task start; append a dated entry when you land something non-trivial.** |

- **TODO.md**: short entries only; link to plan files for detail; delete resolved items promptly.
- **plan/**: create before touching code; detail approach, steps, open questions.
- **WORKLOG.md**: newest entry at top, one dated section per day; delete obsolete bullets rather than keeping stale notes; not for task tracking (use TODO.md), prescriptive rules (belong here), or per-user preferences (use `~/.claude/…` auto-memory). When you finish a non-trivial task, append one or two bullets summarising what changed and why — think commit-log-sized.

### Prose formatting

**Do not hard-wrap prose at a column width.** When writing long-form text — markdown files (README/docs/templates), commit messages, PR descriptions, multi-line docstrings — break at natural units (paragraph, sentence, list item) and let the renderer reflow. Hard-wrapping at 72/80 cols produces awkward line breaks that rot as content shifts.

Applies to all prose in this repo. Exception: source-code inline comments and very short inline snippets where a visual column limit aids scanning.

### Git Worktrees

Default is to `git switch` between branches in-place. Reach for a worktree only when:
- **Dispatching a subagent** for autonomous work that must not collide with the main agent's working tree.
- **Running parallel branches** (e.g. comparing two approaches side by side) where stashing wouldn't cut it.
- **Temporary exploration** the main agent will discard.

```bash
git worktree add .claude/worktrees/<branch-name> -b <branch-name>
```

Worktrees live in `.claude/worktrees/` (gitignored). Clean them up (`git worktree remove`) when the parallel work is done.

## Setup

```bash
uv sync && source .venv/bin/activate
```

Lint / format check before committing:

```bash
uv run ruff check
uv run ruff format --check
```

## Living Contract

The ratified benchmark shape lives in `reference/BankLedger/` — treat it as the canonical exemplar. When changing conventions (markers, manifest shape, `RepoImpl` shape), update `reference/BankLedger/` first; it drives the curation skills and validator. Artifact schemas in `docs/pipeline-schema.md`.
