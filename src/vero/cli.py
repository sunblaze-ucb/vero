"""Single entry point for the gen/eval pipeline: ``vero run``.

Drives the full flow from one hydra-composed config. Behavior is
controlled by stage-toggle flags (``skip_agent``, ``skip_gen``,
``skip_eval``) rather than subcommands, so the command surface is small
and the config is the single source of truth.

Typical invocations::

    vero run                                                   # defaults
    vero run benchmark=tiny_unsat mode=codeproof
    vero run benchmark=bankledger agent=codex skip_agent=true  # materialize only
    vero run run=<prior-run-name> eval.name=retry-longer \\
                 eval.timeout=1200                                # re-eval

See ``conf/run.yaml`` for the config surface.
"""

from __future__ import annotations

import json
import os
import shutil
import subprocess
import sys
from datetime import datetime
from pathlib import Path
from typing import Any

import hydra
from dotenv import load_dotenv
from loguru import logger
from omegaconf import DictConfig, OmegaConf

REPO_ROOT = Path(__file__).resolve().parent.parent.parent


def _find_env_file() -> Path | None:
    """Locate the right ``.env`` for credential loading.

    Searches in order:

    1. ``$VERO_ENV_FILE`` if set (explicit override).
    2. ``REPO_ROOT/.env`` — the worktree's own ``.env``.
    3. The git common-dir's parent — when running inside a worktree, this is
       the upstream repo root, where the curator's main ``.env`` typically
       lives. Falling back here lets ``vero run`` work in any worktree
       without copying ``.env`` around.

    Returns the resolved path or ``None`` if nothing is found.
    """
    explicit = os.environ.get("VERO_ENV_FILE")
    if explicit:
        p = Path(explicit).expanduser()
        if p.is_file():
            return p
    primary = REPO_ROOT / ".env"
    if primary.is_file():
        return primary
    # git worktree fallback: look up the .git file (it's a regular file in a
    # worktree, pointing at the common dir) and follow it back to the upstream
    # repo's root.
    git_marker = REPO_ROOT / ".git"
    if git_marker.is_file():
        try:
            text = git_marker.read_text(encoding="utf-8").strip()
            if text.startswith("gitdir:"):
                gitdir = Path(text.split(":", 1)[1].strip())
                # gitdir typically looks like
                # `/path/to/main/.git/worktrees/<name>`; the upstream repo
                # root is two parents up.
                upstream_root = gitdir.parent.parent.parent
                candidate = upstream_root / ".env"
                if candidate.is_file():
                    return candidate
        except OSError:
            pass
    return None


# ─── path helpers ──────────────────────────────────────────────────


def _resolve_under_repo(p: str | Path) -> Path:
    """Resolve a possibly-relative path against the repo root."""
    q = Path(p)
    return q if q.is_absolute() else (REPO_ROOT / q).resolve()


def _find_run_yaml(root: str, name: str) -> Path:
    """Locate ``<root>/<name>/run.yaml`` or fall back to saved_agent_runs/."""
    primary = _resolve_under_repo(root) / name / "run.yaml"
    if primary.is_file():
        return primary
    fallback = REPO_ROOT / "saved_agent_runs" / name / "run.yaml"
    if fallback.is_file():
        return fallback
    raise FileNotFoundError(f"run '{name}' not found: checked {primary} and {fallback}")


# ─── naming / manifest ─────────────────────────────────────────────


def _auto_name(cfg: DictConfig) -> str:
    ts = datetime.now().strftime("%Y%m%d-%H%M%S")
    return f"{cfg.benchmark.id}-{cfg.agent.kind}-{cfg.mode}-{ts}"


def _git_sha() -> str | None:
    try:
        out = subprocess.check_output(
            ["git", "-C", str(REPO_ROOT), "rev-parse", "HEAD"],
            stderr=subprocess.DEVNULL,
        )
        return out.decode().strip()
    except (subprocess.CalledProcessError, FileNotFoundError):
        return None


def _env_fingerprint(cfg: DictConfig) -> dict[str, Any]:
    info: dict[str, Any] = {
        "python": sys.version.split()[0],
        "platform": sys.platform,
    }
    if cfg.agent.kind == "codex":
        info["codex_binary"] = shutil.which("codex")
    if cfg.agent.kind == "gemini":
        info["gemini_binary"] = shutil.which("gemini")
    if cfg.agent.kind == "gauss":
        info["gauss_binary"] = shutil.which("gauss")
        backend = cfg.agent.get("backend", "claude-code")
        info["gauss_backend"] = backend
        info["gauss_backend_binary"] = shutil.which(
            "claude" if backend == "claude-code" else "codex"
        )
    return info


def _write_run_yaml(cfg: DictConfig, run_root: Path) -> Path:
    """Freeze the fully-resolved config to ``<run_root>/run.yaml``."""
    run_root.mkdir(parents=True, exist_ok=True)
    path = run_root / "run.yaml"
    # resolve=True expands interpolations so a later session can replay.
    text = OmegaConf.to_yaml(cfg, resolve=True)
    path.write_text(text, encoding="utf-8")
    return path


def _write_manifest(
    cfg: DictConfig, run_root: Path, artifact_path: Path | None = None
) -> Path:
    manifest = {
        "name": cfg.name,
        "benchmark_id": cfg.benchmark.id,
        "benchmark_path": str(_resolve_under_repo(cfg.benchmark.path)),
        "mode": cfg.mode,
        "agent": {"kind": cfg.agent.kind, "model": cfg.agent.get("model")},
        "created_at": datetime.now().isoformat(timespec="seconds"),
        "git_sha": _git_sha(),
        "env": _env_fingerprint(cfg),
        "artifact_path": (
            str(artifact_path.relative_to(run_root)) if artifact_path else None
        ),
    }
    path = run_root / "manifest.json"
    path.write_text(json.dumps(manifest, indent=2), encoding="utf-8")
    return path


# ─── re-eval: merge the frozen run on top ──────────────────────────

_REEVAL_OPERATIONAL_FIELDS = (
    "skip_gen",
    "skip_agent",
    "skip_eval",
    "overwrite",
    "root",
)


def _merge_frozen_run(cfg: DictConfig) -> DictConfig:
    """Use the frozen run.yaml as the base for a re-eval, then overlay
    only the fields a re-eval is allowed to change.

    Semantics for re-eval (``run=<name>`` set):

    - ``benchmark``, ``agent``, ``mode``, ``name`` come from the frozen
      config — a re-eval targets the same artifact, same mode.
    - ``eval.*`` comes from the current invocation (that's the point of
      re-eval: new timeout, new eval.name, etc).
    - Operational toggles (``skip_*``, ``overwrite``, ``root``) come
      from the current invocation.
    """
    run_path = _find_run_yaml(cfg.root, cfg.run)
    frozen = OmegaConf.load(run_path)
    frozen.pop("hydra", None)
    logger.info("merging frozen run config from {}", run_path)

    merged = OmegaConf.create(frozen)
    merged.run = cfg.run
    merged.name = cfg.run
    for field in _REEVAL_OPERATIONAL_FIELDS:
        merged[field] = cfg[field]
    merged.eval = OmegaConf.merge(merged.eval, cfg.eval)
    return merged


# ─── env preflight ─────────────────────────────────────────────────

_CLAUDE_CODE_ENV_VARS = (
    "CLAUDECODE",
    "CLAUDE_CODE_ENTRYPOINT",
    "CLAUDE_CODE_SSE_PORT",
    "CLAUDE_CODE_EXECPATH",
)


def _strip_claude_code_env(cfg: DictConfig) -> None:
    """Remove ``CLAUDE_CODE_*`` env vars so the claude CLI subprocess
    (spawned by ``claude_agent_sdk`` or by gauss's claude-code backend)
    doesn't refuse to launch inside an active Claude Code session.

    The SDK's subprocess transport
    (``claude_agent_sdk._internal.transport.subprocess_cli``) copies
    ``os.environ`` at ``open_process()`` time, so popping in-process
    here propagates to the subprocess. No re-exec needed.
    """
    if cfg.skip_agent or cfg.skip_gen:
        return
    # Both the claude backend and a gauss run with backend=claude-code
    # end up spawning a nested claude CLI.
    needs_scrub = cfg.agent.kind == "claude" or (
        cfg.agent.kind == "gauss"
        and cfg.agent.get("backend", "claude-code") == "claude-code"
    )
    if not needs_scrub:
        return
    leaked = [k for k in _CLAUDE_CODE_ENV_VARS if k in os.environ]
    if not leaked:
        return
    for k in leaked:
        os.environ.pop(k, None)
    logger.warning(
        "Unset Claude Code env vars ({}) for the nested claude subprocess.",
        ", ".join(leaked),
    )


def _preflight(cfg: DictConfig) -> None:
    if cfg.agent.kind == "codex" and shutil.which("codex") is None:
        raise SystemExit(
            "agent.kind=codex but `codex` binary not found in PATH. "
            "Install codex-cli (https://github.com/codex-cli/codex) first."
        )
    if cfg.agent.kind == "gemini" and shutil.which("gemini") is None:
        raise SystemExit(
            "agent.kind=gemini but `gemini` binary not found in PATH. "
            "Install gemini-cli (https://github.com/google-gemini/gemini-cli) first."
        )
    if cfg.agent.kind == "gauss":
        if shutil.which("gauss") is None:
            raise SystemExit(
                "agent.kind=gauss but `gauss` binary not found in PATH. "
                "Install from https://github.com/math-inc/OpenGauss first."
            )
        backend = cfg.agent.get("backend", "claude-code")
        backend_bin = "claude" if backend == "claude-code" else "codex"
        if shutil.which(backend_bin) is None:
            raise SystemExit(
                f"agent.kind=gauss backend={backend!r} requires "
                f"`{backend_bin}` on PATH."
            )


# ─── validation ───────────────────────────────────────────────────


def _validate(cfg: DictConfig) -> None:
    if cfg.mode not in ("proof", "codeproof"):
        raise SystemExit(f"mode must be 'proof' or 'codeproof', got {cfg.mode!r}")
    if cfg.skip_gen and not cfg.run:
        raise SystemExit("skip_gen=true requires run=<name> to locate the prior run")
    if cfg.skip_gen and cfg.skip_agent:
        raise SystemExit(
            "skip_gen and skip_agent both true — there's nothing to skip "
            "skip_agent from. Pick one."
        )
    if cfg.skip_gen and cfg.skip_eval:
        raise SystemExit("skip_gen and skip_eval both true — nothing to do.")


# ─── main ──────────────────────────────────────────────────────────

_CONF_DIR = str((REPO_ROOT / "conf").resolve())


@hydra.main(version_base=None, config_path=_CONF_DIR, config_name="run")
def _hydra_main(cfg: DictConfig) -> int:
    env_path = _find_env_file()
    if env_path is not None:
        load_dotenv(env_path, override=False)
        logger.info("loaded credentials from {}", env_path)
    else:
        logger.warning(
            "no .env found at REPO_ROOT or upstream worktree root; agent "
            "credentials must be in the calling shell environment"
        )

    # Ergonomic: `run=<name>` alone means "re-eval this run" → default skip_gen.
    if cfg.run and not cfg.skip_gen and not cfg.skip_agent and not cfg.skip_eval:
        logger.info("run={} set with no stage flags — implying skip_gen=true", cfg.run)
        cfg.skip_gen = True

    if cfg.run:
        cfg = _merge_frozen_run(cfg)

    _validate(cfg)

    if cfg.name is None:
        cfg.name = _auto_name(cfg)

    _preflight(cfg)
    _strip_claude_code_env(cfg)

    run_root = _resolve_under_repo(cfg.root) / cfg.name
    logger.info("run root: {}", run_root)

    if run_root.exists() and not cfg.overwrite and not cfg.skip_gen:
        raise SystemExit(
            f"run root {run_root} already exists; pass overwrite=true to replace "
            f"(or pick a different name=)."
        )

    # Dispatch. Deliberately imported late so `--help` is fast.
    # `run.yaml` + `manifest.json` describe the ORIGINAL gen invocation and
    # are written only when generation runs. Re-eval doesn't touch them —
    # per-eval metadata goes into ``eval/<eval-name>/eval.manifest.json``.
    # Dispatch path forks on iteration config. Single-shot (identical to
    # pre-iteration behaviour) applies ONLY when there is neither a retry loop
    # (iterate.max == 0) NOR time-chunking configured. Chunking must still take
    # the harness even at max=0 — one iteration that checkpoints in chunks.
    iterate_max = int(cfg.iterate.max) if "iterate" in cfg else 0
    chunking = (
        "iterate" in cfg
        and cfg.iterate.get("iteration_time_chunk_seconds", None) is not None
    )
    # Sampled eval: one uninterrupted agent run with a passive perf sampler,
    # graded post-hoc. Supersedes chunking as the perf-vs-time mechanism.
    # Enabled by `eval.sampled=true`.
    sampling = bool(cfg.eval.get("sampled", False))
    if iterate_max > 0 or chunking or sampling:
        if cfg.skip_gen:
            raise SystemExit(
                "skip_gen=true is incompatible with iterate.max>0 / chunking — "
                "there is nothing to iterate on. Either drop skip_gen "
                "or set iterate=off."
            )
        _write_run_yaml(cfg, run_root)
        from vero.cli_iterate import iterate_run

        iterate_run(cfg, run_root)
    else:
        if not cfg.skip_gen:
            _write_run_yaml(cfg, run_root)
            from vero.cli_dispatch import dispatch_generation

            gen_result = dispatch_generation(cfg, run_root)
            _write_manifest(cfg, run_root, artifact_path=gen_result.artifact_path)

        if not cfg.skip_eval:
            from vero.cli_dispatch import dispatch_evaluation

            dispatch_evaluation(cfg, run_root)

    logger.info("done: {}", run_root)
    return 0


def main() -> int:
    """Console-script entry point.

    The user-facing command is ``vero run ...``. Since there's only
    one subcommand we don't wire in argparse — we simply strip the
    ``run`` token before handing off to hydra so it's not mistaken for
    a config override. Hydra-specific flags (``--help``, ``--cfg``,
    ``-c``, ``--multirun``) and config overrides (``key=value``) all
    continue to work unchanged.
    """
    if len(sys.argv) > 1 and sys.argv[1] == "run":
        sys.argv.pop(1)
    return _hydra_main()


if __name__ == "__main__":
    sys.exit(main())
