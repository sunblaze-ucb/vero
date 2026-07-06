"""Lake / Lean invocation helpers.

- :func:`lake_build` — blocking ``lake build [target]`` with timeout.
- :func:`lean_run_file` — compile a single ``.lean`` file via ``lake lean`` (participates in Lake's incremental ``.olean`` cache across back-to-back invocations); returns stdout/stderr verbatim.

Both return :class:`LakeResult`. Callers grade based on return code + output parsing. Nothing here interprets semantics beyond exit codes.
"""

from __future__ import annotations

import subprocess
from dataclasses import dataclass
from pathlib import Path


@dataclass
class LakeResult:
    exit_code: int
    stdout: str
    stderr: str
    combined: str  # stdout + stderr (interleaved by design — lake mixes streams)

    @property
    def ok(self) -> bool:
        return self.exit_code == 0


def lake_build(
    sandbox_dir: Path,
    target: str | None = None,
    *,
    timeout: int = 600,
    extra_args: list[str] | None = None,
) -> LakeResult:
    """Run ``lake build [target]`` from ``sandbox_dir``."""
    cmd = ["lake", "build"]
    if target is not None:
        cmd.append(target)
    if extra_args:
        cmd.extend(extra_args)
    return _run(cmd, cwd=sandbox_dir, timeout=timeout)


def lean_run_file(
    sandbox_dir: Path,
    lean_file: Path,
    *,
    timeout: int = 600,
) -> LakeResult:
    """Compile a single file with ``lake lean <path>``.

    Useful for axiom printing / one-off eval checks: ``#print axioms`` output
    lands on stdout. Unlike ``lake env lean``, this participates in Lake's
    incremental build graph so dependencies get cached ``.olean``s across
    back-to-back per-module compiles.
    """
    cmd = ["lake", "lean", str(lean_file)]
    return _run(cmd, cwd=sandbox_dir, timeout=timeout)


def _run(cmd: list[str], *, cwd: Path, timeout: int) -> LakeResult:
    try:
        proc = subprocess.run(
            cmd,
            cwd=str(cwd),
            capture_output=True,
            text=True,
            timeout=timeout,
        )
    except subprocess.TimeoutExpired as e:
        return LakeResult(
            exit_code=124,
            stdout=(e.stdout or "") if isinstance(e.stdout, str) else "",
            stderr=f"TIMEOUT after {timeout}s: {' '.join(cmd)}",
            combined=f"TIMEOUT after {timeout}s: {' '.join(cmd)}",
        )
    combined = (proc.stdout or "") + (proc.stderr or "")
    return LakeResult(
        exit_code=proc.returncode,
        stdout=proc.stdout or "",
        stderr=proc.stderr or "",
        combined=combined,
    )
