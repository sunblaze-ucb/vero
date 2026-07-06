"""PYTHON_ADJUST_BODIES stage — fill mode-A scaffold Impl bodies from Python source.

Phase 2 of the ``python_from_benchmark_json`` (mode A) workflow. Phase 1
(``PythonFromJsonStage``) emits ``Impl/<File>.lean`` with API signatures
and ``sorry`` bodies inside ``!benchmark @start code def=<name>`` markers.
This stage walks each Impl file, locates the matching Python source under
``<task_dir>/<python_context_path>/``, and asks an agent to translate the
Python ``def`` body into Lean inside the same marker.

The stage is **single-agent** (not orchestrated): mode-A repos are typically
1–7 modules, and the orchestrator's executor-pool overhead is wasted at
that scale. Falls back to a no-op (success) when no ``sorry`` bodies remain
in code markers — i.e. the stage is idempotent on a filled project.

Skill: ``vero-source-python`` + ``vero-translate`` (loaded via the Skill tool).
"""

from __future__ import annotations

import json
import re
from pathlib import Path

import anyio

from vero.curation.lean_project import to_project_name
from vero.curation.stages._skill_preamble import skill_preamble
from vero.curation.stages.base import (
    StageContext,
    StageResult,
    StageRunner,
    compose_prompt,
)

_BUILD_TIMEOUT_SECONDS = 300

# Matches a `!benchmark @start code def=<name>` ... `@end code def=<name>`
# block whose interior is exactly `sorry` (with optional leading whitespace).
# This is the marker shape emitted by PythonFromJsonStage.
_EMPTY_CODE_BLOCK_RE = re.compile(
    r"!benchmark @start code def=(?P<name>[A-Za-z_][\w]*)\s*\n"
    r"(?P<body>\s*sorry\s*\n)"
    r"-- !benchmark @end code def=(?P=name)",
)


def _resolve_python_source_dir(ctx: StageContext) -> Path:
    """Derive the absolute path to the python source directory.

    Mirrors the logic in ``PythonFromJsonStage`` (see ``python_from_json.py``):
    ``<source_dir>/<python_context_path>`` where ``python_context_path`` is
    pulled from ``benchmark.json::metadata.python_context_path`` (fallback
    ``"original_python"``). The benchmark.json itself sits at
    ``<source_dir>/benchmark.json``.
    """
    benchmark_json = ctx.source_dir / "benchmark.json"
    python_context_path = "original_python"
    if benchmark_json.exists():
        try:
            data = json.loads(benchmark_json.read_text(encoding="utf-8"))
            python_context_path = (
                data.get("metadata", {}).get("python_context_path") or "original_python"
            )
        except (json.JSONDecodeError, OSError):
            pass
    return ctx.source_dir / python_context_path


def _read_root_package(lake_root: Path) -> str | None:
    """Read ``manifest.json::root_package``.

    The manifest is the authoritative package-name source — `to_project_name`
    on the config's benchmark_id is a fallback when the manifest is absent.
    """
    manifest_path = lake_root / "manifest.json"
    if not manifest_path.exists():
        return None
    try:
        data = json.loads(manifest_path.read_text(encoding="utf-8"))
    except (json.JSONDecodeError, OSError):
        return None
    pkg = data.get("root_package")
    if isinstance(pkg, str) and pkg:
        return pkg
    return None


def count_unfilled_code_bodies(lake_root: Path) -> int:
    """Count ``!benchmark code def=…`` blocks whose body is still ``sorry``.

    ``lake_root`` is the lake project root (the dir holding ``manifest.json``
    + ``lakefile.toml``, matching the canonical ``reference/BankLedger/``
    layout). The package source tree sits at ``<lake_root>/<Package>/``,
    where ``<Package>`` comes from ``manifest.json::root_package``.
    """
    pkg = _read_root_package(lake_root)
    if pkg is None:
        return 0
    impl_root = lake_root / pkg / "Impl"
    if not impl_root.exists():
        return 0
    total = 0
    for lean_file in impl_root.rglob("*.lean"):
        text = lean_file.read_text(encoding="utf-8", errors="replace")
        total += len(_EMPTY_CODE_BLOCK_RE.findall(text))
    return total


class PythonAdjustBodiesStage(StageRunner):
    """Fill mode-A scaffold Impl bodies by translating from Python source."""

    name = "python_adjust_bodies"
    human_review = True

    def _project_dir(self, ctx: StageContext) -> Path:
        """Lake project root — ``lean_output_dir/<Package>/`` (canonical layout)."""
        return ctx.lean_output_dir / to_project_name(ctx.config.benchmark_id)

    def _build_prompt(
        self,
        ctx: StageContext,
        project_dir: Path,
        python_source_dir: Path,
    ) -> str:
        preamble = skill_preamble("translate", ctx.config.source_language)
        body = [
            "## Goal — fill scaffold Impl bodies from Python source",
            "",
            "The mode-A scaffold at the project path below was emitted with",
            "API signatures + `sorry` bodies inside `!benchmark @start code",
            "def=<name>` markers. Replace each `sorry` with a faithful Lean",
            "translation of the matching Python `def` body.",
            "",
            "## Inputs",
            "",
            f"- **Lean scaffold**: `{project_dir}/`",
            "  - Impl files at `<Project>/Impl/<Module>.lean` carry sigs +",
            "    sorry bodies inside `!benchmark code def=<name>` markers.",
            "  - Spec files are empty scaffolds — DO NOT touch in this stage,",
            "    `spec_write` runs next.",
            "  - `manifest.json` lists every `(module, api_name, sig, type)`",
            "    triple — read-only reference.",
            f"- **Python source**: `{python_source_dir}/`",
            "  - One `.py` per module, mirrors the Impl/ layout (see",
            "    `manifest.packages[].modules[].source_path` if present, or",
            "    match by snake_case name otherwise).",
            "",
            "## Hard rules",
            "",
            "1. Edit ONLY inside `!benchmark @start code def=X` ... `!benchmark",
            "   @end code def=X` markers. Do NOT change sigs, abbrevs, marker",
            "   keys, namespaces, or any line outside the marker interior.",
            "2. The body must be a faithful translation of the Python source —",
            "   same semantics, same edge cases, same input/output. When the",
            "   Python imports an external lib already modeled as `opaque` in",
            "   `global_aux` (e.g. `math.sqrt`), call that opaque.",
            "3. `partial def` is allowed when termination isn't obvious from",
            "   the Lean kernel; annotate with",
            "   `-- @review human: termination via <reason>`.",
            "4. After every Impl is filled, lift `Test.lean`'s",
            "   `/- BY curator -/` ... `-/` wrapper so its `#guard` lines",
            "   become active. (The wrapper hint says the same thing.)",
            "5. Spec files stay frozen — no edits to `<Project>/Spec/*.lean`",
            "   or to `manifest.json`'s `specs[]` lists.",
            "6. `lake build` from `{project_dir}` must pass with only the",
            "   expected `sorry` warnings dropped to zero.",
            "",
            "## Verify before declaring done",
            "",
            f"1. `cd {project_dir} && lake build` — exits 0, no `sorry` warnings",
            "   on filled API defs (warnings on `Spec/*.lean` are expected;",
            "   those are filled by the next stage).",
            "2. Every `!benchmark @start code def=<name>` block has a non-`sorry`",
            "   body. Use `grep -nE 'def=([A-Za-z_]+)' Impl/*.lean` cross-checked",
            "   against the immediately following body line.",
            "",
            "## Approach",
            "",
            "Recommended: process one module at a time, file by file.",
            "After each module, run `lake build <Project>.Impl.<Module>` to",
            "catch type errors early. When a translation needs a helper",
            "(e.g. integer-square-root), put it in `code_aux def=<name>` for",
            "that API or in `global_aux` for module-shared helpers.",
        ]
        return compose_prompt(
            preamble,
            body,
            ctx,
            guidance_header="## Human Guidance",
        )

    async def run(self, ctx: StageContext) -> StageResult:
        project_dir = self._project_dir(ctx)
        if not project_dir.exists():
            return StageResult(
                stage=self.name,
                success=False,
                error=(
                    f"Lean project not found at {project_dir}. "
                    "Run python-from-json (scaffolder) first."
                ),
            )

        python_source_dir = _resolve_python_source_dir(ctx)
        if not python_source_dir.exists():
            return StageResult(
                stage=self.name,
                success=False,
                error=(
                    f"Python source dir not found at {python_source_dir}. "
                    "Expected <source_dir>/<python_context_path>/ "
                    "(benchmark.json::metadata.python_context_path or "
                    "default 'original_python')."
                ),
            )

        # Idempotent skip: nothing to fill.
        remaining = count_unfilled_code_bodies(project_dir)
        if remaining == 0:
            return StageResult(
                stage=self.name,
                success=True,
                output_files=[str(project_dir)],
                human_review_required=False,
            )

        from vero.curation.agent import call_agent

        prompt = self._build_prompt(ctx, project_dir, python_source_dir)
        max_turns = getattr(
            ctx.config, "max_turns_python_adjust", ctx.config.max_turns_translate
        )
        _, session_id = await call_agent(
            model=ctx.config.model,
            permission_mode=ctx.config.permission_mode,
            prompt=prompt,
            tools=["Read", "Write", "Edit", "Bash", "Grep", "Glob"],
            max_turns=max_turns,
            resume_session_id=ctx.resume_session_id,
            api_key=ctx.config.api_key,
            api_base_url=ctx.config.api_base_url,
            **ctx.config.agent_kwargs,
        )

        build_ok, build_output = await _run_lake_build(project_dir)
        package = _read_root_package(project_dir) or to_project_name(
            ctx.config.benchmark_id
        )
        impl_root = project_dir / package / "Impl" if package else None
        impl_files = (
            sorted(str(p) for p in impl_root.rglob("*.lean"))
            if impl_root is not None and impl_root.exists()
            else []
        )

        if not build_ok:
            return StageResult(
                stage=self.name,
                success=False,
                error=f"lake build failed after python_adjust_bodies:\n{build_output[-1500:]}",
                output_files=impl_files,
                human_review_required=True,
                human_review_instructions=(
                    f"Build failed at {project_dir}. Inspect Impl/*.lean and "
                    "re-run with `--stage python_adjust_bodies --force` (or "
                    "`--continue` to resume the agent session)."
                ),
                session_id=session_id or "",
            )

        # Build OK — but also verify all code-block bodies are non-sorry.
        remaining_after = count_unfilled_code_bodies(project_dir)
        if remaining_after > 0:
            return StageResult(
                stage=self.name,
                success=False,
                error=(
                    f"build OK but {remaining_after} `!benchmark code def=…` "
                    "blocks still contain `sorry`. Agent left work undone."
                ),
                output_files=impl_files,
                human_review_required=True,
                human_review_instructions=(
                    "Re-run with `--stage python_adjust_bodies --force` to "
                    "continue filling, or `--continue` to resume the session."
                ),
                session_id=session_id or "",
            )

        return StageResult(
            stage=self.name,
            success=True,
            output_files=impl_files,
            human_review_required=True,
            human_review_instructions=(
                f"Impl bodies filled at {project_dir}. Inspect a sample, then "
                "run `--stage spec_write` to author specs."
            ),
            session_id=session_id or "",
        )


async def _run_lake_build(project_dir: Path) -> tuple[bool, str]:
    try:
        with anyio.fail_after(_BUILD_TIMEOUT_SECONDS):
            proc = await anyio.run_process(
                ["lake", "build"],
                cwd=project_dir,
                check=False,
            )
    except TimeoutError:
        return False, f"lake build timed out after {_BUILD_TIMEOUT_SECONDS}s"
    stdout = proc.stdout.decode("utf-8", errors="replace") if proc.stdout else ""
    stderr = proc.stderr.decode("utf-8", errors="replace") if proc.stderr else ""
    return proc.returncode == 0, stderr or stdout
