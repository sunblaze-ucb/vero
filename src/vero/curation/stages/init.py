"""INIT stage — detect language, create workspace, gather metadata, scaffold Lean project.

Per docs/pipeline-schema.md, INIT writes:
- config.yaml                                   (CurationConfig serialized)
- source_info.md                                (human-readable summary)
- lean_output/<Project>/lakefile.toml          (new top-level-fields form)
- lean_output/<Project>/lean-toolchain         (pinned Lean version)
- lean_output/<Project>/<Project>.lean         (empty root hub)
- lean_output/<Project>/manifest.json          (scaffold with empty packages[])
"""

from __future__ import annotations

import json
import subprocess
from datetime import datetime, timezone
from pathlib import Path

from vero.curation.lean_project import create_lean_project, to_project_name
from vero.curation.models import SourceLanguage
from vero.curation.stages.base import StageContext, StageResult, StageRunner


def detect_language(source_dir: Path) -> SourceLanguage:
    """Detect the source language by file extensions and content markers."""
    dafny_count = len(list(source_dir.rglob("*.dfy")))
    coq_count = len(list(source_dir.rglob("*.v")))
    py_count = len(list(source_dir.rglob("*.py")))
    # Lean-source mode (lean→lean spec extraction): we treat any tree with
    # `*.lean` files but no `lakefile.toml` (so it's not the curation output)
    # as candidate Lean source. Curators can override via `--lang lean` to be
    # explicit.
    lean_count = (
        len(list(source_dir.rglob("*.lean")))
        if not (source_dir / "lakefile.toml").exists()
        else 0
    )
    rs_files = list(source_dir.rglob("*.rs"))

    verus_count = 0
    for f in rs_files[:50]:
        try:
            content = f.read_text(encoding="utf-8", errors="ignore")
            if "verus!" in content or "vstd::" in content:
                verus_count += 1
        except OSError:
            continue

    counts = {
        SourceLanguage.DAFNY: dafny_count,
        SourceLanguage.VERUS: verus_count,
        SourceLanguage.COQ: coq_count,
        SourceLanguage.PYTHON: py_count,
        SourceLanguage.LEAN: lean_count,
    }
    best = max(counts, key=counts.get)
    if counts[best] == 0:
        raise ValueError(
            f"No Dafny (.dfy), Verus (.rs with verus!), Coq (.v), "
            f"Python (.py), or Lean (.lean) source files found in {source_dir}"
        )
    return best


def _git_info(source_dir: Path) -> tuple[str, str]:
    """Return (remote_url, commit_hash) from git, or empty strings."""
    url = ""
    commit = ""
    try:
        result = subprocess.run(
            ["git", "remote", "get-url", "origin"],
            cwd=source_dir,
            capture_output=True,
            text=True,
            timeout=5,
        )
        if result.returncode == 0:
            url = result.stdout.strip()
    except (OSError, subprocess.TimeoutExpired):
        pass
    try:
        result = subprocess.run(
            ["git", "rev-parse", "HEAD"],
            cwd=source_dir,
            capture_output=True,
            text=True,
            timeout=5,
        )
        if result.returncode == 0:
            commit = result.stdout.strip()
    except (OSError, subprocess.TimeoutExpired):
        pass
    return url, commit


def _count_source_files(source_dir: Path, lang: SourceLanguage) -> dict:
    ext_map = {
        SourceLanguage.DAFNY: "*.dfy",
        SourceLanguage.VERUS: "*.rs",
        SourceLanguage.COQ: "*.v",
        SourceLanguage.PYTHON: "*.py",
        SourceLanguage.LEAN: "*.lean",
    }
    files = list(source_dir.rglob(ext_map[lang]))
    total_lines = 0
    for f in files:
        try:
            total_lines += len(
                f.read_text(encoding="utf-8", errors="ignore").splitlines()
            )
        except OSError:
            continue
    return {"file_count": len(files), "total_lines": total_lines}


def _manifest_scaffold(
    *,
    benchmark_id: str,
    project_name: str,
    lean_version: str,
    source_language: str | None,
    repo_url: str,
    commit_hash: str,
    source_subdir: str,
) -> dict:
    """Return a minimal manifest.json scaffold per docs/pipeline-schema.md.

    ``packages`` starts empty; translate stage fills it after emitting
    Impl/Spec/Harness/Bundle files. ``files`` points at the expected
    benchmark-singleton paths so downstream tooling can resolve them even
    before translate runs (paths will exist by end of translate).
    """
    kind = "translated" if source_language else "hand-crafted"
    return {
        "benchmark_id": benchmark_id,
        "description": None,
        "lean_version": lean_version,
        "modes_supported": ["proof", "codeproof"],
        "source": {
            "kind": kind,
            "language": source_language,
            "repo_url": repo_url or None,
            "commit_hash": commit_hash or None,
            "path": source_subdir or "." if source_language else None,
        },
        "curation": {
            "date": datetime.now(timezone.utc).date().isoformat(),
        },
        "root_package": project_name,
        "files": {
            "root_hub": f"{project_name}.lean",
            "harness": f"{project_name}/Harness.lean",
            "test": f"{project_name}/Test.lean",
            "lakefile": "lakefile.toml",
        },
        "packages": [],
    }


class InitStage(StageRunner):
    name = "init"
    human_review = False

    async def run(self, ctx: StageContext) -> StageResult:
        config = ctx.config
        source_dir = ctx.source_dir
        repo_root = ctx.repo_root

        if not source_dir.exists():
            return StageResult(
                stage=self.name,
                success=False,
                error=f"Source directory does not exist: {source_dir}",
            )

        if config.source_language is None:
            config.source_language = detect_language(source_dir)

        url, commit = _git_info(repo_root)
        config.repo_url = url
        config.commit_hash = commit

        if not config.benchmark_id:
            config.benchmark_id = repo_root.name

        ctx.curation_dir.mkdir(parents=True, exist_ok=True)

        config_path = config.save()

        stats = _count_source_files(source_dir, config.source_language)
        subdir_note = (
            f"\n- **Source subdir:** `{config.source_subdir}`"
            if config.source_subdir
            else ""
        )
        info_path = ctx.curation_dir / "source_info.md"
        info_path.write_text(
            f"# Source Information\n\n"
            f"- **Repository root:** `{repo_root}`{subdir_note}\n"
            f"- **Source directory:** `{source_dir}`\n"
            f"- **Language:** {config.source_language.value}\n"
            f"- **Repository URL:** {url or '(not a git repo)'}\n"
            f"- **Commit:** {commit or '(unknown)'}\n"
            f"- **Source files:** {stats['file_count']}\n"
            f"- **Total lines:** {stats['total_lines']}\n",
            encoding="utf-8",
        )

        # Scaffold the Lean project: lakefile + lean-toolchain + empty root hub
        # + manifest.json with empty packages[]. Translate stage populates the
        # rest.
        project_name = to_project_name(config.benchmark_id)
        project_dir = create_lean_project(
            ctx.lean_output_dir,
            project_name,
            lean_version=config.lean_version,
        )

        root_hub = project_dir / f"{project_name}.lean"
        if not root_hub.exists():
            root_hub.write_text(
                f"-- {project_name} root hub — populated by translate stage.\n",
                encoding="utf-8",
            )

        manifest_path = project_dir / "manifest.json"
        if not manifest_path.exists():
            manifest = _manifest_scaffold(
                benchmark_id=config.benchmark_id,
                project_name=project_name,
                lean_version=config.lean_version,
                source_language=config.source_language.value
                if config.source_language
                else None,
                repo_url=url,
                commit_hash=commit,
                source_subdir=config.source_subdir,
            )
            manifest_path.write_text(
                json.dumps(manifest, indent=2) + "\n", encoding="utf-8"
            )

        return StageResult(
            stage=self.name,
            success=True,
            output_files=[
                str(config_path),
                str(info_path),
                str(project_dir / "lakefile.toml"),
                str(manifest_path),
                str(root_hub),
            ],
        )
