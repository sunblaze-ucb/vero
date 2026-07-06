"""SOURCE_INDEX stage — no-LLM source-wide entity registry.

This stage intentionally uses conservative regex extraction instead of trying
to fully parse every source language. Its purpose is not to produce the final
selection; it creates a stable universe of top-level names so later LLM stages
and validators can detect silent drops, role changes, and axiomization.
"""

from __future__ import annotations

import json
import re
from datetime import datetime, timezone
from pathlib import Path

from vero.curation.models import SourceLanguage
from vero.curation.stages.base import StageContext, StageResult, StageRunner


class SourceIndexStage(StageRunner):
    """Build a best-effort source-wide entity registry without LLM calls."""

    name = "source_index"
    human_review = False

    async def run(self, ctx: StageContext) -> StageResult:
        source_dir = ctx.source_dir
        language = ctx.config.source_language
        files = _source_files(source_dir, language)
        entities = []
        for path in files:
            rel = path.relative_to(source_dir).as_posix()
            try:
                text = path.read_text(encoding="utf-8", errors="replace")
            except OSError:
                continue
            for entity in _extract_entities(text, rel, language):
                entities.append(entity)

        out = {
            "version": 1,
            "generated_at": datetime.now(timezone.utc).isoformat(),
            "source_language": language.value if language else None,
            "source_path": str(source_dir),
            "entities": entities,
        }

        vero_dir = ctx.config.workspace / ".vero"
        vero_dir.mkdir(parents=True, exist_ok=True)
        json_path = vero_dir / "source_index.json"
        json_path.write_text(json.dumps(out, indent=2) + "\n", encoding="utf-8")

        return StageResult(
            stage=self.name,
            success=True,
            output_files=[str(json_path)],
        )


def _source_files(source_dir: Path, language: SourceLanguage | None) -> list[Path]:
    suffixes = {
        SourceLanguage.LEAN: {".lean"},
        SourceLanguage.COQ: {".v"},
        SourceLanguage.DAFNY: {".dfy"},
        SourceLanguage.VERUS: {".rs"},
        SourceLanguage.PYTHON: {".py"},
        None: {".lean", ".v", ".dfy", ".rs", ".py"},
    }.get(language, {".lean", ".v", ".dfy", ".rs", ".py"})
    ignored = {".git", ".lake", ".venv", "__pycache__", "target", "build"}
    out = []
    for path in source_dir.rglob("*"):
        if not path.is_file() or path.suffix not in suffixes:
            continue
        if any(part in ignored for part in path.parts):
            continue
        out.append(path)
    return sorted(out)


def _extract_entities(
    text: str,
    relpath: str,
    language: SourceLanguage | None,
) -> list[dict]:
    if language == SourceLanguage.COQ:
        return _extract_with_regex(text, relpath, _COQ_DECL_RE, _coq_kind_role)
    if language == SourceLanguage.DAFNY:
        return _extract_dafny_entities(text, relpath)
    if language == SourceLanguage.VERUS:
        return _extract_with_regex(text, relpath, _VERUS_DECL_RE, _verus_kind_role)
    if language == SourceLanguage.PYTHON:
        return _extract_with_regex(text, relpath, _PYTHON_DECL_RE, _python_kind_role)
    return _extract_with_regex(text, relpath, _LEAN_DECL_RE, _lean_kind_role)


def _extract_with_regex(
    text: str,
    relpath: str,
    pattern: re.Pattern[str],
    classifier,
) -> list[dict]:
    out = []
    for match in pattern.finditer(text):
        kind, name = match.group("kind"), match.group("name")
        default_role, disposition = classifier(kind, name)
        out.append(
            {
                "id": f"{relpath}:{name}:{match.start()}",
                "name": name,
                "qualified_name": name,
                "kind": kind,
                "source_file": relpath,
                "source_line": text.count("\n", 0, match.start()) + 1,
                "signature": match.group(0).strip(),
                "default_role": default_role,
                "disposition": disposition,
                "selected": True,
                "dependencies": [],
                "notes": "best-effort no-LLM extraction; confirm in discover/select",
            }
        )
    return out


def _extract_dafny_entities(text: str, relpath: str) -> list[dict]:
    """Extract Dafny declarations that matter for source traceability.

    This is still intentionally a conservative line-level registry, not a full
    Dafny parser. The regex handles common declaration shapes that JSON uses:
    subset/alias ``type`` declarations, constants, attributed declarations such
    as ``function {:opaque} F``, ``method {:test}``, apostrophe/question-mark
    names, and anonymous constructors.
    """
    out = []
    for match in _DAFNY_DECL_RE.finditer(text):
        kind = match.group("kind")
        raw_name = match.group("name")
        name = raw_name or "constructor"
        default_role, disposition = _dafny_kind_role(kind, name)
        out.append(
            {
                "id": f"{relpath}:{name}:{match.start()}",
                "name": name,
                "qualified_name": name,
                "kind": kind,
                "source_file": relpath,
                "source_line": text.count("\n", 0, match.start()) + 1,
                "signature": match.group(0).strip(),
                "default_role": default_role,
                "disposition": disposition,
                "selected": True,
                "dependencies": [],
                "notes": "best-effort no-LLM extraction; confirm in discover/select",
            }
        )
    return out


_LEAN_DECL_RE = re.compile(
    r"^\s*(?P<kind>def|theorem|lemma|axiom|opaque|inductive|structure|class|abbrev|instance)\s+(?P<name>[A-Za-z_][\w'.]*)\b",
    re.MULTILINE,
)
_COQ_DECL_RE = re.compile(
    r"^\s*(?P<kind>Definition|Fixpoint|Theorem|Lemma|Corollary|Remark|Axiom|"
    r"Parameter|Variable|Hypothesis|Let|Inductive|Record|"
    r"Program\s+Definition)\s+(?P<name>[A-Za-z_][\w']*)\b",
    re.MULTILINE,
)
_DAFNY_DECL_RE = re.compile(
    r"""
    ^\s*
    (?:ghost\s+)?
    (?:static\s+)?
    (?P<kind>function|method|lemma|predicate|datatype|class|module|type|const|constructor)
    \b
    \s*
    (?:(?:\{:[^}\n]*\})\s*)*
    (?P<name>[A-Za-z_][\w?'’]*)?
    """,
    re.MULTILINE | re.VERBOSE,
)
_VERUS_DECL_RE = re.compile(
    r"^\s*(?:pub(?:\([^)]*\))?\s+)?(?:(?:open|closed)\s+)?(?:(?:spec|proof|exec)\s+)?(?P<kind>fn|struct|enum|type)\s+(?P<name>[A-Za-z_]\w*)\b",
    re.MULTILINE,
)
_PYTHON_DECL_RE = re.compile(
    r"^\s*(?P<kind>def|class)\s+(?P<name>[A-Za-z_]\w*)\b",
    re.MULTILINE,
)


def _lean_kind_role(kind: str, _name: str) -> tuple[str, str]:
    return "unclassified", "unclassified"


def _coq_kind_role(kind: str, _name: str) -> tuple[str, str]:
    return "unclassified", "unclassified"


def _dafny_kind_role(kind: str, _name: str) -> tuple[str, str]:
    return "unclassified", "unclassified"


def _verus_kind_role(kind: str, _name: str) -> tuple[str, str]:
    return "unclassified", "unclassified"


def _python_kind_role(kind: str, _name: str) -> tuple[str, str]:
    return "unclassified", "unclassified"
