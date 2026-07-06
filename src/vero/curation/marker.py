"""Marker validation and task extraction utilities.

Markers follow the format:
    -- !benchmark @start <key> [def=<name>]
    <content>
    -- !benchmark @end <key> [def=<name>]

The `def=` parameter identifies the definition name (function, spec, or theorem).
Legacy `api=` is also accepted for backward compatibility.
"""

from __future__ import annotations

import re
from pathlib import Path

from vero.curation.models import TaskEntry

MARKER_START = re.compile(r"--\s*!benchmark\s+@start\s+(\w+)(?:\s+(.*?))?\s*$")
MARKER_END = re.compile(r"--\s*!benchmark\s+@end\s+(\w+)(?:\s+(.*?))?\s*$")

# Active `!benchmark` key set per Convention #2 (ratified in the reference
# repo; see `reference/BankLedger/ARCHITECTURE.md`). `spec` /
# `spec_aux` / `claim_aux` are retired; the old `def_aux` / `def_body` /
# `precond*` / `postcond*` keys are gone.
VALID_KEYS = {
    "imports",
    "global_aux",
    "code",
    "code_aux",
    "proof",
    "proof_aux",
    "claim",
}

# Keys we used to accept and now reject. Kept around so the validator can
# flag them with a specific "retired" message rather than a generic "unknown
# key" one.
RETIRED_KEYS = {
    "def_aux",
    "def_body",
    "spec",
    "spec_aux",
    "claim_aux",
    "precond",
    "precond_aux",
    "postcond",
    "postcond_aux",
}


IGNORED_LEAN_DIRS = frozenset({".lake", "build", ".git", "__pycache__"})


def _iter_project_lean_files(project_dir: Path) -> list[Path]:
    """Lean files belonging to the project source tree, excluding caches."""
    out = []
    for lean_file in project_dir.rglob("*.lean"):
        rel_parts = lean_file.relative_to(project_dir).parts
        if any(part in IGNORED_LEAN_DIRS for part in rel_parts):
            continue
        out.append(lean_file)
    return sorted(out)


def _parse_params(param_str: str | None) -> dict[str, str]:
    """Parse 'api=foo def=bar' into {'api': 'foo', 'def': 'bar'}."""
    if not param_str:
        return {}
    result = {}
    for token in param_str.strip().split():
        if "=" in token:
            k, v = token.split("=", 1)
            result[k] = v
    return result


def validate_markers(content: str) -> list[str]:
    """Return a list of validation error messages for markers in Lean content."""
    errors: list[str] = []
    stack: list[tuple[int, str, str, dict]] = []  # (line, key, param_str, params)

    for i, line in enumerate(content.splitlines(), start=1):
        start_m = MARKER_START.search(line)
        end_m = MARKER_END.search(line)

        if start_m:
            key = start_m.group(1)
            param_str = start_m.group(2) or ""
            params = _parse_params(param_str)
            if key not in VALID_KEYS:
                if key in RETIRED_KEYS:
                    errors.append(
                        f"Line {i}: retired marker key '{key}'; see "
                        "reference/BankLedger/ARCHITECTURE.md "
                        "for the active 7-key set"
                    )
                else:
                    errors.append(f"Line {i}: unknown marker key '{key}'")
            stack.append((i, key, param_str, params))

        if end_m:
            key = end_m.group(1)
            param_str = end_m.group(2) or ""
            if not stack:
                errors.append(f"Line {i}: @end '{key}' without matching @start")
            else:
                start_line, start_key, start_param_str, _ = stack.pop()
                if key != start_key:
                    errors.append(
                        f"Line {i}: @end key '{key}' does not match "
                        f"@start key '{start_key}' at line {start_line}"
                    )
                elif param_str.strip() != start_param_str.strip():
                    errors.append(
                        f"Line {i}: @end params '{param_str.strip()}' do not match "
                        f"@start params '{start_param_str.strip()}' at line {start_line}"
                    )

    for start_line, key, param_str, _ in stack:
        errors.append(
            f"Line {start_line}: @start '{key} {param_str}' has no matching @end"
        )

    return errors


def extract_tasks(content: str, file_path: str) -> list[TaskEntry]:
    """Extract all benchmark tasks from markers in a Lean file."""
    tasks: list[TaskEntry] = []
    lines = content.splitlines()
    i = 0

    while i < len(lines):
        start_m = MARKER_START.search(lines[i])
        if start_m:
            key = start_m.group(1)
            params = _parse_params(start_m.group(2))
            start_line = i + 1  # 1-based
            content_lines = []
            i += 1
            while i < len(lines):
                end_m = MARKER_END.search(lines[i])
                if end_m and end_m.group(1) == key:
                    break
                content_lines.append(lines[i])
                i += 1

            body = "\n".join(content_lines).strip()
            api_name = params.get("def", params.get("api", ""))

            tasks.append(
                TaskEntry(
                    key=key,
                    api=api_name,
                    file=file_path,
                    line=start_line,
                    content=body,
                    is_sorry="sorry" in body,
                )
            )
        i += 1

    return tasks


def extract_tasks_from_project(project_dir: Path) -> list[TaskEntry]:
    """Extract all benchmark tasks from all .lean files in a project."""
    all_tasks: list[TaskEntry] = []
    for lean_file in _iter_project_lean_files(project_dir):
        content = lean_file.read_text(encoding="utf-8")
        rel_path = str(lean_file.relative_to(project_dir))
        all_tasks.extend(extract_tasks(content, rel_path))
    return all_tasks


def _strip_block_comments(content: str) -> str:
    """Replace Lean block comments (`/- … -/`, nesting allowed) with blanks.

    Preserves line boundaries so line-based counting stays aligned with the
    original file. Non-comment characters pass through unchanged.
    """
    out = []
    depth = 0
    i = 0
    n = len(content)
    while i < n:
        ch = content[i]
        if depth == 0 and ch == "/" and i + 1 < n and content[i + 1] == "-":
            depth = 1
            i += 2
            continue
        if depth > 0:
            if ch == "/" and i + 1 < n and content[i + 1] == "-":
                depth += 1
                i += 2
                continue
            if ch == "-" and i + 1 < n and content[i + 1] == "/":
                depth -= 1
                i += 2
                continue
            # Inside a comment: drop the char but preserve newlines.
            out.append("\n" if ch == "\n" else " ")
            i += 1
            continue
        out.append(ch)
        i += 1
    return "".join(out)


def count_metrics(project_dir: Path) -> dict:
    """Count sorry, opaque, axiom, #guard across all .lean files.

    `sorry` occurrences inside `--` line comments or `/- … -/` block comments
    (including module docstrings `/-! … -/`) are excluded.
    """
    sorry = 0
    opaque = 0
    axiom = 0
    guard = 0
    total_lines = 0
    file_count = 0

    for lean_file in _iter_project_lean_files(project_dir):
        content = lean_file.read_text(encoding="utf-8")
        total_lines += len(content.splitlines())
        file_count += 1
        scan_lines = _strip_block_comments(content).splitlines()
        for line in scan_lines:
            stripped = line.strip()
            if "sorry" in stripped and not stripped.startswith("--"):
                sorry += 1
            if stripped.startswith("opaque "):
                opaque += 1
            if stripped.startswith("axiom "):
                axiom += 1
            if stripped.startswith("#guard"):
                guard += 1

    return {
        "sorry_count": sorry,
        "opaque_count": opaque,
        "axiom_count": axiom,
        "guard_count": guard,
        "total_lines": total_lines,
        "file_count": file_count,
    }
