"""Parser for the three marker prefixes: !benchmark, !solution, !curation."""

from __future__ import annotations

import re
from dataclasses import dataclass, field
from pathlib import Path
from typing import Literal

MarkerPrefix = Literal["benchmark", "solution", "curation"]
MarkerBoundary = Literal["start", "end"]

# Active !benchmark key set per Convention #2 (ratified)
BENCHMARK_KEYS = frozenset(
    {
        "imports",
        "global_aux",
        "code",
        "code_aux",
        "proof",
        "proof_aux",
        "claim",
    }
)


@dataclass
class MarkerLine:
    """A parsed marker line."""

    prefix: MarkerPrefix
    line_no: int
    raw: str

    # !benchmark-specific
    boundary: MarkerBoundary | None = None  # start | end
    key: str | None = None  # imports, code, proof, claim, ...

    # !solution-specific (no key; structure carried in fields)

    # !curation-specific
    curation_kind: str | None = None  # review, v1, human, question, answer
    curation_body: str | None = None

    # Shared fields (def, kind, target, targets, specs, ...)
    fields: dict[str, str] = field(default_factory=dict)


_BENCHMARK_RE = re.compile(
    r"--\s*!benchmark\s+@(?P<boundary>start|end)\s+(?P<key>\w+)(?P<rest>.*)$"
)
_SOLUTION_RE = re.compile(r"--\s*!solution\s+@(?P<boundary>start|end)(?P<rest>.*)$")
_CURATION_RE = re.compile(r"--\s*!curation\s+@(?P<kind>\S+)(?P<rest>.*)$")
_FIELD_RE = re.compile(r"(\w+)\s*=\s*(\S+)")


def parse_marker_line(line: str, line_no: int) -> MarkerLine | None:
    """Parse a single line if it is a marker. Return None otherwise."""
    if m := _BENCHMARK_RE.search(line):
        fields = dict(_FIELD_RE.findall(m.group("rest")))
        return MarkerLine(
            prefix="benchmark",
            line_no=line_no,
            raw=line.rstrip("\n"),
            boundary=m.group("boundary"),
            key=m.group("key"),
            fields=fields,
        )
    if m := _SOLUTION_RE.search(line):
        fields = dict(_FIELD_RE.findall(m.group("rest")))
        return MarkerLine(
            prefix="solution",
            line_no=line_no,
            raw=line.rstrip("\n"),
            boundary=m.group("boundary"),
            fields=fields,
        )
    if m := _CURATION_RE.search(line):
        return MarkerLine(
            prefix="curation",
            line_no=line_no,
            raw=line.rstrip("\n"),
            curation_kind=m.group("kind"),
            curation_body=m.group("rest").strip(),
        )
    return None


def parse_file_markers(path: Path) -> list[MarkerLine]:
    """Parse all marker lines in a Lean file, in file order.

    Skips markers inside /-! ... -/ and /- ... -/ block comments (per Convention #2.9).
    """
    markers: list[MarkerLine] = []
    in_block_comment = False
    for i, line in enumerate(path.read_text().splitlines(), start=1):
        stripped = line.lstrip()
        if in_block_comment:
            if "-/" in line:
                in_block_comment = False
            continue
        # Detect block-comment openers that don't close on the same line
        if stripped.startswith("/-"):
            # Find first /- and check for matching -/ after it
            start_idx = stripped.index("/-")
            if "-/" not in stripped[start_idx + 2 :]:
                in_block_comment = True
            continue
        parsed = parse_marker_line(line, i)
        if parsed:
            markers.append(parsed)
    return markers


@dataclass
class SlotPair:
    """A matched @start / @end pair."""

    key: str  # marker key, or "solution" for !solution
    prefix: MarkerPrefix  # benchmark | solution
    def_name: str | None  # def= value (None for imports/global_aux benchmark slots)
    fields: dict[str, str]  # start marker's fields
    start_line: int
    end_line: int


def pair_slots(markers: list[MarkerLine]) -> tuple[list[SlotPair], list[str]]:
    """Match @start / @end pairs. Return (pairs, errors).

    Validates:
    - Every @start has a matching @end with same prefix + key + def.
    - No overlapping pairs (no nesting).
    """
    pairs: list[SlotPair] = []
    errors: list[str] = []
    stack: list[MarkerLine] = []

    # Only consider benchmark + solution markers (curation is single-line)
    structured = [m for m in markers if m.prefix in ("benchmark", "solution")]

    for m in structured:
        if m.boundary == "start":
            if stack:
                top = stack[-1]
                errors.append(
                    f"nested @start at line {m.line_no} (inside @start from line {top.line_no})"
                )
            stack.append(m)
        elif m.boundary == "end":
            if not stack:
                errors.append(
                    f"unexpected @end at line {m.line_no} with no matching @start"
                )
                continue
            top = stack.pop()
            # Validate match
            if top.prefix != m.prefix:
                errors.append(
                    f"prefix mismatch at line {m.line_no}: @end !{m.prefix} but @start was !{top.prefix} at line {top.line_no}"
                )
            if top.key != m.key:
                errors.append(
                    f"key mismatch at line {m.line_no}: @end key={m.key} but @start key={top.key} at line {top.line_no}"
                )
            top_def = top.fields.get("def")
            end_def = m.fields.get("def")
            if top_def != end_def:
                errors.append(
                    f"def mismatch at line {m.line_no}: @end def={end_def} but @start def={top_def} at line {top.line_no}"
                )
            pairs.append(
                SlotPair(
                    key=top.key or "solution",
                    prefix=top.prefix,
                    def_name=top_def,
                    fields=top.fields,
                    start_line=top.line_no,
                    end_line=m.line_no,
                )
            )

    for unmatched in stack:
        errors.append(f"unclosed @start at line {unmatched.line_no}")

    return pairs, errors
