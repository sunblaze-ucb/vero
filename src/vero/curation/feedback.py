"""Parse and render versioned review comments for human-in-the-loop feedback.

## Comment format in Lean files

Current round (human edits these):
    -- @review v2 [ ] push — Stack.dfy:5, spec-fn
    -- @human: consider also adding a reverse function
    -- @question: Should peek return Option or use a hypothesis?

Previous round (context only, agent does NOT act on these):
    -- @v1 [ ] push — should return Option  [RESOLVED]
    -- @v1-human: split into two files  [NOTED]
    -- @v1-answer: peek uses Option since Lean has no requires  [ANSWERED]

## Comment format in markdown files

Current round review section at bottom:
    ## Review (v2)
    - [x] Stack — approved
    - [ ] Helpers — fromSeq should handle empty list
    <!-- @question: Should reverse be included? -->

Previous round (collapsed):
    <details><summary>Review v1 (resolved)</summary>
    - [ ] Stack — use Option for pop  [RESOLVED]
    </details>
"""

from __future__ import annotations

import re
from pathlib import Path

# ── Discovery / Selection markdown parsing ──────────────────────────────


def parse_discovery_selections(discovery_dir: Path) -> dict[str, bool]:
    """Parse all discovery/*.md files and return {qualified_name: selected}."""
    selections: dict[str, bool] = {}
    checkbox_re = re.compile(r"^\s*-\s*\[([ xX])\]\s*`([^`]+)`")
    for md_file in sorted(discovery_dir.glob("*.md")):
        for line in md_file.read_text(encoding="utf-8").splitlines():
            m = checkbox_re.match(line)
            if m:
                selections[m.group(2)] = m.group(1).lower() == "x"
    return selections


def parse_discovery_notes(discovery_dir: Path) -> dict[str, str]:
    """Parse human notes from discovery files."""
    notes: dict[str, str] = {}
    checkbox_re = re.compile(r"^\s*-\s*\[([ xX])\]\s*`([^`]+)`")
    notes_re = re.compile(r"^\s*-\s*Notes:\s*(.*)")
    current_item = None
    for md_file in sorted(discovery_dir.glob("*.md")):
        for line in md_file.read_text(encoding="utf-8").splitlines():
            m = checkbox_re.match(line)
            if m:
                current_item = m.group(2)
                continue
            m = notes_re.match(line)
            if m and current_item:
                note = m.group(1).strip()
                if note and note != "_add notes here_":
                    notes[current_item] = note
    return notes


def parse_human_guidance(path: Path) -> dict:
    """Parse human_guidance.md into sections."""
    if not path.exists():
        return {}
    content = path.read_text(encoding="utf-8")
    result: dict = {"instructions": "", "per_file": {}, "known_issues": ""}
    current_section = None
    current_file = None
    buffer: list[str] = []

    for line in content.splitlines():
        if line.startswith("## Instructions for Agent"):
            if current_section and buffer:
                _flush(result, current_section, current_file, buffer)
            current_section, current_file, buffer = "instructions", None, []
        elif line.startswith("## Per-File"):
            if current_section and buffer:
                _flush(result, current_section, current_file, buffer)
            current_section, current_file, buffer = "per_file", None, []
        elif line.startswith("## Known Issues"):
            if current_section and buffer:
                _flush(result, current_section, current_file, buffer)
            current_section, current_file, buffer = "known_issues", None, []
        elif line.startswith("### ") and current_section == "per_file":
            if current_file and buffer:
                result["per_file"][current_file] = "\n".join(buffer).strip()
            current_file, buffer = line[4:].strip(), []
        else:
            buffer.append(line)

    if current_section and buffer:
        _flush(result, current_section, current_file, buffer)
    return result


def _flush(
    result: dict, section: str, current_file: str | None, buffer: list[str]
) -> None:
    text = "\n".join(buffer).strip()
    if section == "instructions":
        result["instructions"] = text
    elif section == "known_issues":
        result["known_issues"] = text
    elif section == "per_file" and current_file:
        result["per_file"][current_file] = text


# ── Lean file versioned review comments ─────────────────────────────────

# Current round patterns
_REVIEW_RE = re.compile(
    r"^--\s*@review\s+v(\d+)\s*\[([ xX])\]\s*(\S+)(?:\s*—\s*(.*))?$"
)
_HUMAN_RE = re.compile(r"^--\s*@human:\s*(.*)")
_QUESTION_RE = re.compile(r"^--\s*@question(?:\s+(\S+))?\s*—?\s*(.*)")

# Previous round patterns (context only — agent should NOT act on these)
_PREV_REVIEW_RE = re.compile(
    r"^--\s*@v(\d+)\s*\[([ xX])\]\s*(\S+)(?:\s*—\s*(.*))?\s*\[(RESOLVED|NOTED|KEPT)\]"
)
_PREV_HUMAN_RE = re.compile(r"^--\s*@v(\d+)-human:\s*(.*)\s*\[(RESOLVED|NOTED)\]")
_PREV_ANSWER_RE = re.compile(r"^--\s*@v(\d+)-answer:\s*(.*)\s*\[(ANSWERED)\]")


def extract_lean_feedback(project_dir: Path) -> dict:
    """Extract versioned review comments from all .lean files.

    Returns:
        {
            "version": int,  # highest version found (0 if none)
            "reviews": [{"file", "line", "version", "name", "approved", "feedback"}, ...],
            "comments": [{"file", "line", "comment"}, ...],
            "questions": [{"file", "line", "name", "text"}, ...],
            "history": [{"file", "line", "version", "type", "text", "resolution"}, ...],
        }
    """
    results: dict = {
        "version": 0,
        "reviews": [],
        "comments": [],
        "questions": [],
        "history": [],
    }

    for lean_file in sorted(project_dir.rglob("*.lean")):
        content = lean_file.read_text(encoding="utf-8")
        rel_path = str(lean_file.relative_to(project_dir))

        for i, line in enumerate(content.splitlines(), start=1):
            stripped = line.strip()

            # Current round: @review vN [x] name — feedback
            m = _REVIEW_RE.match(stripped)
            if m:
                ver = int(m.group(1))
                results["version"] = max(results["version"], ver)
                results["reviews"].append(
                    {
                        "file": rel_path,
                        "line": i,
                        "version": ver,
                        "name": m.group(3),
                        "approved": m.group(2).lower() == "x",
                        "feedback": (m.group(4) or "").strip(),
                    }
                )
                continue

            # Current round: @human: free text
            m = _HUMAN_RE.match(stripped)
            if m:
                results["comments"].append(
                    {
                        "file": rel_path,
                        "line": i,
                        "comment": m.group(1).strip(),
                    }
                )
                continue

            # Current round: @question [name] — text
            m = _QUESTION_RE.match(stripped)
            if m:
                results["questions"].append(
                    {
                        "file": rel_path,
                        "line": i,
                        "name": (m.group(1) or "").strip(),
                        "text": m.group(2).strip(),
                    }
                )
                continue

            # Previous rounds (context only)
            for prev_re, prev_type in [
                (_PREV_REVIEW_RE, "review"),
                (_PREV_HUMAN_RE, "human"),
                (_PREV_ANSWER_RE, "answer"),
            ]:
                m = prev_re.match(stripped)
                if m:
                    results["history"].append(
                        {
                            "file": rel_path,
                            "line": i,
                            "version": int(m.group(1)),
                            "type": prev_type,
                            "text": m.group(2).strip()
                            if prev_type != "review"
                            else f"{m.group(3)}: {(m.group(4) or '').strip()}",
                            "resolution": m.group(len(m.groups())),
                        }
                    )
                    break

    return results


def format_lean_feedback_for_prompt(feedback: dict, current_version: int) -> str:
    """Format extracted feedback into a prompt section for the agent.

    Only includes CURRENT version reviews/comments as actionable items.
    Previous versions are shown as context only.
    """
    reviews = [
        r for r in feedback.get("reviews", []) if r["version"] == current_version
    ]
    comments = feedback.get("comments", [])
    questions = feedback.get("questions", [])
    history = feedback.get("history", [])

    if not reviews and not comments and not questions:
        return ""

    lines = [f"## Human Feedback (Review Round v{current_version})", ""]

    # Actionable: unapproved reviews with feedback
    pending = [r for r in reviews if not r["approved"] and r["feedback"]]
    if pending:
        lines.append("### Feedback to address:\n")
        for r in pending:
            lines.append(
                f"- **{r['file']}:{r['line']}** `{r['name']}` — {r['feedback']}"
            )
        lines.append("")

    # Approved items
    approved = [r for r in reviews if r["approved"]]
    if approved:
        lines.append(f"### Approved ({len(approved)} items — do not change):\n")
        for r in approved:
            note = f" — {r['feedback']}" if r["feedback"] else ""
            lines.append(f"- `{r['name']}`{note}")
        lines.append("")

    # Unanswered agent questions still pending
    if questions:
        lines.append("### Your previous questions (check if human answered):\n")
        for q in questions:
            name = f" `{q['name']}`" if q["name"] else ""
            lines.append(f"- **{q['file']}:{q['line']}**{name} — {q['text']}")
        lines.append("")

    # Free-form human comments
    if comments:
        lines.append("### Free-form feedback:\n")
        for c in comments:
            lines.append(f"- **{c['file']}:{c['line']}** — {c['comment']}")
        lines.append("")

    # Previous round context
    if history:
        prev_versions = sorted(set(h["version"] for h in history), reverse=True)
        lines.append("### Previous rounds (context only — do NOT re-address):\n")
        for v in prev_versions[:2]:  # show at most last 2 rounds
            v_items = [h for h in history if h["version"] == v]
            lines.append(f"**v{v}:** {len(v_items)} items resolved")
            for h in v_items[:5]:  # cap at 5 per round
                lines.append(f"  - [{h['resolution']}] {h['text']}")
            if len(v_items) > 5:
                lines.append(f"  - ... and {len(v_items) - 5} more")
        lines.append("")

    return "\n".join(lines)


# ── Markdown file versioned review sections ─────────────────────────────


def get_current_review_version(content: str) -> int:
    """Extract the current review version from markdown content.

    Looks for `## Review (vN)` or `## Review Round vN` headers.
    Returns 0 if no review section found.
    """
    m = re.search(r"##\s+Review.*?v(\d+)", content)
    return int(m.group(1)) if m else 0


def append_review_section(content: str, version: int, items: list[str]) -> str:
    """Append a new review section to markdown content.

    If a previous version exists, collapse it into a <details> block.
    """
    lines = content.rstrip().splitlines()

    # Find and collapse previous review section
    prev_start = None
    for i, line in enumerate(lines):
        if re.match(r"##\s+Review", line):
            prev_start = i
            break

    if prev_start is not None:
        prev_version = get_current_review_version("\n".join(lines[prev_start:]))
        prev_lines = lines[prev_start:]
        # Replace with collapsed details
        collapsed = [
            f"<details><summary>Review v{prev_version} (resolved)</summary>",
            "",
            *prev_lines[1:],  # skip the ## header
            "",
            "</details>",
            "",
        ]
        lines = lines[:prev_start] + collapsed

    # Add new review section
    lines.extend(
        [
            f"## Review (v{version})",
            "",
            *items,
            "",
        ]
    )

    return "\n".join(lines) + "\n"
