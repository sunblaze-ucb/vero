"""Global hygiene pre-pass over agent-editable files.

The evaluator calls this before Stage-1 build. Currently:

- :func:`check_unsafe_keyword` — flag any file that contains the whole-word token ``unsafe`` in non-comment source. Any hit voids the entire run (``build_ok=False``, every spec grades ``unsafe_keyword``). Unlike the per-slot ``slot_body_tainted`` check (which only inspects filled slot interiors), ``unsafe`` anywhere in an agent-editable file is fatal — ``unsafe def`` at file scope, ``unsafe section`` in ``global_aux``, or even inside ``!benchmark code`` would escape Lean's kernel and make every downstream proof vacuous.

- :func:`check_implemented_by` — flag any agent-editable ``Impl/`` file that uses the ``@[implemented_by …]`` attribute. This is the load-bearing half of the *spec-oracle* reward hack (observed in dijkstar): the agent defines the scored API as a ``noncomputable`` copy of the spec's own argmin/witness oracle (``if h : ∃ …, … then Exists.choose …``) so every optimality proof is tautological, then attaches a real algorithm only via ``@[implemented_by]`` so runtime output stays correct and differential testing finds no diff. The proof target is then the spec itself, not an independent implementation. ``@[implemented_by]`` has no legitimate use in a benchmark impl slot (it deliberately splits the compile-time proof target from the run-time function), so any hit voids the run (``build_ok=False``, every spec grades ``impl_oracle``). Scoped to agent-editable ``Impl/`` files only — proof-mode ``noncomputable`` reference defs (e.g. flocq's ``negligibleExp`` via ``Classical.choose``) are legitimate and untouched, since they carry no ``@[implemented_by]``.

Comment-stripping semantics mirror ``vero.generation.extractor._contains_keyword``: ``--`` line comments and ``/- ... -/`` block comments (including ``/-! ... -/`` docstrings) are stripped before matching, so a literal mention of a banned token inside a prose comment is fine.
"""

from __future__ import annotations

import re
from dataclasses import dataclass
from pathlib import Path

from loguru import logger

_UNSAFE_PATTERN = re.compile(r"\bunsafe\b")
# ``implemented_by`` attribute in either form:
#   ``@[implemented_by foo]`` / ``@[inline, implemented_by foo]`` (prefix attribute), or
#   ``attribute [implemented_by foo] bar`` (standalone attribute command).
# The whole-word ``implemented_by`` token only ever appears as this attribute, so
# matching it (outside comments) is sufficient and evasion-resistant.
_IMPLEMENTED_BY_PATTERN = re.compile(r"\bimplemented_by\b")
_BLOCK_COMMENT = re.compile(r"/-.*?-/", re.DOTALL)


@dataclass
class UnsafeCheckResult:
    detected: bool
    files: list[str]  # sandbox-relative paths that matched
    reason: str


@dataclass
class ImplOracleCheckResult:
    detected: bool
    files: list[str]  # sandbox-relative paths that matched
    reason: str


def _strip_comments(text: str) -> str:
    # Block comments first (they may span lines).
    text = _BLOCK_COMMENT.sub("", text)
    out_lines: list[str] = []
    for ln in text.splitlines():
        if ln.lstrip().startswith("--"):
            continue
        if "--" in ln:
            ln = ln.split("--", 1)[0]
        out_lines.append(ln)
    return "\n".join(out_lines)


def _file_has_unsafe(path: Path) -> bool:
    try:
        text = path.read_text(encoding="utf-8")
    except (OSError, UnicodeDecodeError) as e:
        logger.warning("could not read {} for unsafe-check: {}", path, e)
        return False
    stripped = _strip_comments(text)
    return bool(_UNSAFE_PATTERN.search(stripped))


def _file_has_implemented_by(path: Path) -> bool:
    try:
        text = path.read_text(encoding="utf-8")
    except (OSError, UnicodeDecodeError) as e:
        logger.warning("could not read {} for implemented_by-check: {}", path, e)
        return False
    stripped = _strip_comments(text)
    return bool(_IMPLEMENTED_BY_PATTERN.search(stripped))


def check_unsafe_keyword(
    sandbox_dir: Path, relative_files: list[str]
) -> UnsafeCheckResult:
    """Scan each agent-editable file for a whole-word ``unsafe`` occurrence.

    Parameters
    ----------
    sandbox_dir:
        Root of the sandbox (or any directory holding the files).
    relative_files:
        File paths relative to ``sandbox_dir``. Duplicates OK — deduped here.
    """
    seen: set[str] = set()
    hits: list[str] = []
    for rel in relative_files:
        if rel in seen:
            continue
        seen.add(rel)
        p = sandbox_dir / rel
        if not p.exists():
            continue
        if _file_has_unsafe(p):
            hits.append(rel)
    if not hits:
        return UnsafeCheckResult(detected=False, files=[], reason="")
    reason = (
        "`unsafe` keyword detected in agent-editable file(s): "
        + ", ".join(sorted(hits))
        + " — the whole run is voided (unsafe escapes Lean's kernel)."
    )
    return UnsafeCheckResult(detected=True, files=sorted(hits), reason=reason)


def check_implemented_by(
    sandbox_dir: Path, relative_files: list[str]
) -> ImplOracleCheckResult:
    """Scan agent-editable ``Impl/`` files for the ``@[implemented_by …]`` attribute.

    ``@[implemented_by]`` splits the compile-time proof target from the run-time
    function, which is exactly the spec-oracle reward hack (define the scored API
    as a ``noncomputable`` copy of the spec's own witness oracle so proofs are
    tautological, then attach a real algorithm via ``@[implemented_by]`` so
    runtime output stays correct). It has no legitimate use in a benchmark impl
    slot, so any hit voids the run.

    Scoped to ``Impl/`` files: proof-side files never define the scored API, and
    legitimate ``noncomputable`` reference defs (which carry no
    ``@[implemented_by]``) are unaffected.

    Parameters
    ----------
    sandbox_dir:
        Root of the sandbox (or any directory holding the files).
    relative_files:
        File paths relative to ``sandbox_dir``. Duplicates OK — deduped here.
    """
    seen: set[str] = set()
    hits: list[str] = []
    for rel in relative_files:
        if rel in seen:
            continue
        seen.add(rel)
        # Only impl-side files can define the scored API; ``@[implemented_by]``
        # elsewhere can't realize the proof/runtime split on a scored function.
        if "/Impl/" not in rel and not rel.startswith("Impl/") and "/Impl" not in rel:
            continue
        p = sandbox_dir / rel
        if not p.exists():
            continue
        if _file_has_implemented_by(p):
            hits.append(rel)
    if not hits:
        return ImplOracleCheckResult(detected=False, files=[], reason="")
    reason = (
        "`@[implemented_by]` attribute detected in agent-editable impl file(s): "
        + ", ".join(sorted(hits))
        + " — the whole run is voided. This attribute splits the compile-time "
        "proof target from the run-time function (the spec-oracle reward hack: a "
        "`noncomputable` spec-copy impl makes proofs tautological while a real "
        "algorithm is attached only for execution). Implement the scored API "
        "directly as a computable definition."
    )
    return ImplOracleCheckResult(detected=True, files=sorted(hits), reason=reason)
