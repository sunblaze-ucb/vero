"""Artifact extractor — schema-driven.

The extractor first computes, from the source ``Benchmark`` + mode, the exact set of marker slots that the pipeline planted in the sandbox (:func:`expected_slots`). It then parses each planted file and matches each expected slot against its parsed counterpart by ``(prefix, key, def_name)``. The result is:

- :attr:`Artifact.slots` — one :class:`ExtractedSlot` per expected slot, with ``found=True|False`` and (if found) the interior body + hash.
- :attr:`Artifact.extras` — slots the agent added that were NOT in the expected schedule. Always flagged; evaluator may penalise or ignore.
- :attr:`Artifact.file_errors` — files whose marker grammar is broken (parse failure); all expected slots in those files report ``found=False`` with ``error != ""``.

This keeps the artifact shape deterministic regardless of what the agent did: whether it wrote to a slot, left it untouched, deleted the markers, or added new ones, the artifact always has one entry per expected slot, in a predictable order.
"""

from __future__ import annotations

import hashlib
import json
from dataclasses import asdict, dataclass, field, fields
from pathlib import Path
from typing import Literal

from loguru import logger

from vero.generation.benchmark import Benchmark, load_slots

Mode = Literal["proof", "codeproof"]


# ─── Expected-slot schedule ─────────────────────────────────────


@dataclass(frozen=True)
class ExpectedSlot:
    """A slot the pipeline planted and therefore expects back from the agent."""

    file: str  # path relative to sandbox root
    prefix: str  # "benchmark" | "solution"
    key: str  # benchmark key or "solution"
    def_name: str | None  # identifier attached to the slot, if any
    expected_kind: str | None = None  # for proof/claim/solution slots
    expected_target: str | None = None  # for proof slots (the spec name)


# ─── Extracted result ───────────────────────────────────────────


@dataclass
class ExtractedSlot:
    """One expected slot's state after the agent has run."""

    # Identity (copied from the expected slot — stable regardless of
    # what the agent did):
    file: str
    prefix: str
    key: str
    def_name: str | None
    expected_kind: str | None
    expected_target: str | None

    # Observed state:
    found: bool
    body_lines: list[str] = field(default_factory=list)
    body_hash: str = ""
    is_empty: bool = True
    contains_sorry: bool = False
    contains_axiom: bool = False
    contains_admit: bool = False
    actual_fields: dict[str, str] = field(default_factory=dict)
    start_line: int | None = None
    end_line: int | None = None
    error: str = ""  # "missing" | "parse_error: …" | "kind_mismatch: …" | ""


@dataclass
class ExtraSlot:
    """A parsed slot the agent added that wasn't in the expected schedule."""

    file: str
    prefix: str
    key: str
    def_name: str | None
    fields: dict[str, str]
    start_line: int
    end_line: int
    body_lines: list[str]


@dataclass
class Artifact:
    benchmark_id: str
    mode: str
    sandbox_dir: str
    slots: list[ExtractedSlot]
    extras: list[ExtraSlot] = field(default_factory=list)
    file_errors: dict[str, str] = field(default_factory=dict)


# ─── Helpers ────────────────────────────────────────────────────


def _hash_body(lines: tuple[str, ...] | list[str]) -> str:
    h = hashlib.sha1()
    h.update("\n".join(lines).encode("utf-8"))
    return h.hexdigest()


def _is_effectively_empty(lines: tuple[str, ...] | list[str]) -> bool:
    for ln in lines:
        s = ln.strip()
        if not s:
            continue
        if s.startswith("--"):
            continue
        return False
    return True


def _contains_keyword(lines: tuple[str, ...] | list[str], word: str) -> bool:
    """True iff any non-comment line contains ``word`` as a whole token.

    Block-comments (``/- ... -/``) and line-comments (``-- ...``) are both
    stripped before matching. Whole-word means the keyword is flanked by
    non-word characters on both sides, so ``sorryAx`` doesn't match
    ``sorry`` and ``Axiom.Foo`` doesn't match ``axiom``.
    """
    import re

    pat = re.compile(rf"\b{re.escape(word)}\b")
    joined = "\n".join(lines)
    # Strip block comments first (they may span multiple lines).
    joined = re.sub(r"/-.*?-/", "", joined, flags=re.DOTALL)
    for ln in joined.splitlines():
        stripped = ln.lstrip()
        if stripped.startswith("--"):
            continue
        code = ln.split("--", 1)[0] if "--" in ln else ln
        if pat.search(code):
            return True
    return False


def _contains_sorry(lines: tuple[str, ...] | list[str]) -> bool:
    return _contains_keyword(lines, "sorry")


def _contains_axiom(lines: tuple[str, ...] | list[str]) -> bool:
    return _contains_keyword(lines, "axiom")


def _contains_admit(lines: tuple[str, ...] | list[str]) -> bool:
    return _contains_keyword(lines, "admit")


# ─── Expected schedule construction ─────────────────────────────


_JOINT_SLOT = "joint_unsatisfiability"


def expected_slots(bench: Benchmark, mode: Mode) -> list[ExpectedSlot]:
    """Enumerate every slot the pipeline planted for this benchmark + mode.

    This is the ONLY place that knows what the benchmark shape promises.
    Callers (extract, evaluator, reporter) drive off this list.
    """
    out: list[ExpectedSlot] = []

    # Impl/<Module>.lean — per module: imports, global_aux, and per API:
    # code_aux + code. Spec-only modules (impl_rel is None) have no impl
    # file, so they contribute no impl slots.
    for m in bench.iter_modules():
        if m.impl_rel is None:
            continue
        out.append(
            ExpectedSlot(
                file=m.impl_rel, prefix="benchmark", key="imports", def_name=None
            )
        )
        out.append(
            ExpectedSlot(
                file=m.impl_rel, prefix="benchmark", key="global_aux", def_name=None
            )
        )
        for api in m.apis:
            out.append(
                ExpectedSlot(
                    file=m.impl_rel,
                    prefix="benchmark",
                    key="code_aux",
                    def_name=api.name,
                )
            )
            out.append(
                ExpectedSlot(
                    file=m.impl_rel, prefix="benchmark", key="code", def_name=api.name
                )
            )

    # Proof/<Module>.lean — per mode. Modules with no specs have no proof
    # stub file, so they contribute no proof slots.
    if mode == "proof":
        proof_kinds = ("prove", "disprove")
    else:
        proof_kinds = ("prove", "unsat", "sat")
    for m in bench.iter_modules():
        if not m.specs:
            continue
        proof_rel = f"{m.package}/Proof/{m.name}.lean"
        out.append(
            ExpectedSlot(
                file=proof_rel, prefix="benchmark", key="imports", def_name=None
            )
        )
        out.append(
            ExpectedSlot(
                file=proof_rel, prefix="benchmark", key="global_aux", def_name=None
            )
        )
        for spec in m.specs:
            bare = spec[len("spec_") :] if spec.startswith("spec_") else spec
            for kind in proof_kinds:
                thm = f"{kind}_{bare}"
                out.append(
                    ExpectedSlot(
                        file=proof_rel,
                        prefix="benchmark",
                        key="proof_aux",
                        def_name=thm,
                    )
                )
                out.append(
                    ExpectedSlot(
                        file=proof_rel,
                        prefix="benchmark",
                        key="proof",
                        def_name=thm,
                        expected_kind=kind,
                        expected_target=spec,
                    )
                )

    # Joint.lean — codeproof only.
    if mode == "codeproof":
        joint_rel = f"{bench.root_package}/Proof/Joint.lean"
        out.extend(
            [
                ExpectedSlot(
                    file=joint_rel, prefix="benchmark", key="imports", def_name=None
                ),
                ExpectedSlot(
                    file=joint_rel,
                    prefix="benchmark",
                    key="global_aux",
                    def_name=None,
                ),
                ExpectedSlot(
                    file=joint_rel,
                    prefix="solution",
                    key="solution",
                    def_name=_JOINT_SLOT,
                    expected_kind="joint_unsat",
                ),
                ExpectedSlot(
                    file=joint_rel,
                    prefix="benchmark",
                    key="proof_aux",
                    def_name=_JOINT_SLOT,
                ),
                ExpectedSlot(
                    file=joint_rel,
                    prefix="benchmark",
                    key="claim",
                    def_name=_JOINT_SLOT,
                    expected_kind="joint_unsat",
                ),
                ExpectedSlot(
                    file=joint_rel,
                    prefix="benchmark",
                    key="proof",
                    def_name=_JOINT_SLOT,
                    expected_kind="joint_unsat",
                ),
            ]
        )

    return out


# ─── Extraction ─────────────────────────────────────────────────


def _missing(es: ExpectedSlot, error: str) -> ExtractedSlot:
    return ExtractedSlot(
        file=es.file,
        prefix=es.prefix,
        key=es.key,
        def_name=es.def_name,
        expected_kind=es.expected_kind,
        expected_target=es.expected_target,
        found=False,
        body_lines=[],
        body_hash=_hash_body([]),
        is_empty=True,
        contains_sorry=False,
        contains_axiom=False,
        contains_admit=False,
        actual_fields={},
        start_line=None,
        end_line=None,
        error=error,
    )


def _from_parsed(es: ExpectedSlot, parsed, root: Path) -> ExtractedSlot:
    body = list(parsed.body)
    err = ""
    # Field consistency — agent must not tamper with kind=/target= on the
    # start marker. Report (but don't fail) if they did.
    if es.expected_kind is not None:
        actual_kind = parsed.fields.get("kind")
        if actual_kind is not None and actual_kind != es.expected_kind:
            err = f"kind_mismatch: expected {es.expected_kind!r}, got {actual_kind!r}"
    if not err and es.expected_target is not None:
        actual_target = parsed.fields.get("target")
        if actual_target is not None and actual_target != es.expected_target:
            err = f"target_mismatch: expected {es.expected_target!r}, got {actual_target!r}"
    return ExtractedSlot(
        file=es.file,
        prefix=es.prefix,
        key=es.key,
        def_name=es.def_name,
        expected_kind=es.expected_kind,
        expected_target=es.expected_target,
        found=True,
        body_lines=body,
        body_hash=_hash_body(body),
        is_empty=_is_effectively_empty(body),
        contains_sorry=_contains_sorry(body),
        contains_axiom=_contains_axiom(body),
        contains_admit=_contains_admit(body),
        actual_fields=dict(parsed.fields),
        start_line=parsed.start_line,
        end_line=parsed.end_line,
        error=err,
    )


def _extra(parsed, root: Path) -> ExtraSlot:
    return ExtraSlot(
        file=str(parsed.file.relative_to(root)),
        prefix=parsed.prefix,
        key=parsed.key,
        def_name=parsed.def_name,
        fields=dict(parsed.fields),
        start_line=parsed.start_line,
        end_line=parsed.end_line,
        body_lines=list(parsed.body),
    )


def extract(sandbox_dir: Path, bench: Benchmark, *, mode: Mode) -> Artifact:
    """Schema-driven extraction.

    Parameters
    ----------
    sandbox_dir:
        Directory to scan for marker slots.
    bench:
        Source benchmark (NOT loaded from the sandbox — the sandbox may no longer have ``manifest.json``). Drives the expected-slot schedule.
    mode:
        Evaluation mode.
    """
    sandbox_dir = Path(sandbox_dir).resolve()
    expected = expected_slots(bench, mode)

    # Group expected by file.
    by_file: dict[str, list[ExpectedSlot]] = {}
    for es in expected:
        by_file.setdefault(es.file, []).append(es)

    slots: list[ExtractedSlot] = []
    extras: list[ExtraSlot] = []
    file_errors: dict[str, str] = {}

    for file_rel, es_in_file in by_file.items():
        path = sandbox_dir / file_rel
        if not path.exists():
            logger.warning("expected file missing from sandbox: {}", file_rel)
            for es in es_in_file:
                slots.append(_missing(es, "file_missing"))
            continue
        try:
            parsed_all = load_slots(path)
        except ValueError as e:
            logger.warning("marker parse failed in {}: {}", file_rel, e)
            file_errors[file_rel] = str(e)
            for es in es_in_file:
                slots.append(_missing(es, f"parse_error: {e}"))
            continue

        # Index parsed slots by (prefix, key, def_name).
        index = {}
        for p in parsed_all:
            index[(p.prefix, p.key, p.def_name)] = p

        for es in es_in_file:
            key = (es.prefix, es.key, es.def_name)
            parsed_slot = index.pop(key, None)
            if parsed_slot is None:
                slots.append(_missing(es, "missing"))
            else:
                slots.append(_from_parsed(es, parsed_slot, sandbox_dir))

        # Anything left is an extra (agent added a marker we didn't plant).
        for (_prefix, _key, _def), p in index.items():
            extras.append(_extra(p, sandbox_dir))

    if extras:
        logger.warning(
            "{} unexpected marker slot(s) in sandbox — agent added markers beyond the schedule",
            len(extras),
        )

    return Artifact(
        benchmark_id=bench.benchmark_id,
        mode=mode,
        sandbox_dir=str(sandbox_dir),
        slots=slots,
        extras=extras,
        file_errors=file_errors,
    )


# ─── Serialisation ──────────────────────────────────────────────


def artifact_to_json(a: Artifact) -> str:
    return json.dumps(
        {
            "benchmark_id": a.benchmark_id,
            "mode": a.mode,
            "sandbox_dir": a.sandbox_dir,
            "slots": [asdict(s) for s in a.slots],
            "extras": [asdict(x) for x in a.extras],
            "file_errors": dict(a.file_errors),
        },
        indent=2,
    )


def write_artifact(a: Artifact, path: Path) -> None:
    path.write_text(artifact_to_json(a), encoding="utf-8")


def artifact_from_dict(d: dict) -> Artifact:
    """Reconstruct an :class:`Artifact` from its ``artifact_to_json`` dict.

    The inverse of :func:`artifact_to_json` — used by the resume path to
    seed a fresh sandbox with a prior run's filled slot bodies. Tolerant of
    unknown keys (forward-compat) by filtering to each dataclass's fields.
    """

    def _pick(cls, raw: dict) -> dict:
        allowed = {f.name for f in fields(cls)}
        return {k: v for k, v in raw.items() if k in allowed}

    slots = [ExtractedSlot(**_pick(ExtractedSlot, s)) for s in d.get("slots", [])]
    extras = [ExtraSlot(**_pick(ExtraSlot, x)) for x in d.get("extras", [])]
    return Artifact(
        benchmark_id=d.get("benchmark_id", ""),
        mode=d.get("mode", ""),
        sandbox_dir=d.get("sandbox_dir", ""),
        slots=slots,
        extras=extras,
        file_errors=dict(d.get("file_errors", {})),
    )


def read_artifact(path: Path) -> Artifact:
    """Load an ``artifact.json`` written by :func:`write_artifact`."""
    return artifact_from_dict(json.loads(Path(path).read_text(encoding="utf-8")))


# ─── Convenience views used by the evaluator ────────────────────


def slots_by(
    a: Artifact,
    *,
    key: str | None = None,
    prefix: str | None = None,
) -> list[ExtractedSlot]:
    out = a.slots
    if prefix is not None:
        out = [s for s in out if s.prefix == prefix]
    if key is not None:
        out = [s for s in out if s.key == key]
    return out


def proof_slot(a: Artifact, def_name: str) -> ExtractedSlot | None:
    """Return the expected ``!benchmark proof`` slot for ``def_name``.

    Always returns the expected slot (found or missing) when ``def_name``
    is part of the schedule; returns None only for names the schedule
    doesn't know about.
    """
    for s in a.slots:
        if s.prefix == "benchmark" and s.key == "proof" and s.def_name == def_name:
            return s
    return None


def solution_slot(a: Artifact, def_name: str) -> ExtractedSlot | None:
    """Return the expected ``!solution`` slot for ``def_name``."""
    for s in a.slots:
        if s.prefix == "solution" and s.def_name == def_name:
            return s
    return None
