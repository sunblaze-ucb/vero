"""Skill-invocation preamble for stage prompts.

Skills are loaded lazily by the model via the built-in ``Skill`` tool (see
``agent.py``). Each stage prompt names the skills the agent should invoke for
its language; this module centralizes those mappings so that routing logic is
not duplicated across stage files.
"""

from __future__ import annotations

from vero.curation.models import SourceLanguage

_PRIMARY_SKILL = {
    "discover": "vero-discover",
    "select": "vero-select",
    "plan": "vero-plan",
    "translate": "vero-translate",
    "spec_write": "vero-spec-write",
}

_SOURCE_SKILL = {
    SourceLanguage.DAFNY: (
        "vero-source-dafny",
        "Dafny-specific type/function mappings",
    ),
    SourceLanguage.VERUS: (
        "vero-source-verus",
        "Verus-specific type/function mappings",
    ),
    SourceLanguage.COQ: ("vero-source-coq", "Coq-specific type/function mappings"),
    SourceLanguage.PYTHON: (
        "vero-source-python",
        "Python→Lean type/function mappings + stdlib opaque-modeling guidance",
    ),
    SourceLanguage.LEAN: (
        "vero-source-lean",
        "Lean source — extract specs from existing theorems, no new translation",
    ),
}

_PITFALL_SKILL = {
    SourceLanguage.DAFNY: (
        "vero-dafny-pitfalls",
        "known Dafny→Lean translation pitfalls",
    ),
    SourceLanguage.VERUS: (
        "vero-verus-pitfalls",
        "known Verus→Lean translation pitfalls",
    ),
    SourceLanguage.COQ: ("vero-coq-pitfalls", "known Coq→Lean translation pitfalls"),
    SourceLanguage.PYTHON: (
        "vero-python-pitfalls",
        "known Python→Lean translation pitfalls + stdlib opaque modeling",
    ),
    # Lean source has no separate pitfalls skill — Lean→Lean reuses
    # vero-lean-pitfalls (already loaded for `translate`).
}

_STAGE_PRIMARY_DESC = {
    "discover": "the discovery workflow and output format",
    "select": "the dependency-closure and layout workflow",
    "plan": "the translation-plan and architecture-sketch workflow",
    "translate": "the translation workflow (layer-by-layer, markers, review comments)",
    "spec_write": "the two-substep spec authoring workflow (reason → formalize)",
}


def skill_preamble(stage: str, language: SourceLanguage | None = None) -> str:
    """Build a prompt preamble listing skills the agent should invoke.

    Args:
        stage: one of ``"discover"``, ``"select"``, ``"plan"``, ``"translate"``.
        language: source language for stages that need a language-specific
            skill pair. Omit for ``"select"``.

    Returns:
        A markdown block naming the skills, suitable for prepending to the
        stage's user prompt. The model is expected to invoke each skill
        via the ``Skill`` tool before acting.
    """
    entries: list[tuple[str, str]] = []

    primary = _PRIMARY_SKILL.get(stage)
    if primary is None:
        raise ValueError(f"Unknown stage: {stage!r}")
    entries.append((primary, _STAGE_PRIMARY_DESC[stage]))

    if language is not None and stage in {"discover", "plan", "translate"}:
        source = _SOURCE_SKILL.get(language)
        if source:
            entries.append(source)

    if stage == "translate":
        if language is not None:
            pitfall = _PITFALL_SKILL.get(language)
            if pitfall:
                entries.append(pitfall)
        entries.append(("vero-lean-pitfalls", "known Lean 4 pitfalls"))

    lines = ["## Skills to use", ""]
    if stage == "translate":
        lines.append(
            "Before doing any translation, invoke these skills in order via the "
            "`Skill` tool:"
        )
    else:
        lines.append("Before starting, invoke these skills via the `Skill` tool:")
    for i, (name, desc) in enumerate(entries, 1):
        lines.append(f"{i}. `{name}` — {desc}")
    lines.append("")
    lines.append(
        "Keep their guidance in mind throughout. Re-invoke a skill if you "
        "need to refresh its content."
    )
    return "\n".join(lines)
