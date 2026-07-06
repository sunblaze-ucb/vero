"""Lean source utilities — theorem→spec extraction for the lean_spec workflow.

This module exposes pure helpers used by the agent (via ``vero-source-lean``)
to mechanise the simple cases of theorem→spec extraction:

- :func:`enumerate_theorems` finds ``theorem`` / ``lemma`` declarations and
  returns name + signature + proof-term span. Used to pre-populate the
  discovery and select markdown.
- :func:`enumerate_executables` returns top-level ``def`` declarations that
  look like API candidates (excludes ``def spec_*``, ``def _*``, and nested
  defs inside type-class instances).
- :func:`reshape_theorem_to_spec` mechanically rewrites a theorem signature
  into a ``def spec_<name> (impl : RepoImpl) : Prop := …`` shell. The agent
  is expected to swap bare API references → ``impl.<repo_impl_field>.<fn>``
  by hand (the helper doesn't know the bundle field name) but the
  scaffold is the boring part.

These helpers are deliberately regex-based — Lean's full syntax is too
rich for a hand-rolled parser, but the common shapes (``theorem name
[binders] : Prop := by tactics``) are easy.
"""

from __future__ import annotations

import re
from dataclasses import dataclass

_THEOREM_RE = re.compile(
    r"^[ \t]*(?:@\[[^\]]*\][ \t\n]*)?(theorem|lemma)[ \t]+(?P<name>\S+)(?P<sig>[\s\S]*?)(?P<sep>:=|where)(?=\s)",
    re.MULTILINE,
)

_DEF_RE = re.compile(
    r"^[ \t]*(?:@\[[^\]]*\][ \t\n]*)?def[ \t]+(?P<name>\S+)(?P<sig>[\s\S]*?)(?::=|where)(?=\s)",
    re.MULTILINE,
)


@dataclass(frozen=True)
class TheoremDecl:
    name: str
    sig: str
    line_no: int


@dataclass(frozen=True)
class DefDecl:
    name: str
    sig: str
    line_no: int


def _line_no(text: str, offset: int) -> int:
    return text.count("\n", 0, offset) + 1


def enumerate_theorems(source: str) -> list[TheoremDecl]:
    """Find every theorem / lemma declaration in a Lean source string."""
    out: list[TheoremDecl] = []
    for m in _THEOREM_RE.finditer(source):
        sig = re.sub(r"\s+", " ", m.group("sig")).strip()
        # Drop a leading `:` so callers see just the signature body.
        if sig.startswith(":"):
            sig = sig[1:].strip()
        out.append(
            TheoremDecl(
                name=m.group("name"),
                sig=sig,
                line_no=_line_no(source, m.start()),
            )
        )
    return out


def enumerate_executables(source: str) -> list[DefDecl]:
    """Find candidate API defs — top-level, not `spec_*` / `_*`."""
    out: list[DefDecl] = []
    for m in _DEF_RE.finditer(source):
        name = m.group("name")
        # Strip leading namespace path for the filter check (Foo.bar → bar).
        tail = name.rsplit(".", 1)[-1]
        if tail.startswith("spec_") or tail.startswith("_"):
            continue
        sig = re.sub(r"\s+", " ", m.group("sig")).strip()
        if sig.startswith(":"):
            sig = sig[1:].strip()
        out.append(DefDecl(name=name, sig=sig, line_no=_line_no(source, m.start())))
    return out


def reshape_theorem_to_spec(decl: TheoremDecl) -> str:
    """Emit a `def spec_<name> (impl : RepoImpl) : Prop := …` shell.

    The shell captures the theorem's signature as the spec body. The agent
    is expected to bundle-qualify API references by hand. The proof is
    dropped (replaced by `sorry` since this is a *spec* not a theorem,
    callers only consume the `: Prop := <body>` part).
    """
    spec_name = decl.name if decl.name.startswith("spec_") else f"spec_{decl.name}"
    body = decl.sig.strip()
    if not body:
        body = "True  -- TODO: fill from theorem statement"
    return (
        f"def {spec_name} (impl : RepoImpl) : Prop :=\n"
        f"  -- shell from theorem `{decl.name}` (line {decl.line_no})\n"
        f"  -- bundle-qualify API refs (impl.<repo_impl_field>.<fn>) before declaring done\n"
        f"  {body}\n"
    )
