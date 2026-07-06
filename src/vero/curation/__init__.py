"""Curation Pipeline v2 — Verified Code (Dafny/Verus/Coq) to Lean 4 Benchmarks.

Uses Claude Code SDK to translate formally-verified source code into compilable
Lean 4 projects with sorry stubs as benchmark tasks. Output is a Lean project
with `-- !benchmark @start/@end` markers for task boundary extraction.

Usage:
    python -m vero.curation run /path/to/source output/project --lang dafny
    python -m vero.curation run output/project --stage select
    python -m vero.curation status output/project
"""
