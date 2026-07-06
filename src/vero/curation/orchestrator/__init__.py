"""Orchestrator-executor architecture for scalable annotation.

Decomposes the translation stage into per-module tasks, runs them in
parallel (respecting layer dependencies), and assembles the results
into a coherent Lean project.
"""

from vero.curation.orchestrator.orchestrator import TranslationOrchestrator

__all__ = ["TranslationOrchestrator"]
