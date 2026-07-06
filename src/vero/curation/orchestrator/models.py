"""Data models for the orchestrator-executor pipeline."""

from __future__ import annotations

from pydantic import BaseModel


class TranslationUnit(BaseModel):
    """One parallelizable unit: one module's Impl + Spec."""

    module_name: str  # e.g. "Account"
    package_name: str  # e.g. "BankLedger"
    layer: int  # 0 = no inter-module deps
    impl_path: str  # relative: "BankLedger/Impl/Account.lean"
    spec_path: str  # relative: "BankLedger/Spec/Account.lean"
    upstream_files: list[str] = []  # source files this module translates from
    apis: list[dict] = []  # [{lean_name, sig_abbrev, lean_type, ...}]
    api_helpers: list[dict] = []  # fully-defined helpers, no Bundle fields
    specs: list[dict] = []  # [{name, lean_form, ...}]
    spec_helpers: list[dict] = []  # frozen vocabulary used by specs/APIs
    types: list[dict] = []  # [{name, lean_form, is_foundation}]
    dependencies: list[str] = []  # module names this depends on


class ExecutorResult(BaseModel):
    """Result from a single executor run."""

    module_name: str
    success: bool
    impl_content: str = ""
    spec_content: str = ""
    build_ok: bool = False
    build_output: str = ""
    marker_errors: list[str] = []
    error: str = ""
    attempt: int = 1
    session_id: str = ""


class OrchestratorState(BaseModel):
    """Persisted orchestration progress — survives restarts."""

    units: list[TranslationUnit] = []
    completed: dict[str, ExecutorResult] = {}  # module_name → result
    failed: dict[str, ExecutorResult] = {}  # module_name → result
    current_layer: int = 0
    total_layers: int = 0
