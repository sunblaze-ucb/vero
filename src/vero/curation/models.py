"""Data models for the curation pipeline."""

from __future__ import annotations

from enum import Enum
from typing import Optional

from pydantic import BaseModel


class SourceLanguage(str, Enum):
    DAFNY = "dafny"
    VERUS = "verus"
    COQ = "coq"
    PYTHON = "python"
    LEAN = "lean"


class ItemCategory(str, Enum):
    TYPE = "type"
    SPEC_FN = "spec-fn"
    EXEC_FN = "exec-fn"
    PREDICATE = "predicate"
    THEOREM = "theorem"
    AXIOM = "axiom"
    TEST = "test"
    OPAQUE = "opaque"


class Visibility(str, Enum):
    PUBLIC = "public"
    INTERNAL = "internal"
    PRIVATE = "private"


class SpecKind(str, Enum):
    FUNCTIONAL = "functional"
    INVARIANT_HELPER = "helper"
    CHARACTERIZING = "characterizing"
    TAUTOLOGICAL = "tautological"


class BodyDisposition(str, Enum):
    GIVEN = "given"
    SORRY = "sorry"
    OPAQUE = "opaque"
    BY_SORRY = "by_sorry"


class EntityRole(str, Enum):
    UNCLASSIFIED = "unclassified"
    SCORED_API = "scored_api"
    SCORED_SPEC = "scored_spec"
    API_HELPER = "api_helper"
    SEMANTIC_MODEL = "semantic_model"
    SPEC_HELPER = "spec_helper"
    TRUSTED_THEORY = "trusted_theory"
    TRUSTED_EXTERNAL = "trusted_external"
    PROOF_HELPER_TASK = "proof_helper_task"
    TRUSTED_THEOREM = "trusted_theorem"
    REFERENCE_API = "reference_api"
    DROPPED_WITH_REASON = "dropped_with_reason"
    REQUIRES_HUMAN_REVIEW = "requires_human_review"


class EntityDisposition(str, Enum):
    UNCLASSIFIED = "unclassified"
    PROVIDED = "provided"
    SCORED = "scored"
    HIDDEN = "hidden"
    DROPPED = "dropped"
    AXIOMATIZED = "axiomatized"
    OPAQUE = "opaque"


class DiscoveredItem(BaseModel):
    """One item discovered in the source repository."""

    name: str
    qualified_name: str
    category: ItemCategory
    visibility: Visibility
    spec_kind: Optional[SpecKind] = None
    body_disposition: BodyDisposition
    source_file: str
    source_line: int
    signature_summary: str
    dependencies: list[str] = []
    notes: str = ""
    role: Optional[EntityRole] = None
    default_role: Optional[EntityRole] = None
    disposition: Optional[EntityDisposition] = None
    source_id: str = ""
    drop_reason: str = ""

    # Filled during SELECT stage
    selected: bool = False
    closure_added: bool = False
    lean_file: str = ""
    lean_name: str = ""
    layer: int = -1


class DiscoveryReport(BaseModel):
    """Full output of the DISCOVER stage."""

    source_language: SourceLanguage
    source_dir: str
    commit_hash: str = ""
    repo_url: str = ""
    items: list[DiscoveredItem] = []
    file_summaries: dict[str, dict] = {}


class SourceIndexEntity(BaseModel):
    """One best-effort no-LLM source-index entity."""

    id: str
    name: str
    qualified_name: str = ""
    kind: str
    source_file: str
    source_line: int = 0
    signature: str = ""
    default_role: EntityRole = EntityRole.REQUIRES_HUMAN_REVIEW
    disposition: EntityDisposition = EntityDisposition.PROVIDED
    selected: bool = True
    dependencies: list[str] = []
    notes: str = ""


class SourceIndex(BaseModel):
    """No-LLM source-wide entity registry."""

    version: int = 1
    source_language: Optional[SourceLanguage] = None
    source_path: str = ""
    entities: list[SourceIndexEntity] = []


class SelectionPlan(BaseModel):
    """Output of the SELECT stage."""

    selected_items: list[DiscoveredItem] = []
    layers: dict[int, list[str]] = {}
    lean_files: dict[str, list[str]] = {}
    closure_warnings: list[str] = []
    estimated_sorry: int = 0
    estimated_opaque: int = 0
    estimated_axiom: int = 0


class TaskEntry(BaseModel):
    """One benchmark task extracted from markers in the Lean project."""

    key: str  # e.g., "code", "spec", "proof"
    api: str  # e.g., "deposit"
    file: str  # e.g., "Contract.lean"
    line: int
    content: str
    is_sorry: bool = False


class FileMapEntry(BaseModel):
    """Maps a source file to its Lean translation."""

    source: str
    lean: str
    layer: int = 0


class SpecIndexEntry(BaseModel):
    """Tracks a spec/theorem in the Lean project back to its source."""

    name: str
    file: str
    line: int = 0
    source_theorem: str = ""


class CurationManifest(BaseModel):
    """Metadata stored alongside the Lean project as manifest.json."""

    benchmark_id: str
    source_language: SourceLanguage
    repo_url: str = ""
    commit_hash: str = ""
    curation_timestamp: str = ""
    lean_version: str = "4.22.0"
    discovery: Optional[DiscoveryReport] = None
    selection: Optional[SelectionPlan] = None
    metrics: dict = {}
    task_index: list[TaskEntry] = []
    file_map: list[FileMapEntry] = []
    spec_index: list[SpecIndexEntry] = []
