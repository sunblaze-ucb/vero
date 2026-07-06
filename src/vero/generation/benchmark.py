"""Benchmark loader — read ``manifest.json`` and enumerate marker slots.

Thin wrapper around ``manifest.json`` + ``validation/markers.py``. The loader exposes typed views used by the sandbox builder, agent runner, extractor, and evaluator:

- :class:`Benchmark` — manifest-backed root object.
- :class:`Package` — one entry of ``manifest.packages[]``.
- :class:`Module` — one entry of ``package.modules[]``.
- :class:`ApiInfo` — one entry of ``module.apis[]``.
- :class:`SlotRef` — a paired ``!benchmark`` or ``!solution`` slot with file path, key, def name, and fields.

All paths in ``manifest.json`` are relative to the benchmark root (the directory containing ``manifest.json``). Helpers that return file paths return absolute paths resolved against the root.
"""

from __future__ import annotations

import json
from dataclasses import dataclass, field
from pathlib import Path
from typing import Iterable, Iterator

from vero.curation.validation.markers import (
    SlotPair,
    pair_slots,
    parse_file_markers,
)


@dataclass(frozen=True)
class ApiInfo:
    name: str
    sig: str
    type: str


def manifest_spec_name(entry: object) -> str:
    """Return the Lean declaration name for legacy or rich manifest spec entries."""
    if isinstance(entry, str):
        return entry
    if isinstance(entry, dict):
        name = entry.get("name")
        if isinstance(name, str) and name:
            return name
    raise ValueError(
        f"manifest spec entry must be a string or dict with name: {entry!r}"
    )


@dataclass(frozen=True)
class Module:
    package: str
    name: str
    # impl_rel is None for spec-only modules (no executable code to fill).
    # spec_rel is None for opaque / vocabulary-only modules (no specs to prove).
    impl_rel: str | None
    spec_rel: str | None
    apis: tuple[ApiInfo, ...]
    specs: tuple[str, ...]

    def impl_path(self, root: Path) -> Path | None:
        if self.impl_rel is None:
            return None
        return (root / self.impl_rel).resolve()

    def spec_path(self, root: Path) -> Path | None:
        if self.spec_rel is None:
            return None
        return (root / self.spec_rel).resolve()

    def proof_rel(self) -> str:
        """Path to ``<Package>/Proof/<Module>.lean`` relative to benchmark root."""
        return f"{self.package}/Proof/{self.name}.lean"


@dataclass(frozen=True)
class Package:
    name: str
    bundle_rel: str
    bundle_type: str
    repo_impl_field: str
    modules: tuple[Module, ...]


@dataclass(frozen=True)
class SlotRef:
    file: Path  # absolute path
    key: str  # one of the 7 benchmark keys, or "solution"
    prefix: str  # "benchmark" | "solution"
    def_name: str | None
    fields: dict[str, str]
    start_line: int  # 1-based line of @start
    end_line: int  # 1-based line of @end
    body: tuple[str, ...] = field(default_factory=tuple)


class Benchmark:
    """Loaded benchmark rooted at a directory containing ``manifest.json``."""

    def __init__(self, root: Path):
        self.root = Path(root).resolve()
        manifest_path = self.root / "manifest.json"
        if not manifest_path.exists():
            raise FileNotFoundError(f"manifest.json not found at {manifest_path}")
        self.manifest: dict = json.loads(manifest_path.read_text())
        # Detect legacy pre-bundle manifests (e.g. lean-regex curated under the
        # old pipeline) — they have `task_index` instead of `packages` and lack
        # `root_package` / `files`. Refuse early with a clear message instead
        # of crashing with a KeyError mid-construction.
        if "root_package" not in self.manifest or "packages" not in self.manifest:
            legacy_marker = "task_index" in self.manifest
            hint = (
                " (legacy pre-bundle manifest detected — task_index/file_map "
                "shape; re-curate via the `lean_spec` or `verified_to_lean` "
                "workflow to produce the new bundle paradigm)"
                if legacy_marker
                else ""
            )
            raise ValueError(
                f"manifest at {manifest_path} is missing required keys "
                f"`root_package` / `packages`{hint}"
            )
        self.benchmark_id: str = self.manifest["benchmark_id"]
        self.lean_version: str = self.manifest["lean_version"]
        self.modes_supported: tuple[str, ...] = tuple(
            self.manifest.get("modes_supported", [])
        )
        self.root_package: str = self.manifest["root_package"]
        self.trusted_axioms: tuple[str, ...] = tuple(
            self.manifest.get("trusted_axioms", [])
        )
        files = self.manifest.get("files", {})
        self.root_hub_rel: str = files.get("root_hub", f"{self.root_package}.lean")
        self.harness_rel: str = files.get(
            "harness", f"{self.root_package}/Harness.lean"
        )
        self.test_rel: str = files.get("test", f"{self.root_package}/Test.lean")
        self.lakefile_rel: str = files.get("lakefile", "lakefile.toml")
        self.packages: tuple[Package, ...] = tuple(self._load_packages())

    # ─── Manifest parsing ───────────────────────────────────────

    def _load_packages(self) -> Iterable[Package]:
        for raw in self.manifest.get("packages", []):
            modules = []
            for m in raw.get("modules", []):
                apis = tuple(
                    ApiInfo(name=a["name"], sig=a["sig"], type=a.get("type", ""))
                    for a in m.get("apis", [])
                )
                modules.append(
                    Module(
                        package=raw["name"],
                        name=m["name"],
                        impl_rel=m.get("impl"),
                        spec_rel=m.get("spec"),
                        apis=apis,
                        specs=tuple(
                            manifest_spec_name(spec) for spec in m.get("specs", [])
                        ),
                    )
                )
            yield Package(
                name=raw["name"],
                bundle_rel=raw["bundle"],
                bundle_type=raw["bundle_type"],
                repo_impl_field=raw["repo_impl_field"],
                modules=tuple(modules),
            )

    # ─── Convenience views ──────────────────────────────────────

    @property
    def root_hub_path(self) -> Path:
        return (self.root / self.root_hub_rel).resolve()

    @property
    def harness_path(self) -> Path:
        return (self.root / self.harness_rel).resolve()

    @property
    def test_path(self) -> Path:
        return (self.root / self.test_rel).resolve()

    def iter_modules(self) -> Iterator[Module]:
        for pkg in self.packages:
            yield from pkg.modules

    def all_impl_files(self) -> list[Path]:
        return [
            p for m in self.iter_modules() if (p := m.impl_path(self.root)) is not None
        ]

    def all_spec_files(self) -> list[Path]:
        return [
            p for m in self.iter_modules() if (p := m.spec_path(self.root)) is not None
        ]

    # Paths to *generated* Proof files for a given mode, per module.
    def proof_file_rel(self, module: Module) -> str:
        return module.proof_rel()

    def proof_file_path(self, module: Module) -> Path:
        return (self.root / self.proof_file_rel(module)).resolve()

    def joint_file_rel(self) -> str:
        return f"{self.root_package}/Proof/Joint.lean"

    def joint_file_path(self) -> Path:
        return (self.root / self.joint_file_rel()).resolve()


# ─── Slot extraction ───────────────────────────────────────────


def _slot_body(file_lines: list[str], pair: SlotPair) -> tuple[str, ...]:
    """Lines strictly between @start (exclusive) and @end (exclusive), verbatim."""
    start = pair.start_line  # 1-based, this IS the @start line
    end = pair.end_line  # 1-based, this IS the @end line
    # file_lines is 0-indexed; interior = (start, end) exclusive of both
    return tuple(file_lines[start : end - 1])


def load_slots(file: Path) -> list[SlotRef]:
    """Read every paired ``!benchmark``/``!solution`` slot from ``file``.

    Lines inside block comments are skipped per the marker parser's rules.
    """
    file = Path(file).resolve()
    markers = parse_file_markers(file)
    pairs, errors = pair_slots(markers)
    if errors:
        raise ValueError(f"marker pairing errors in {file}: {errors}")
    file_lines = file.read_text().splitlines()
    out: list[SlotRef] = []
    for p in pairs:
        out.append(
            SlotRef(
                file=file,
                key=p.key,
                prefix=p.prefix,
                def_name=p.def_name,
                fields=dict(p.fields),
                start_line=p.start_line,
                end_line=p.end_line,
                body=_slot_body(file_lines, p),
            )
        )
    return out


def all_editable_files(bench: Benchmark) -> list[Path]:
    """Every file in the curation-stage benchmark that carries marker slots.

    This is ``Impl/*.lean`` for the curation-stage artifact. The
    post-materialize sandbox also adds ``Proof/*.lean`` and
    ``Proof/Joint.lean`` (codeproof); those are enumerated by
    :func:`proof_editable_files`.
    """
    return bench.all_impl_files()


def proof_editable_files(bench: Benchmark, mode: str) -> list[Path]:
    """``Proof/*.lean`` files that exist (or will exist) after materialize.

    Modules without any specs get no proof stub file, so they're excluded.
    """
    out = [bench.proof_file_path(m) for m in bench.iter_modules() if m.specs]
    if mode == "codeproof":
        out.append(bench.joint_file_path())
    return out
