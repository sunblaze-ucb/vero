"""Lean 4 project scaffolding helpers.

Scaffolds a Lean project that matches the ratified paradigm
(see ``reference/BankLedger/`` for the canonical shape). The lakefile
uses the top-level-fields form with ``defaultTargets`` and ``srcDir="."``;
the ``[package]`` form is gone. Default Lean is pinned to 4.29.1 but
callers may override.

Mathlib is declared as a require by default so materialized benchmarks
can ``import Mathlib.…`` from any Impl/Spec/Proof file. The mathlib
revision is pinned to a Lean-version-matching tag (e.g. lean
``v4.29.1`` ⇒ mathlib ``v4.29.1``); since these tags are immutable,
gen-side and eval-side sandboxes resolve to the same mathlib commit on
their respective first builds even though no ``lake-manifest.json`` is
committed at curation time.
"""

from __future__ import annotations

from pathlib import Path

_LAKEFILE_TEMPLATE_NO_MATHLIB = """\
name = "{project_name}"
version = "0.1.0"
defaultTargets = ["{project_name}"]

[[lean_lib]]
name = "{project_name}"
srcDir = "."
leanOptions = [{{ name = "autoImplicit", value = false }}]
"""

_LAKEFILE_TEMPLATE_MATHLIB = """\
name = "{project_name}"
version = "0.1.0"
defaultTargets = ["{project_name}"]

[[require]]
scope = "leanprover-community"
name = "mathlib"
rev = "{mathlib_rev}"

[[lean_lib]]
name = "{project_name}"
srcDir = "."
leanOptions = [{{ name = "autoImplicit", value = false }}]
"""


def _default_mathlib_rev(lean_version: str) -> str:
    """Mathlib publishes a matching ``vX.Y.Z`` tag for each Lean release."""
    return f"v{lean_version}"


def create_lean_project(
    output_dir: Path,
    project_name: str,
    lean_version: str = "4.29.1",
    *,
    with_mathlib: bool = True,
    mathlib_rev: str | None = None,
) -> Path:
    """Create a minimal Lean 4 project scaffold.

    Returns the project root directory (``<output_dir>/<project_name>``).

    Parameters
    ----------
    with_mathlib:
        Add a ``[[require]]`` block pinning ``mathlib`` to ``mathlib_rev``
        (default: the matching ``vX.Y.Z`` tag for ``lean_version``). Set
        ``False`` for tests or for benchmarks that genuinely don't want
        mathlib (e.g. to keep a tiny exemplar's CI fast).
    mathlib_rev:
        Pin for the mathlib require. ``None`` means
        ``v{lean_version}``. Ignored when ``with_mathlib`` is ``False``.
    """
    project_dir = output_dir / project_name
    project_dir.mkdir(parents=True, exist_ok=True)
    (project_dir / project_name).mkdir(exist_ok=True)

    (project_dir / "lean-toolchain").write_text(
        f"leanprover/lean4:v{lean_version}\n",
        encoding="utf-8",
    )

    if with_mathlib:
        body = _LAKEFILE_TEMPLATE_MATHLIB.format(
            project_name=project_name,
            mathlib_rev=mathlib_rev or _default_mathlib_rev(lean_version),
        )
    else:
        body = _LAKEFILE_TEMPLATE_NO_MATHLIB.format(project_name=project_name)
    (project_dir / "lakefile.toml").write_text(body, encoding="utf-8")

    return project_dir


def write_root_import_hub(
    project_dir: Path,
    project_name: str,
    lean_files: list[str],
) -> Path:
    """Write the root .lean file that imports all modules.

    ``lean_files`` is a list of module paths relative to the project
    directory, e.g. ``["BankLedger/Impl/Account", "BankLedger/Harness"]``.
    """
    root_file = project_dir / f"{project_name}.lean"
    lines = [f"import {f.replace('/', '.')}" for f in lean_files]
    root_file.write_text("\n".join(lines) + "\n", encoding="utf-8")
    return root_file


def to_project_name(benchmark_id: str) -> str:
    """Convert ``'deposit-sc-dafny'`` → ``'DepositScDafny'`` (valid Lean name).

    Also handles benchmark ids with sub-path segments like
    ``'geodesy/distance'`` — slashes / dots are normalised the same as
    hyphens / underscores so the result is a single CamelCase token.
    """
    parts = (
        benchmark_id.replace("-", " ")
        .replace("_", " ")
        .replace("/", " ")
        .replace(".", " ")
        .split()
    )
    return "".join(p.capitalize() for p in parts)
