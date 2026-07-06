"""Tool implementations for the orchestrator agent.

These are invoked via the CLI dispatcher (``dispatch.py``) when the
orchestrator agent calls Bash commands. Each function reads/writes
state from the workspace directory.
"""

from __future__ import annotations

import asyncio
import fcntl
import json
from pathlib import Path

import anyio

from vero.curation.config import CurationConfig
from vero.curation.marker import count_metrics, validate_markers
from vero.curation.orchestrator.executor import run_executor
from vero.curation.orchestrator.models import (
    ExecutorResult,
    OrchestratorState,
    TranslationUnit,
)


def _state_path(workspace: Path) -> Path:
    return workspace / "curation" / "orchestrator_state.json"


def _layer_lock_path(workspace: Path, layer: int) -> Path:
    return workspace / "curation" / "locks" / f"dispatch_layer_{layer}.lock"


def _try_acquire_layer_lock(workspace: Path, layer: int):
    """Acquire a non-blocking process lock for one layer dispatch.

    The lock is intentionally held for the full async executor run. Closing the
    returned file releases it, and the OS releases it automatically if the
    dispatch process is killed.
    """
    path = _layer_lock_path(workspace, layer)
    path.parent.mkdir(parents=True, exist_ok=True)
    lock_file = path.open("w", encoding="utf-8")
    try:
        fcntl.flock(lock_file.fileno(), fcntl.LOCK_EX | fcntl.LOCK_NB)
    except BlockingIOError:
        lock_file.close()
        return None
    lock_file.write(json.dumps({"layer": layer}) + "\n")
    lock_file.flush()
    return lock_file


def load_state(workspace: Path) -> OrchestratorState:
    path = _state_path(workspace)
    if path.exists():
        return OrchestratorState.model_validate_json(path.read_text(encoding="utf-8"))
    return OrchestratorState()


def save_state(workspace: Path, state: OrchestratorState) -> None:
    path = _state_path(workspace)
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(
        state.model_dump_json(indent=2),
        encoding="utf-8",
    )


def analyze_plan(workspace: Path) -> dict:
    """Parse plan.json and return structured decomposition."""
    vero_dir = workspace / ".vero"
    plan_path = vero_dir / "plan.json"

    if not plan_path.exists():
        return {"error": f"plan.json not found at {plan_path}"}

    plan = json.loads(plan_path.read_text(encoding="utf-8"))
    api_namespace = plan.get("api_namespace", "")

    units: list[TranslationUnit] = []
    all_module_types: dict[str, list[str]] = {}  # module → type names
    symbol_owner: dict[str, str] = {}

    for pkg in plan.get("packages", []):
        for mod in pkg.get("modules", []):
            mod_name = mod["name"]
            types = mod.get("types", [])
            type_names = [t["name"] for t in types]
            all_module_types[mod_name] = type_names
            for collection in ("types", "apis", "api_helpers", "spec_helpers"):
                for item in mod.get(collection, []):
                    for name in {
                        item.get("lean_name"),
                        item.get("name"),
                        item.get("upstream_name"),
                    }:
                        if name and name not in symbol_owner:
                            symbol_owner[name] = mod_name

    module_deps: dict[str, list[str]] = {}
    for pkg in plan.get("packages", []):
        for mod in pkg.get("modules", []):
            module_deps[mod["name"]] = _find_module_deps(
                mod,
                all_module_types,
                symbol_owner,
            )

    # Assign layers with a simple topological pass. A module can run once all
    # modules that own referenced types/APIs/helpers have run. If a real cycle
    # remains, keep those modules in one final layer and preserve their deps in
    # the state so the orchestrator can diagnose it.
    module_layers: dict[str, int] = {}
    assigned: set[str] = set()
    remaining = [
        mod for pkg in plan.get("packages", []) for mod in pkg.get("modules", [])
    ]
    layer = 0
    while remaining:
        next_remaining = []
        progressed = False
        already_assigned = set(assigned)
        for mod in remaining:
            deps = module_deps.get(mod["name"], [])
            if all(dep in already_assigned for dep in deps):
                module_layers[mod["name"]] = layer
                assigned.add(mod["name"])
                progressed = True
            else:
                next_remaining.append(mod)
        if not progressed:
            for mod in next_remaining:
                module_layers[mod["name"]] = layer
                assigned.add(mod["name"])
            remaining = []
        else:
            remaining = next_remaining
            layer += 1

    # Build TranslationUnit objects
    for pkg in plan.get("packages", []):
        pkg_name = pkg["name"]
        for mod in pkg.get("modules", []):
            mod_name = mod["name"]
            mod_path = mod_name.replace(".", "/")
            mod_layer = module_layers.get(mod_name, 0)

            deps = module_deps.get(mod_name, [])

            unit = TranslationUnit(
                module_name=mod_name,
                package_name=pkg_name,
                layer=mod_layer,
                impl_path=f"{pkg_name}/Impl/{mod_path}.lean",
                spec_path=f"{pkg_name}/Spec/{mod_path}.lean",
                upstream_files=mod.get("upstream_files", []),
                apis=mod.get("apis", []),
                api_helpers=mod.get("api_helpers", []),
                specs=mod.get("specs", []),
                spec_helpers=mod.get("spec_helpers", []),
                types=mod.get("types", []),
                dependencies=deps,
            )
            units.append(unit)

    # Group by layer for display
    layers: dict[int, list[str]] = {}
    for u in units:
        layers.setdefault(u.layer, []).append(u.module_name)

    # Save units to state
    state = load_state(workspace)
    state.units = units
    state.total_layers = max(layers.keys(), default=0) + 1
    save_state(workspace, state)

    return {
        "api_namespace": api_namespace,
        "total_modules": len(units),
        "total_layers": state.total_layers,
        "layers": {str(k): v for k, v in sorted(layers.items())},
        "modules": [
            {
                "name": u.module_name,
                "package": u.package_name,
                "layer": u.layer,
                "apis": [a.get("lean_name", "") for a in u.apis],
                "api_helpers": [
                    h.get("lean_name", h.get("name", "")) for h in u.api_helpers
                ],
                "types": [t.get("name", "") for t in u.types],
                "spec_helpers": [
                    h.get("lean_name", h.get("name", "")) for h in u.spec_helpers
                ],
                "specs": [s.get("name", "") for s in u.specs],
                "dependencies": u.dependencies,
            }
            for u in units
        ],
    }


def _find_module_deps(
    mod: dict,
    all_module_types: dict[str, list[str]],
    symbol_owner: dict[str, str],
) -> list[str]:
    """Return modules that own symbols referenced by this module.

    Translation executors must import externally-owned vocabulary rather than
    re-emitting it. Dependencies therefore include not only API type references
    but also explicit ``apis_referenced`` / ``spec_helpers_referenced`` entries
    and symbol occurrences in frozen spec forms.
    """
    own = mod.get("name")
    deps: list[str] = []

    def add(owner: str | None) -> None:
        if owner and owner != own and owner not in deps:
            deps.append(owner)

    texts: list[str] = []
    for collection in ("types", "api_helpers", "spec_helpers"):
        for item in mod.get(collection, []):
            texts.append(item.get("lean_form", ""))
    for api in mod.get("apis", []):
        texts.append(api.get("lean_type", ""))
    for spec in mod.get("specs", []):
        texts.append(spec.get("lean_form", ""))
        for name in spec.get("apis_referenced", []) or []:
            add(symbol_owner.get(name))
        for name in spec.get("spec_helpers_referenced", []) or []:
            add(symbol_owner.get(name))

    for other_mod, type_names in all_module_types.items():
        if other_mod == own:
            continue
        for text in texts:
            if any(_contains_symbol(text, tn) for tn in type_names):
                add(other_mod)

    for name, owner in symbol_owner.items():
        if owner == own:
            continue
        if any(_contains_symbol(text, name) for text in texts):
            add(owner)

    return deps


def _contains_symbol(text: str, name: str) -> bool:
    """Approximate Lean identifier occurrence without parsing Lean."""
    if not text or not name:
        return False
    import re

    return (
        re.search(rf"(?<![A-Za-z0-9_'.]){re.escape(name)}(?![A-Za-z0-9_'.])", text)
        is not None
    )


async def dispatch_executor(
    workspace: Path,
    module_name: str,
    shared_context: str = "",
) -> dict:
    """Run a single executor agent for one module."""
    config = CurationConfig.load(workspace / "config.yaml")
    state = load_state(workspace)

    # Find the unit
    unit = None
    for u in state.units:
        if u.module_name == module_name:
            unit = u
            break
    if unit is None:
        return {"error": f"Module '{module_name}' not found in state"}

    # Already completed?
    if module_name in state.completed:
        return {
            "status": "already_completed",
            "module": module_name,
        }

    from vero.curation.lean_project import to_project_name

    project_name = to_project_name(config.benchmark_id)
    project_dir = config.lean_output_dir / project_name

    result = await run_executor(
        unit=unit,
        project_dir=project_dir,
        source_dir=config.effective_source_dir,
        shared_context=shared_context,
        language=config.source_language.value if config.source_language else "dafny",
        api_namespace=_get_api_namespace(workspace),
        model=config.model,
        permission_mode=config.permission_mode,
        max_turns=config.max_turns_per_module,
        api_key=config.api_key,
        api_base_url=config.api_base_url,
        enable_lean_mcp=config.enable_lean_mcp,
        **config.agent_kwargs,
    )

    # Update state
    if result.success:
        state.completed[module_name] = result
    else:
        state.failed[module_name] = result
    save_state(workspace, state)

    return {
        "module": module_name,
        "success": result.success,
        "marker_errors": result.marker_errors,
        "error": result.error,
        "impl_written": bool(result.impl_content),
        "spec_written": bool(result.spec_content),
    }


async def dispatch_layer(
    workspace: Path,
    layer: int,
    max_concurrent: int = 4,
) -> dict:
    """Run all executor agents for a given layer in parallel."""
    lock_file = _try_acquire_layer_lock(workspace, layer)
    if lock_file is None:
        return {
            "layer": layer,
            "status": "already_running",
            "lock_path": str(_layer_lock_path(workspace, layer)),
            "completed": [],
            "failed": [],
        }

    config = CurationConfig.load(workspace / "config.yaml")
    try:
        state = load_state(workspace)

        # Get units for this layer that aren't already completed
        units = [
            u
            for u in state.units
            if u.layer == layer and u.module_name not in state.completed
        ]

        if not units:
            return {
                "layer": layer,
                "status": "no_pending_modules",
                "completed": [],
                "failed": [],
            }

        # Build shared context from completed lower layers
        shared_context = build_shared_context(workspace, state, layer)

        from vero.curation.lean_project import to_project_name

        project_name = to_project_name(config.benchmark_id)
        project_dir = config.lean_output_dir / project_name
        api_namespace = _get_api_namespace(workspace)

        sem = asyncio.Semaphore(max_concurrent)

        async def run_with_sem(unit: TranslationUnit) -> ExecutorResult:
            async with sem:
                return await run_executor(
                    unit=unit,
                    project_dir=project_dir,
                    source_dir=config.effective_source_dir,
                    shared_context=shared_context,
                    language=(
                        config.source_language.value
                        if config.source_language
                        else "dafny"
                    ),
                    api_namespace=api_namespace,
                    model=config.model,
                    permission_mode=config.permission_mode,
                    max_turns=config.max_turns_per_module,
                    api_key=config.api_key,
                    api_base_url=config.api_base_url,
                    enable_lean_mcp=config.enable_lean_mcp,
                    **config.agent_kwargs,
                )

        completed_names = []
        failed_names = []
        failed_errors: dict[str, str | list[str]] = {}

        # Persist each executor result as soon as it lands. A large layer can be
        # interrupted by an API/tool failure; partial successes should survive.
        tasks = [asyncio.create_task(run_with_sem(u)) for u in units]
        for task in asyncio.as_completed(tasks):
            result = await task
            if result.success:
                state.completed[result.module_name] = result
                completed_names.append(result.module_name)
            else:
                state.failed[result.module_name] = result
                failed_names.append(result.module_name)
                failed_errors[result.module_name] = result.error or result.marker_errors
            save_state(workspace, state)

        state.current_layer = layer
        save_state(workspace, state)

        return {
            "layer": layer,
            "total": len(units),
            "completed": completed_names,
            "failed": failed_names,
            "errors": failed_errors,
        }
    finally:
        fcntl.flock(lock_file.fileno(), fcntl.LOCK_UN)
        lock_file.close()


def build_shared_context(
    workspace: Path,
    state: OrchestratorState,
    target_layer: int,
) -> str:
    """Build shared context string from completed modules in lower layers."""
    config = CurationConfig.load(workspace / "config.yaml")

    from vero.curation.lean_project import to_project_name

    project_name = to_project_name(config.benchmark_id)
    project_dir = config.lean_output_dir / project_name

    context_parts: list[str] = []

    for unit in state.units:
        if unit.layer >= target_layer:
            continue
        if unit.module_name not in state.completed:
            continue

        # Read the impl file to extract types and sig abbrevs
        impl_path = project_dir / unit.impl_path
        if impl_path.exists():
            content = impl_path.read_text(encoding="utf-8")
            context_parts.append(
                f"--- From {unit.module_name} (layer {unit.layer}) ---\n"
                f"File: {unit.impl_path}\n"
                f"```lean\n{content}\n```\n"
            )

    if not context_parts:
        return ""

    return (
        "The following modules from earlier layers are already translated. "
        "You can import and use their types and signatures:\n\n"
        + "\n".join(context_parts)
    )


def get_progress(workspace: Path) -> dict:
    """Return current orchestration progress."""
    state = load_state(workspace)

    return {
        "total_modules": len(state.units),
        "total_layers": state.total_layers,
        "current_layer": state.current_layer,
        "completed": list(state.completed.keys()),
        "failed": list(state.failed.keys()),
        "pending": [
            u.module_name
            for u in state.units
            if u.module_name not in state.completed
            and u.module_name not in state.failed
        ],
        "completed_count": len(state.completed),
        "failed_count": len(state.failed),
    }


def get_result(workspace: Path, module_name: str) -> dict:
    """Return detailed result for a specific module."""
    state = load_state(workspace)

    result = state.completed.get(module_name) or state.failed.get(module_name)
    if result is None:
        return {"error": f"No result found for module '{module_name}'"}

    return {
        "module": module_name,
        "success": result.success,
        "marker_errors": result.marker_errors,
        "error": result.error,
        "attempt": result.attempt,
        "impl_lines": len(result.impl_content.splitlines())
        if result.impl_content
        else 0,
        "spec_lines": len(result.spec_content.splitlines())
        if result.spec_content
        else 0,
    }


async def run_build(workspace: Path) -> dict:
    """Run lake build on the project."""
    config = CurationConfig.load(workspace / "config.yaml")

    from vero.curation.lean_project import to_project_name

    project_name = to_project_name(config.benchmark_id)
    project_dir = config.lean_output_dir / project_name

    try:
        with anyio.fail_after(300):
            proc = await anyio.run_process(
                ["lake", "build", project_name],
                cwd=project_dir,
                check=False,
            )
    except TimeoutError:
        return {"success": False, "output": "lake build timed out after 300s"}

    stdout = proc.stdout.decode("utf-8", errors="replace") if proc.stdout else ""
    stderr = proc.stderr.decode("utf-8", errors="replace") if proc.stderr else ""
    output = stderr or stdout

    return {
        "success": proc.returncode == 0,
        "output": output,
    }


def validate_all_markers(workspace: Path) -> dict:
    """Validate markers across all Lean files in the project."""
    config = CurationConfig.load(workspace / "config.yaml")

    from vero.curation.lean_project import to_project_name

    project_name = to_project_name(config.benchmark_id)
    project_dir = config.lean_output_dir / project_name

    all_errors: list[str] = []
    files_checked = 0

    for lean_file in project_dir.rglob("*.lean"):
        content = lean_file.read_text(encoding="utf-8")
        errors = validate_markers(content)
        rel = lean_file.relative_to(project_dir)
        for e in errors:
            all_errors.append(f"{rel}: {e}")
        files_checked += 1

    metrics = count_metrics(project_dir)

    return {
        "valid": len(all_errors) == 0,
        "files_checked": files_checked,
        "errors": all_errors,
        "metrics": metrics,
    }


def _get_api_namespace(workspace: Path) -> str:
    """Read api_namespace from plan.json."""
    plan_path = workspace / ".vero" / "plan.json"
    if plan_path.exists():
        plan = json.loads(plan_path.read_text(encoding="utf-8"))
        return plan.get("api_namespace", "")
    return ""
