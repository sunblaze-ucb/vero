"""Tests for orchestrated translate executor prompt shaping."""

from __future__ import annotations

import json
from pathlib import Path

from vero.curation.orchestrator.executor import (
    _build_executor_prompt,
    _has_repo_impl_spec_helper,
)
from vero.curation.orchestrator.models import TranslationUnit
from vero.curation.orchestrator.tools import analyze_plan, load_state


def test_repo_impl_spec_helper_requires_spec_side_emission() -> None:
    unit = TranslationUnit(
        module_name="PiggyBank",
        package_name="PiggybankV2",
        layer=1,
        impl_path="PiggybankV2/Impl/PiggyBank.lean",
        spec_path="PiggybankV2/Spec/PiggyBank.lean",
        spec_helpers=[
            {
                "name": "contract",
                "lean_form": (
                    "noncomputable def contract (impl : RepoImpl) := "
                    "impl.piggybankV2.init"
                ),
            }
        ],
    )

    assert _has_repo_impl_spec_helper(unit)


def test_executor_prompt_places_repo_impl_helpers_in_spec() -> None:
    unit = TranslationUnit(
        module_name="PiggyBank",
        package_name="PiggybankV2",
        layer=1,
        impl_path="PiggybankV2/Impl/PiggyBank.lean",
        spec_path="PiggybankV2/Spec/PiggyBank.lean",
        spec_helpers=[
            {
                "name": "contract",
                "nl_description": "RepoImpl-dependent contract wrapper.",
                "lean_form": (
                    "noncomputable def contract (impl : RepoImpl) := "
                    "impl.piggybankV2.init"
                ),
            }
        ],
    )

    prompt = _build_executor_prompt(
        unit=unit,
        project_dir=Path("/tmp/PiggybankV2"),
        source_dir=Path("/tmp/source"),
        shared_context="",
        language="coq",
        api_namespace="PiggybankV2",
    )

    assert "RepoImpl-dependent spec helpers" in prompt
    assert "that helper in the module's Spec/*.lean file" in prompt
    assert "Pure helpers that do not mention RepoImpl belong in Impl/*.lean" in prompt


def test_analyze_plan_orders_spec_only_modules_after_referenced_modules(
    tmp_path: Path,
) -> None:
    workspace = tmp_path / "workspace"
    vero = workspace / ".vero"
    vero.mkdir(parents=True)
    plan = {
        "version": 1,
        "api_namespace": "Demo",
        "packages": [
            {
                "name": "Demo",
                "is_root": True,
                "bundle_type": "DemoBundle",
                "repo_impl_field": "demo",
                "modules": [
                    {
                        "name": "Foundation",
                        "types": [
                            {
                                "name": "Address",
                                "lean_form": "abbrev Address := Nat",
                                "is_foundation": True,
                            }
                        ],
                        "apis": [],
                        "specs": [],
                    },
                    {
                        "name": "PiggyBank",
                        "types": [
                            {
                                "name": "State",
                                "lean_form": "structure State where owner : Address",
                            }
                        ],
                        "apis": [
                            {
                                "lean_name": "init",
                                "sig_abbrev": "InitSig",
                                "lean_type": "Address -> State",
                            }
                        ],
                        "specs": [],
                    },
                    {
                        "name": "PiggyBankCorrect",
                        "types": [],
                        "apis": [],
                        "specs": [
                            {
                                "name": "spec_owner",
                                "lean_form": (
                                    "forall s : State, "
                                    "(impl.demo.init s.owner).owner = s.owner"
                                ),
                            }
                        ],
                    },
                ],
            }
        ],
        "test_cases": [],
    }
    (vero / "plan.json").write_text(json.dumps(plan), encoding="utf-8")

    result = analyze_plan(workspace)

    assert result["layers"] == {
        "0": ["Foundation"],
        "1": ["PiggyBank"],
        "2": ["PiggyBankCorrect"],
    }
    modules = {module["name"]: module for module in result["modules"]}
    assert modules["PiggyBankCorrect"]["dependencies"] == ["PiggyBank"]


def test_analyze_plan_uses_nested_paths_for_dotted_modules(tmp_path: Path) -> None:
    workspace = tmp_path / "workspace"
    vero = workspace / ".vero"
    vero.mkdir(parents=True)
    plan = {
        "version": 1,
        "api_namespace": "Flocq",
        "packages": [
            {
                "name": "Flocq",
                "modules": [
                    {
                        "name": "Core.Zaux",
                        "types": [],
                        "apis": [{"lean_name": "iter_nat"}],
                        "specs": [],
                    }
                ],
            }
        ],
    }
    (vero / "plan.json").write_text(json.dumps(plan), encoding="utf-8")

    analyze_plan(workspace)

    state = load_state(workspace)
    assert len(state.units) == 1
    unit = state.units[0]
    assert unit.impl_path == "Flocq/Impl/Core/Zaux.lean"
    assert unit.spec_path == "Flocq/Spec/Core/Zaux.lean"
