"""Tests for PLAN-stage artifact validation."""

from __future__ import annotations

import json
from pathlib import Path

from vero.curation.stages.plan import _validate_plan_json


def _write_source_index(path: Path) -> None:
    path.write_text(
        json.dumps(
            {
                "version": 1,
                "entities": [
                    {
                        "id": "Core/Digits.v:digits2_Pnat_correct:1171",
                        "name": "digits2_Pnat_correct",
                        "qualified_name": "digits2_Pnat_correct",
                        "kind": "Theorem",
                        "source_file": "Core/Digits.v",
                        "source_line": 42,
                        "signature": "Theorem digits2_Pnat_correct : ...",
                    }
                ],
            }
        ),
        encoding="utf-8",
    )


def test_validate_plan_json_rejects_generated_source_item(tmp_path: Path) -> None:
    plan = tmp_path / "plan.json"
    source_index = tmp_path / "source_index.json"
    _write_source_index(source_index)
    plan.write_text(
        json.dumps(
            {
                "version": 1,
                "packages": [
                    {
                        "name": "Flocq",
                        "is_root": True,
                        "modules": [
                            {
                                "name": "CoreDefs",
                                "spec_helpers": [
                                    {
                                        "name": "sourceSpec",
                                        "lean_form": "def sourceSpec (_sourceId : String) : Prop := True",
                                        "source_id": "generated:sourceSpec",
                                        "source_file": "",
                                    }
                                ],
                            }
                        ],
                    }
                ],
            }
        ),
        encoding="utf-8",
    )

    success, error = _validate_plan_json(plan, source_index)

    assert success is False
    assert "missing or generated source provenance" in error
    assert "sourceSpec" in error


def test_validate_plan_json_accepts_source_backed_spec(tmp_path: Path) -> None:
    plan = tmp_path / "plan.json"
    source_index = tmp_path / "source_index.json"
    _write_source_index(source_index)
    plan.write_text(
        json.dumps(
            {
                "version": 1,
                "packages": [
                    {
                        "name": "Flocq",
                        "is_root": True,
                        "modules": [
                            {
                                "name": "CoreDigits",
                                "specs": [
                                    {
                                        "name": "spec_digits2_Pnat_correct",
                                        "lean_form": "∀ n, True",
                                        "source_id": "Core/Digits.v:digits2_Pnat_correct:1171",
                                        "source_file": "Core/Digits.v",
                                        "source_line": 42,
                                        "source_theorem": "digits2_Pnat_correct",
                                        "source_signature": "Theorem digits2_Pnat_correct : ...",
                                    }
                                ],
                            }
                        ],
                    }
                ],
            }
        ),
        encoding="utf-8",
    )

    success, error = _validate_plan_json(plan, source_index)

    assert success is True
    assert error == ""


def test_validate_plan_json_rejects_unclear_translated_spec(tmp_path: Path) -> None:
    plan = tmp_path / "plan.json"
    source_index = tmp_path / "source_index.json"
    _write_source_index(source_index)
    plan.write_text(
        json.dumps(
            {
                "version": 1,
                "packages": [
                    {
                        "name": "Flocq",
                        "is_root": True,
                        "modules": [
                            {
                                "name": "CoreDigits",
                                "specs": [
                                    {
                                        "name": "spec_digits2_Pnat_correct",
                                        "lean_form": "∀ n, True",
                                        "source_id": "Core/Digits.v:digits2_Pnat_correct:1171",
                                        "source_file": "Core/Digits.v",
                                        "source_line": 42,
                                        "source_theorem": "digits2_Pnat_correct",
                                        "equivalence_status": "unclear",
                                    }
                                ],
                            }
                        ],
                    }
                ],
            }
        ),
        encoding="utf-8",
    )

    success, error = _validate_plan_json(plan, source_index)

    assert success is False
    assert "equivalence_status='unclear'" in error


def test_validate_plan_json_normalizes_given_disposition(tmp_path: Path) -> None:
    plan = tmp_path / "plan.json"
    source_index = tmp_path / "source_index.json"
    _write_source_index(source_index)
    plan.write_text(
        json.dumps(
            {
                "version": 1,
                "packages": [
                    {
                        "name": "Flocq",
                        "is_root": True,
                        "modules": [
                            {
                                "name": "CoreDigits",
                                "specs": [
                                    {
                                        "name": "spec_digits2_Pnat_correct",
                                        "lean_form": "∀ n, True",
                                        "disposition": "given",
                                        "source_id": "Core/Digits.v:digits2_Pnat_correct:1171",
                                        "source_file": "Core/Digits.v",
                                        "source_line": 42,
                                        "source_theorem": "digits2_Pnat_correct",
                                    }
                                ],
                            }
                        ],
                    }
                ],
            }
        ),
        encoding="utf-8",
    )

    success, error = _validate_plan_json(plan, source_index)

    assert success is True
    assert error == ""
    normalized = json.loads(plan.read_text(encoding="utf-8"))
    assert (
        normalized["packages"][0]["modules"][0]["specs"][0]["disposition"] == "provided"
    )


def test_validate_plan_json_rejects_unknown_disposition(tmp_path: Path) -> None:
    plan = tmp_path / "plan.json"
    source_index = tmp_path / "source_index.json"
    _write_source_index(source_index)
    plan.write_text(
        json.dumps(
            {
                "version": 1,
                "packages": [
                    {
                        "name": "Flocq",
                        "is_root": True,
                        "modules": [
                            {
                                "name": "CoreDigits",
                                "specs": [
                                    {
                                        "name": "spec_digits2_Pnat_correct",
                                        "lean_form": "∀ n, True",
                                        "disposition": "trusted",
                                        "source_id": "Core/Digits.v:digits2_Pnat_correct:1171",
                                        "source_file": "Core/Digits.v",
                                        "source_line": 42,
                                        "source_theorem": "digits2_Pnat_correct",
                                    }
                                ],
                            }
                        ],
                    }
                ],
            }
        ),
        encoding="utf-8",
    )

    success, error = _validate_plan_json(plan, source_index)

    assert success is False
    assert "unsupported disposition='trusted'" in error
