from __future__ import annotations

from pathlib import Path

from vero.curation.marker import count_metrics, extract_tasks_from_project


def test_extraction_ignores_lake_cache(tmp_path: Path) -> None:
    (tmp_path / "Pkg").mkdir()
    (tmp_path / "Pkg" / "Impl.lean").write_text(
        "-- !benchmark @start code def=real\n"
        "  real_body\n"
        "-- !benchmark @end code def=real\n"
        "#guard true\n"
    )

    cache = tmp_path / ".lake" / "packages" / "dep"
    cache.mkdir(parents=True)
    (cache / "Noisy.lean").write_text(
        "-- !benchmark @start code def=noise\n"
        "  sorry\n"
        "-- !benchmark @end code def=noise\n"
        "opaque hidden : Nat\n"
        "axiom hidden_axiom : True\n"
        "#guard true\n"
    )

    tasks = extract_tasks_from_project(tmp_path)
    metrics = count_metrics(tmp_path)

    assert [task.api for task in tasks] == ["real"]
    assert metrics["sorry_count"] == 0
    assert metrics["opaque_count"] == 0
    assert metrics["axiom_count"] == 0
    assert metrics["guard_count"] == 1
    assert metrics["file_count"] == 1
