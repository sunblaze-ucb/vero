"""Unconstrained curator conversion obligations must not become scored tasks."""

import json
import shutil
from pathlib import Path

import pytest

from vero.curation.validation.checks import check_spec_shape
from vero.generation.benchmark import Benchmark
from vero.generation.proof_materialize import materialize_proof


@pytest.mark.parametrize("mode", ["proof", "codeproof"])
def test_conversion_hold_preserves_specs_without_scoring_them(tmp_path, mode):
    benchmark = Path(__file__).resolve().parents[2] / "benchmarks" / "verdict"
    bench = Benchmark(benchmark)
    conversion = next(m for m in bench.iter_modules() if m.name == "Convert")
    assert conversion.specs == ()
    assert sum(len(m.specs) for m in bench.iter_modules()) == 116
    module = next(
        m
        for p in bench.manifest["packages"]
        for m in p["modules"]
        if m["name"] == "Convert"
    )
    held = {s["name"] for s in module["spec_helpers"]}
    assert held == {
        "spec_cert_from_parsed_sig_alg_outer",
        "spec_cert_from_parsed_sig_alg_inner",
        "spec_cert_from_parsed_validity",
    }
    assert all(s["role"] == "requires_human_review" for s in module["spec_helpers"])
    assert check_spec_shape(benchmark).status == "pass"
    assert all(
        f"def {name} " in (benchmark / conversion.spec_rel).read_text() for name in held
    )
    shutil.copyfile(benchmark / "manifest.json", tmp_path / "manifest.json")
    result = materialize_proof(tmp_path, mode=mode)
    assert result.files_written
    assert not (tmp_path / "Verdict/Proof/Convert.lean").exists()
    assert all(
        not any(name in path.read_text() for name in held)
        for path in result.files_written
    )
    assert json.loads((tmp_path / "manifest.json").read_text()) == bench.manifest
