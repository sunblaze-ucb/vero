"""The supplied proof-mode parent must not introduce sorryAx into clean proofs."""

import shutil
import subprocess
from pathlib import Path

import pytest

from vero.evaluation.axioms import _parse_axioms_output
from vero.generation.sandbox import create_sandbox


@pytest.mark.slow
@pytest.mark.skipif(shutil.which("lake") is None, reason="Lean toolchain unavailable")
def test_verdict_reference_is_axiom_clean(tmp_path):
    benchmark = Path(__file__).resolve().parents[2] / "benchmarks" / "verdict"
    sandbox = tmp_path / "verdict"
    create_sandbox(benchmark, sandbox, mode="proof")
    probe = sandbox / "CanonicalProbe.lean"
    probe.write_text(
        "import Verdict.Harness\n"
        "theorem canonical_probe : canonical = canonical := by rfl\n"
        "#print axioms canonical\n"
        "#print axioms canonical_probe\n"
    )
    result = subprocess.run(
        ["lake", "lean", str(probe)],
        cwd=sandbox,
        text=True,
        capture_output=True,
        timeout=600,
    )
    output = result.stdout + result.stderr
    assert result.returncode == 0, output
    checks = _parse_axioms_output(output, ["canonical", "canonical_probe"])
    assert all(check.status == "clean" for check in checks), checks
