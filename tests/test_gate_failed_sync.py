"""Regression: gate must not pass after a failed sync under default policy."""
from __future__ import annotations

from pathlib import Path

import pytest

from pdd.evidence_manifest import validation_from_sync
from pdd.evidence_store import sha256_file
from pdd.gate_main import run_gate_policy
from pdd.gate_policy import default_policy
from tests.test_gate_main import _write_routine_manifest


def _failed_coverage_sync_result() -> dict:
    """Shape recorded when sync runs tests but coverage stays below target."""
    return {
        "overall_success": False,
        "results_by_language": {
            "python": {
                "success": False,
                "operations_completed": [
                    "generate",
                    "example",
                    "crash",
                    "test",
                    "test_extend",
                ],
                "error": "Coverage 0.0% below target 90.0% after 2 test_extend attempts",
            }
        },
    }


def test_validation_from_sync_failed_coverage_records_failed_tests() -> None:
    validation = validation_from_sync(
        _failed_coverage_sync_result(),
        skip_tests=False,
        skip_verify=False,
    )
    assert validation["unit_tests"] == "failed"
    assert validation["verify"] == "not_available"
    assert validation["detect_stories"] == "not_applicable"


def test_validation_from_sync_ignores_stale_overall_success_flag() -> None:
    """Top-level overall_success must not override per-language failure."""
    buggy = {
        "overall_success": True,
        "results_by_language": {
            "python": {
                "success": False,
                "operations_completed": ["test", "verify"],
            }
        },
    }
    validation = validation_from_sync(buggy, skip_tests=False, skip_verify=False)
    assert validation["unit_tests"] == "failed"
    assert validation["verify"] == "failed"


@pytest.mark.parametrize(
    "sync_result",
    [
        _failed_coverage_sync_result(),
        {
            "overall_success": False,
            "results_by_language": {
                "python": {"success": False, "operations_completed": ["generate"]},
            },
        },
        {
            "overall_success": True,
            "results_by_language": {
                "python": {"success": False, "operations_completed": ["test"]},
            },
        },
    ],
)
def test_gate_never_passes_default_policy_after_failed_sync_shape(
    tmp_path: Path,
    sync_result: dict,
) -> None:
    code = tmp_path / "src" / "refund.py"
    code.parent.mkdir(parents=True)
    code.write_text("def refund():\n    return 1\n", encoding="utf-8")
    validation = validation_from_sync(sync_result, skip_tests=False, skip_verify=False)
    manifest = tmp_path / ".pdd" / "evidence" / "devunits" / "refund.latest.json"
    _write_routine_manifest(
        manifest,
        basename="refund",
        output_rel="src/refund.py",
        output_hash=sha256_file(code),
        validation=validation,
    )
    result = run_gate_policy(tmp_path, target="refund", policy_path=None)
    assert not result.passed, (
        f"expected gate failure for validation={validation}, "
        f"codes={[failure.code for failure in result.failures]}"
    )


def test_stale_passing_manifest_can_false_pass_gate(tmp_path: Path) -> None:
    """Documents stale-manifest risk when a new failed sync does not refresh evidence."""
    code = tmp_path / "src" / "refund.py"
    code.parent.mkdir(parents=True)
    code.write_text("def refund():\n    return 1\n", encoding="utf-8")
    _write_routine_manifest(
        tmp_path / ".pdd" / "evidence" / "devunits" / "refund.latest.json",
        basename="refund",
        output_rel="src/refund.py",
        output_hash=sha256_file(code),
        validation={
            "detect_stories": "pass",
            "verify": "pass",
            "unit_tests": "pass",
        },
    )
    policy = default_policy()
    policy.require["no_unchecked_critical_rules"] = False
    result = run_gate_policy(tmp_path, target="refund")
    # Stale good manifest passes — evidence refresh on every sync attempt is required.
    assert result.passed


def test_sync_exception_evidence_overwrites_stale_passing_manifest(
    tmp_path: Path,
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    """``pdd sync --evidence`` must refresh manifest even when sync_main raises."""
    from click.testing import CliRunner

    from pdd import cli

    project = tmp_path / "demo"
    project.mkdir()
    prompts = project / "prompts"
    prompts.mkdir()
    (prompts / "refund_python.prompt").write_text("# refund\n", encoding="utf-8")
    (project / ".pddrc").write_text(
        'version: "1.0"\ncontexts:\n  default:\n    paths: ["**"]\n'
        "    defaults:\n      generate_output_path: src/\n"
        "      test_output_path: tests/\n",
        encoding="utf-8",
    )
    stale = project / ".pdd" / "evidence" / "devunits" / "refund.latest.json"
    code = project / "src" / "refund.py"
    code.parent.mkdir(parents=True)
    code.write_text("def refund():\n    return 1\n", encoding="utf-8")
    _write_routine_manifest(
        stale,
        basename="refund",
        output_rel="src/refund.py",
        output_hash=sha256_file(code),
        validation={
            "detect_stories": "pass",
            "verify": "pass",
            "unit_tests": "pass",
        },
    )

    monkeypatch.chdir(project)

    def _raise_sync(**_kwargs: object) -> tuple[str, float, str]:
        raise RuntimeError("boom")

    monkeypatch.setattr("pdd.sync_main.sync_main", _raise_sync)

    runner = CliRunner()
    result = runner.invoke(
        cli.cli,
        ["sync", "refund", "--evidence"],
        env={"PDD_SKIP_UPDATE_CHECK": "1", "CI": "1"},
    )

    gate = run_gate_policy(project, target="refund")
    assert not gate.passed, result.output
