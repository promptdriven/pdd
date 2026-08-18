"""
Example usage of pdd.gate_main — evidence policy gate for PDD dev units.

Demonstrates:
  - GateFailure: one policy violation with code, message, fix_command
  - GateResult: aggregated outcome with exit_code, as_dict()
  - run_gate_policy(): evaluates all manifests or a named target
  - gate_cmd: Click command for ``pdd checkup gate``
"""
from __future__ import annotations

import sys
import os
from pathlib import Path
from unittest.mock import MagicMock, patch

sys.path.insert(0, os.path.join(os.path.dirname(__file__), "../.."))

from pdd.gate_main import (  # noqa: E402
    GateFailure,
    GateResult,
    gate_cmd,
    run_gate_policy,
)
from pdd.gate_policy import default_policy  # noqa: E402
from click.testing import CliRunner  # noqa: E402


def example_gate_failure_as_dict() -> None:
    """GateFailure serializes its three fields to a plain dict."""
    failure = GateFailure(
        code="cost_limit",
        message="mymodule: run cost $25.00 exceeds policy limit $20.00",
        fix_command="Lower model cost or raise limits.max_cost_usd in policy",
    )
    d = failure.as_dict()
    print("GateFailure.as_dict():", d)
    assert d["code"] == "cost_limit"
    assert d["message"].startswith("mymodule")
    assert d["fix_command"] != ""


def example_gate_result_passed() -> None:
    """GateResult with no failures: passed=True, exit_code=0."""
    result = GateResult(
        passed=True,
        failures=[],
        policy=default_policy(),
        manifests_checked=3,
    )
    print("GateResult passed:", result.passed)
    print("GateResult exit_code:", result.exit_code)
    d = result.as_dict()
    assert d["passed"] is True
    assert d["exit_code"] == 0
    assert d["manifests_checked"] == 3
    assert d["failures"] == []


def example_gate_result_failed() -> None:
    """GateResult with failures: passed=False, exit_code=1."""
    failure = GateFailure(code="missing_evidence", message="No manifest found", fix_command="pdd --evidence generate mymodule")
    result = GateResult(passed=False, failures=[failure], policy=default_policy(), manifests_checked=0)
    print("GateResult failed exit_code:", result.exit_code)
    d = result.as_dict()
    assert d["passed"] is False
    assert d["exit_code"] == 1
    assert len(d["failures"]) == 1
    assert d["failures"][0]["code"] == "missing_evidence"


def example_run_gate_policy_no_manifests(tmp_path: Path) -> None:
    """run_gate_policy returns a no_manifests failure when the devunits dir is empty."""
    result = run_gate_policy(tmp_path)
    print("no_manifests result passed:", result.passed)
    print("no_manifests failures:", [f.code for f in result.failures])
    assert result.passed is False
    assert any(f.code == "no_manifests" for f in result.failures)
    assert result.exit_code == 1


def example_run_gate_policy_unknown_target(tmp_path: Path) -> None:
    """run_gate_policy returns unknown_target when the basename cannot be resolved."""
    with patch("pdd.gate_main.devunits_dir") as mock_devunits, \
         patch("pdd.gate_main.resolve_prompt_path", return_value=None):
        mock_devunits.return_value = tmp_path / ".pdd" / "evidence" / "devunits"
        result = run_gate_policy(tmp_path, target="nonexistent_module")

    print("unknown_target result passed:", result.passed)
    assert result.passed is False
    assert any(f.code == "unknown_target" for f in result.failures)


def example_run_gate_policy_with_target_path(tmp_path: Path) -> None:
    """run_gate_policy accepts a .latest.json path directly as TARGET."""
    manifest_path = tmp_path / "mymodule.latest.json"
    manifest_path.write_text(
        '{"schema_version": "1", "validation": {"detect_stories": "pass", "verify": "pass", "unit_tests": "pass"}, "generation": {}, "outputs": []}',
        encoding="utf-8",
    )

    mock_view = MagicMock()
    mock_view.basename = "mymodule"
    mock_view.path = manifest_path
    mock_view.validation = {"detect_stories": "pass", "verify": "pass", "unit_tests": "pass"}
    mock_view.generation = {}
    mock_view.rule_manifest = False
    mock_view.prompt_path = None
    mock_view.outputs = []

    with patch("pdd.gate_main.ManifestView.from_file", return_value=mock_view), \
         patch("pdd.gate_main.evaluate_manifest", return_value=[]):
        result = run_gate_policy(tmp_path, target=str(manifest_path))

    print("direct-path result passed:", result.passed)
    print("manifests_checked:", result.manifests_checked)
    assert result.passed is True
    assert result.manifests_checked == 1


def example_gate_cmd_json_output(tmp_path: Path) -> None:
    """gate_cmd with --json emits a structured GateResult payload."""
    runner = CliRunner()
    mock_result = GateResult(
        passed=True,
        failures=[],
        policy=default_policy(),
        manifests_checked=2,
    )
    with patch("pdd.gate_main.run_gate_policy", return_value=mock_result):
        result = runner.invoke(gate_cmd, ["--json"])

    print("gate_cmd --json exit_code:", result.exit_code)
    print("gate_cmd --json output snippet:", result.output[:120])
    assert result.exit_code == 0
    assert '"passed"' in result.output
    assert '"manifests_checked"' in result.output


def example_gate_cmd_text_output_pass(tmp_path: Path) -> None:
    """gate_cmd prints a green pass message on success (no --json)."""
    runner = CliRunner()
    mock_result = GateResult(
        passed=True,
        failures=[],
        policy=default_policy(),
        manifests_checked=1,
    )
    with patch("pdd.gate_main.run_gate_policy", return_value=mock_result):
        result = runner.invoke(gate_cmd, [])

    print("gate_cmd text pass exit_code:", result.exit_code)
    print("gate_cmd text pass output:", result.output.strip())
    assert result.exit_code == 0
    assert "passed" in result.output.lower()


def example_gate_cmd_text_output_fail(tmp_path: Path) -> None:
    """gate_cmd prints violation details and exits 1 on failure (no --json)."""
    runner = CliRunner()
    failure = GateFailure(
        code="cost_limit",
        message="mymodule: run cost $30.00 exceeds policy limit $20.00",
        fix_command="Lower model cost",
    )
    mock_result = GateResult(
        passed=False,
        failures=[failure],
        policy=default_policy(),
        manifests_checked=1,
    )
    with patch("pdd.gate_main.run_gate_policy", return_value=mock_result):
        result = runner.invoke(gate_cmd, [])

    print("gate_cmd text fail exit_code:", result.exit_code)
    print("gate_cmd text fail output:", result.output.strip())
    assert result.exit_code == 1
    assert "cost_limit" in result.output


if __name__ == "__main__":
    import tempfile

    print("=== GateFailure.as_dict ===")
    example_gate_failure_as_dict()
    print()

    print("=== GateResult passed ===")
    example_gate_result_passed()
    print()

    print("=== GateResult failed ===")
    example_gate_result_failed()
    print()

    with tempfile.TemporaryDirectory() as tmp:
        tmp_path = Path(tmp)

        print("=== run_gate_policy — no manifests ===")
        example_run_gate_policy_no_manifests(tmp_path)
        print()

        print("=== run_gate_policy — unknown target ===")
        example_run_gate_policy_unknown_target(tmp_path)
        print()

        print("=== run_gate_policy — direct .latest.json path ===")
        example_run_gate_policy_with_target_path(tmp_path)
        print()

        print("=== gate_cmd --json output ===")
        example_gate_cmd_json_output(tmp_path)
        print()

        print("=== gate_cmd text pass ===")
        example_gate_cmd_text_output_pass(tmp_path)
        print()

        print("=== gate_cmd text fail ===")
        example_gate_cmd_text_output_fail(tmp_path)
        print()

    print("All examples passed.")
