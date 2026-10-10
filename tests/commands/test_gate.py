# Test plan for pdd.gate_main (and pdd.commands.gate integration):
#
# Requirement 1: gate_cmd Click command: pdd checkup gate [TARGET] [--policy PATH]
#                [--stories-dir PATH] [--tests-dir PATH] [--json]
#   - test_gate_cmd_has_correct_options
#   - test_gate_cmd_json_output_structure
#   - test_gate_cmd_text_pass_output
#   - test_gate_cmd_text_fail_output
#
# Requirement 2: TARGET omitted -> evaluate all *.latest.json manifests
#   - test_run_gate_policy_no_manifests_failure
#   - test_run_gate_policy_lists_all_manifests (via mocked list_latest_manifests)
#
# Requirement 3: TARGET basename -> evaluate one dev unit's latest manifest
#   - test_run_gate_policy_target_basename_found
#   - test_run_gate_policy_target_basename_missing_evidence
#   - test_run_gate_policy_target_basename_unknown
#
# Requirement 4: TARGET path ending in .latest.json -> evaluate that manifest file
#   - test_run_gate_policy_target_latest_json_path
#
# Requirement 5: Exit 0 on pass, 1 on failure
#   - test_gate_result_exit_code_pass
#   - test_gate_result_exit_code_fail
#   - test_gate_cmd_exits_0_on_pass
#   - test_gate_cmd_exits_1_on_fail
#
# Requirement 6: --json emits structured GateResult
#   - test_gate_cmd_json_output_structure
#
# GateFailure dataclass
#   - test_gate_failure_as_dict
#
# GateResult dataclass
#   - test_gate_result_as_dict_passed
#   - test_gate_result_as_dict_failed
#   - test_gate_result_exit_code_pass
#   - test_gate_result_exit_code_fail
#
# _check_validation_flags
#   - test_check_validation_flags_all_pass
#   - test_check_validation_flags_missing_required
#   - test_check_validation_flags_not_available
#   - test_check_validation_flags_skipped_verify_allowed
#   - test_check_validation_flags_skipped_verify_not_allowed
#   - test_check_validation_flags_skipped_tests_allowed
#   - test_check_validation_flags_skipped_tests_not_allowed
#   - test_check_validation_flags_stories_stale
#
# _check_cost_limits
#   - test_check_cost_limits_below_limit
#   - test_check_cost_limits_above_limit
#   - test_check_cost_limits_no_limit
#   - test_check_cost_limits_ctx_items_exceeded
#
# evaluate_manifest
#   - test_evaluate_manifest_no_failures
#
# Waiver policy (pdd.commands.gate integration - existing tests below)
#   - test_top_level_pdd_gate_is_not_registered
#   - test_checkup_gate_help
#   - test_checkup_gate_allow_waivers_passes_for_valid_fixture
#   - test_checkup_gate_forbid_waivers_fails_when_any_waiver_exists
#   - test_checkup_gate_no_allow_waivers_fails_when_any_waiver_exists
#   - test_checkup_gate_require_expiration_fails_missing_expiration
#   - test_checkup_gate_enforce_expiration_fails_expired_waiver
#   - test_checkup_gate_fails_unknown_rule_waiver
#   - test_checkup_gate_fails_malformed_waiver
#   - test_checkup_gate_enforce_expiration_fails_unparseable_expires
#   - test_checkup_gate_fails_waiver_rule_mismatch
#   - test_explicit_policy_file_missing_fails_closed
#   - test_explicit_policy_file_without_gate_section_fails_closed

"""Tests for ``pdd checkup gate`` waiver policy enforcement."""
from __future__ import annotations

import json
import textwrap
from pathlib import Path
from unittest.mock import MagicMock, patch

import pytest
from click.testing import CliRunner

from pdd.commands.checkup import checkup
from pdd.commands.gate import gate_cmd
from pdd.gate_main import (
    GateFailure,
    GateResult,
    _check_cost_limits,
    _check_validation_flags,
    evaluate_manifest,
    run_gate_policy,
)
from pdd.gate_main import gate_cmd as gate_cmd_main
from pdd.gate_policy import GatePolicy, GateLimits, default_policy

FIXTURES = Path(__file__).parents[1] / "fixtures" / "contract_check"


def _invoke_checkup_gate(*args: str):
    return CliRunner().invoke(
        checkup,
        ["gate", *args],
        obj={"quiet": True},
    )


def _write_prompt(tmp_path: Path, name: str, content: str) -> Path:
    path = tmp_path / name
    path.write_text(textwrap.dedent(content), encoding="utf-8")
    return path


def test_top_level_pdd_gate_is_not_registered() -> None:
    from pdd.core.cli import cli  # pylint: disable=import-outside-toplevel

    assert "gate" not in cli.commands
    result = CliRunner().invoke(cli, ["gate"], obj={"quiet": True})
    assert result.exit_code != 0
    assert "No such command" in result.output


def test_checkup_gate_help() -> None:
    result = CliRunner().invoke(checkup, ["gate", "--help"], obj={"quiet": True})
    assert result.exit_code == 0
    assert "waiver" in result.output.lower()
    assert "evidence" in result.output.lower()


def test_checkup_gate_allow_waivers_passes_for_valid_fixture() -> None:
    result = _invoke_checkup_gate(
        str(FIXTURES / "waiver_valid_python.prompt"),
        "--allow-waivers",
    )
    assert result.exit_code == 0, result.output


def test_checkup_gate_forbid_waivers_fails_when_any_waiver_exists() -> None:
    result = _invoke_checkup_gate(
        str(FIXTURES / "waiver_valid_python.prompt"),
        "--forbid-waivers",
    )
    assert result.exit_code == 1, result.output
    assert "waivers-forbidden" in result.output


def test_checkup_gate_no_allow_waivers_fails_when_any_waiver_exists() -> None:
    result = _invoke_checkup_gate(
        str(FIXTURES / "waiver_valid_python.prompt"),
        "--no-allow-waivers",
    )
    assert result.exit_code == 1, result.output
    assert "waivers-forbidden" in result.output


def test_checkup_gate_require_expiration_fails_missing_expiration() -> None:
    result = _invoke_checkup_gate(
        str(FIXTURES / "waiver_missing_fields_python.prompt"),
        "--require-expiration",
    )
    assert result.exit_code == 1, result.output
    assert "missing-expiration" in result.output


def test_checkup_gate_enforce_expiration_fails_expired_waiver() -> None:
    result = _invoke_checkup_gate(
        str(FIXTURES / "waiver_expired_python.prompt"),
        "--enforce-expiration",
    )
    assert result.exit_code == 1, result.output
    assert "expired" in result.output


def test_checkup_gate_fails_unknown_rule_waiver(tmp_path: Path) -> None:
    prompt = _write_prompt(
        tmp_path,
        "unknown_rule_python.prompt",
        """
        <contract_rules>
        R1: The system MUST validate input.
        </contract_rules>
        <coverage>
        - R1: WAIVED W1
        </coverage>
        <waivers>
        W1:
          Rule: R99
          Reason: Temporary gap.
          Approved by: security-review
          Expires: 2099-06-01
        </waivers>
        """,
    )
    result = _invoke_checkup_gate(str(prompt))
    assert result.exit_code == 1, result.output
    assert "unknown-rule" in result.output


def test_checkup_gate_fails_malformed_waiver(tmp_path: Path) -> None:
    prompt = _write_prompt(
        tmp_path,
        "malformed_waiver_python.prompt",
        """
        <contract_rules>
        R1: The system MUST validate input.
        </contract_rules>
        <coverage>
        - R1: WAIVED W1
        </coverage>
        <waivers>
        W1:
          Rule: R1
          Reason: Missing approver and expiry.
        </waivers>
        """,
    )
    result = _invoke_checkup_gate(str(prompt))
    assert result.exit_code == 1, result.output
    assert "malformed" in result.output


def test_checkup_gate_enforce_expiration_fails_unparseable_expires(tmp_path: Path) -> None:
    prompt = _write_prompt(
        tmp_path,
        "unparseable_expires_python.prompt",
        """
        <contract_rules>
        R1: The system MUST validate input.
        </contract_rules>
        <coverage>
        - R1: WAIVED W1
        </coverage>
        <waivers>
        W1:
          Rule: R1
          Reason: Temporary gap.
          Approved by: security-review
          Expires: not-a-date
        </waivers>
        """,
    )
    result = _invoke_checkup_gate(str(prompt), "--enforce-expiration")
    assert result.exit_code == 1, result.output
    assert "malformed" in result.output


def test_checkup_gate_fails_waiver_rule_mismatch(tmp_path: Path) -> None:
    prompt = _write_prompt(
        tmp_path,
        "waiver_rule_mismatch_python.prompt",
        """
        <contract_rules>
        R1: The system MUST validate input.
        R2: The system MUST log errors.
        </contract_rules>
        <coverage>
        - R1: WAIVED W2
        </coverage>
        <waivers>
        W2:
          Rule: R2
          Reason: Temporary gap.
          Approved by: security-review
          Expires: 2099-06-01
        </waivers>
        """,
    )
    result = _invoke_checkup_gate(str(prompt))
    assert result.exit_code == 1, result.output
    assert "WAIVER_RULE_MISMATCH" in result.output


def test_explicit_policy_file_missing_fails_closed(tmp_path: Path) -> None:
    missing = tmp_path / "missing-policy.yaml"
    result = CliRunner().invoke(
        gate_cmd,
        [
            str(FIXTURES / "waiver_valid_python.prompt"),
            "--policy-file",
            str(missing),
        ],
        obj={"quiet": True},
    )
    assert result.exit_code != 0
    assert "Policy file not found" in result.output


def test_explicit_policy_file_without_gate_section_fails_closed(tmp_path: Path) -> None:
    policy = tmp_path / "policy.yaml"
    policy.write_text("version: '1.0'\n", encoding="utf-8")
    result = CliRunner().invoke(
        gate_cmd,
        [
            str(FIXTURES / "waiver_valid_python.prompt"),
            "--policy-file",
            str(policy),
        ],
        obj={"quiet": True},
    )
    assert result.exit_code != 0
    assert "no top-level `gate:` mapping" in result.output


# ============================================================
# Tests for pdd.gate_main (core evidence gate logic)
# ============================================================


def _make_manifest(
    *,
    basename: str = "mymodule",
    validation: dict | None = None,
    generation: dict | None = None,
    rule_manifest: bool = False,
    prompt_path: Path | None = None,
) -> MagicMock:
    """Build a minimal ManifestView mock."""
    m = MagicMock()
    m.basename = basename
    m.path = Path(f".pdd/evidence/devunits/{basename}.latest.json")
    m.validation = validation if validation is not None else {}
    m.generation = generation if generation is not None else {}
    m.rule_manifest = rule_manifest
    m.prompt_path = prompt_path
    m.outputs = []
    return m


def test_gate_failure_as_dict() -> None:
    failure = GateFailure(
        code="cost_limit",
        message="mymodule: run cost $25.00 exceeds policy limit $20.00",
        fix_command="Lower model cost",
    )
    d = failure.as_dict()
    assert d["code"] == "cost_limit"
    assert d["message"] == "mymodule: run cost $25.00 exceeds policy limit $20.00"
    assert d["fix_command"] == "Lower model cost"


def test_gate_result_exit_code_pass() -> None:
    result = GateResult(passed=True, failures=[], policy=default_policy(), manifests_checked=1)
    assert result.exit_code == 0


def test_gate_result_exit_code_fail() -> None:
    failure = GateFailure(code="no_manifests", message="No manifests", fix_command="")
    result = GateResult(passed=False, failures=[failure], policy=default_policy(), manifests_checked=0)
    assert result.exit_code == 1


def test_gate_result_as_dict_passed() -> None:
    result = GateResult(passed=True, failures=[], policy=default_policy(), manifests_checked=3)
    d = result.as_dict()
    assert d["passed"] is True
    assert d["exit_code"] == 0
    assert d["manifests_checked"] == 3
    assert d["failures"] == []
    assert "policy" in d


def test_gate_result_as_dict_failed() -> None:
    failure = GateFailure(code="cost_limit", message="too expensive", fix_command="fix it")
    result = GateResult(passed=False, failures=[failure], policy=default_policy(), manifests_checked=1)
    d = result.as_dict()
    assert d["passed"] is False
    assert d["exit_code"] == 1
    assert len(d["failures"]) == 1
    assert d["failures"][0]["code"] == "cost_limit"


def test_run_gate_policy_no_manifests_failure(tmp_path: Path) -> None:
    """TARGET omitted with no manifests on disk -> no_manifests failure."""
    result = run_gate_policy(tmp_path)
    assert result.passed is False
    assert any(f.code == "no_manifests" for f in result.failures)
    assert result.exit_code == 1


def test_run_gate_policy_lists_all_manifests(tmp_path: Path) -> None:
    """TARGET omitted -> all latest manifests evaluated."""
    manifest_a = _make_manifest(basename="mod_a")
    manifest_b = _make_manifest(basename="mod_b")

    with patch("pdd.gate_main.list_latest_manifests") as mock_list, \
         patch("pdd.gate_main.ManifestView.from_file", side_effect=[manifest_a, manifest_b]), \
         patch("pdd.gate_main.evaluate_manifest", return_value=[]) as mock_eval:
        mock_list.return_value = [
            tmp_path / "mod_a.latest.json",
            tmp_path / "mod_b.latest.json",
        ]
        result = run_gate_policy(tmp_path)

    assert result.passed is True
    assert result.manifests_checked == 2
    assert mock_eval.call_count == 2


def test_run_gate_policy_target_latest_json_path(tmp_path: Path) -> None:
    """TARGET ending in .latest.json -> evaluate that exact file."""
    manifest_path = tmp_path / "mymodule.latest.json"
    manifest_path.write_text("{}", encoding="utf-8")
    mock_view = _make_manifest(basename="mymodule")

    with patch("pdd.gate_main.ManifestView.from_file", return_value=mock_view), \
         patch("pdd.gate_main.evaluate_manifest", return_value=[]):
        result = run_gate_policy(tmp_path, target=str(manifest_path))

    assert result.passed is True
    assert result.manifests_checked == 1


def test_run_gate_policy_target_basename_found(tmp_path: Path) -> None:
    """TARGET basename with existing latest manifest -> evaluate it."""
    devunits = tmp_path / ".pdd" / "evidence" / "devunits"
    devunits.mkdir(parents=True)
    latest = devunits / "mymodule.latest.json"
    latest.write_text("{}", encoding="utf-8")
    mock_view = _make_manifest(basename="mymodule")

    with patch("pdd.gate_main.ManifestView.from_file", return_value=mock_view), \
         patch("pdd.gate_main.evaluate_manifest", return_value=[]):
        result = run_gate_policy(tmp_path, target="mymodule")

    assert result.passed is True
    assert result.manifests_checked == 1


def test_run_gate_policy_target_basename_missing_evidence(tmp_path: Path) -> None:
    """TARGET basename with no manifest but resolvable prompt -> missing_evidence failure."""
    devunits = tmp_path / ".pdd" / "evidence" / "devunits"
    devunits.mkdir(parents=True)
    mock_prompt = tmp_path / "prompts" / "mymodule_python.prompt"

    with patch("pdd.gate_main.resolve_prompt_path", return_value=mock_prompt), \
         patch("pdd.gate_main.evaluate_manifest", return_value=[]):
        result = run_gate_policy(tmp_path, target="mymodule")

    assert result.passed is False
    assert any(f.code == "missing_evidence" for f in result.failures)


def test_run_gate_policy_target_basename_unknown(tmp_path: Path) -> None:
    """TARGET basename that cannot be resolved -> unknown_target failure."""
    devunits = tmp_path / ".pdd" / "evidence" / "devunits"
    devunits.mkdir(parents=True)

    with patch("pdd.gate_main.resolve_prompt_path", return_value=None):
        result = run_gate_policy(tmp_path, target="no_such_module")

    assert result.passed is False
    assert any(f.code == "unknown_target" for f in result.failures)


def test_gate_cmd_has_correct_options() -> None:
    """gate_cmd from gate_main exposes target, --policy, --stories-dir, --tests-dir, --json."""
    param_names = {p.name for p in gate_cmd_main.params}
    assert "target" in param_names
    assert "policy_path" in param_names
    assert "stories_dir" in param_names
    assert "tests_dir" in param_names
    assert "json_format" in param_names


def test_gate_cmd_exits_0_on_pass() -> None:
    """gate_cmd exit code 0 when GateResult.passed is True."""
    runner = CliRunner()
    mock_result = GateResult(passed=True, failures=[], policy=default_policy(), manifests_checked=1)
    with patch("pdd.gate_main.run_gate_policy", return_value=mock_result):
        result = runner.invoke(gate_cmd_main, [])
    assert result.exit_code == 0


def test_gate_cmd_exits_1_on_fail() -> None:
    """gate_cmd exit code 1 when GateResult.passed is False."""
    runner = CliRunner()
    failure = GateFailure(code="no_manifests", message="No manifests", fix_command="run pdd --evidence")
    mock_result = GateResult(passed=False, failures=[failure], policy=default_policy(), manifests_checked=0)
    with patch("pdd.gate_main.run_gate_policy", return_value=mock_result):
        result = runner.invoke(gate_cmd_main, [])
    assert result.exit_code == 1


def test_gate_cmd_text_pass_output() -> None:
    """gate_cmd prints pass message to output on success."""
    runner = CliRunner()
    mock_result = GateResult(passed=True, failures=[], policy=default_policy(), manifests_checked=1)
    with patch("pdd.gate_main.run_gate_policy", return_value=mock_result):
        result = runner.invoke(gate_cmd_main, [])
    assert result.exit_code == 0
    assert "passed" in result.output.lower()


def test_gate_cmd_text_fail_output() -> None:
    """gate_cmd prints failure code and fix_command on failure."""
    runner = CliRunner()
    failure = GateFailure(code="cost_limit", message="too expensive", fix_command="lower cost")
    mock_result = GateResult(passed=False, failures=[failure], policy=default_policy(), manifests_checked=1)
    with patch("pdd.gate_main.run_gate_policy", return_value=mock_result):
        result = runner.invoke(gate_cmd_main, [])
    assert result.exit_code == 1
    assert "cost_limit" in result.output
    assert "lower cost" in result.output


def test_gate_cmd_json_output_structure() -> None:
    """gate_cmd --json emits a JSON object with passed, exit_code, manifests_checked, failures."""
    runner = CliRunner()
    mock_result = GateResult(passed=True, failures=[], policy=default_policy(), manifests_checked=2)
    with patch("pdd.gate_main.run_gate_policy", return_value=mock_result):
        result = runner.invoke(gate_cmd_main, ["--json"])
    assert result.exit_code == 0
    payload = json.loads(result.output)
    assert payload["passed"] is True
    assert payload["exit_code"] == 0
    assert payload["manifests_checked"] == 2
    assert payload["failures"] == []


def test_check_validation_flags_all_pass() -> None:
    """No failures when all required validation statuses are passing."""
    policy = GatePolicy(
        require={"stories_pass": True, "verify_pass": True, "unit_tests_pass": True},
        allow={},
        limits=GateLimits(),
    )
    manifest = _make_manifest(
        validation={
            "detect_stories": "pass",
            "verify": "pass",
            "unit_tests": "pass",
        }
    )
    with patch("pdd.gate_main.prompt_changed_since_manifest", return_value=False):
        failures = _check_validation_flags(manifest, policy)
    assert failures == []


def test_check_validation_flags_missing_required() -> None:
    """Missing validation field -> <key>_missing failure code."""
    policy = GatePolicy(
        require={"stories_pass": True},
        allow={},
        limits=GateLimits(),
    )
    manifest = _make_manifest(validation={})
    with patch("pdd.gate_main.prompt_changed_since_manifest", return_value=False):
        failures = _check_validation_flags(manifest, policy)
    assert len(failures) == 1
    assert failures[0].code == "stories_pass_missing"


def test_check_validation_flags_not_available() -> None:
    """not_available validation -> <key>_not_available failure code."""
    policy = GatePolicy(
        require={"verify_pass": True},
        allow={},
        limits=GateLimits(),
    )
    manifest = _make_manifest(validation={"verify": "not_available"})
    with patch("pdd.gate_main.prompt_changed_since_manifest", return_value=False):
        failures = _check_validation_flags(manifest, policy)
    assert len(failures) == 1
    assert failures[0].code == "verify_not_available"


def test_check_validation_flags_skipped_verify_allowed() -> None:
    """Skipped verify with policy.allows skipped_verify -> no failure."""
    policy = GatePolicy(
        require={"verify_pass": True},
        allow={"skipped_verify": True},
        limits=GateLimits(),
    )
    manifest = _make_manifest(validation={"verify": "skipped"})
    with patch("pdd.gate_main.prompt_changed_since_manifest", return_value=False):
        failures = _check_validation_flags(manifest, policy)
    assert failures == []


def test_check_validation_flags_skipped_verify_not_allowed() -> None:
    """Skipped verify without policy allow -> skipped_verify failure."""
    policy = GatePolicy(
        require={"verify_pass": True},
        allow={"skipped_verify": False},
        limits=GateLimits(),
    )
    manifest = _make_manifest(validation={"verify": "skipped"})
    with patch("pdd.gate_main.prompt_changed_since_manifest", return_value=False):
        failures = _check_validation_flags(manifest, policy)
    assert len(failures) == 1
    assert failures[0].code == "skipped_verify"


def test_check_validation_flags_skipped_tests_allowed() -> None:
    """Skipped unit_tests with policy.allows skipped_tests -> no failure."""
    policy = GatePolicy(
        require={"unit_tests_pass": True},
        allow={"skipped_tests": True},
        limits=GateLimits(),
    )
    manifest = _make_manifest(validation={"unit_tests": "skipped"})
    with patch("pdd.gate_main.prompt_changed_since_manifest", return_value=False):
        failures = _check_validation_flags(manifest, policy)
    assert failures == []


def test_check_validation_flags_skipped_tests_not_allowed() -> None:
    """Skipped unit_tests without allow -> skipped_tests failure."""
    policy = GatePolicy(
        require={"unit_tests_pass": True},
        allow={"skipped_tests": False},
        limits=GateLimits(),
    )
    manifest = _make_manifest(validation={"unit_tests": "not_applicable"})
    with patch("pdd.gate_main.prompt_changed_since_manifest", return_value=False):
        failures = _check_validation_flags(manifest, policy)
    assert len(failures) == 1
    assert failures[0].code == "skipped_tests"


def test_check_validation_flags_stories_stale(tmp_path: Path) -> None:
    """Prompt changed after manifest was written -> stories_stale_after_prompt_change."""
    policy = GatePolicy(
        require={"stories_pass": True},
        allow={},
        limits=GateLimits(),
    )
    manifest = _make_manifest(validation={"detect_stories": "pass"})
    with patch("pdd.gate_main.prompt_changed_since_manifest", return_value=True):
        failures = _check_validation_flags(manifest, policy)
    assert any(f.code == "stories_stale_after_prompt_change" for f in failures)


def test_check_cost_limits_below_limit() -> None:
    """No failure when cost is within the limit."""
    policy = GatePolicy(require={}, allow={}, limits=GateLimits(max_cost_usd=20.0))
    manifest = _make_manifest(generation={"cost_usd": 10.0})
    failures = _check_cost_limits(manifest, policy)
    assert failures == []


def test_check_cost_limits_above_limit() -> None:
    """cost_limit failure when run cost exceeds policy limit."""
    policy = GatePolicy(require={}, allow={}, limits=GateLimits(max_cost_usd=20.0))
    manifest = _make_manifest(generation={"cost_usd": 25.0})
    failures = _check_cost_limits(manifest, policy)
    assert len(failures) == 1
    assert failures[0].code == "cost_limit"
    assert "$25.00" in failures[0].message
    assert "$20.00" in failures[0].message


def test_check_cost_limits_no_limit() -> None:
    """No failure when max_cost_usd is None."""
    policy = GatePolicy(require={}, allow={}, limits=GateLimits(max_cost_usd=None))
    manifest = _make_manifest(generation={"cost_usd": 999.0})
    failures = _check_cost_limits(manifest, policy)
    assert failures == []


def test_check_cost_limits_ctx_items_exceeded() -> None:
    """nondeterministic_context_limit failure when ctx items exceed policy limit.

    max_cost_usd must not be None (the function returns early when it is),
    and cost must be within limit so only the ctx-items check fires.
    """
    policy = GatePolicy(
        require={}, allow={},
        limits=GateLimits(max_cost_usd=100.0, max_nondeterministic_context_items=5),
    )
    manifest = _make_manifest(generation={"cost_usd": 1.0, "nondeterministic_context_items": 10})
    failures = _check_cost_limits(manifest, policy)
    assert len(failures) == 1
    assert failures[0].code == "nondeterministic_context_limit"


def test_evaluate_manifest_no_failures() -> None:
    """evaluate_manifest returns empty list when all checks pass."""
    policy = GatePolicy(require={}, allow={}, limits=GateLimits(max_cost_usd=None))
    manifest = _make_manifest()
    with patch("pdd.gate_main._check_validation_flags", return_value=[]), \
         patch("pdd.gate_main._check_output_freshness", return_value=[]), \
         patch("pdd.gate_main._check_cost_limits", return_value=[]), \
         patch("pdd.gate_main._check_critical_rules", return_value=[]), \
         patch("pdd.gate_main._check_contracts_pipeline", return_value=[]):
        failures = evaluate_manifest(manifest, Path("/tmp"), policy, stories_dir=None, tests_dir=None)
    assert failures == []
