"""Tests for ``pdd checkup gate`` policy enforcement."""
from __future__ import annotations

import json
import os
from pathlib import Path

import pytest

from pdd.evidence_manifest import validation_from_sync
from pdd.evidence_store import ManifestView, sha256_file
from pdd.gate_main import evaluate_manifest, run_gate_policy
from pdd.gate_policy import GatePolicy, GateLimits, load_policy


def _write_routine_manifest(
    path: Path,
    *,
    basename: str,
    output_rel: str,
    output_hash: str,
    validation: dict[str, str],
) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    payload = {
        "schema_version": 1,
        "run": {"id": f"run-{basename}", "command": "pdd sync", "pdd_version": "0.0.0"},
        "prompt": {"path": f"prompts/{basename}_python.prompt"},
        "outputs": [{"path": output_rel, "sha256": output_hash}],
        "validation": validation,
        "generation": {"cost_usd": 1.0},
        "contracts": {},
    }
    path.write_text(json.dumps(payload, indent=2) + "\n", encoding="utf-8")


def _production_default_validation() -> dict[str, str]:
    """Validation block shape from ``write_evidence_manifest`` before overrides."""
    return {
        "detect_stories": "not_available",
        "unit_tests": "not_available",
        "verify": "not_available",
    }


def test_load_policy_yaml(tmp_path: Path) -> None:
    policy_file = tmp_path / "policy.yml"
    policy_file.write_text(
        "require:\n  stories_pass: false\nlimits:\n  max_cost_usd: 5\n",
        encoding="utf-8",
    )
    policy = load_policy(policy_file)
    assert policy.requires("stories_pass") is False
    assert policy.limits.max_cost_usd == 5


def test_gate_fails_on_stale_output(tmp_path: Path) -> None:
    project = tmp_path
    code = project / "src" / "refund.py"
    code.parent.mkdir(parents=True)
    code.write_text("def refund():\n    return 1\n", encoding="utf-8")
    manifest_path = project / ".pdd" / "evidence" / "devunits" / "refund.latest.json"
    _write_routine_manifest(
        manifest_path,
        basename="refund",
        output_rel="src/refund.py",
        output_hash="deadbeef",
        validation={
            "detect_stories": "pass",
            "verify": "pass",
            "unit_tests": "pass",
        },
    )
    result = run_gate_policy(project, target="refund")
    assert not result.passed
    assert any(failure.code == "stale_output" for failure in result.failures)


def test_gate_passes_fresh_manifest(tmp_path: Path) -> None:
    project = tmp_path
    code = project / "src" / "refund.py"
    code.parent.mkdir(parents=True)
    code.write_text("def refund():\n    return 1\n", encoding="utf-8")
    from pdd.evidence_store import sha256_file

    manifest_path = project / ".pdd" / "evidence" / "devunits" / "refund.latest.json"
    _write_routine_manifest(
        manifest_path,
        basename="refund",
        output_rel="src/refund.py",
        output_hash=sha256_file(code),
        validation={
            "detect_stories": "pass",
            "verify": "pass",
            "unit_tests": "pass",
        },
    )
    policy = GatePolicy(
        require={
            "stories_pass": True,
            "verify_pass": True,
            "unit_tests_pass": True,
            "generated_outputs_fresh": True,
            "no_unchecked_critical_rules": False,
        },
        allow={"waivers": True, "story_only_rules": True, "skipped_verify": False},
        limits=GateLimits(max_cost_usd=20.0),
    )
    manifest = ManifestView.from_file(manifest_path, project)
    failures = evaluate_manifest(
        manifest,
        project,
        policy,
        stories_dir=None,
        tests_dir=None,
    )
    assert failures == []


def test_gate_json_output_shape(tmp_path: Path) -> None:
    result = run_gate_policy(tmp_path)
    payload = result.as_dict()
    assert "failures" in payload
    assert "policy" in payload


def test_gate_cli_json_with_manifest(tmp_path: Path, monkeypatch: pytest.MonkeyPatch) -> None:
    """``pdd checkup gate --json`` emits machine-readable output for a fresh manifest."""
    from click.testing import CliRunner

    from pdd import cli
    from pdd.evidence_store import sha256_file

    project = tmp_path
    monkeypatch.chdir(project)
    code = project / "src" / "refund.py"
    code.parent.mkdir(parents=True)
    code.write_text("def refund():\n    return 1\n", encoding="utf-8")
    manifest_path = project / ".pdd" / "evidence" / "devunits" / "refund.latest.json"
    _write_routine_manifest(
        manifest_path,
        basename="refund",
        output_rel="src/refund.py",
        output_hash=sha256_file(code),
        validation={
            "detect_stories": "pass",
            "verify": "pass",
            "unit_tests": "pass",
        },
    )

    result = CliRunner().invoke(
        cli.cli,
        ["--quiet", "checkup", "gate", "--json", "refund"],
        catch_exceptions=False,
    )
    assert result.exit_code == 0
    payload = json.loads(result.output)
    assert payload["passed"] is True
    assert payload["manifests_checked"] >= 1


def test_gate_cli_custom_policy_yaml(tmp_path: Path, monkeypatch: pytest.MonkeyPatch) -> None:
    """``pdd checkup gate --policy`` loads YAML overrides (e.g. disable stories_pass)."""
    from click.testing import CliRunner

    from pdd import cli
    from pdd.evidence_store import sha256_file

    project = tmp_path
    monkeypatch.chdir(project)
    code = project / "src" / "refund.py"
    code.parent.mkdir(parents=True)
    code.write_text("def refund():\n    return 1\n", encoding="utf-8")
    manifest_path = project / ".pdd" / "evidence" / "devunits" / "refund.latest.json"
    _write_routine_manifest(
        manifest_path,
        basename="refund",
        output_rel="src/refund.py",
        output_hash=sha256_file(code),
        validation={
            "detect_stories": "fail",
            "verify": "pass",
            "unit_tests": "pass",
        },
    )
    policy_file = project / "policy.yml"
    policy_file.write_text(
        "require:\n  stories_pass: false\n  verify_pass: true\n  unit_tests_pass: true\n",
        encoding="utf-8",
    )

    result = CliRunner().invoke(
        cli.cli,
        ["--quiet", "checkup", "gate", "--policy", str(policy_file), "refund"],
        catch_exceptions=False,
    )
    assert result.exit_code == 0


def test_checkup_gate_cli_json_with_manifest(
    tmp_path: Path,
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    """``pdd checkup gate --json`` dispatches to gate command and emits JSON."""
    from click.testing import CliRunner

    from pdd import cli
    from pdd.evidence_store import sha256_file

    project = tmp_path
    monkeypatch.chdir(project)
    code = project / "src" / "refund.py"
    code.parent.mkdir(parents=True)
    code.write_text("def refund():\n    return 1\n", encoding="utf-8")
    manifest_path = project / ".pdd" / "evidence" / "devunits" / "refund.latest.json"
    _write_routine_manifest(
        manifest_path,
        basename="refund",
        output_rel="src/refund.py",
        output_hash=sha256_file(code),
        validation={
            "detect_stories": "pass",
            "verify": "pass",
            "unit_tests": "pass",
        },
    )
    result = CliRunner().invoke(
        cli.cli,
        ["--quiet", "checkup", "gate", "--json", "refund"],
        catch_exceptions=False,
    )
    assert result.exit_code == 0
    payload = json.loads(result.output)
    assert payload["passed"] is True


def test_gate_fails_when_skip_tests_disallowed(tmp_path: Path) -> None:
    project = tmp_path
    code = project / "src" / "refund.py"
    code.parent.mkdir(parents=True)
    code.write_text("def refund():\n    return 1\n", encoding="utf-8")
    from pdd.evidence_store import sha256_file

    manifest_path = project / ".pdd" / "evidence" / "devunits" / "refund.latest.json"
    _write_routine_manifest(
        manifest_path,
        basename="refund",
        output_rel="src/refund.py",
        output_hash=sha256_file(code),
        validation={
            "detect_stories": "pass",
            "verify": "pass",
            "unit_tests": "skipped",
        },
    )
    result = run_gate_policy(project, target="refund")
    assert not result.passed
    assert any(f.code == "skipped_tests" for f in result.failures)


def test_gate_fails_when_prompt_changed_after_manifest(tmp_path: Path) -> None:
    project = tmp_path
    prompt = project / "prompts" / "refund_python.prompt"
    prompt.parent.mkdir(parents=True)
    prompt.write_text("v1\n", encoding="utf-8")
    code = project / "src" / "refund.py"
    code.parent.mkdir(parents=True)
    code.write_text("def refund():\n    return 1\n", encoding="utf-8")
    from pdd.evidence_store import sha256_file

    manifest_path = project / ".pdd" / "evidence" / "devunits" / "refund.latest.json"
    _write_routine_manifest(
        manifest_path,
        basename="refund",
        output_rel="src/refund.py",
        output_hash=sha256_file(code),
        validation={
            "detect_stories": "pass",
            "verify": "pass",
            "unit_tests": "pass",
        },
    )
    # Ensure prompt is newer than manifest to trigger stale story validation.
    prompt.write_text("v2\n", encoding="utf-8")
    # Force a clearly-later mtime so the freshness check is deterministic on
    # fast filesystems where the manifest write and the prompt rewrite can land
    # in the same mtime tick (the check compares prompt mtime > manifest mtime).
    manifest_mtime = manifest_path.stat().st_mtime
    os.utime(prompt, (manifest_mtime + 10, manifest_mtime + 10))
    result = run_gate_policy(project, target="refund")
    assert not result.passed
    assert any(f.code == "stories_stale_after_prompt_change" for f in result.failures)


def test_gate_fails_nondeterministic_context_limit(tmp_path: Path) -> None:
    project = tmp_path
    code = project / "src" / "refund.py"
    code.parent.mkdir(parents=True)
    code.write_text("def refund():\n    return 1\n", encoding="utf-8")
    from pdd.evidence_store import sha256_file

    manifest_path = project / ".pdd" / "evidence" / "devunits" / "refund.latest.json"
    _write_routine_manifest(
        manifest_path,
        basename="refund",
        output_rel="src/refund.py",
        output_hash=sha256_file(code),
        validation={
            "detect_stories": "pass",
            "verify": "pass",
            "unit_tests": "pass",
        },
    )
    payload = json.loads(manifest_path.read_text(encoding="utf-8"))
    payload.setdefault("generation", {})["nondeterministic_context_items"] = 2
    manifest_path.write_text(json.dumps(payload, indent=2) + "\n", encoding="utf-8")
    policy_file = project / "policy.yml"
    policy_file.write_text(
        "limits:\n  max_nondeterministic_context_items: 0\n",
        encoding="utf-8",
    )

    result = run_gate_policy(project, target="refund", policy_path=policy_file)
    assert not result.passed
    assert any(f.code == "nondeterministic_context_limit" for f in result.failures)


def test_gate_fails_generate_only_not_available_validation(tmp_path: Path) -> None:
    """Generate-only manifests default validation fields to not_available."""
    project = tmp_path
    code = project / "src" / "refund.py"
    code.parent.mkdir(parents=True)
    code.write_text("def refund():\n    return 1\n", encoding="utf-8")
    manifest_path = project / ".pdd" / "evidence" / "devunits" / "refund.latest.json"
    _write_routine_manifest(
        manifest_path,
        basename="refund",
        output_rel="src/refund.py",
        output_hash=sha256_file(code),
        validation=_production_default_validation(),
    )
    result = run_gate_policy(project, target="refund")
    assert not result.passed
    codes = {failure.code for failure in result.failures}
    assert "detect_stories_not_available" in codes
    assert "unit_tests_not_available" in codes
    assert "verify_not_available" in codes


def test_gate_fails_sync_skip_not_applicable_validation(tmp_path: Path) -> None:
    """Sync with --skip-tests/--skip-verify records not_applicable, not pass."""
    project = tmp_path
    code = project / "src" / "refund.py"
    code.parent.mkdir(parents=True)
    code.write_text("def refund():\n    return 1\n", encoding="utf-8")
    validation = validation_from_sync({}, skip_tests=True, skip_verify=True)
    assert validation["unit_tests"] == "not_applicable"
    assert validation["verify"] == "not_applicable"
    manifest_path = project / ".pdd" / "evidence" / "devunits" / "refund.latest.json"
    _write_routine_manifest(
        manifest_path,
        basename="refund",
        output_rel="src/refund.py",
        output_hash=sha256_file(code),
        validation=validation,
    )
    result = run_gate_policy(project, target="refund")
    assert not result.passed
    codes = {failure.code for failure in result.failures}
    assert "skipped_tests" in codes
    assert "skipped_verify" in codes
    assert "stories_pass" in codes


def test_gate_allows_skipped_verify_and_tests_when_policy_permits(
    tmp_path: Path,
) -> None:
    """``allow.skipped_*: true`` satisfies skip-shaped verify/tests validation."""
    project = tmp_path
    code = project / "src" / "refund.py"
    code.parent.mkdir(parents=True)
    code.write_text("def refund():\n    return 1\n", encoding="utf-8")
    validation = validation_from_sync({}, skip_tests=True, skip_verify=True)
    validation["detect_stories"] = "passed"
    manifest_path = project / ".pdd" / "evidence" / "devunits" / "refund.latest.json"
    _write_routine_manifest(
        manifest_path,
        basename="refund",
        output_rel="src/refund.py",
        output_hash=sha256_file(code),
        validation=validation,
    )
    policy_file = project / "policy.yml"
    policy_file.write_text(
        "allow:\n  skipped_verify: true\n  skipped_tests: true\n",
        encoding="utf-8",
    )
    result = run_gate_policy(project, target="refund", policy_path=policy_file)
    assert result.passed
    assert result.failures == []


def test_checkup_gate_without_target_runs_all_manifests(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    """Bare ``pdd checkup gate`` must run the gate, not print help and exit 0."""
    from click.testing import CliRunner

    from pdd import cli

    project = tmp_path
    monkeypatch.chdir(project)
    code = project / "src" / "refund.py"
    code.parent.mkdir(parents=True)
    code.write_text("def refund():\n    return 1\n", encoding="utf-8")
    manifest_path = project / ".pdd" / "evidence" / "devunits" / "refund.latest.json"
    _write_routine_manifest(
        manifest_path,
        basename="refund",
        output_rel="src/refund.py",
        output_hash=sha256_file(code),
        validation=_production_default_validation(),
    )
    result = CliRunner().invoke(cli.cli, ["checkup", "gate"], catch_exceptions=False)
    assert result.exit_code == 1
    assert "Usage:" not in result.output
    assert "PDD gate failed" in result.output
    assert "not_available" in result.output


def test_checkup_gate_without_target_empty_project(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    """Bare ``pdd checkup gate`` with no manifests reports no_manifests, not help."""
    from click.testing import CliRunner

    from pdd import cli

    monkeypatch.chdir(tmp_path)
    result = CliRunner().invoke(cli.cli, ["checkup", "gate"], catch_exceptions=False)
    assert result.exit_code == 1
    assert "No evidence manifests found" in result.output
    assert "Usage:" not in result.output


def test_top_level_cli_has_no_gate_command() -> None:
    """``pdd --help`` must not register a top-level ``gate`` command."""
    from pdd import cli

    assert "gate" not in cli.cli.commands


def test_checkup_gate_help_shows_gate_options() -> None:
    """``pdd checkup gate --help`` renders gate-specific options."""
    from click.testing import CliRunner

    from pdd import cli

    result = CliRunner().invoke(cli.cli, ["checkup", "gate", "--help"])
    assert result.exit_code == 0
    assert "pdd checkup gate" in result.output
    assert "--policy" in result.output
    assert "--json" in result.output
    assert "evidence" in result.output.lower()
