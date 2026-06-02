"""Tests for capability contracts and ``pdd policy check``."""
from __future__ import annotations

import json
from pathlib import Path

from click.testing import CliRunner

from pdd import cli
from pdd.contract_ir import extract_capabilities, parse_prompt_contracts
from pdd.policy_check import run_policy_check

FIXTURE_DIR = Path(__file__).resolve().parent / "fixtures" / "policy_check"
_CLI_ENV = {"PDD_AUTO_UPDATE": "false"}


def _cli_json_payload(output: str) -> list:
    """Extract the JSON array from mixed CLI output (debug snapshots, etc.)."""
    start = output.index("[")
    end = output.rindex("]") + 1
    return json.loads(output[start:end])


def test_extract_capabilities_parses_modals() -> None:
    """Capability bullets retain modal metadata for policy enforcement."""
    prompt = FIXTURE_DIR / "forbidden_network_python.prompt"
    ir = parse_prompt_contracts(prompt)
    capabilities = extract_capabilities(ir.sections["capabilities"])
    assert any(c.is_must_not and "network" in c.text.lower() for c in capabilities)
    assert any(not c.is_must_not for c in capabilities)


def test_allowed_code_passes_with_matching_prompt() -> None:
    """Allowed imports and env reads pass when capabilities permit them."""
    prompt = FIXTURE_DIR / "allowed_refund_python.prompt"
    target = FIXTURE_DIR / "allowed_refund.py"
    result = run_policy_check(target, prompt)
    assert result.passed
    assert result.issues == []


def test_forbidden_network_import_fails() -> None:
    """Network libraries are flagged when capabilities forbid them."""
    prompt = FIXTURE_DIR / "forbidden_network_python.prompt"
    target = FIXTURE_DIR / "forbidden_network.py"
    result = run_policy_check(target, prompt)
    assert not result.passed
    assert any(i.category == "network" for i in result.issues)


def test_sensitive_logging_fails() -> None:
    """Logging sensitive variable names is reported as leakage."""
    prompt = FIXTURE_DIR / "sensitive_log_python.prompt"
    target = FIXTURE_DIR / "sensitive_log.py"
    result = run_policy_check(target, prompt)
    assert not result.passed
    assert any(i.category == "leakage" for i in result.issues)


def test_legacy_prompt_without_capabilities_does_not_fail() -> None:
    """Modules without capability sections stay permissive unless strict."""
    legacy_prompt = (
        Path(__file__).resolve().parent / "fixtures" / "test_generation" / "refund_policy_python.prompt"
    )
    target = FIXTURE_DIR / "forbidden_network.py"
    result = run_policy_check(target, legacy_prompt, strict=False)
    assert result.passed


def test_strict_mode_flags_side_effects_without_capabilities() -> None:
    """Strict mode enforces checks even when the prompt omits capabilities."""
    legacy_prompt = (
        Path(__file__).resolve().parent / "fixtures" / "test_generation" / "refund_policy_python.prompt"
    )
    target = FIXTURE_DIR / "forbidden_network.py"
    result = run_policy_check(target, legacy_prompt, strict=True)
    assert not result.passed


def test_invalid_python_fails_gracefully(tmp_path: Path) -> None:
    """Syntax errors surface as system issues instead of raising."""
    broken = tmp_path / "broken.py"
    broken.write_text("def oops(\n", encoding="utf-8")
    result = run_policy_check(broken)
    assert not result.passed
    assert any(i.category == "system" for i in result.issues)


def test_policy_check_cli_json_output() -> None:
    """CLI ``--json`` returns structured findings for CI integration."""
    target = FIXTURE_DIR / "forbidden_network.py"
    prompt = FIXTURE_DIR / "forbidden_network_python.prompt"
    result = CliRunner().invoke(
        cli.cli,
        ["policy", "check", str(target), "--prompt", str(prompt), "--json"],
        env=_CLI_ENV,
    )
    assert result.exit_code != 0, result.output
    payload = _cli_json_payload(result.output)
    assert payload[0]["passed"] is False
    assert payload[0]["capabilities"]
    assert payload[0]["issues"]
