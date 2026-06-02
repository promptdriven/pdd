"""CLI wiring tests for ``pdd policy check``."""
from __future__ import annotations

import json
from pathlib import Path

from click.testing import CliRunner

from pdd import cli

FIXTURE_DIR = Path(__file__).resolve().parents[1] / "fixtures" / "policy_check"
_CLI_ENV = {"PDD_AUTO_UPDATE": "false"}


def _cli_json_payload(output: str) -> list:
    start = output.index("[")
    end = output.rindex("]") + 1
    return json.loads(output[start:end])


def test_policy_check_passes_for_compliant_module() -> None:
    """Compliant modules exit zero in human-readable mode."""
    target = FIXTURE_DIR / "allowed_refund.py"
    prompt = FIXTURE_DIR / "allowed_refund_python.prompt"
    result = CliRunner().invoke(
        cli.cli,
        ["policy", "check", str(target), "--prompt", str(prompt)],
        env=_CLI_ENV,
    )
    assert result.exit_code == 0, result.output
    assert "PASS" in result.output


def test_policy_check_strict_exits_with_failure_code() -> None:
    """Strict mode uses exit code 2 when violations are present."""
    target = FIXTURE_DIR / "forbidden_network.py"
    prompt = FIXTURE_DIR / "forbidden_network_python.prompt"
    result = CliRunner().invoke(
        cli.cli,
        ["policy", "check", str(target), "--prompt", str(prompt), "--strict"],
        env=_CLI_ENV,
    )
    assert result.exit_code == 2, result.output


def test_policy_check_json_lists_targets() -> None:
    """JSON mode returns one record per scanned file."""
    target = FIXTURE_DIR / "forbidden_network.py"
    prompt = FIXTURE_DIR / "forbidden_network_python.prompt"
    result = CliRunner().invoke(
        cli.cli,
        ["policy", "check", str(target), "--prompt", str(prompt), "--json"],
        env=_CLI_ENV,
    )
    records = _cli_json_payload(result.output)
    assert records[0]["target"].endswith("forbidden_network.py")
    assert records[0]["issues"]
