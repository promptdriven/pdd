"""End-to-end waiver workflow checks across contracts, coverage, gate, and evidence."""
from __future__ import annotations

import json
from pathlib import Path

import pytest
from click.testing import CliRunner

from pdd.commands.contracts import contracts_check
from pdd.commands.coverage import coverage_cmd
from pdd.commands.gate import gate_cmd
from pdd.evidence_manifest import write_evidence_manifest

FIXTURES = Path(__file__).parent / "fixtures" / "contract_check"
VALID = FIXTURES / "waiver_valid_python.prompt"
EXPIRED = FIXTURES / "waiver_expired_python.prompt"


def test_contracts_check_json_includes_waiver_status() -> None:
    result = CliRunner().invoke(
        contracts_check,
        [str(VALID), "--json"],
    )
    assert result.exit_code == 0, result.output
    payload = json.loads(result.output)
    assert len(payload) == 1
    waivers = payload[0]["waivers"]
    assert len(waivers) == 1
    assert waivers[0]["id"] == "W1"
    assert waivers[0]["status"] == "active"
    assert waivers[0]["rule_id"] == "R3"


def test_coverage_json_shows_waived_rule_with_status() -> None:
    result = CliRunner().invoke(
        coverage_cmd,
        [str(VALID), "--json"],
    )
    # Exit 1: R1/R2 are test-only gaps; waiver metadata is still emitted.
    assert result.exit_code == 1, result.output
    payload = json.loads(result.output)
    rules = payload["results"][0]["rules"]
    r3 = next(rule for rule in rules if rule["rule_id"] == "R3")
    assert r3["status"] == "waived"
    assert r3["waiver"] == "W1"
    assert r3["waiver_status"] == "active"
    assert r3["waiver_expires"] == "2099-06-01"


def test_gate_json_reports_policy_outcome() -> None:
    result = CliRunner().invoke(
        gate_cmd,
        [str(VALID), "--allow-waivers", "--json"],
    )
    assert result.exit_code == 0, result.output
    payload = json.loads(result.output)
    assert payload["ok"] is True
    assert len(payload["waivers"]) == 1
    assert payload["waivers"][0]["policy_outcome"] == "pass"


def test_gate_enforce_expiration_fails_expired_fixture() -> None:
    result = CliRunner().invoke(
        gate_cmd,
        [str(EXPIRED), "--enforce-expiration", "--json"],
    )
    assert result.exit_code == 1, result.output
    payload = json.loads(result.output)
    assert payload["ok"] is False
    assert any("expired" in reason for row in payload["waivers"] for reason in row["policy_reasons"])


def test_evidence_manifest_includes_contract_waivers(tmp_path: Path) -> None:
    prompt = tmp_path / "prompts" / "waiver_python.prompt"
    output = tmp_path / "src" / "waiver.py"
    prompt.parent.mkdir()
    output.parent.mkdir()
    prompt.write_text(VALID.read_text(encoding="utf-8"), encoding="utf-8")
    output.write_text("def upload():\n    return True\n", encoding="utf-8")

    manifest_path = write_evidence_manifest(
        command="pdd generate",
        prompt_file=prompt,
        output_files=[output],
        project_root=tmp_path,
    )
    manifest = json.loads(manifest_path.read_text(encoding="utf-8"))
    contracts = manifest["contracts"]
    assert contracts["status"] == "available"
    assert "waivers" in contracts
    assert contracts["waivers"][0]["id"] == "W1"
    assert contracts["waivers"][0]["rule_id"] == "R3"
    r3 = contracts["rules"]["R3"]
    assert r3["status"] == "waived"
    assert r3["waiver"] == "W1"
    assert r3["waiver_status"] == "active"
