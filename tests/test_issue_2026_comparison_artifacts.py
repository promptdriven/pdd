"""Integrity checks for the zero-cost comparison artifacts in issue #2026."""

from __future__ import annotations

import json
import xml.etree.ElementTree as ET
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1] / "research" / "issue-2026"
ARTIFACTS = ROOT / "artifacts"
EXPECTED_COMMIT = "3d4a0c82eeb22b2f3f8b97dbe94289123cc66a6c"
EXPECTED_TREE = "29f3d82202e1d648b20449db8efc2a8d0c78288d"
EXPECTED_MANIFEST = ["textutil", "greeter"]


def load_json(path: Path) -> dict:
    return json.loads(path.read_text())


def test_frozen_fixture_is_issue_7() -> None:
    fixture = load_json(ARTIFACTS / "fixture-issue-7.json")
    assert fixture["number"] == 7
    assert fixture["html_url"] == "https://github.com/e2e-org/greeter-proj/issues/7"
    assert "prompts/greeter_python.prompt" in fixture["body"]
    assert "prompts/textutil_python.prompt" in fixture["body"]


def test_paired_arms_are_equivalent_and_provider_free() -> None:
    records = [load_json(path) for path in sorted((ARTIFACTS / "candidate").glob("execution-*.json"))]
    assert [record["mode"] for record in records] == [
        "regular", "agentic", "agentic", "regular", "regular", "agentic"
    ]
    assert {record["before"]["commit"] for record in records} == {EXPECTED_COMMIT}
    assert {record["before"]["tree"] for record in records} == {EXPECTED_TREE}
    assert len({json.dumps(record["before"]["files"], sort_keys=True) for record in records}) == 1

    for record in records:
        assert record["manifest"] == EXPECTED_MANIFEST
        assert record["before"]["status"] == ""
        assert record["after"]["status"] == "?? .pdd/"
        assert record["worktree_diff"] == ""
        assert len(record["after"]["generated_files"]) == 2
        assert all(command["returncode"] == 0 for command in record["commands"])
        assert [command["command"][-2:] for command in record["commands"]] == (
            [["--agentic", "--no-steer"], ["--agentic", "--no-steer"]]
            if record["mode"] == "agentic"
            else [["--dry-run", "--no-steer"], ["--dry-run", "--no-steer"]]
        )
        assert record["logs"]["claude_calls.log"] == ""
        assert record["logs"]["gh_writes.log"] == ""
        assert record["logs"]["TRIPWIRE.log"] == ""


def test_planning_reproduces_historical_scope_defect_and_candidate_fix() -> None:
    baseline = load_json(ARTIFACTS / "baseline" / "planning-result.json")
    candidate = load_json(ARTIFACTS / "candidate" / "planning-result.json")
    assert baseline["before"]["commit"] == candidate["before"]["commit"]
    assert baseline["before"]["tree"] == candidate["before"]["tree"]
    assert "Dry run complete: 1 module(s) would sync: greeter" in baseline["result"]["stdout"]
    assert "edge omitted from schedule" in baseline["result"]["stdout"]
    assert "Dry run complete: 2 module(s) would sync: greeter, textutil" in candidate["result"]["stdout"]
    assert "'greeter': ['textutil']" in candidate["result"]["stdout"]
    for record in (baseline, candidate):
        assert record["logs"]["claude_calls.log"] == ""
        assert record["logs"]["TRIPWIRE.log"] == ""


def test_network_probe_and_junit_evidence_passed() -> None:
    summary = load_json(ARTIFACTS / "candidate" / "summary.json")
    assert summary["validation"] == "passed"
    assert summary["network_isolation"]["all_blocked"] is True
    assert all(attempt["blocked"] for attempt in summary["network_isolation"]["attempts"])

    testsuites = ET.parse(ARTIFACTS / "hermetic-candidate-f680c761.xml").getroot()
    testsuite = testsuites.find("testsuite")
    assert testsuite is not None
    assert int(testsuite.attrib["tests"]) == 14
    assert int(testsuite.attrib["failures"]) == 0
    assert int(testsuite.attrib["errors"]) == 0
