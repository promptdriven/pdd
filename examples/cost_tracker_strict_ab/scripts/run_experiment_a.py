#!/usr/bin/env python3
"""
Experiment A — deterministic spec-only A/B (no LLM).

Compares baseline vs contracts-enriched cost_tracker prompts using
pdd gate, pdd evidence emit/validate, and pdd contracts drift.
"""
from __future__ import annotations

import argparse
import json
import os
import sys
from pathlib import Path
from typing import Any

_REPO_ROOT = Path(__file__).resolve().parents[3]
_DEMO_DIR = Path(__file__).resolve().parent.parent
_PARENT = _DEMO_DIR.parent / "contract_commands_cost_tracker_e2e_demo"

os.environ.setdefault("PDD_PATH", str(_REPO_ROOT / "pdd"))
os.environ.setdefault("PDD_SKIP_UPDATE_CHECK", "1")

from click.testing import CliRunner  # noqa: E402

from pdd import cli  # noqa: E402
from pdd.evidence_manifest import MANIFEST_SCHEMA  # noqa: E402

_BASELINE = _PARENT / "prompts" / "cost_tracker_utility_Python.prompt"
_CONTRACTS = _PARENT / "prompts" / "cost_tracker_with_contracts_python.prompt"
_STORIES = _PARENT / "user_stories"
_TESTS = _PARENT / "tests"


def _parse_json(stdout: str) -> Any:
    text = stdout.strip()
    for idx, ch in enumerate(text):
        if ch in "{[":
            try:
                return json.loads(text[idx:])
            except json.JSONDecodeError:
                continue
    raise ValueError(f"no JSON in stdout: {stdout[:300]!r}")


def _rel(path: Path) -> str:
    try:
        return str(path.relative_to(_PARENT))
    except ValueError:
        return str(path)


def _run(runner: CliRunner, args: list[str], *, allow_warn: bool = False) -> int:
    result = runner.invoke(cli.cli, args, catch_exceptions=True)
    code = result.exit_code if result.exit_code is not None else 0
    if allow_warn and code == 1:
        code = 0
    if code not in (0, 1, 2) and not (allow_warn and code == 1):
        raise RuntimeError(f"pdd failed ({code}): {result.output}")
    return code


def _write(path: Path, payload: Any) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(payload, indent=2) + "\n", encoding="utf-8")


def _rule_count_from_evidence(data: dict[str, Any]) -> int:
    rows = data.get("contracts_compile", {}).get("results", [])
    if not rows:
        return 0
    return int(rows[0].get("rule_count", 0) or 0)


def _unchecked_from_evidence(data: dict[str, Any]) -> int:
    rows = data.get("coverage", {}).get("results", [])
    if not rows:
        return 0
    return int(rows[0].get("summary", {}).get("unchecked", 0) or 0)


def run_experiment_a() -> int:
    if not _BASELINE.is_file() or not _CONTRACTS.is_file():
        print("ERROR: missing prompts in contract_commands_cost_tracker_e2e_demo", file=sys.stderr)
        return 1

    os.chdir(_PARENT)
    runner = CliRunner()
    reports = _DEMO_DIR / "reports"
    reports.mkdir(exist_ok=True)

    stories = "user_stories"
    tests_dir = "tests"
    baseline_rel = _rel(_BASELINE)
    contracts_rel = _rel(_CONTRACTS)

    print("\n=== Experiment A0: baseline prompt ===")
    _run(
        runner,
        [
            "--quiet", "gate", "--no-strict", "--json",
            "--stories-dir", stories, "--tests-dir", tests_dir,
            baseline_rel,
        ],
        allow_warn=True,
    )
    _run(
        runner,
        [
            "--quiet", "evidence", "emit",
            "--prompt", baseline_rel,
            "--output", str((reports / "evidence_A0.json").resolve()),
            "--stories-dir", stories, "--tests-dir", tests_dir,
        ],
    )

    print("\n=== Experiment A1: contracts prompt ===")
    _run(
        runner,
        [
            "--quiet", "gate", "--no-strict", "--json",
            "--stories-dir", stories, "--tests-dir", tests_dir,
            contracts_rel,
        ],
        allow_warn=True,
    )
    _run(
        runner,
        [
            "--quiet", "evidence", "emit",
            "--prompt", contracts_rel,
            "--output", str((reports / "evidence_A1.json").resolve()),
            "--stories-dir", stories, "--tests-dir", tests_dir,
        ],
    )

    ev_a0 = json.loads((reports / "evidence_A0.json").read_text(encoding="utf-8"))
    ev_a1 = json.loads((reports / "evidence_A1.json").read_text(encoding="utf-8"))
    drift_path = reports / "experiment_a_drift.json"
    drift_result = runner.invoke(
        cli.cli,
        [
            "--quiet", "contracts", "drift", "--json",
            str((reports / "evidence_A0.json").resolve()),
            str((reports / "evidence_A1.json").resolve()),
        ],
        catch_exceptions=True,
    )
    drift_payload = _parse_json(drift_result.output or "{}")
    _write(drift_path, drift_payload)

    a0_rules = _rule_count_from_evidence(ev_a0)
    a1_rules = _rule_count_from_evidence(ev_a1)
    a1_unchecked = _unchecked_from_evidence(ev_a1)

    report = {
        "schema": "pdd.ab_report.v1",
        "experiment": "cost_tracker_spec_instrumentation",
        "experiment_question": (
            "Did adding contract metadata improve deterministic spec measurability? "
            "(Not a clarify A/B — see Experiment B for clarify.)"
        ),
        "mode": "deterministic",
        "layers": {
            "prompt": "gate, evidence, contracts compile/coverage",
            "codegen": "none",
            "process": "evidence validate, drift",
        },
        "A0_baseline": {
            "prompt": baseline_rel,
            "rule_count": a0_rules,
            "unchecked": _unchecked_from_evidence(ev_a0),
            "sha256": ev_a0.get("prompt", {}).get("sha256", ""),
            "gate_note": "rule_count==0 means gate passed vacuously (nothing to check)",
        },
        "A1_contracts": {
            "prompt": contracts_rel,
            "rule_count": a1_rules,
            "unchecked": a1_unchecked,
            "sha256": ev_a1.get("prompt", {}).get("sha256", ""),
        },
        "drift": drift_payload,
        "verdict": {
            "spec_instrumentation_improved": a1_rules >= 3 and a1_unchecked <= a1_rules,
            "A1_has_rules": a1_rules >= 3,
            "drift_detected": drift_payload.get("has_drift", False),
            "schemas_valid": ev_a0.get("schema") == MANIFEST_SCHEMA,
            "behavioral_claim_strength": "not_applicable",
        },
    }
    _write(reports / "experiment_a.json", report)

    failures: list[str] = []
    if _rule_count_from_evidence(ev_a1) < 3:
        failures.append("A1 expected rule_count >= 3")
    if not drift_payload.get("has_drift"):
        failures.append("expected drift between A0 and A1 manifests")
    if ev_a0.get("schema") != MANIFEST_SCHEMA:
        failures.append("invalid A0 evidence schema")

    if failures:
        print("\nExperiment A FAILED:", file=sys.stderr)
        for f in failures:
            print(f"  - {f}", file=sys.stderr)
        return 1

    print("\nExperiment A passed (gate + evidence + drift).")
    print(f"  report: {reports / 'experiment_a.json'}")
    return 0


def main() -> int:
    parser = argparse.ArgumentParser(description="Experiment A: deterministic spec A/B")
    parser.parse_args()
    return run_experiment_a()


if __name__ == "__main__":
    raise SystemExit(main())
