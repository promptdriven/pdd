"""Tests for ``pdd checkup drift`` regeneration stability."""
from __future__ import annotations

import json
from pathlib import Path
from types import SimpleNamespace
from unittest.mock import patch

from pdd.drift_main import run_drift
from pdd.evidence_store import sha256_file


def _write_fixture(project: Path) -> tuple[Path, Path]:
    prompt = project / "prompts" / "refund_payment_python.prompt"
    prompt.parent.mkdir(parents=True)
    prompt.write_text("<prompt>\nRefund module.\n</prompt>\n", encoding="utf-8")
    code = project / "pdd" / "refund_payment.py"
    code.parent.mkdir(parents=True)
    code.write_text(
        "def refund_payment(amount: int) -> int:\n    return amount\n",
        encoding="utf-8",
    )
    return prompt, code


def test_drift_regenerates_even_with_one_run(tmp_path: Path) -> None:
    _write_fixture(tmp_path)
    with patch("pdd.drift_main._regenerate_code") as mock_regenerate:
        report = run_drift("refund_payment", tmp_path, runs=1, dry_run=False)
    assert report.status == "stable"
    mock_regenerate.assert_called_once()


def test_drift_uses_best_output_from_manifest(tmp_path: Path) -> None:
    prompt, code = _write_fixture(tmp_path)
    extra = tmp_path / "artifacts" / "notes.txt"
    extra.parent.mkdir(parents=True)
    extra.write_text("n/a\n", encoding="utf-8")
    manifest = tmp_path / ".pdd" / "evidence" / "devunits" / "refund_payment.latest.json"
    manifest.parent.mkdir(parents=True)
    manifest.write_text(
        json.dumps(
            {
                "schema_version": 1,
                "prompt": {"path": str(prompt.relative_to(tmp_path))},
                "outputs": [
                    {"path": str(extra.relative_to(tmp_path)), "sha256": sha256_file(extra)},
                    {"path": str(code.relative_to(tmp_path)), "sha256": sha256_file(code)},
                ],
                "validation": {"unit_tests": "pass", "detect_stories": "pass", "verify": "pass"},
            },
            indent=2,
        )
        + "\n",
        encoding="utf-8",
    )
    report = run_drift(
        "refund_payment",
        tmp_path,
        runs=1,
        dry_run=True,
        from_evidence=manifest,
    )
    assert report.code_path.endswith("refund_payment.py")


def test_drift_behavior_unstable_when_any_run_fails(tmp_path: Path) -> None:
    _write_fixture(tmp_path)
    with patch("pdd.drift_main._run_pytest", side_effect=[True, False]):
        report = run_drift("refund_payment", tmp_path, runs=2, dry_run=True)
    assert report.status == "unstable"
    assert not report.behavior_unchanged


def test_drift_fails_when_configured_story_verify_policy_fail(tmp_path: Path) -> None:
    prompt, code = _write_fixture(tmp_path)
    manifest = tmp_path / ".pdd" / "evidence" / "devunits" / "refund_payment.latest.json"
    manifest.parent.mkdir(parents=True)
    manifest.write_text(
        json.dumps(
            {
                "schema_version": 1,
                "prompt": {"path": str(prompt.relative_to(tmp_path))},
                "outputs": [{"path": str(code.relative_to(tmp_path)), "sha256": sha256_file(code)}],
                "validation": {"unit_tests": "pass", "detect_stories": "failed", "verify": "failed"},
            },
            indent=2,
        )
        + "\n",
        encoding="utf-8",
    )
    with patch("pdd.drift_main.run_gate_policy", return_value=SimpleNamespace(passed=False)):
        report = run_drift(
            "refund_payment",
            tmp_path,
            runs=1,
            dry_run=True,
            from_evidence=manifest,
        )
    assert report.status == "unstable"
    snap = report.snapshots[0]
    assert not snap.stories_passed
    assert not snap.verify_passed
    assert not snap.policy_passed
