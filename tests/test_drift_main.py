"""Tests for ``pdd checkup drift`` regeneration stability."""
from __future__ import annotations

import json
from pathlib import Path
from types import SimpleNamespace
from unittest.mock import patch

import pytest

from pdd.drift_main import (
    DEFAULT_MAX_COST_USD,
    RunSnapshot,
    _public_api,
    run_drift,
)
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


def test_drift_does_not_mutate_baseline_code_file(tmp_path: Path) -> None:
    _prompt, code = _write_fixture(tmp_path)
    original = code.read_bytes()

    def _fake_regenerate(_prompt_path: Path, output_path: Path, **kwargs) -> float:
        output_path.parent.mkdir(parents=True, exist_ok=True)
        output_path.write_text("def mutated(amount: int) -> int:\n    return amount\n", encoding="utf-8")
        return 0.01

    with patch("pdd.drift_main._regenerate_code", side_effect=_fake_regenerate):
        with patch("pdd.drift_main._evaluate_candidate") as mock_eval:
            mock_eval.return_value = (
                RunSnapshot(1, "x", ["def mutated"], True, True, True, True),
                0.0,
            )
            run_drift("refund_payment", tmp_path, runs=1, dry_run=False)

    assert code.read_bytes() == original


def test_drift_public_api_change_fails_against_baseline(tmp_path: Path) -> None:
    _write_fixture(tmp_path)

    def _fake_regenerate(_prompt_path: Path, output_path: Path, **kwargs) -> float:
        output_path.parent.mkdir(parents=True, exist_ok=True)
        output_path.write_text("class RefundService:\n    pass\n", encoding="utf-8")
        return 0.0

    with patch("pdd.drift_main._regenerate_code", side_effect=_fake_regenerate):
        with patch("pdd.drift_main._evaluate_candidate") as mock_eval:
            mock_eval.return_value = (
                RunSnapshot(1, "b", ["class RefundService"], True, True, True, True),
                0.0,
            )
            report = run_drift("refund_payment", tmp_path, runs=1, dry_run=False)

    assert report.baseline_public_api == ["def refund_payment"]
    assert not report.public_api_unchanged
    assert report.status == "unstable"


def test_drift_regenerates_into_isolated_paths(tmp_path: Path) -> None:
    _write_fixture(tmp_path)
    seen_outputs: list[Path] = []

    def _fake_regenerate(_prompt_path: Path, output_path: Path, **kwargs) -> float:
        seen_outputs.append(output_path)
        output_path.parent.mkdir(parents=True, exist_ok=True)
        output_path.write_text(
            "def refund_payment(amount: int) -> int:\n    return amount\n",
            encoding="utf-8",
        )
        return 0.0

    with patch("pdd.drift_main._regenerate_code", side_effect=_fake_regenerate):
        with patch("pdd.drift_main._evaluate_candidate") as mock_eval:
            mock_eval.return_value = (
                RunSnapshot(1, "a", ["def refund_payment"], True, True, True, True),
                0.0,
            )
            run_drift("refund_payment", tmp_path, runs=2, dry_run=False)

    assert len(seen_outputs) == 2
    assert all("candidates" in path.as_posix() for path in seen_outputs)
    assert all(path.name == "refund_payment.py" for path in seen_outputs)


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
                "validation": {"unit_tests": "pass"},
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


def test_drift_behavior_unstable_when_tests_fail(tmp_path: Path) -> None:
    _write_fixture(tmp_path)

    def _failing_eval(*_args, **_kwargs):
        return (
            RunSnapshot(1, "a", ["def refund_payment"], False, True, True, True),
            0.0,
        )

    with patch("pdd.drift_main._evaluate_candidate", side_effect=_failing_eval):
        report = run_drift("refund_payment", tmp_path, runs=1, dry_run=True)

    assert report.status == "unstable"
    assert not report.behavior_unchanged


def test_drift_reruns_stories_when_configured(tmp_path: Path) -> None:
    prompt, code = _write_fixture(tmp_path)
    manifest = tmp_path / ".pdd" / "evidence" / "devunits" / "refund_payment.latest.json"
    manifest.parent.mkdir(parents=True)
    manifest.write_text(
        json.dumps(
            {
                "schema_version": 1,
                "prompt": {"path": str(prompt.relative_to(tmp_path))},
                "outputs": [{"path": str(code.relative_to(tmp_path)), "sha256": sha256_file(code)}],
                "validation": {"detect_stories": "pass"},
            },
            indent=2,
        )
        + "\n",
        encoding="utf-8",
    )

    with patch("pdd.drift_main._run_stories_check", return_value=(False, 0.5)) as mock_stories:
        with patch("pdd.drift_main._run_pytest_for_candidate", return_value=True):
            report = run_drift(
                "refund_payment",
                tmp_path,
                runs=1,
                dry_run=True,
                from_evidence=manifest,
            )

    mock_stories.assert_called_once()
    assert report.status == "unstable"
    assert not report.snapshots[0].stories_passed


def test_drift_max_cost_stops_regeneration(tmp_path: Path) -> None:
    _write_fixture(tmp_path)

    with patch("pdd.drift_main._regenerate_code", return_value=2.0):
        with patch("pdd.drift_main._evaluate_candidate") as mock_eval:
            mock_eval.return_value = (
                RunSnapshot(1, "a", ["def refund_payment"], True, True, True, True),
                0.0,
            )
            report = run_drift(
                "refund_payment",
                tmp_path,
                runs=3,
                dry_run=False,
                max_cost_usd=1.0,
            )

    assert report.cost_budget_exceeded
    assert report.status == "unstable"
    assert len(report.snapshots) == 0


def test_drift_integration_real_eval_baseline_unchanged(tmp_path: Path) -> None:
    """Exercise ``run_drift`` with only regeneration mocked; real candidate evaluation."""
    _prompt, code = _write_fixture(tmp_path)
    original = code.read_bytes()
    stable_source = code.read_text(encoding="utf-8")

    def _fake_regenerate(_prompt_path: Path, output_path: Path, **kwargs) -> float:
        output_path.parent.mkdir(parents=True, exist_ok=True)
        output_path.write_text(stable_source, encoding="utf-8")
        return 0.01

    with patch("pdd.drift_main._regenerate_code", side_effect=_fake_regenerate):
        report = run_drift("refund_payment", tmp_path, runs=1, dry_run=False)

    assert code.read_bytes() == original
    assert report.status == "stable"
    assert report.public_api_unchanged
    assert len(report.snapshots) == 1
    assert report.snapshots[0].tests_passed


def test_drift_applies_default_max_cost_for_non_dry_run(tmp_path: Path) -> None:
    _write_fixture(tmp_path)

    with patch("pdd.drift_main._regenerate_code", return_value=0.0):
        with patch("pdd.drift_main._evaluate_candidate") as mock_eval:
            mock_eval.return_value = (
                RunSnapshot(1, "a", ["def refund_payment"], True, True, True, True),
                0.0,
            )
            report = run_drift("refund_payment", tmp_path, runs=1, dry_run=False)

    assert report.max_cost_usd == DEFAULT_MAX_COST_USD


def test_drift_policy_fails_closed_when_gate_unavailable(tmp_path: Path) -> None:
    _prompt, code = _write_fixture(tmp_path)
    stable_source = code.read_text(encoding="utf-8")
    (tmp_path / ".pdd").mkdir(parents=True)
    (tmp_path / ".pdd" / "policy.yml").write_text("rules: []\n", encoding="utf-8")

    def _fake_regenerate(_prompt_path: Path, output_path: Path, **kwargs) -> float:
        output_path.parent.mkdir(parents=True, exist_ok=True)
        output_path.write_text(stable_source, encoding="utf-8")
        return 0.0

    with patch("pdd.drift_main._GATE_POLICY_AVAILABLE", False):
        with patch("pdd.drift_main._regenerate_code", side_effect=_fake_regenerate):
            report = run_drift("refund_payment", tmp_path, runs=1, dry_run=False)

    assert report.policy_check_unavailable
    assert not report.policy_check_skipped
    assert report.status == "unstable"
    assert not report.behavior_unchanged
    assert report.snapshots[0].policy_passed is False


def test_public_api_detects_renamed_symbol(tmp_path: Path) -> None:
    path = tmp_path / "mod.py"
    path.write_text("def refund_payment() -> None:\n    pass\n", encoding="utf-8")
    assert _public_api(path) == ["def refund_payment"]
    path.write_text("class RefundService:\n    pass\n", encoding="utf-8")
    assert _public_api(path) == ["class RefundService"]
