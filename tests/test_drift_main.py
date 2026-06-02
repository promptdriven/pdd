"""Tests for ``pdd checkup drift`` regeneration stability."""
from __future__ import annotations

import json
from pathlib import Path
from unittest.mock import patch

import pytest

from pdd.drift_main import (
    DEFAULT_MAX_COST_USD,
    RunSnapshot,
    _build_pytest_overlay,
    _public_api,
    _run_pytest_for_candidate,
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


def _write_pytest_package_fixture(project: Path) -> tuple[Path, Path]:
    """Project with ``pdd`` package, module, and a test that imports it."""
    prompt, code = _write_fixture(project)
    init_py = code.parent / "__init__.py"
    if not init_py.is_file():
        init_py.write_text("", encoding="utf-8")
    test_file = project / "tests" / "test_refund_payment.py"
    test_file.parent.mkdir(parents=True, exist_ok=True)
    test_file.write_text(
        "from pdd.refund_payment import refund_payment\n\n"
        "def test_refund_payment_returns_input() -> None:\n"
        "    assert refund_payment(5) == 5\n",
        encoding="utf-8",
    )
    return prompt, code


def _write_pytest_local_import_fixture(project: Path) -> tuple[Path, Path]:
    """Project where the module under test imports another local package module."""
    prompt, code = _write_pytest_package_fixture(project)
    helper = project / "pdd" / "helper.py"
    helper.write_text(
        "def adjust(amount: int) -> int:\n    return amount + 1\n",
        encoding="utf-8",
    )
    code.write_text(
        "from pdd.helper import adjust\n\n"
        "def refund_payment(amount: int) -> int:\n    return adjust(amount)\n",
        encoding="utf-8",
    )
    test_file = project / "tests" / "test_refund_payment.py"
    test_file.write_text(
        "from pdd.refund_payment import refund_payment\n\n"
        "def test_refund_payment_uses_helper() -> None:\n"
        "    assert refund_payment(5) == 6\n",
        encoding="utf-8",
    )
    return prompt, code


def test_build_pytest_overlay_copies_conftest_and_fixtures(tmp_path: Path) -> None:
    """``conftest.py`` and fixtures must be present in the overlay for pytest."""
    _write_pytest_package_fixture(tmp_path)
    conftest = tmp_path / "tests" / "conftest.py"
    conftest.write_text(
        "import pytest\n\n@pytest.fixture\ndef multiplier() -> int:\n    return 2\n",
        encoding="utf-8",
    )
    test_file = tmp_path / "tests" / "test_refund_payment.py"
    test_file.write_text(
        "from pdd.refund_payment import refund_payment\n\n"
        "def test_refund_payment_uses_conftest(multiplier: int) -> None:\n"
        "    assert refund_payment(3) == 3 * multiplier\n",
        encoding="utf-8",
    )
    code = tmp_path / "pdd" / "refund_payment.py"
    code.write_text(
        "def refund_payment(amount: int) -> int:\n    return amount * 2\n",
        encoding="utf-8",
    )
    candidate = tmp_path / "candidate.py"
    candidate.write_text(code.read_text(encoding="utf-8"), encoding="utf-8")
    overlay = tmp_path / "overlay"
    overlay.mkdir()

    overlay_tests = _build_pytest_overlay(candidate, code, tmp_path, overlay)
    assert overlay_tests is not None
    overlay_conftest = overlay / "tests" / "conftest.py"
    assert overlay_conftest.is_file()
    assert "multiplier" in overlay_conftest.read_text(encoding="utf-8")

    sandbox = tmp_path / "sandbox"
    sandbox.mkdir()
    assert _run_pytest_for_candidate(candidate, code, tmp_path, sandbox) is True


def _write_src_cross_package_fixture(project: Path) -> Path:
    """``src/pkg_b`` module importing a sibling package under ``src/pkg_a``."""
    for package in ("pkg_a", "pkg_b"):
        init_py = project / "src" / package / "__init__.py"
        init_py.parent.mkdir(parents=True, exist_ok=True)
        init_py.write_text("", encoding="utf-8")
    (project / "src" / "pkg_a" / "helper.py").write_text(
        "def adjust(amount: int) -> int:\n    return amount + 1\n",
        encoding="utf-8",
    )
    code = project / "src" / "pkg_b" / "refund_payment.py"
    code.write_text(
        "from pkg_a.helper import adjust\n\n"
        "def refund_payment(amount: int) -> int:\n    return adjust(amount)\n",
        encoding="utf-8",
    )
    test_file = project / "tests" / "test_refund_payment.py"
    test_file.parent.mkdir(parents=True, exist_ok=True)
    test_file.write_text(
        "from pkg_b.refund_payment import refund_payment\n\n"
        "def test_refund_payment_cross_package() -> None:\n"
        "    assert refund_payment(5) == 6\n",
        encoding="utf-8",
    )
    return code


def test_pytest_for_candidate_supports_cross_package_src_imports(tmp_path: Path) -> None:
    """Copy the full ``src/`` tree so siblings like ``pkg_a`` are importable from ``pkg_b``."""
    code = _write_src_cross_package_fixture(tmp_path)
    sandbox = tmp_path / "sandbox"
    sandbox.mkdir()
    candidate = tmp_path / "candidate.py"
    candidate.write_text(code.read_text(encoding="utf-8"), encoding="utf-8")

    assert _run_pytest_for_candidate(candidate, code, tmp_path, sandbox) is True


def test_pytest_for_candidate_supports_local_package_imports(tmp_path: Path) -> None:
    """Stable candidates that import sibling project modules must still pass pytest."""
    _write_pytest_local_import_fixture(tmp_path)
    code = tmp_path / "pdd" / "refund_payment.py"
    sandbox = tmp_path / "sandbox"
    sandbox.mkdir()

    stable_candidate = tmp_path / "stable_candidate.py"
    stable_candidate.write_text(code.read_text(encoding="utf-8"), encoding="utf-8")

    assert _run_pytest_for_candidate(stable_candidate, code, tmp_path, sandbox) is True


def test_pytest_for_candidate_exercises_candidate_not_baseline(tmp_path: Path) -> None:
    """Broken candidate must fail even when baseline module on disk still passes."""
    _write_pytest_package_fixture(tmp_path)
    code = tmp_path / "pdd" / "refund_payment.py"
    sandbox = tmp_path / "sandbox"
    sandbox.mkdir()

    good_candidate = tmp_path / "good_candidate.py"
    good_candidate.write_text(
        "def refund_payment(amount: int) -> int:\n    return amount\n",
        encoding="utf-8",
    )
    bad_candidate = tmp_path / "bad_candidate.py"
    bad_candidate.write_text(
        "def refund_payment(amount: int) -> int:\n    return 0\n",
        encoding="utf-8",
    )

    assert _run_pytest_for_candidate(good_candidate, code, tmp_path, sandbox) is True
    assert _run_pytest_for_candidate(bad_candidate, code, tmp_path, sandbox) is False

    code.write_text(
        "def refund_payment(amount: int) -> int:\n    return 0\n",
        encoding="utf-8",
    )
    sandbox_b = tmp_path / "sandbox_b"
    sandbox_b.mkdir()
    assert _run_pytest_for_candidate(good_candidate, code, tmp_path, sandbox_b) is True


def test_drift_passes_from_evidence_without_policy_gate(tmp_path: Path) -> None:
    """Ordinary evidence manifests must not imply policy when gate is absent on main."""
    prompt, code = _write_fixture(tmp_path)
    manifest = tmp_path / ".pdd" / "evidence" / "devunits" / "refund_payment.latest.json"
    manifest.parent.mkdir(parents=True)
    manifest.write_text(
        json.dumps(
            {
                "schema_version": 1,
                "prompt": {"path": str(prompt.relative_to(tmp_path))},
                "outputs": [{"path": str(code.relative_to(tmp_path)), "sha256": sha256_file(code)}],
                "validation": {
                    "detect_stories": "not_available",
                    "verify": "not_available",
                    "unit_tests": "not_available",
                },
            },
            indent=2,
        )
        + "\n",
        encoding="utf-8",
    )

    with patch("pdd.drift_main._POLICY_CHECK_AVAILABLE", False):
        report = run_drift(
            "refund_payment",
            tmp_path,
            runs=1,
            dry_run=True,
            from_evidence=manifest,
        )

    assert report.policy_check_skipped
    assert not report.policy_check_unavailable
    assert report.status == "stable"


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


def test_drift_policy_fails_closed_when_capability_check_unavailable(tmp_path: Path) -> None:
    """Capabilities in the prompt require policy_check; missing module fails closed."""
    _prompt, code = _write_fixture(tmp_path)
    _prompt.write_text(
        _prompt.read_text(encoding="utf-8")
        + "\n<capabilities>\n- MAY write refund records.\n</capabilities>\n",
        encoding="utf-8",
    )
    stable_source = code.read_text(encoding="utf-8")

    def _fake_regenerate(_prompt_path: Path, output_path: Path, **kwargs) -> float:
        output_path.parent.mkdir(parents=True, exist_ok=True)
        output_path.write_text(stable_source, encoding="utf-8")
        return 0.0

    with patch("pdd.drift_main._POLICY_CHECK_AVAILABLE", False):
        with patch("pdd.drift_main._regenerate_code", side_effect=_fake_regenerate):
            report = run_drift("refund_payment", tmp_path, runs=1, dry_run=False)

    assert report.policy_check_unavailable
    assert not report.policy_check_skipped
    assert report.status == "unstable"
    assert not report.behavior_unchanged
    assert report.snapshots[0].policy_passed is False


def test_drift_evidence_gate_fails_closed_when_gate_unavailable(tmp_path: Path) -> None:
    """``.pdd/policy.yml`` requires checkup gate; missing gate module fails closed."""
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
