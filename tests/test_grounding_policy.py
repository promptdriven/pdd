"""Tests for grounding policy evaluation."""
from __future__ import annotations

from pathlib import Path

import pytest

from pdd.grounding_policy import GroundingPolicy, check, load_policy


def test_load_policy_missing_file_returns_defaults(tmp_path: Path) -> None:
  policy = load_policy(str(tmp_path / "missing.yaml"))
  assert policy.require_review_for_critical_modules is False
  assert policy.require_pinned_examples_for == []


def test_load_policy_prefers_project_dot_pdd(tmp_path: Path, monkeypatch: pytest.MonkeyPatch) -> None:
    monkeypatch.chdir(tmp_path)
    monkeypatch.setenv("PDD_PATH", str(tmp_path / "package"))
    policy_file = tmp_path / ".pdd" / "grounding_policy.yaml"
    policy_file.parent.mkdir(parents=True)
    policy_file.write_text(
        "grounding:\n  require_pinned_examples_for:\n    - auth\n",
        encoding="utf-8",
    )
    policy = load_policy()
    assert policy.require_pinned_examples_for == ["auth"]


def test_load_policy_parses_yaml(tmp_path: Path, monkeypatch: pytest.MonkeyPatch) -> None:
    monkeypatch.chdir(tmp_path)
    policy_file = tmp_path / ".pdd" / "grounding_policy.yaml"
    policy_file.parent.mkdir(parents=True)
    policy_file.write_text(
        """
grounding:
  require_review_for_critical_modules: true
  require_pinned_examples_for:
    - auth
    - payments
""",
        encoding="utf-8",
    )
    policy = load_policy(str(policy_file))
    assert policy.require_review_for_critical_modules is True
    assert policy.require_pinned_examples_for == ["auth", "payments"]


def test_check_review_required_violation() -> None:
  policy = GroundingPolicy(
      require_review_for_critical_modules=True,
      require_pinned_examples_for=["payments"],
  )
  violations = check(
      policy,
      "payments",
      {"mode": "cloud", "pinned": ["payments"], "reviewed": False},
  )
  codes = {item.code for item in violations}
  assert "grounding.review_required" in codes


def test_check_pin_required_violation() -> None:
  policy = GroundingPolicy(require_pinned_examples_for=["auth"])
  violations = check(policy, "auth", {"mode": "cloud", "pinned": [], "reviewed": True})
  assert any(item.code == "grounding.pin_required" for item in violations)


def test_check_unavailable_warning_for_critical_module() -> None:
  policy = GroundingPolicy(require_pinned_examples_for=["compliance"])
  violations = check(policy, "compliance", {"mode": "unavailable", "pinned": [], "reviewed": False})
  warning = next(v for v in violations if v.code == "grounding.unavailable_for_critical_module")
  assert warning.severity == "warning"


def test_check_non_critical_module_is_clean() -> None:
  policy = GroundingPolicy(require_pinned_examples_for=["auth"])
  assert check(policy, "refund", {"mode": "unavailable"}) == []
