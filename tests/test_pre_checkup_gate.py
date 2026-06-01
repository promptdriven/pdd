from __future__ import annotations

from pathlib import Path
from types import SimpleNamespace

from pdd import pre_checkup_gate


def test_run_pre_checkup_gate_runs_drift_before_build(monkeypatch, tmp_path):
    order = []

    def fake_drift(*_args, **_kwargs):
        order.append("drift")
        return pre_checkup_gate._CheckOutcome(True, ["drift ok"], 0.25)

    def fake_build(*_args, **_kwargs):
        order.append("build")
        return pre_checkup_gate._CheckOutcome(True, ["build ok"], 0.0)

    monkeypatch.setattr(pre_checkup_gate, "_run_drift_sync", fake_drift)
    monkeypatch.setattr(pre_checkup_gate, "_run_build_smoke", fake_build)

    passed, message, cost = pre_checkup_gate.run_pre_checkup_gate(
        tmp_path,
        ["pdd/example.py"],
        quiet=True,
    )

    assert passed is True
    assert order == ["drift", "build"]
    assert "drift ok" in message
    assert "build ok" in message
    assert cost == 0.25


def test_docs_only_diff_skips_build_smoke(monkeypatch, tmp_path):
    called = False

    def fake_discover(*_args, **_kwargs):
        nonlocal called
        called = True
        return []

    monkeypatch.setattr(pre_checkup_gate, "discover_gates", fake_discover)

    outcome = pre_checkup_gate._run_build_smoke(
        tmp_path,
        ["README.md", "docs/usage.rst"],
        base_ref=None,
        issue_number=1293,
        timeout_per_check=1.0,
    )

    assert outcome.ok is True
    assert "skipped" in outcome.messages[0]
    assert called is False


def test_metadata_sync_failure_hard_blocks(monkeypatch, tmp_path):
    prompt_dir = tmp_path / "pdd" / "prompts"
    prompt_dir.mkdir(parents=True)
    prompt_path = prompt_dir / "foo_python.prompt"
    prompt_path.write_text("<pdd-reason>x</pdd-reason>\n", encoding="utf-8")
    code_path = tmp_path / "pdd" / "foo.py"
    code_path.parent.mkdir(exist_ok=True)
    code_path.write_text("def foo():\n    return 1\n", encoding="utf-8")
    (tmp_path / "architecture.json").write_text(
        '[{"filename":"foo_python.prompt","filepath":"pdd/foo.py"}]',
        encoding="utf-8",
    )

    monkeypatch.setattr(
        pre_checkup_gate,
        "sync_all_prompts_to_architecture",
        lambda **_kwargs: {"success": True},
    )
    monkeypatch.setattr(
        pre_checkup_gate,
        "run_metadata_sync",
        lambda *_args, **_kwargs: SimpleNamespace(ok=False, failing_stage="fingerprint"),
    )
    monkeypatch.setattr(pre_checkup_gate, "detect_drift", lambda **_kwargs: ([], []))

    outcome = pre_checkup_gate._run_drift_sync(
        tmp_path,
        ["pdd/prompts/foo_python.prompt"],
        base_ref=None,
        strict=False,
    )

    assert outcome.ok is False
    assert "metadata-sync failed" in " ".join(outcome.messages)
    assert "fingerprint" in " ".join(outcome.messages)


def test_residual_non_update_drift_warns_by_default_and_blocks_strict(monkeypatch, tmp_path):
    prompt_dir = tmp_path / "pdd" / "prompts"
    prompt_dir.mkdir(parents=True)
    prompt_path = prompt_dir / "foo_python.prompt"
    prompt_path.write_text("<pdd-reason>x</pdd-reason>\n", encoding="utf-8")
    code_path = tmp_path / "pdd" / "foo.py"
    code_path.parent.mkdir(exist_ok=True)
    code_path.write_text("def foo():\n    return 1\n", encoding="utf-8")
    (tmp_path / "architecture.json").write_text(
        '[{"filename":"foo_python.prompt","filepath":"pdd/foo.py"}]',
        encoding="utf-8",
    )
    drift = SimpleNamespace(basename="foo", operation="example", reason="example stale")

    monkeypatch.setattr(
        pre_checkup_gate,
        "sync_all_prompts_to_architecture",
        lambda **_kwargs: {"success": True},
    )
    monkeypatch.setattr(
        pre_checkup_gate,
        "run_metadata_sync",
        lambda *_args, **_kwargs: SimpleNamespace(ok=True, failing_stage=None),
    )
    monkeypatch.setattr(pre_checkup_gate, "detect_drift", lambda **_kwargs: ([], [drift]))

    default = pre_checkup_gate._run_drift_sync(
        tmp_path,
        ["pdd/prompts/foo_python.prompt"],
        base_ref=None,
        strict=False,
    )
    strict = pre_checkup_gate._run_drift_sync(
        tmp_path,
        ["pdd/prompts/foo_python.prompt"],
        base_ref=None,
        strict=True,
    )

    assert default.ok is True
    assert "residual non-update drift" in " ".join(default.messages)
    assert strict.ok is False
    assert "residual non-update drift" in " ".join(strict.messages)


def test_quarantined_targeted_tests_report_without_blocking(monkeypatch, tmp_path):
    tests_dir = tmp_path / "tests"
    tests_dir.mkdir()
    (tmp_path / "pdd").mkdir()
    (tmp_path / "pdd" / "foo.py").write_text("def foo():\n    return 1\n", encoding="utf-8")
    (tests_dir / "test_foo.py").write_text(
        "def test_known_flake():\n    assert False\n",
        encoding="utf-8",
    )
    monkeypatch.setenv(pre_checkup_gate._QUARANTINE_ENV, "tests/test_foo.py")

    failures, notes = pre_checkup_gate._run_targeted_tests(
        tmp_path,
        ["pdd/foo.py"],
        timeout=10.0,
    )

    assert failures == []
    assert "targeted-tests quarantine failed" in " ".join(notes)


def test_caller_compatibility_flags_invalid_keyword(tmp_path):
    pkg = tmp_path / "pkg"
    pkg.mkdir()
    (pkg / "__init__.py").write_text("", encoding="utf-8")
    (pkg / "api.py").write_text(
        "def build(name):\n    return name\n",
        encoding="utf-8",
    )
    (tmp_path / "consumer.py").write_text(
        "from pkg.api import build\n\nbuild(title='bad')\n",
        encoding="utf-8",
    )

    failures = pre_checkup_gate._check_caller_compatibility(
        tmp_path,
        ["pkg/api.py"],
    )

    assert failures
    assert "invalid keyword" in failures[0]
