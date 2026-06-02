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

    failures, _notes = pre_checkup_gate._check_caller_compatibility(
        tmp_path,
        ["pkg/api.py"],
    )

    assert failures
    assert "invalid keyword" in failures[0]


def _write_pkg_module(tmp_path: Path, name: str, body: str) -> None:
    pkg = tmp_path / "pkg"
    pkg.mkdir(exist_ok=True)
    (pkg / "__init__.py").write_text("", encoding="utf-8")
    (pkg / f"{name}.py").write_text(body, encoding="utf-8")


def test_caller_compat_allows_existing_nonfunction_imports(tmp_path):
    """Regression for #1293 FM3: importing existing private helpers, classes,
    and constants from a changed module must NOT be reported as missing.

    Before the fix, existence was checked against a public-functions-only list,
    so any caller importing a private helper/class/constant was falsely flagged
    (202 false positives on the PR's own orchestrators)."""
    _write_pkg_module(
        tmp_path,
        "api",
        "PUBLIC_CONST = 1\n"
        "def build(name):\n    return name\n"
        "def _private_helper():\n    return 2\n"
        "class Widget:\n    pass\n",
    )
    (tmp_path / "consumer.py").write_text(
        "from pkg.api import build, _private_helper, Widget, PUBLIC_CONST\n",
        encoding="utf-8",
    )

    failures, _notes = pre_checkup_gate._check_caller_compatibility(
        tmp_path,
        ["pkg/api.py"],
        timeout=30.0,
    )

    assert failures == [], failures


def test_caller_compat_flags_removed_symbol(tmp_path):
    """A caller importing a symbol the module does NOT export is still flagged
    (true positive — the half the check is meant to catch)."""
    _write_pkg_module(
        tmp_path,
        "api",
        "def build(name):\n    return name\n",
    )
    (tmp_path / "consumer.py").write_text(
        "from pkg.api import build, gone_symbol\n",
        encoding="utf-8",
    )

    failures, _notes = pre_checkup_gate._check_caller_compatibility(
        tmp_path,
        ["pkg/api.py"],
        timeout=30.0,
    )

    assert any("missing symbol gone_symbol" in f for f in failures), failures
    assert not any("missing symbol build" in f for f in failures), failures


def test_caller_compat_honors_dynamic_exports(tmp_path):
    """Existence uses the interpreter's real export set, so a name provided via
    module-level ``__getattr__`` (PEP 562) is NOT falsely reported missing —
    an AST-only reconstruction of top-level defs would miss it."""
    _write_pkg_module(
        tmp_path,
        "dyn",
        "def __getattr__(name):\n"
        "    if name == 'DYNAMIC':\n"
        "        return 42\n"
        "    raise AttributeError(name)\n",
    )
    (tmp_path / "consumer.py").write_text(
        "from pkg.dyn import DYNAMIC\n",
        encoding="utf-8",
    )

    failures, _notes = pre_checkup_gate._check_caller_compatibility(
        tmp_path,
        ["pkg/dyn.py"],
        timeout=30.0,
    )

    assert failures == [], failures


def test_caller_compat_skips_existence_when_module_unimportable(tmp_path):
    """If the changed module cannot be imported (already hard-blocked by the
    import check), the existence sweep must NOT treat every imported symbol as
    missing — it returns None and is skipped."""
    _write_pkg_module(
        tmp_path,
        "broken",
        "import this_module_does_not_exist_anywhere\n"
        "def build(name):\n    return name\n",
    )
    (tmp_path / "consumer.py").write_text(
        "from pkg.broken import build\n",
        encoding="utf-8",
    )

    failures, _notes = pre_checkup_gate._check_caller_compatibility(
        tmp_path,
        ["pkg/broken.py"],
        timeout=30.0,
    )

    assert not any("missing symbol" in f for f in failures), failures


def test_caller_compat_flags_alias_import_call(tmp_path):
    """Issue #1293 (FM3): an alias-style call with an invalid keyword —
    ``import pkg.api as api; api.build(title='bad')`` — must be flagged, not
    missed (the sweep previously handled only ``from x import f; f(...)``)."""
    _write_pkg_module(tmp_path, "api", "def build(name):\n    return name\n")
    (tmp_path / "consumer.py").write_text(
        "import pkg.api as api\n\napi.build(title='bad')\n", encoding="utf-8"
    )

    failures, _notes = pre_checkup_gate._check_caller_compatibility(
        tmp_path, ["pkg/api.py"], timeout=30.0
    )

    assert any("invalid keyword" in f for f in failures), failures


def test_caller_compat_alias_call_respects_shadowing(tmp_path):
    """Shadowing guard: a name that collides with an alias but is locally
    rebound (here a function parameter ``api``) must NOT be misattributed to the
    module — ast.walk ignores scope, so without the guard this would be a false
    positive that hard-blocks a good PR."""
    _write_pkg_module(tmp_path, "api", "def build(name):\n    return name\n")
    (tmp_path / "consumer.py").write_text(
        "def handler(api):\n    return api.build(1, 2, 3)\n", encoding="utf-8"
    )

    failures, _notes = pre_checkup_gate._check_caller_compatibility(
        tmp_path, ["pkg/api.py"], timeout=30.0
    )

    assert failures == [], failures


def test_build_smoke_passes_full_changed_set_to_discover_gates(monkeypatch, tmp_path):
    """Issue #1293 (security): discover_gates MUST receive the FULL changed set,
    not the code-only-stripped list. checkup_gates skips npm-family/build gates
    when the PR touches package.json / package-manager config (corepack +
    runner-redirect RCE guards); stripping those files here would hide them from
    the guards and let a fork PR run gates against PR-controlled config."""
    seen = {}

    def fake_discover(worktree, changed_files, *, base_ref=None):
        seen["changed_files"] = list(changed_files)
        return []

    monkeypatch.setattr(pre_checkup_gate, "discover_gates", fake_discover)
    monkeypatch.setattr(pre_checkup_gate, "run_gates", lambda *a, **k: [])
    monkeypatch.setattr(pre_checkup_gate, "_check_python_imports", lambda *a, **k: [])
    monkeypatch.setattr(pre_checkup_gate, "_check_route_probe", lambda *a, **k: [])
    monkeypatch.setattr(
        pre_checkup_gate, "_check_caller_compatibility", lambda *a, **k: ([], [])
    )
    monkeypatch.setattr(
        pre_checkup_gate, "_run_targeted_tests", lambda *a, **k: ([], [])
    )

    outcome = pre_checkup_gate._run_build_smoke(
        tmp_path,
        ["package.json", "pyproject.toml", "pdd/foo.py"],
        base_ref=None,
        issue_number=1293,
        timeout_per_check=5.0,
    )

    assert outcome.ok is True
    # The config files must reach discover_gates so its RCE-skip guards can fire.
    assert "package.json" in seen["changed_files"], seen
    assert "pyproject.toml" in seen["changed_files"], seen


def test_targeted_tests_select_directly_changed_test_file(tmp_path):
    """Issue #1293 (FM1): a PR that edits a test file directly must run that
    test. The stem-based matching only finds tests *of* a changed module, so a
    changed `tests/test_flow.py` was previously never selected and a failing
    edited test could pass the gate."""
    tests_dir = tmp_path / "tests"
    tests_dir.mkdir()
    (tests_dir / "test_flow.py").write_text(
        "def test_x():\n    assert True\n", encoding="utf-8"
    )

    candidates = pre_checkup_gate._targeted_test_candidates(
        tmp_path, ["tests/test_flow.py"]
    )

    assert "tests/test_flow.py" in candidates, candidates


def test_targeted_tests_failing_changed_test_blocks(tmp_path):
    """End-to-end: a directly-changed test that FAILS must make the gate's
    targeted-test phase fail (closing the FM1 hole at the run layer too)."""
    tests_dir = tmp_path / "tests"
    tests_dir.mkdir()
    (tests_dir / "test_flow.py").write_text(
        "def test_boom():\n    assert False\n", encoding="utf-8"
    )

    failures, _notes = pre_checkup_gate._run_targeted_tests(
        tmp_path, ["tests/test_flow.py"], timeout=60.0
    )

    assert any("targeted-tests failed" in f for f in failures), failures


def test_targeted_tests_note_for_changed_js_ts_test(tmp_path):
    """Issue #1293 (FM1 follow-on): a changed JS/TS test is not executed (the
    gate runs pytest), but it must be SURFACED as a note rather than silently
    skipped, so reviewers/checkup know it wasn't run."""
    (tmp_path / "tests").mkdir()

    failures, notes = pre_checkup_gate._run_targeted_tests(
        tmp_path, ["tests/foo.test.ts"], timeout=10.0
    )

    assert failures == []
    assert any("JS/TS test" in n and "foo.test.ts" in n for n in notes), notes


def test_python_import_env_drops_secrets_keeps_pythonpath(monkeypatch, tmp_path):
    """Issue #1293 (security): the gate executes worktree code, so its subprocess
    env must drop secret-bearing vars (LLM/cloud/VCS keys + tokens) while keeping
    the controlled PYTHONPATH=worktree the import/existence probes need."""
    monkeypatch.setenv("ANTHROPIC_API_KEY", "sk-should-be-dropped")
    monkeypatch.setenv("GITHUB_TOKEN", "ghp_should_be_dropped")
    monkeypatch.setenv("SOME_SECRET", "nope")
    monkeypatch.setenv("PDD_PATH", str(tmp_path))  # non-secret -> preserved

    env = pre_checkup_gate._python_import_env(tmp_path)

    assert "ANTHROPIC_API_KEY" not in env
    assert "GITHUB_TOKEN" not in env
    assert "SOME_SECRET" not in env
    assert env.get("PYTHONPATH") == str(tmp_path)
    assert env.get("PDD_PATH") == str(tmp_path)  # non-secret vars survive
    assert env.get("CI") == "1"


def test_targeted_tests_exclude_integration_marker_and_handle_no_tests(tmp_path):
    """Issue #1293 (security/perf): the gate must NOT run integration/e2e/real
    suites (could trigger real-LLM calls), and pytest exit 5 (no tests left after
    the marker filter) must be treated as a non-failure, not a hard block."""
    tests_dir = tmp_path / "tests"
    tests_dir.mkdir()
    # The ONLY test is integration-marked + would fail if run; after the marker
    # exclusion nothing is collected (exit 5) -> the gate must NOT fail.
    (tests_dir / "test_flow.py").write_text(
        "import pytest\n\n@pytest.mark.integration\ndef test_x():\n    assert False\n",
        encoding="utf-8",
    )

    failures, _notes = pre_checkup_gate._run_targeted_tests(
        tmp_path, ["tests/test_flow.py"], timeout=60.0
    )

    assert failures == [], failures
