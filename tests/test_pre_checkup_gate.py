from __future__ import annotations

import json
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


def test_drift_sync_does_not_rewrite_unrelated_architecture_entries(monkeypatch, tmp_path):
    """The gate's drift-sync must scope architecture.json to the touched prompt.

    Greg's blocker on PR #1327 (issue #1293): the Step 12.5 gate runs after the
    change orchestrator's ``_scope_architecture_to_changed_files()`` protection
    and before Step 13's ``git add -A``, so if drift-sync rewrote unrelated
    modules' architecture.json entries it would silently commit repo-wide drift
    into a feature PR (the fix path can commit the same via ``_commit_and_push``).

    This drives the REAL ``sync_all_prompts_to_architecture`` inside
    ``_run_drift_sync`` — only ``detect_drift`` is stubbed (to avoid invoking
    heal/LLM on a bare fixture) and ``run_metadata_sync`` is a no-op success — so
    it also proves the per-prompt metadata-sync step does not leak. The unrelated
    entry must be left untouched while the touched prompt actually syncs (a fix
    that simply skips everything would fail the second assertion).
    """
    prompt_dir = tmp_path / "pdd" / "prompts"
    prompt_dir.mkdir(parents=True)
    (tmp_path / "pdd" / "foo.py").write_text("def foo():\n    return 1\n", encoding="utf-8")
    (tmp_path / "pdd" / "bar.py").write_text("def bar():\n    return 2\n", encoding="utf-8")
    # Touched + unrelated prompt, each with a reason that DIFFERS from its stale
    # arch entry, so a full-scan sync would rewrite BOTH.
    (prompt_dir / "foo_python.prompt").write_text(
        "<pdd-reason>Fresh foo</pdd-reason>\n", encoding="utf-8"
    )
    (prompt_dir / "bar_python.prompt").write_text(
        "<pdd-reason>Fresh bar</pdd-reason>\n", encoding="utf-8"
    )
    arch_path = tmp_path / "architecture.json"
    arch_path.write_text(
        json.dumps(
            [
                {"filename": "foo_python.prompt", "filepath": "pdd/foo.py",
                 "reason": "Stale foo", "description": "DF", "dependencies": [],
                 "priority": 1, "tags": []},
                {"filename": "bar_python.prompt", "filepath": "pdd/bar.py",
                 "reason": "Stale bar", "description": "DB", "dependencies": [],
                 "priority": 2, "tags": []},
            ],
            indent=2,
        ),
        encoding="utf-8",
    )
    bar_before = {m["filename"]: m for m in json.loads(arch_path.read_text())}["bar_python.prompt"]

    # Metadata-sync a no-op success; skip heal/LLM. The leak under test lives in
    # architecture-sync, which runs for real here.
    monkeypatch.setattr(
        pre_checkup_gate,
        "run_metadata_sync",
        lambda *_a, **_k: SimpleNamespace(ok=True, failing_stage=None),
    )
    monkeypatch.setattr(pre_checkup_gate, "detect_drift", lambda **_k: ([], []))

    outcome = pre_checkup_gate._run_drift_sync(
        tmp_path,
        ["pdd/prompts/foo_python.prompt"],
        base_ref=None,
        strict=False,
    )

    synced = {m["filename"]: m for m in json.loads(arch_path.read_text())}
    # Unrelated entry untouched — compare the PARSED dict (re-serialization can
    # shift formatting even when values do not change, so byte comparison would
    # be brittle).
    assert synced["bar_python.prompt"] == bar_before
    assert synced["bar_python.prompt"]["reason"] == "Stale bar"
    # ...while the touched prompt actually synced from its prompt file.
    assert synced["foo_python.prompt"]["reason"] == "Fresh foo"
    assert outcome.ok is True


def test_drift_sync_uses_top_level_prompts_dir(monkeypatch, tmp_path):
    prompt_dir = tmp_path / "prompts"
    app_dir = tmp_path / "app"
    prompt_dir.mkdir()
    app_dir.mkdir()
    (app_dir / "async_helpers.py").write_text("def fetch_data():\n    return None\n", encoding="utf-8")
    (prompt_dir / "async_helpers_Python.prompt").write_text(
        "<pdd-reason>Fresh top-level prompt reason</pdd-reason>\n",
        encoding="utf-8",
    )
    arch_path = tmp_path / "architecture.json"
    arch_path.write_text(
        json.dumps(
            [
                {
                    "filename": "async_helpers_Python.prompt",
                    "filepath": "app/async_helpers.py",
                    "reason": "Stale reason",
                    "description": "Description",
                    "dependencies": [],
                    "priority": 1,
                    "tags": [],
                }
            ],
            indent=2,
        ),
        encoding="utf-8",
    )

    monkeypatch.setattr(
        pre_checkup_gate,
        "run_metadata_sync",
        lambda *_a, **_k: SimpleNamespace(ok=True, failing_stage=None),
    )
    monkeypatch.setattr(pre_checkup_gate, "detect_drift", lambda **_k: ([], []))

    outcome = pre_checkup_gate._run_drift_sync(
        tmp_path,
        ["app/async_helpers.py"],
        base_ref=None,
        strict=False,
    )

    synced = json.loads(arch_path.read_text(encoding="utf-8"))[0]
    assert synced["reason"] == "Fresh top-level prompt reason"
    assert outcome.ok is True
    assert "Prompt file not found" not in " ".join(outcome.messages)


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


def test_route_like_source_ignores_token_mentions_not_calls():
    """Regression: _route_like_source must use the AST (real router/app calls,
    @*.route decorators), NOT a raw substring scan. A file that merely MENTIONS
    the framework tokens in a string/comment — e.g. this gate module's own token
    list, or a test — must NOT be classified route-like, else the route-probe
    hard-blocks any PR touching it. Real constructors/decorators must still match."""
    # Tokens present only as string literals -> not route-like.
    mentions = (
        'TOKENS = ("APIRouter(", "FastAPI(", "@app.route", "Blueprint(")\n'
        '# documents APIRouter( usage\n'
    )
    assert pre_checkup_gate._route_like_source(mentions) is False
    # The gate module references those tokens itself; must not self-flag.
    own = Path(pre_checkup_gate.__file__).read_text(encoding="utf-8")
    assert pre_checkup_gate._route_like_source(own) is False
    # Real constructs still detected.
    assert pre_checkup_gate._route_like_source("from fastapi import APIRouter\nr = APIRouter()\n") is True
    assert pre_checkup_gate._route_like_source("app = FastAPI()\n") is True
    assert pre_checkup_gate._route_like_source("@app.route('/x')\ndef h():\n    pass\n") is True


def test_caller_compat_allows_star_unpack_calls(tmp_path):
    """Regression: a positional ``*args`` spread makes the static positional
    count meaningless, so arity checks must be skipped — ``render(*pair)`` and
    ``render(1, 2, *rest)`` are valid Python and must NOT be flagged. A genuine
    over-supply without a spread must still be caught (teeth preserved)."""
    _write_pkg_module(tmp_path, "api", "def render(a, b):\n    return a + b\n")
    (tmp_path / "consumer.py").write_text(
        "from pkg.api import render\n"
        "pair = (1, 2)\nrender(*pair)\n"
        "rest = [3]\nrender(1, 2, *rest)\n",
        encoding="utf-8",
    )
    failures, _notes = pre_checkup_gate._check_caller_compatibility(
        tmp_path, ["pkg/api.py"], timeout=30.0
    )
    assert failures == [], failures

    (tmp_path / "bad.py").write_text(
        "from pkg.api import render\nrender(1, 2, 3)\n", encoding="utf-8"
    )
    failures2, _ = pre_checkup_gate._check_caller_compatibility(
        tmp_path, ["pkg/api.py"], timeout=30.0
    )
    assert any("positional" in f for f in failures2), failures2


def test_non_utf8_file_does_not_fail_closed(tmp_path):
    """Regression: a non-UTF-8 .py anywhere in the worktree raises
    UnicodeDecodeError (a ValueError, NOT OSError). The caller-compat sweep reads
    every .py, so an unrelated non-UTF-8 file would escape to the top-level
    handler and fail the gate CLOSED on every PR. It must be skipped instead."""
    (tmp_path / "pkg").mkdir()
    (tmp_path / "pkg" / "__init__.py").write_text("", encoding="utf-8")
    (tmp_path / "pkg" / "api.py").write_text("def build(name):\n    return name\n", encoding="utf-8")
    (tmp_path / "latin.py").write_bytes(b"# coding: latin-1\nx = '\xe9'\n")

    passed, message, _cost = pre_checkup_gate.run_pre_checkup_gate(
        tmp_path, ["pkg/api.py"], quiet=True, timeout_per_check=30.0
    )
    assert passed is True, message
    assert "infrastructure error" not in message, message


def test_norm_preserves_leading_dot():
    """Regression: _norm must use removeprefix('./'), not lstrip('./') (which
    strips a CHARACTER SET). Leading dots in real names must survive, or the
    package-manager-config RCE skip-guard and the docs-only .github/ short
    circuit silently break."""
    assert pre_checkup_gate._norm(".npmrc") == ".npmrc"
    assert pre_checkup_gate._norm(".github/workflows/ci.yml") == ".github/workflows/ci.yml"
    assert pre_checkup_gate._norm(".pre-commit-config.yaml") == ".pre-commit-config.yaml"
    assert pre_checkup_gate._norm("./rel/x.py") == "rel/x.py"


def test_caller_compat_resolves_relative_imports(tmp_path):
    """Regression: relative imports (`from .api import x`) are the normal
    internal-import style here, so the caller-compat sweep MUST resolve them to
    the absolute dotted module — an absolute-only match silently missed every
    relative caller of a changed module (removed symbols AND bad call sigs)."""
    _write_pkg_module(tmp_path, "api", "def build(name):\n    return name\n")
    (tmp_path / "pkg" / "rel_consumer.py").write_text(
        "from .api import build, gone_symbol\nbuild(1, 2, 3)\n", encoding="utf-8"
    )
    failures, _notes = pre_checkup_gate._check_caller_compatibility(
        tmp_path, ["pkg/api.py"], timeout=30.0
    )
    assert any("missing symbol gone_symbol" in f for f in failures), failures
    assert any("positional" in f for f in failures), failures
    # A relative level that escapes the package must not raise / must no-op.
    assert pre_checkup_gate._resolve_from_import_module("pkg/api.py", "x", 5) is None


def test_route_probe_is_nonblocking_note(tmp_path):
    """Regression (FM2): the route-probe is a best-effort heuristic that does NOT
    reliably catch 'router never mounted' yet false-blocks valid non-FastAPI
    route modules. It MUST be surfaced as a non-blocking note, not a hard block —
    a route-like module with no introspectable routes must still pass build/smoke."""
    (tmp_path / "routes.py").write_text(
        "class _App:\n"
        "    def route(self, *a, **k):\n"
        "        def deco(fn):\n            return fn\n"
        "        return deco\n"
        "app = _App()\n"
        "@app.route('/y')\n"
        "def y():\n    return 'ok'\n",
        encoding="utf-8",
    )
    outcome = pre_checkup_gate._run_build_smoke(
        tmp_path, ["routes.py"], base_ref=None, issue_number=1, timeout_per_check=60.0
    )
    assert outcome.ok is True, outcome.messages
    assert any("route-probe note" in m for m in outcome.messages), outcome.messages


def test_touched_invalid_architecture_json_blocks(tmp_path):
    """Regression: _load_architecture swallows a parse error (returns []), so a PR
    that breaks architecture.json would silently no-op drift-sync and pass. When
    the PR itself touches architecture.json and it no longer parses, the gate MUST
    hard-block — but only then (absent / pre-existingly broken must not block)."""
    (tmp_path / "architecture.json").write_text("{ not: valid json ]", encoding="utf-8")
    passed, message, _cost = pre_checkup_gate.run_pre_checkup_gate(
        tmp_path, ["architecture.json"], quiet=True, timeout_per_check=30.0
    )
    assert passed is False, message
    assert "architecture.json" in message and "not valid JSON" in message, message

    # Valid architecture.json touched -> this check does not block.
    (tmp_path / "architecture.json").write_text("[]", encoding="utf-8")
    assert pre_checkup_gate._touched_architecture_json_error(
        tmp_path, ["architecture.json"]
    ) is None
    # Not touched by the PR -> never blocks, even if broken.
    (tmp_path / "architecture.json").write_text("{ broken ]", encoding="utf-8")
    assert pre_checkup_gate._touched_architecture_json_error(
        tmp_path, ["pdd/foo.py"]
    ) is None


def test_touched_wrong_shape_architecture_json_blocks(tmp_path):
    """Regression: valid JSON is not enough — a scalar (`"oops"`) or a dict
    without a `modules` list parses fine but yields an EMPTY module graph
    silently, so drift-sync runs against nothing and the gate passes vacuously.
    A touched arch.json of an unrecognized shape MUST block; legitimate empty
    shapes (`[]`, `{"modules": []}`) MUST NOT."""
    arch = tmp_path / "architecture.json"
    for bad in ['"oops"', "{}", "42", "true"]:
        arch.write_text(bad, encoding="utf-8")
        err = pre_checkup_gate._touched_architecture_json_error(
            tmp_path, ["architecture.json"]
        )
        assert err and "not a recognized architecture shape" in err, (bad, err)
    for ok in ["[]", '{"modules": []}', '[{"filename": "x"}]']:
        arch.write_text(ok, encoding="utf-8")
        assert pre_checkup_gate._touched_architecture_json_error(
            tmp_path, ["architecture.json"]
        ) is None, ok


def test_touched_malformed_architecture_entries_block_not_crash(tmp_path):
    """Regression: a recognized container with malformed ENTRIES must cleanly
    block, never crash. Empty-dict entries ([{}]) map nothing -> the gate would
    pass vacuously; a non-dict member (["oops"]) makes downstream entry.get(...)
    raise -> the gate crashes fail-closed with an opaque error. Both must become
    a deterministic 'malformed module entries' block."""
    arch = tmp_path / "architecture.json"
    for bad in ['[{}]', '{"modules": [{}]}', '["oops"]', '{"modules": ["oops"]}']:
        arch.write_text(bad, encoding="utf-8")
        err = pre_checkup_gate._touched_architecture_json_error(
            tmp_path, ["architecture.json"]
        )
        assert err and "malformed module entries" in err, (bad, err)
        passed, message, _cost = pre_checkup_gate.run_pre_checkup_gate(
            tmp_path, ["architecture.json"], quiet=True, timeout_per_check=20.0
        )
        assert passed is False and "infrastructure error" not in message, (bad, message)


def test_nondict_arch_entry_does_not_crash_untouched_path(tmp_path):
    """Defensive: a malformed architecture.json the PR did NOT touch must not
    crash the drift-sync entry walk (entry.get on a non-dict) and fail the gate
    closed for every PR — non-dict entries are skipped."""
    (tmp_path / "architecture.json").write_text(
        '["oops", {"filename": "y_python.prompt", "filepath": "pdd/y.py"}]',
        encoding="utf-8",
    )
    (tmp_path / "pdd").mkdir()
    (tmp_path / "pdd" / "foo.py").write_text("x = 1\n", encoding="utf-8")
    outcome = pre_checkup_gate._run_drift_sync(
        tmp_path, ["pdd/foo.py"], base_ref=None, strict=False
    )
    assert outcome.ok is True, outcome.messages


def test_gate_validates_heal_regenerated_code(monkeypatch, tmp_path):
    """Regression: drift-sync heal regenerates code; the gate MUST validate the
    tree it PRODUCED, not just the pre-heal PR diff. A prompt-only PR whose heal
    writes broken code must block (build/smoke runs on the regenerated file even
    though it was never in changed_files). NOTE: heal is faked here (it is a real
    LLM call); this closes the validate-our-own-output mechanism, not a sighting."""
    (tmp_path / "pdd" / "prompts").mkdir(parents=True)
    (tmp_path / "pdd" / "foo.py").write_text("def ok():\n    return 1\n", encoding="utf-8")
    (tmp_path / "pdd" / "prompts" / "foo_python.prompt").write_text(
        "<pdd-reason>x</pdd-reason>\n", encoding="utf-8"
    )
    (tmp_path / "architecture.json").write_text(
        '[{"filename":"foo_python.prompt","filepath":"pdd/foo.py"}]', encoding="utf-8"
    )
    drift = SimpleNamespace(
        basename="foo", operation="update", reason="r", language="python",
        code_path=str(tmp_path / "pdd" / "foo.py"),
    )

    def fake_heal(_d, _env):
        (tmp_path / "pdd" / "foo.py").write_text("def broken(:\n", encoding="utf-8")
        return True

    calls = {"n": 0}

    def fake_detect(**_k):
        calls["n"] += 1
        return ([drift], []) if calls["n"] == 1 else ([], [])

    monkeypatch.setattr(pre_checkup_gate, "sync_all_prompts_to_architecture", lambda **_k: {"success": True})
    monkeypatch.setattr(pre_checkup_gate, "run_metadata_sync", lambda *_a, **_k: SimpleNamespace(ok=True, failing_stage=None))
    monkeypatch.setattr(pre_checkup_gate, "detect_drift", fake_detect)
    monkeypatch.setattr(pre_checkup_gate, "heal_module", fake_heal)

    passed, message, _cost = pre_checkup_gate.run_pre_checkup_gate(
        tmp_path, ["pdd/prompts/foo_python.prompt"], quiet=True, timeout_per_check=30.0
    )
    assert passed is False, message
    assert "foo.py" in message, message
    assert "infrastructure error" not in message, message


def test_drift_sync_reports_only_real_mutations(monkeypatch, tmp_path):
    """The synced-paths feedback must NOT grow on an in-sync repo (heal fires only
    on update-drift). With no drift, the only synced path is architecture.json
    (whose shape check is a no-op on a valid file) — no spurious code files that
    would false-block on a clean tree."""
    (tmp_path / "pdd" / "prompts").mkdir(parents=True)
    (tmp_path / "pdd" / "foo.py").write_text("def ok():\n    return 1\n", encoding="utf-8")
    (tmp_path / "pdd" / "prompts" / "foo_python.prompt").write_text(
        "<pdd-reason>x</pdd-reason>\n", encoding="utf-8"
    )
    (tmp_path / "architecture.json").write_text(
        '[{"filename":"foo_python.prompt","filepath":"pdd/foo.py"}]', encoding="utf-8"
    )
    monkeypatch.setattr(pre_checkup_gate, "sync_all_prompts_to_architecture", lambda **_k: {"success": True})
    monkeypatch.setattr(pre_checkup_gate, "run_metadata_sync", lambda *_a, **_k: SimpleNamespace(ok=True, failing_stage=None))
    monkeypatch.setattr(pre_checkup_gate, "detect_drift", lambda **_k: ([], []))

    outcome = pre_checkup_gate._run_drift_sync(
        tmp_path, ["pdd/prompts/foo_python.prompt"], base_ref=None, strict=False
    )
    assert [p for p in outcome.synced_paths if p != "architecture.json"] == [], outcome.synced_paths


def _foo_prompt_repo(tmp_path, arch="[{\"filename\":\"foo_python.prompt\",\"filepath\":\"pdd/foo.py\"}]"):
    (tmp_path / "pdd" / "prompts").mkdir(parents=True)
    (tmp_path / "pdd" / "foo.py").write_text("def ok():\n    return 1\n", encoding="utf-8")
    (tmp_path / "pdd" / "prompts" / "foo_python.prompt").write_text(
        "<pdd-reason>x</pdd-reason>\n", encoding="utf-8"
    )
    (tmp_path / "architecture.json").write_text(arch, encoding="utf-8")


def test_pre_existing_broken_arch_untouched_does_not_false_block(monkeypatch, tmp_path):
    """Regression (round-7): adding architecture.json to the validated set
    unconditionally when sync ran false-blocked a prompt-only PR on a PRE-EXISTING
    broken architecture.json the PR never touched and sync left unchanged. It must
    be revalidated ONLY when sync actually rewrote it."""
    _foo_prompt_repo(tmp_path, arch='{"oops": 1}')  # pre-existing broken, PR doesn't touch it
    monkeypatch.setattr(pre_checkup_gate, "sync_all_prompts_to_architecture", lambda **_k: {"success": True})
    monkeypatch.setattr(pre_checkup_gate, "run_metadata_sync", lambda *_a, **_k: SimpleNamespace(ok=True, failing_stage=None))
    monkeypatch.setattr(pre_checkup_gate, "detect_drift", lambda **_k: ([], []))
    passed, message, _ = pre_checkup_gate.run_pre_checkup_gate(
        tmp_path, ["pdd/prompts/foo_python.prompt"], quiet=True, timeout_per_check=20.0
    )
    assert passed is True, message


def test_sync_that_writes_broken_arch_is_caught(monkeypatch, tmp_path):
    """But a sync that itself REWRITES architecture.json into a broken state is
    still caught (the content changed, so it is revalidated)."""
    _foo_prompt_repo(tmp_path)  # valid before sync

    def corrupt_sync(**_k):
        (tmp_path / "architecture.json").write_text('{"modules": ["oops"]}', encoding="utf-8")
        return {"success": True}

    monkeypatch.setattr(pre_checkup_gate, "sync_all_prompts_to_architecture", corrupt_sync)
    monkeypatch.setattr(pre_checkup_gate, "run_metadata_sync", lambda *_a, **_k: SimpleNamespace(ok=True, failing_stage=None))
    monkeypatch.setattr(pre_checkup_gate, "detect_drift", lambda **_k: ([], []))
    passed, message, _ = pre_checkup_gate.run_pre_checkup_gate(
        tmp_path, ["pdd/prompts/foo_python.prompt"], quiet=True, timeout_per_check=20.0
    )
    assert passed is False, message
    assert "infrastructure error" not in message, message


def test_gate_validates_heal_regenerated_example(monkeypatch, tmp_path):
    """Regression (round-7): the produced-tree validation tracked only regenerated
    code; a heal that rewrites a broken EXAMPLE must be caught too. Tracked by
    content change of the module's example_path."""
    _foo_prompt_repo(tmp_path)
    (tmp_path / "context").mkdir()
    (tmp_path / "context" / "foo_example.py").write_text("print('ok')\n", encoding="utf-8")
    drift = SimpleNamespace(
        basename="foo", operation="update", reason="r", language="python",
        code_path=str(tmp_path / "pdd" / "foo.py"),
        example_path=str(tmp_path / "context" / "foo_example.py"),
    )

    def heal_breaks_example(_d, _e):
        (tmp_path / "context" / "foo_example.py").write_text("def broken(:\n", encoding="utf-8")
        return True

    calls = {"n": 0}

    def fake_detect(**_k):
        calls["n"] += 1
        return ([drift], []) if calls["n"] == 1 else ([], [])

    monkeypatch.setattr(pre_checkup_gate, "sync_all_prompts_to_architecture", lambda **_k: {"success": True})
    monkeypatch.setattr(pre_checkup_gate, "run_metadata_sync", lambda *_a, **_k: SimpleNamespace(ok=True, failing_stage=None))
    monkeypatch.setattr(pre_checkup_gate, "detect_drift", fake_detect)
    monkeypatch.setattr(pre_checkup_gate, "heal_module", heal_breaks_example)
    passed, message, _ = pre_checkup_gate.run_pre_checkup_gate(
        tmp_path, ["pdd/prompts/foo_python.prompt"], quiet=True, timeout_per_check=30.0
    )
    assert passed is False, message
    assert "foo_example.py" in message, message


def test_gate_validates_heal_CREATED_example_when_example_path_unset(monkeypatch, tmp_path):
    """Regression (round-8): an update-heal runs a follow-up `pdd example` that may
    CREATE the example when example_path started None — so its path is absent from
    the pre-heal drift. The gate must derive the canonical example path (PDD's own
    resolver) and validate it, or a broken created example slips through. Heal here
    writes the broken example to exactly where the resolver points (as real heal
    does), so the gate's derived path matches."""
    import os
    from pdd.sync_determine_operation import get_pdd_file_paths

    _foo_prompt_repo(tmp_path)
    cwd = os.getcwd()
    os.chdir(tmp_path)
    try:
        ex_path = get_pdd_file_paths("foo", "python", prompts_dir="pdd/prompts").get("example")
    finally:
        os.chdir(cwd)
    assert ex_path, "resolver returned no example path"
    drift = SimpleNamespace(
        basename="foo", operation="update", reason="r", language="python",
        code_path=str(tmp_path / "pdd" / "foo.py"), example_path=None,  # unset pre-heal
    )

    def heal_creates_broken_example(_d, _e):
        exp = pathlib.Path(ex_path)
        exp.parent.mkdir(parents=True, exist_ok=True)
        exp.write_text("def broken(:\n", encoding="utf-8")
        return True

    calls = {"n": 0}

    def fake_detect(**_k):
        calls["n"] += 1
        return ([drift], []) if calls["n"] == 1 else ([], [])

    monkeypatch.setattr(pre_checkup_gate, "sync_all_prompts_to_architecture", lambda **_k: {"success": True})
    monkeypatch.setattr(pre_checkup_gate, "run_metadata_sync", lambda *_a, **_k: SimpleNamespace(ok=True, failing_stage=None))
    monkeypatch.setattr(pre_checkup_gate, "detect_drift", fake_detect)
    monkeypatch.setattr(pre_checkup_gate, "heal_module", heal_creates_broken_example)
    passed, message, _ = pre_checkup_gate.run_pre_checkup_gate(
        tmp_path, ["pdd/prompts/foo_python.prompt"], quiet=True, timeout_per_check=30.0
    )
    assert passed is False, message
    assert "infrastructure error" not in message, message


def test_touched_nonstring_entry_metadata_blocks(tmp_path):
    """Regression (round-7): a touched architecture.json whose entry filename/
    filepath is a truthy NON-string ([{"filename": 1}]) must block — `1` is
    truthy but `_norm(str(1))` maps nothing, a vacuous pass under the prior
    truthy-only check. (Structural terminus: the gate does NOT check the files
    referenced exist — that is architecture_sync's job.)"""
    arch = tmp_path / "architecture.json"
    for bad in ['[{"filename": 1}]', '{"modules":[{"filepath": 1}]}']:
        arch.write_text(bad, encoding="utf-8")
        err = pre_checkup_gate._touched_architecture_json_error(tmp_path, ["architecture.json"])
        assert err and "malformed module entries" in err, (bad, err)


def test_caller_compat_resolves_from_dot_import_submodule(tmp_path):
    """Regression: `from . import api; api.build(...)` (and `from . import api as a`)
    binds the SUBMODULE, so the call is a module.attr call. The sweep must resolve
    it like `import pkg.api as api`, not miss it. (Last static caller-compat form
    resolved; dynamic/getattr/star re-exports stay with checkup.)"""
    _write_pkg_module(tmp_path, "api", "def build(name):\n    return name\n")
    (tmp_path / "pkg" / "consumer.py").write_text(
        "from . import api\napi.build(1, 2, 3)\n"
        "from . import api as a2\na2.build(title='bad')\n",
        encoding="utf-8",
    )
    failures, _notes = pre_checkup_gate._check_caller_compatibility(
        tmp_path, ["pkg/api.py"], timeout=30.0
    )
    assert any("positional" in f for f in failures), failures
    assert any("invalid keyword" in f for f in failures), failures


def test_python_import_env_drops_secrets_keeps_pythonpath(monkeypatch, tmp_path):
    """Issue #1293 (security): the gate imports + pytest-runs untrusted PR code,
    so its subprocess env is built by ALLOWLIST — credential surfaces are dropped
    while the controlled PYTHONPATH=worktree / PDD_PATH the probes need survive.
    The allowlist is security-over-convenience: non-secret config a target repo
    might read at import time (DATABASE_URL, DJANGO_SECRET_KEY) is dropped too."""
    monkeypatch.setenv("ANTHROPIC_API_KEY", "sk-should-be-dropped")  # provider key
    monkeypatch.setenv("GITHUB_TOKEN", "ghp_should_be_dropped")  # VCS token
    monkeypatch.setenv("MYPROVIDER_API_KEY", "drop-me")  # generic *_API_KEY
    monkeypatch.setenv("DJANGO_SECRET_KEY", "drop-me")  # *_SECRET_KEY -> dropped
    monkeypatch.setenv("DATABASE_URL", "drop-me")  # credential surface -> dropped
    monkeypatch.setenv("PDD_PATH", str(tmp_path))  # allowlisted -> preserved
    monkeypatch.setenv("LANG", "C.UTF-8")  # allowlisted non-secret runtime var

    env = pre_checkup_gate._python_import_env(tmp_path)

    # credential surfaces dropped
    for k in (
        "ANTHROPIC_API_KEY", "GITHUB_TOKEN", "MYPROVIDER_API_KEY",
        "DJANGO_SECRET_KEY", "DATABASE_URL",
    ):
        assert k not in env, f"{k} should be stripped by the allowlist"
    # controlled + allowlisted vars survive
    assert env.get("PYTHONPATH") == str(tmp_path)
    assert env.get("PDD_PATH") == str(tmp_path)
    assert env.get("LANG") == "C.UTF-8"
    assert env.get("CI") == "1"  # forced for the subprocess regardless of ambient CI


def test_scrub_redacts_secrets_without_secret_named_source():
    """Issue #1293 (CodeQL FP fix): `_scrub` applies the loop's compiled secret
    patterns directly instead of calling `checkup_review_loop._scrub_secrets`
    (CodeQL mis-models any call to a `*secret*`-named function as a SECRET SOURCE,
    which propagated through the gate message into the orchestrators' returns and
    the example scripts' prints — 34 false positives). This test guards that the
    refactor did NOT weaken redaction: secrets must still be redacted, and the
    output must be byte-identical to the old `_scrub_secrets` + local-regex path."""
    from pdd.checkup_review_loop import _scrub_secrets

    # Token-shaped inputs assembled at runtime so no contiguous secret literal
    # sits in this source file (GitHub push-protection / secret-scanning would
    # otherwise block this test). Equivalence below holds for any input.
    body = "A1b2C3d4E5f6G7h8I9j0KLMN"  # 24 chars, satisfies the {20,} patterns
    sk = "s" "k-" + body
    ghp = "gh" "p_" + body
    xox = "xo" "xb-" + "0123456789" + body
    gh_tok = "GITHUB_" "TOKEN=" + ghp
    pem = "-----BEGIN " "RSA PRIVATE KEY" "-----\nABCDEF\n-----END " "RSA PRIVATE KEY" "-----"
    url = "https://user:" "pa55word" "@example.com/repo.git"
    battery = [
        "Authorization: Bearer " + sk,
        "token " + sk,
        ghp,
        xox,
        gh_tok,
        url,
        pem,
        "normal status: build-smoke failed for foo.py exit=1",
        "",
    ]

    def old_path(text):
        value = "" if text is None else str(text)
        value = _scrub_secrets(value)
        return pre_checkup_gate._SECRET_RE.sub("[REDACTED]", value)

    for s in battery:
        assert pre_checkup_gate._scrub(s) == old_path(s), f"redaction drift for {s!r}"

    # Sanity: the obvious token forms are actually redacted (not passed through).
    for s in ("Authorization: Bearer " + sk, ghp, gh_tok):
        assert "[REDACTED]" in pre_checkup_gate._scrub(s)
    # Non-secret status text is untouched.
    assert pre_checkup_gate._scrub("build-smoke failed for foo.py") == "build-smoke failed for foo.py"


def test_python_import_env_strips_github_tokens_and_token_suffixes(monkeypatch, tmp_path):
    """Issue #1293 (security, code review): the denylist predecessor leaked the
    PDD GitHub-token envs and generic token-shaped vars into worktree subprocesses.
    Regression: every credential surface below must be absent; every PDD_* except
    PDD_PATH must be dropped."""
    leaky = {
        "PDD_GH_TOKEN_FILE": "/tmp/tok",          # checkup_review_loop._github_token_from_env
        "PDD_GITHUB_TOKEN": "ghp_leak",           # checkup_review_loop._github_token_from_env
        "SLACK_BOT_TOKEN": "xo" "xb-" "leak",      # generic *_TOKEN (split literal)
        "ACME_API_TOKEN": "leak",                 # generic *_API_TOKEN
        "ACME_SECRET_KEY": "leak",                # generic *_SECRET_KEY
        "PDD_CLOUD_API_KEY": "leak",              # PDD_* (not PDD_PATH)
        "PDD_TEST_BOT_TOKEN": "leak",             # PDD_* token
    }
    for k, v in leaky.items():
        monkeypatch.setenv(k, v)
    monkeypatch.setenv("PDD_PATH", str(tmp_path))  # the one PDD_* kept

    env = pre_checkup_gate._python_import_env(tmp_path)

    for k in leaky:
        assert k not in env, f"{k} must be stripped from the worktree subprocess env"
    # No PDD_* other than PDD_PATH survives.
    assert {k for k in env if k.startswith("PDD_")} == {"PDD_PATH"}
    assert env.get("PDD_PATH") == str(tmp_path)


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


# ---------------------------------------------------------------------------
# Issue #1614 — pre_checkup_gate drift-sync targets root architecture.json
# for prompts outside pdd/prompts
# ---------------------------------------------------------------------------

def _ext_prompt_repo(tmp_path, root_arch_content="[]"):
    """Foreign-prompts-dir fixture for issue #1614 tests.

    Creates:
    - extensions/github_pdd_app/prompts/ext_module_python.prompt  (fresh reason)
    - extensions/github_pdd_app/architecture.json                 (stale reason)
    - architecture.json (root, configurable via root_arch_content)

    Returns the Path to the foreign architecture.json.
    """
    ext_prompts_dir = tmp_path / "extensions" / "github_pdd_app" / "prompts"
    ext_prompts_dir.mkdir(parents=True)
    (ext_prompts_dir / "ext_module_python.prompt").write_text(
        "<pdd-reason>Fresh ext reason</pdd-reason>\n", encoding="utf-8"
    )
    ext_arch = tmp_path / "extensions" / "github_pdd_app" / "architecture.json"
    ext_arch.write_text(
        json.dumps(
            [
                {
                    "filename": "ext_module_python.prompt",
                    "filepath": "extensions/github_pdd_app/ext_module.py",
                    "reason": "Stale ext reason",
                    "description": "Ext module desc",
                    "dependencies": [],
                    "priority": 1,
                    "tags": [],
                }
            ],
            indent=2,
        ),
        encoding="utf-8",
    )
    (tmp_path / "architecture.json").write_text(root_arch_content, encoding="utf-8")
    return ext_arch


def test_drift_sync_foreign_prompt_dir_does_not_corrupt_root_architecture(monkeypatch, tmp_path):
    """Issue #1614 (failure mode 1): when a changed prompt resolves to a foreign
    prompts_dir (outside pdd/prompts), sync_all_prompts_to_architecture must be called
    with that directory's own architecture.json, NOT the repo-root one.

    Buggy behavior: architecture_path=worktree/"architecture.json" is passed for every
    group regardless of prompts_dir. register_untracked_prompts rglobs the foreign
    prompts_dir against the root arch, finds ext_module_python.prompt absent there, and
    registers a new module entry into the root architecture.json — corrupting it.

    This test drives the REAL sync_all_prompts_to_architecture (only run_metadata_sync
    and detect_drift are stubbed) to observe the actual file mutation.
    """
    ext_arch = _ext_prompt_repo(tmp_path, root_arch_content="[]")

    monkeypatch.setattr(
        pre_checkup_gate,
        "run_metadata_sync",
        lambda *_a, **_k: SimpleNamespace(ok=True, failing_stage=None),
    )
    monkeypatch.setattr(pre_checkup_gate, "detect_drift", lambda **_k: ([], []))

    outcome = pre_checkup_gate._run_drift_sync(
        tmp_path,
        ["extensions/github_pdd_app/prompts/ext_module_python.prompt"],
        base_ref=None,
        strict=False,
    )

    # Root arch must stay empty — the foreign prompt must NOT be registered here.
    root_arch_data = json.loads((tmp_path / "architecture.json").read_text())
    assert root_arch_data == [], (
        f"Root architecture.json was corrupted by the foreign-prompt sync: "
        f"expected [], got {root_arch_data}"
    )
    # Foreign arch must be updated with the fresh reason from the prompt file.
    ext_arch_data = json.loads(ext_arch.read_text())
    assert len(ext_arch_data) == 1
    assert ext_arch_data[0]["reason"] == "Fresh ext reason", ext_arch_data
    assert outcome.ok is True


def test_drift_sync_nested_prompt_dir_uses_nearest_ancestor_architecture(monkeypatch, tmp_path):
    """Issue #1614: the owning architecture.json can be more than one level
    above the prompts directory.

    Example: extensions/github_pdd_app/src/prompts is owned by
    extensions/github_pdd_app/architecture.json, not src/architecture.json and
    not the repo root architecture.json.
    """
    nested_prompts_dir = (
        tmp_path / "extensions" / "github_pdd_app" / "src" / "prompts"
    )
    nested_prompts_dir.mkdir(parents=True)
    (nested_prompts_dir / "ext_module_python.prompt").write_text(
        "<pdd-reason>Fresh nested reason</pdd-reason>\n", encoding="utf-8"
    )
    ext_arch = tmp_path / "extensions" / "github_pdd_app" / "architecture.json"
    ext_arch.write_text(
        json.dumps(
            [
                {
                    "filename": "ext_module_python.prompt",
                    "filepath": "extensions/github_pdd_app/src/ext_module.py",
                    "reason": "Stale nested reason",
                    "description": "Ext module desc",
                    "dependencies": [],
                    "priority": 1,
                    "tags": [],
                }
            ],
            indent=2,
        ),
        encoding="utf-8",
    )
    (tmp_path / "architecture.json").write_text("[]", encoding="utf-8")

    captured_arch_paths = []

    def capturing_metadata_sync(*_args, **kwargs):
        captured_arch_paths.append(kwargs.get("architecture_path"))
        return SimpleNamespace(ok=True, failing_stage=None)

    monkeypatch.setattr(pre_checkup_gate, "run_metadata_sync", capturing_metadata_sync)
    monkeypatch.setattr(pre_checkup_gate, "detect_drift", lambda **_k: ([], []))

    outcome = pre_checkup_gate._run_drift_sync(
        tmp_path,
        ["extensions/github_pdd_app/src/prompts/ext_module_python.prompt"],
        base_ref=None,
        strict=False,
    )

    assert json.loads((tmp_path / "architecture.json").read_text()) == []
    ext_arch_data = json.loads(ext_arch.read_text())
    assert ext_arch_data[0]["reason"] == "Fresh nested reason", ext_arch_data
    assert "extensions/github_pdd_app/architecture.json" in outcome.synced_paths
    assert captured_arch_paths
    assert all(path.resolve() == ext_arch.resolve() for path in captured_arch_paths)
    assert outcome.ok is True


def test_drift_sync_foreign_prompt_dir_metadata_sync_receives_foreign_arch_path(monkeypatch, tmp_path):
    """Issue #1614 (failure mode 2): run_metadata_sync must receive the nearest-ancestor
    architecture.json for a foreign-prompts-dir prompt, not the repo-root one.

    Buggy behavior: architecture_path=worktree/"architecture.json" (root) is passed for
    every prompt regardless of which prompts_dir was resolved for that group. A metadata-
    sync step that runs the fingerprint pipeline against the root arch for a prompt it
    does not own trips spurious failures and blocks a legitimate PR.

    sync_all_prompts_to_architecture is stubbed to isolate the run_metadata_sync call
    site; the capturing stub records every architecture_path it receives.
    """
    ext_arch = _ext_prompt_repo(tmp_path)

    captured_arch_paths = []

    def capturing_metadata_sync(*_args, **kwargs):
        captured_arch_paths.append(kwargs.get("architecture_path"))
        return SimpleNamespace(ok=True, failing_stage=None)

    monkeypatch.setattr(
        pre_checkup_gate,
        "sync_all_prompts_to_architecture",
        lambda **_k: {"success": True},
    )
    monkeypatch.setattr(pre_checkup_gate, "run_metadata_sync", capturing_metadata_sync)
    monkeypatch.setattr(pre_checkup_gate, "detect_drift", lambda **_k: ([], []))

    pre_checkup_gate._run_drift_sync(
        tmp_path,
        ["extensions/github_pdd_app/prompts/ext_module_python.prompt"],
        base_ref=None,
        strict=False,
    )

    assert captured_arch_paths, "run_metadata_sync was never called for the foreign prompt"
    expected = tmp_path / "extensions" / "github_pdd_app" / "architecture.json"
    for arch_path in captured_arch_paths:
        assert arch_path == expected, (
            f"run_metadata_sync received the wrong architecture_path: "
            f"expected {expected}, got {arch_path}"
        )


# Scope addition: covers expansion item "synced_paths tracking at
# pdd/pre_checkup_gate.py:406-443 tracks only root architecture.json — after
# per-dir fix foreign arch rewrites are not included in synced_paths and won't
# be validated by _run_build_smoke" identified by Step 6 but absent from Step
# 8's plan (Step 8 listed it as Test 3, included below).
def test_drift_sync_foreign_arch_write_tracked_in_synced_paths(monkeypatch, tmp_path):
    """Issue #1614 (expansion item): when sync_all_prompts_to_architecture rewrites the
    FOREIGN architecture.json (because the fix correctly targets it), that rewrite must
    appear in outcome.synced_paths so _run_build_smoke can validate the produced tree.

    The current arch_path tracking (lines 406-443) only watches worktree/"architecture.json"
    (root). After the per-dir arch-path fix, the foreign arch is rewritten but the root
    arch is untouched, so the root-only signature check never fires and the foreign arch
    write is silently dropped from synced_paths.

    This test drives the REAL sync_all_prompts_to_architecture (the stale-reason fixture
    ensures the sync WILL rewrite the foreign arch) and asserts the foreign arch's
    repo-relative path appears in synced_paths.
    """
    ext_arch = _ext_prompt_repo(tmp_path, root_arch_content="[]")

    monkeypatch.setattr(
        pre_checkup_gate,
        "run_metadata_sync",
        lambda *_a, **_k: SimpleNamespace(ok=True, failing_stage=None),
    )
    monkeypatch.setattr(pre_checkup_gate, "detect_drift", lambda **_k: ([], []))

    outcome = pre_checkup_gate._run_drift_sync(
        tmp_path,
        ["extensions/github_pdd_app/prompts/ext_module_python.prompt"],
        base_ref=None,
        strict=False,
    )

    assert "extensions/github_pdd_app/architecture.json" in outcome.synced_paths, (
        f"Foreign architecture.json rewrite was not tracked in synced_paths; "
        f"got {outcome.synced_paths}"
    )


def test_drift_sync_foreign_prompt_falls_back_to_root_arch_when_no_own_arch(monkeypatch, tmp_path):
    """Issue #1614 (edge case / regression): when a foreign prompts_dir has no ancestor
    architecture.json between itself and the repo root, the nearest-ancestor walk-up
    must fall back to worktree/"architecture.json" and still function correctly.

    This confirms the fix does not break the no-own-arch fallback path.
    """
    # Foreign prompt dir without its own architecture.json anywhere up the tree.
    no_arch_prompts_dir = tmp_path / "extensions" / "no_arch_app" / "prompts"
    no_arch_prompts_dir.mkdir(parents=True)
    (no_arch_prompts_dir / "ext_module_python.prompt").write_text(
        "<pdd-reason>Fresh ext reason</pdd-reason>\n", encoding="utf-8"
    )
    # Root arch owns the entry (no intermediate arch.json exists).
    (tmp_path / "architecture.json").write_text(
        json.dumps(
            [
                {
                    "filename": "ext_module_python.prompt",
                    "filepath": "extensions/no_arch_app/ext_module.py",
                    "reason": "Stale ext reason",
                    "description": "Ext module desc",
                    "dependencies": [],
                    "priority": 1,
                    "tags": [],
                }
            ],
            indent=2,
        ),
        encoding="utf-8",
    )

    monkeypatch.setattr(
        pre_checkup_gate,
        "run_metadata_sync",
        lambda *_a, **_k: SimpleNamespace(ok=True, failing_stage=None),
    )
    monkeypatch.setattr(pre_checkup_gate, "detect_drift", lambda **_k: ([], []))

    outcome = pre_checkup_gate._run_drift_sync(
        tmp_path,
        ["extensions/no_arch_app/prompts/ext_module_python.prompt"],
        base_ref=None,
        strict=False,
    )

    # Root arch must be updated (fallback to root arch worked).
    root_arch_data = json.loads((tmp_path / "architecture.json").read_text())
    assert len(root_arch_data) == 1
    assert root_arch_data[0]["reason"] == "Fresh ext reason", root_arch_data
    assert outcome.ok is True


def test_drift_sync_standard_pdd_prompts_still_uses_root_architecture(monkeypatch, tmp_path):
    """Issue #1614 (regression): the arch-per-prompts-dir resolution must NOT break the
    standard case. Prompts under pdd/prompts/ have no pdd/architecture.json, so the
    nearest-ancestor walk-up must resolve to the repo-root architecture.json for both
    sync_all_prompts_to_architecture and run_metadata_sync.
    """
    prompt_dir = tmp_path / "pdd" / "prompts"
    prompt_dir.mkdir(parents=True)
    (tmp_path / "pdd" / "foo.py").write_text("def foo():\n    return 1\n", encoding="utf-8")
    (prompt_dir / "foo_python.prompt").write_text(
        "<pdd-reason>Fresh foo</pdd-reason>\n", encoding="utf-8"
    )
    arch_path = tmp_path / "architecture.json"
    arch_path.write_text(
        json.dumps(
            [
                {
                    "filename": "foo_python.prompt",
                    "filepath": "pdd/foo.py",
                    "reason": "Stale foo",
                    "description": "Foo desc",
                    "dependencies": [],
                    "priority": 1,
                    "tags": [],
                }
            ],
            indent=2,
        ),
        encoding="utf-8",
    )
    # No pdd/architecture.json — walk-up must skip and find root.

    captured_arch_paths = []

    def capturing_metadata_sync(*_args, **kwargs):
        captured_arch_paths.append(kwargs.get("architecture_path"))
        return SimpleNamespace(ok=True, failing_stage=None)

    monkeypatch.setattr(pre_checkup_gate, "run_metadata_sync", capturing_metadata_sync)
    monkeypatch.setattr(pre_checkup_gate, "detect_drift", lambda **_k: ([], []))

    outcome = pre_checkup_gate._run_drift_sync(
        tmp_path,
        ["pdd/prompts/foo_python.prompt"],
        base_ref=None,
        strict=False,
    )

    # Real sync must have updated the root arch entry.
    arch_data = json.loads(arch_path.read_text())
    assert arch_data[0]["reason"] == "Fresh foo", arch_data
    # run_metadata_sync must have received the root arch path (not pdd/architecture.json).
    assert captured_arch_paths, "run_metadata_sync was never called"
    for ap in captured_arch_paths:
        assert ap == tmp_path / "architecture.json", (
            f"Standard pdd/prompts case: expected root arch path, got {ap}"
        )
    assert outcome.ok is True
