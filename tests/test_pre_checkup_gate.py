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
    """Issue #1293 (security): the gate executes worktree code, so its subprocess
    env must drop secret-bearing vars (LLM/cloud/VCS keys + tokens) while keeping
    the controlled PYTHONPATH=worktree the import/existence probes need."""
    monkeypatch.setenv("ANTHROPIC_API_KEY", "sk-should-be-dropped")  # prefix
    monkeypatch.setenv("GITHUB_TOKEN", "ghp_should_be_dropped")  # prefix
    monkeypatch.setenv("MYPROVIDER_API_KEY", "drop-me")  # canonical suffix
    monkeypatch.setenv("PDD_PATH", str(tmp_path))  # non-secret -> preserved
    # Must NOT be over-stripped (a target repo's unit test may legitimately read
    # these); the scrub is precise, not a broad KEY/SECRET substring match.
    monkeypatch.setenv("DJANGO_SECRET_KEY", "keep-me")
    monkeypatch.setenv("DATABASE_URL", "keep-me-too")

    env = pre_checkup_gate._python_import_env(tmp_path)

    assert "ANTHROPIC_API_KEY" not in env
    assert "GITHUB_TOKEN" not in env
    assert "MYPROVIDER_API_KEY" not in env
    assert env.get("DJANGO_SECRET_KEY") == "keep-me"  # not over-stripped
    assert env.get("DATABASE_URL") == "keep-me-too"
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
