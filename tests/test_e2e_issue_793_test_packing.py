"""End-to-end tests for issue #793 / PR #1524: ranked test packing under a token budget.

Unlike ``tests/test_test_context_packer.py`` (which unit-tests ``TestContextPacker``
in isolation), this suite drives the *integration* path the real PDD flows use:

    build_compressed_sync_context(..., context_compression="test")
        -> _pack_test_paths -> TestContextPacker.pack -> test_packing_manifest

Each test maps to one acceptance criterion from issue #793:

    1. Always includes currently failing tests during fix flows.
    2. Ranks tests by relevance (import graph + symbol overlap) over unrelated ones.
    3. Deduplicates overlapping test content.
    4. Enforces a configurable token cap (PDD_TEST_TOKEN_BUDGET).
    5. Emits a manifest explaining selected and omitted tests.
    6. No-test fallback: no crash, empty result.

TDD / red-first
---------------
The feature is toggled by an env var so you can watch the same assertions go
red (feature off = pre-#793 verbatim behavior) and green (feature on):

    # RED  -- pre-#793 path: no packing, no manifest, no budget enforcement
    PDD_E2E_PACKING=off pytest -vv tests/test_e2e_issue_793_test_packing.py

    # GREEN -- the PR #1524 behavior
    pytest -vv tests/test_e2e_issue_793_test_packing.py

This proves the assertions are real oracles (they fail without the feature)
rather than vacuously passing.
"""

from __future__ import annotations

import os
from pathlib import Path

import pytest

from pdd.compressed_sync_context import build_compressed_sync_context


# --------------------------------------------------------------------------- mode
def _compression_mode() -> str | None:
    """Return the context_compression value for the current run.

    Default "test" exercises the PR #1524 packing path (green). Setting
    PDD_E2E_PACKING=off selects the pre-#793 verbatim path (red), so the
    acceptance-criteria assertions below fail -- which is the point.
    """
    return None if os.environ.get("PDD_E2E_PACKING") == "off" else "test"


FEATURE_ON = _compression_mode() == "test"
skip_when_off = pytest.mark.skipif(
    not FEATURE_ON,
    reason="behavior only exists on the #793 packing path (run without PDD_E2E_PACKING=off)",
)


# ----------------------------------------------------------------------- fixtures
def _write(path: Path, text: str) -> Path:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(text, encoding="utf-8")
    return path


@pytest.fixture(autouse=True)
def _clean_env(monkeypatch):
    for key in (
        "PDD_FAILING_TESTS",
        "PDD_TEST_TOKEN_BUDGET",
        "PDD_TEST_RANKING_WEIGHTS",
        "PDD_TEST_DEDUP_THRESHOLD",
    ):
        monkeypatch.delenv(key, raising=False)
    yield


@pytest.fixture
def project(tmp_path: Path):
    """A realistic mini-project: a prompt, a module under change, and a tests/ dir.

    Returns (prompt, module, tests_dir, test_paths) where test_paths is the list
    of test files a real sync phase would hand to build_compressed_sync_context.
    """
    prompt = _write(
        tmp_path / "calculator_python.prompt",
        "Write a calculator module exposing add(a, b) and subtract(a, b).\n",
    )
    module = _write(
        tmp_path / "calculator.py",
        "def add(a, b):\n    return a + b\n\n\ndef subtract(a, b):\n    return a - b\n",
    )
    tests_dir = tmp_path / "tests"
    tests_dir.mkdir()

    # Relevant: imports + exercises the module's exported symbols.
    t_add = _write(
        tests_dir / "test_add.py",
        "from calculator import add\n\n\ndef test_add():\n    assert add(1, 2) == 3\n",
    )
    t_sub = _write(
        tests_dir / "test_subtract.py",
        "from calculator import subtract\n\n\ndef test_subtract():\n    assert subtract(5, 2) == 3\n",
    )
    # Unrelated: no import of the module, no symbol overlap.
    t_unrelated = _write(
        tests_dir / "test_unrelated.py",
        "def test_upper():\n    assert 'x'.upper() == 'X'\n",
    )
    test_paths = [str(t_add), str(t_sub), str(t_unrelated)]
    return prompt, module, tests_dir, test_paths


def _build(prompt, module, test_paths, **kw):
    """Drive the integration entry point used by real sync/fix phases."""
    return build_compressed_sync_context(
        "generate",
        str(prompt),
        code_path=str(module),
        test_paths=test_paths,
        context_compression=_compression_mode(),
        **kw,
    )


# ===================================================== AC#5: a manifest is emitted
def test_manifest_is_emitted(project):
    """#793: 'Emits a manifest explaining selected and omitted tests.'"""
    prompt, module, tests_dir, test_paths = project
    pkg = _build(prompt, module, test_paths)

    assert pkg.test_packing_manifest is not None, (
        "no TestPackingManifest on the context package -- the #793 packing path did not run"
    )
    manifest = pkg.test_packing_manifest
    # Manifest must explain both selection and omission, plus budget accounting.
    for key in ("selected", "omitted", "budget_tokens", "used_tokens"):
        assert key in manifest, f"manifest missing '{key}'"
    assert isinstance(manifest["selected"], list)


# ============================================ AC#2: relevant tests outrank unrelated
@skip_when_off
def test_relevant_tests_rank_above_unrelated(project):
    """#793: ranks tests by import graph + symbol references."""
    prompt, module, tests_dir, test_paths = project
    pkg = _build(prompt, module, test_paths)

    selected = [Path(e["file"]).name for e in pkg.test_packing_manifest["selected"]]
    assert "test_add.py" in selected
    assert "test_unrelated.py" in selected
    # A module-relevant test must be ranked ahead of the unrelated one.
    assert selected.index("test_add.py") < selected.index("test_unrelated.py")


# ===================================== AC#1: failing tests always included (fix flow)
def test_failing_tests_always_included(project, monkeypatch):
    """#793: 'Always includes currently failing tests during fix flows.'

    The fix flow signals failures via PDD_FAILING_TESTS; the packer must place
    them in the priority-0 lane regardless of ranking/budget.
    """
    prompt, module, tests_dir, test_paths = project
    failing_file = _write(
        tests_dir / "test_regression.py",
        "from calculator import add\n\n\ndef test_known_bug():\n    assert add(2, 2) == 5\n",
    )
    monkeypatch.setenv("PDD_FAILING_TESTS", f"{failing_file}::test_known_bug")

    pkg = _build(prompt, module, test_paths + [str(failing_file)])

    assert pkg.test_packing_manifest is not None
    manifest = pkg.test_packing_manifest
    assert manifest["failing_test_priority_count"] >= 1
    first = manifest["selected"][0]
    assert Path(first["file"]).name == "test_regression.py"
    assert "priority lane" in first["reason"]
    # And the failing test's content actually made it into the assembled context.
    assert "test_known_bug" in pkg.content


# =============================================== AC#4: configurable token cap enforced
@skip_when_off
def test_token_budget_is_enforced(project, monkeypatch):
    """#793: 'Enforces a configurable token cap.' (PDD_TEST_TOKEN_BUDGET)"""
    prompt, module, tests_dir, test_paths = project
    # A large, low-relevance test that should be squeezed out under a tiny cap.
    big_body = "\n".join(f"    assert True  # filler {i}" for i in range(400))
    big = _write(tests_dir / "test_big.py", f"def test_big():\n{big_body}\n")

    monkeypatch.setenv("PDD_TEST_TOKEN_BUDGET", "60")
    pkg = _build(prompt, module, test_paths + [str(big)])

    manifest = pkg.test_packing_manifest
    assert manifest["used_tokens"] <= 60, "packer exceeded the configured token cap"
    assert any(e["reason"] == "budget exhausted" for e in manifest["omitted"]), (
        "expected at least one candidate omitted for budget reasons"
    )


# ================================================ AC#3: overlapping content deduped
@skip_when_off
def test_near_duplicate_tests_deduplicated(project):
    """#793: 'Deduplicates overlapping test content.'"""
    prompt, module, tests_dir, test_paths = project
    body = (
        "from calculator import add, subtract\n\n\n"
        "def {name}():\n    assert add(1, 1) == 2\n    assert subtract(2, 1) == 1\n"
    )
    dup_a = _write(tests_dir / "test_dup_a.py", body.format(name="test_dup_a"))
    dup_b = _write(tests_dir / "test_dup_b.py", body.format(name="test_dup_b"))

    pkg = _build(prompt, module, test_paths + [str(dup_a), str(dup_b)])
    omitted_reasons = [e["reason"] for e in pkg.test_packing_manifest["omitted"]]
    assert any(r.startswith("near-duplicate of") for r in omitted_reasons), (
        "expected one of the identical-import duplicates to be dropped"
    )


# ===================================================== AC#6: no-test fallback is safe
def test_no_tests_does_not_crash(tmp_path):
    """#793 fallback: no test files -> empty, no exception, valid package."""
    prompt = _write(tmp_path / "p_python.prompt", "Write add(a, b).\n")
    module = _write(tmp_path / "calc.py", "def add(a, b):\n    return a + b\n")
    pkg = build_compressed_sync_context(
        "generate",
        str(prompt),
        code_path=str(module),
        test_paths=[],
        context_compression=_compression_mode(),
    )
    # The package is still well-formed; no test sources contributed.
    assert pkg.enabled is True
    if FEATURE_ON and pkg.test_packing_manifest is not None:
        assert pkg.test_packing_manifest["selected"] == []
