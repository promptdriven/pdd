"""Tests for scripts/ci_detect_changed_modules.py."""

from __future__ import annotations

import importlib.util
import subprocess
from pathlib import Path

import pytest


def _load_module():
    script_path = (
        Path(__file__).resolve().parents[1] / "scripts" / "ci_detect_changed_modules.py"
    )
    spec = importlib.util.spec_from_file_location(
        "ci_detect_changed_modules", script_path
    )
    module = importlib.util.module_from_spec(spec)
    assert spec.loader is not None
    spec.loader.exec_module(module)
    return module


def _repo_root() -> Path:
    return Path(__file__).resolve().parents[1]


def test_basename_from_nested_code_paths():
    module = _load_module()

    assert module._basename_from_path("pdd/commands/checkup.py") == "commands/checkup"
    assert module._basename_from_path("pdd/core/cloud.py") == "core/cloud"
    assert (
        module._basename_from_path("pdd/server/routes/auth.py")
        == "server/routes/auth"
    )


def test_basename_excludes_package_main_shim():
    module = _load_module()

    assert module._basename_from_path("pdd/__main__.py") is None
    assert module._basename_from_path("pdd/prompts/__main___python.prompt") is None
    assert module._basename_from_path("context/__main___example.py") is None
    assert module._basename_from_path("tests/test___main__.py") is None


def test_basename_excludes_ci_helper_script_tests():
    module = _load_module()

    assert module._basename_from_path("tests/test_ci_detect_changed_modules.py") is None
    assert module._basename_from_path("tests/test_copy_package_data_to_public.py") is None


def test_basename_excludes_ci_detect_prompt_and_module():
    """The detector's own prompt and packaged copy must never be flagged for
    auto-heal. The bare-basename form covers the canonical path
    (pdd/prompts/ci_detect_changed_modules_python.prompt + the packaged
    module); the path-qualified form is kept as defensive coverage in case
    the prompt is ever relocated back under a subdirectory, since that
    placement would otherwise re-introduce the auto-heal failure mode where
    a bogus pdd/scripts/ci_detect_changed_modules.py path gets fed to
    ``pdd example``."""
    module = _load_module()

    assert (
        module._basename_from_path(
            "pdd/prompts/ci_detect_changed_modules_python.prompt"
        )
        is None
    )
    assert module._basename_from_path("pdd/ci_detect_changed_modules.py") is None
    assert (
        module._basename_from_path(
            "pdd/prompts/scripts/ci_detect_changed_modules_python.prompt"
        )
        is None
    )


def test_basename_excludes_agent_reviewed_model_catalog():
    module = _load_module()

    assert module._basename_from_path("pdd/generate_model_catalog.py") is None
    assert (
        module._basename_from_path("pdd/prompts/generate_model_catalog_python.prompt")
        is None
    )
    assert module._basename_from_path("context/generate_model_catalog_example.py") is None
    assert module._basename_from_path("tests/test_generate_model_catalog.py") is None


def test_basename_from_nested_context_and_tests():
    module = _load_module()

    assert (
        module._basename_from_path("context/core/errors_example.py")
        == "core/errors"
    )
    assert module._basename_from_path("tests/core/test_cloud.py") == "core/cloud"
    assert (
        module._basename_from_path("tests/server/test_security.py")
        == "server/security"
    )


def test_reverse_dep_detects_recursive_nested_include(monkeypatch):
    module = _load_module()
    monkeypatch.chdir(_repo_root())

    result = module._reverse_dep_basenames(["context/core/errors_example.py"])

    assert "core/cloud" in result


def test_reverse_dep_respects_selected_function_changes(tmp_path, monkeypatch):
    module = _load_module()
    monkeypatch.chdir(tmp_path)

    prompt_dir = tmp_path / "prompts"
    context_dir = tmp_path / "context"
    prompt_dir.mkdir()
    context_dir.mkdir()

    (prompt_dir / "old_consumer_python.prompt").write_text(
        '<include select="def:old_func">context/shared_example.py</include>',
        encoding="utf-8",
    )
    (prompt_dir / "new_consumer_python.prompt").write_text(
        '<include select="def:new_func">context/shared_example.py</include>',
        encoding="utf-8",
    )
    (context_dir / "shared_example.py").write_text(
        "def old_func():\n    return 'old'\n\n"
        "def new_func():\n    return 'new'\n",
        encoding="utf-8",
    )

    monkeypatch.setattr(
        module,
        "_changed_python_defs",
        lambda path, diff_base: {"new_func"}
        if path == "context/shared_example.py"
        else None,
    )

    result = module._reverse_dep_basenames(
        ["context/shared_example.py"], diff_base="origin/main...HEAD"
    )

    assert "new_consumer" in result
    assert "old_consumer" not in result


def test_reverse_dep_without_diff_base_keeps_conservative_matching(
    tmp_path, monkeypatch
):
    module = _load_module()
    monkeypatch.chdir(tmp_path)

    prompt_dir = tmp_path / "prompts"
    context_dir = tmp_path / "context"
    prompt_dir.mkdir()
    context_dir.mkdir()

    (prompt_dir / "old_consumer_python.prompt").write_text(
        '<include select="def:old_func">context/shared_example.py</include>',
        encoding="utf-8",
    )
    (context_dir / "shared_example.py").write_text(
        "def old_func():\n    return 'old'\n",
        encoding="utf-8",
    )

    result = module._reverse_dep_basenames(["context/shared_example.py"])

    assert "old_consumer" in result


def test_reverse_dep_detects_include_many(monkeypatch):
    module = _load_module()
    monkeypatch.chdir(_repo_root())

    result = module._reverse_dep_basenames(["context/auto_update_example.py"])

    assert "core/cli" in result


def test_extract_include_refs_splits_on_newlines():
    """<include-many> bodies often list one entry per line — both commas and
    newlines must be honored. The preprocessor and sync-order code both accept
    newline-delimited entries (see frontend/components/...GenerationProgressModal
    for a real example), so the reverse-dep scan needs to as well."""
    module = _load_module()

    body = "<include-many>\na.py\nb.py\n</include-many>"
    refs = module._extract_include_refs(body)
    assert refs == [("a.py", None), ("b.py", None)]

    indented = (
        "<include-many>\n"
        "    ./Icon/CheckIcon.tsx\n"
        "    ./Icon/SpinnerIcon.tsx\n"
        "</include-many>"
    )
    refs = module._extract_include_refs(indented)
    assert refs == [
        ("Icon/CheckIcon.tsx", None),
        ("Icon/SpinnerIcon.tsx", None),
    ]


def test_reverse_dep_detects_newline_delimited_include_many(tmp_path, monkeypatch):
    """A real prompt with newline-only include-many entries must still pull its
    consumer into auto-heal when one of those entries changes."""
    module = _load_module()
    monkeypatch.chdir(tmp_path)

    prompt_dir = tmp_path / "pdd" / "prompts" / "frontend" / "components"
    prompt_dir.mkdir(parents=True)
    (prompt_dir / "Modal_typescriptreact.prompt").write_text(
        "<include-many>\n"
        "    ./Icon/CheckIcon.tsx\n"
        "    ./Icon/SpinnerIcon.tsx\n"
        "</include-many>\n"
    )

    result = module._reverse_dep_basenames(
        ["pdd/prompts/frontend/components/Icon/CheckIcon.tsx"]
    )

    assert "frontend/components/Modal" in result


def test_detect_combines_nested_direct_and_reverse_dependencies(monkeypatch):
    module = _load_module()
    monkeypatch.chdir(_repo_root())
    monkeypatch.setattr(
        module,
        "_git_changed_files",
        lambda diff_base: [
            "pdd/server/routes/auth.py",
            "context/auto_update_example.py",
        ],
    )

    result = module.detect("origin/main...HEAD")

    assert "server/routes/auth" in result
    assert "core/cli" in result


def test_detect_excludes_package_main_shim(monkeypatch):
    module = _load_module()
    monkeypatch.chdir(_repo_root())
    monkeypatch.setattr(
        module,
        "_git_changed_files",
        lambda diff_base: [
            "pdd/__main__.py",
            "pdd/prompts/__main___python.prompt",
            "context/__main___example.py",
            "tests/test___main__.py",
        ],
    )

    assert module.detect("origin/main...HEAD") == []


# ---------------------------------------------------------------------------
# Issue #1284: the auto-heal module detector must ignore whitespace-only
# changes. A whitespace-only edit to a PDD-prefixed file (pdd/, prompts/,
# context/, tests/) must NOT flag a module for healing, or it triggers the
# same spurious heal that blocks an approved, otherwise-green PR (#1243).
#
# These tests run a REAL git repo (not a mocked `_git_changed_files`) so they
# assert observable post-`git` behavior. Step 5/6 verified that both
# `git diff --name-only` and `git diff -w --name-only` list whitespace-only
# files; only `git diff -w --numstat` (path column) omits them. So these tests
# fail on the current whitespace-blind code and pass once detection is
# whitespace-aware.
# ---------------------------------------------------------------------------


def _init_git_repo(repo: Path) -> None:
    subprocess.run(["git", "init"], cwd=repo, check=True, capture_output=True, text=True)
    subprocess.run(
        ["git", "config", "user.email", "issue-1284-test@example.com"],
        cwd=repo,
        check=True,
        capture_output=True,
        text=True,
    )
    subprocess.run(
        ["git", "config", "user.name", "Issue 1284 Test"],
        cwd=repo,
        check=True,
        capture_output=True,
        text=True,
    )


def _commit_all(repo: Path, message: str) -> str:
    subprocess.run(["git", "add", "-A"], cwd=repo, check=True, capture_output=True, text=True)
    subprocess.run(
        ["git", "commit", "-m", message],
        cwd=repo,
        check=True,
        capture_output=True,
        text=True,
    )
    rev = subprocess.run(
        ["git", "rev-parse", "HEAD"],
        cwd=repo,
        check=True,
        capture_output=True,
        text=True,
    )
    return rev.stdout.strip()


@pytest.fixture
def clean_git_env(monkeypatch):
    """Drop ambient git env vars so git operates on the temp repo, not an ambient one."""
    for var in ("GIT_DIR", "GIT_WORK_TREE", "GIT_INDEX_FILE"):
        monkeypatch.delenv(var, raising=False)


# --- Test 5: scripts/ copy _git_changed_files (sibling source) -------------
def test_scripts_git_changed_files_ignores_whitespace_only(
    tmp_path, monkeypatch, clean_git_env
):
    """scripts/ copy: a whitespace-only edit to a PDD-prefixed file is not returned.

    Includes a functional-change control so an over-broad fix that drops genuine
    changes would fail. Reproduces issue #1284 for the auto-heal module-selection
    gate's source-of-truth copy.
    """
    module = _load_module()

    repo = tmp_path / "repo"
    (repo / "pdd").mkdir(parents=True)
    _init_git_repo(repo)

    code = repo / "pdd" / "foo.py"
    code.write_text("def f():\n    return 1\n", encoding="utf-8")
    base_sha = _commit_all(repo, "base: clean code")

    code.write_text("def f():   \n    return 1\n", encoding="utf-8")
    _commit_all(repo, "chore: trailing whitespace cleanup")

    monkeypatch.chdir(repo)
    changed = module._git_changed_files(base_sha)

    assert "pdd/foo.py" not in changed, (
        "whitespace-only edit must not be reported as a changed PDD file; "
        f"got: {sorted(changed)}"
    )

    # Control: a functional change must still be detected.
    code.write_text("def f():\n    return 2\n", encoding="utf-8")
    func_sha = _commit_all(repo, "feat: change return value")
    changed_func = module._git_changed_files(base_sha)
    assert "pdd/foo.py" in changed_func, (
        f"a functional change must still be detected; got: {sorted(changed_func)}"
    )
    assert func_sha  # silence unused-var linters; sha proves the commit landed


# --- Test 6: pdd/ mirror copy _git_changed_files (sibling mirror) ----------
def test_pdd_mirror_git_changed_files_ignores_whitespace_only(
    tmp_path, monkeypatch, clean_git_env
):
    """pdd/ byte-identical mirror: same whitespace-only no-op behavior.

    Step 6 flagged that the pdd/ packaged copy and the scripts/ source must be
    fixed together; a fix applied to only one copy would pass Test 5 but fail
    here. This independently exercises the mirror's own code path.
    """
    import pdd.ci_detect_changed_modules as pkg_module

    repo = tmp_path / "repo"
    (repo / "pdd").mkdir(parents=True)
    _init_git_repo(repo)

    code = repo / "pdd" / "foo.py"
    code.write_text("def f():\n    return 1\n", encoding="utf-8")
    base_sha = _commit_all(repo, "base: clean code")

    code.write_text("def f():   \n    return 1\n", encoding="utf-8")
    _commit_all(repo, "chore: trailing whitespace cleanup")

    monkeypatch.chdir(repo)
    changed = pkg_module._git_changed_files(base_sha)

    assert "pdd/foo.py" not in changed, (
        "whitespace-only edit must not be reported by the pdd/ mirror copy; "
        f"got: {sorted(changed)}"
    )


# --- Test 7: caller-side detect() module-selection gate --------------------
def test_detect_flags_no_module_for_whitespace_only_change(
    tmp_path, monkeypatch, clean_git_env
):
    """``detect()`` must return no modules for a whitespace-only commit.

    This is the auto-heal module-selection entry point (distinct from
    ``detect_drift``). Before the fix, a whitespace-only edit to ``pdd/foo.py``
    flags ``foo`` for heal; after the fix it returns ``[]``. A functional-change
    control asserts ``foo`` is still flagged when there is a real change.
    """
    module = _load_module()

    repo = tmp_path / "repo"
    (repo / "pdd").mkdir(parents=True)
    _init_git_repo(repo)

    code = repo / "pdd" / "foo.py"
    code.write_text("def f():\n    return 1\n", encoding="utf-8")
    base_sha = _commit_all(repo, "base: clean code")

    code.write_text("def f():   \n    return 1\n", encoding="utf-8")
    _commit_all(repo, "chore: trailing whitespace cleanup")

    monkeypatch.chdir(repo)
    assert module.detect(base_sha) == [], (
        "a whitespace-only commit must flag no modules for auto-heal; "
        f"got: {module.detect(base_sha)}"
    )

    # Control: a functional change must still flag the module.
    code.write_text("def f():\n    return 2\n", encoding="utf-8")
    _commit_all(repo, "feat: change return value")
    assert "foo" in module.detect(base_sha), (
        f"a functional change must flag the module; got: {module.detect(base_sha)}"
    )
