"""Tests for pdd.story_regression_gate (issue #1702).

Test plan (each test fails if its requirement is violated):

story_id_from_path
  - test_story_id_strips_prefix_and_suffix
  - test_story_id_plain_stem_without_prefix

discover_story_markers (AST scan, never executes test code)
  - test_discover_reads_story_id_and_hash
  - test_discover_supports_positional_story_id
  - test_discover_ignores_non_story_markers
  - test_discover_missing_dir_returns_empty
  - test_discover_does_not_import_test_module   (regression: import-time crash)
  - test_discover_duplicate_story_id_is_deterministic

classify_story (the core missing/stale/ok logic)
  - test_classify_missing_when_no_marker
  - test_classify_stale_on_hash_mismatch
  - test_classify_stale_when_no_recorded_hash
  - test_classify_ok_when_hash_matches
  - test_metadata_only_edit_is_not_stale         (regression: reuse normalized hash)

evaluate_stories
  - test_evaluate_classifies_all_sorted
  - test_evaluate_only_story_ids_scopes

changed_story_ids (offline git diff)
  - test_changed_story_ids_detects_new_story
  - test_changed_story_ids_returns_none_without_git_repo

config + mode resolution (mirrors #1425 prompt gate)
  - test_config_default_is_warn
  - test_config_reads_pyproject
  - test_config_boolean_false_is_off
  - test_config_boolean_true_ignored_defaults_warn
  - test_config_unknown_value_ignored
  - test_resolve_disabled_is_off
  - test_resolve_cli_override_wins
  - test_resolve_invalid_cli_override_raises
  - test_resolve_falls_back_to_config

run_story_regression_gate (warn / strict / off)
  - test_gate_off_skips_all_work
  - test_gate_warn_reports_but_passes
  - test_gate_strict_fails_on_offending
  - test_gate_strict_passes_when_all_fresh

determinism / public-safe
  - test_gate_decision_is_deterministic_without_secrets
"""
from __future__ import annotations

import shutil
import subprocess
from pathlib import Path

import click
import pytest

from pdd import story_regression_gate as srg
from pdd.story_regression_gate import (
    STATUS_STORY_REGRESSION_MISSING,
    STATUS_STORY_REGRESSION_OK,
    STATUS_STORY_REGRESSION_STALE,
    StoryRegressionGateResult,
    changed_story_ids,
    classify_story,
    discover_story_markers,
    evaluate_stories,
    load_story_regression_gate_config,
    resolve_story_regression_gate_mode,
    run_story_regression_gate,
    story_id_from_path,
)
from pdd.user_story_tests import _story_content_hash


# --------------------------------------------------------------------------- #
# Fixtures / helpers
# --------------------------------------------------------------------------- #

FRESH_STORY = "# Story: refund\n\nA refund returns the charged amount.\n"
OTHER_STORY = "# Story: checkout\n\nTax is added at checkout.\n"


def _write(path: Path, text: str) -> Path:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(text, encoding="utf-8")
    return path


def _test_module(*decls: str) -> str:
    return "import pytest\n\n" + "\n\n".join(decls) + "\n"


def _marked(story_id: str, story_hash: str | None, func: str) -> str:
    if story_hash is None:
        deco = f'@pytest.mark.story(story_id="{story_id}")'
    else:
        deco = f'@pytest.mark.story(story_id="{story_id}", story_hash="{story_hash}")'
    return f"{deco}\ndef {func}():\n    assert True"


@pytest.fixture
def fixture_tree(tmp_path: Path):
    """A project with three stories and one marked-test module."""
    stories = tmp_path / "user_stories"
    tests = tmp_path / "tests"
    _write(stories / "story__refund.md", FRESH_STORY)
    _write(stories / "story__checkout.md", OTHER_STORY)
    _write(stories / "story__export.md", "# Story: export\n\nExport a receipt.\n")

    fresh_hash = _story_content_hash(FRESH_STORY)
    _write(
        tests / "test_demo.py",
        _test_module(
            _marked("refund", fresh_hash, "test_refund"),
            _marked("checkout", "0000000000000000", "test_checkout"),
        ),
    )
    return tmp_path, stories, tests


# --------------------------------------------------------------------------- #
# story_id_from_path
# --------------------------------------------------------------------------- #

def test_story_id_strips_prefix_and_suffix():
    assert story_id_from_path("user_stories/story__pdd_sync.md") == "pdd_sync"


def test_story_id_plain_stem_without_prefix():
    assert story_id_from_path("notes.md") == "notes"


# --------------------------------------------------------------------------- #
# discover_story_markers
# --------------------------------------------------------------------------- #

def test_discover_reads_story_id_and_hash(tmp_path: Path):
    _write(tmp_path / "test_a.py", _test_module(_marked("alpha", "abc123", "test_alpha")))
    markers = discover_story_markers(tmp_path)
    assert set(markers) == {"alpha"}
    assert markers["alpha"].story_hash == "abc123"
    assert markers["alpha"].test_name == "test_alpha"


def test_discover_supports_positional_story_id(tmp_path: Path):
    src = _test_module('@pytest.mark.story("beta")\ndef test_beta():\n    assert True')
    _write(tmp_path / "test_b.py", src)
    markers = discover_story_markers(tmp_path)
    assert "beta" in markers
    assert markers["beta"].story_hash is None


def test_discover_ignores_non_story_markers(tmp_path: Path):
    src = _test_module(
        '@pytest.mark.slow\ndef test_slow():\n    assert True',
        '@pytest.mark.parametrize("x", [1])\ndef test_p(x):\n    assert x',
    )
    _write(tmp_path / "test_c.py", src)
    assert discover_story_markers(tmp_path) == {}


def test_discover_missing_dir_returns_empty(tmp_path: Path):
    assert discover_story_markers(tmp_path / "nope") == {}


def test_discover_does_not_import_test_module(tmp_path: Path):
    # A module that explodes at import time must NOT break discovery.
    src = (
        "import pytest\n"
        "raise RuntimeError('importing this module must never happen')\n\n"
        + _marked("gamma", "deadbeef", "test_gamma")
    )
    _write(tmp_path / "test_explodes.py", src)
    markers = discover_story_markers(tmp_path)
    assert markers["gamma"].story_hash == "deadbeef"


def test_discover_duplicate_story_id_is_deterministic(tmp_path: Path):
    # Two files claim the same id; first by sorted file path wins.
    _write(tmp_path / "test_a.py", _test_module(_marked("dup", "hashA", "test_a")))
    _write(tmp_path / "test_b.py", _test_module(_marked("dup", "hashB", "test_b")))
    markers = discover_story_markers(tmp_path)
    assert markers["dup"].story_hash == "hashA"
    assert markers["dup"].test_file.endswith("test_a.py")


# --------------------------------------------------------------------------- #
# classify_story
# --------------------------------------------------------------------------- #

def test_classify_missing_when_no_marker(tmp_path: Path):
    story = _write(tmp_path / "story__x.md", FRESH_STORY)
    result = classify_story(story, {})
    assert result.status == STATUS_STORY_REGRESSION_MISSING
    assert result.recorded_hash is None
    assert result.test_file is None
    assert result.current_hash == _story_content_hash(FRESH_STORY)


def test_classify_stale_on_hash_mismatch(tmp_path: Path):
    story = _write(tmp_path / "story__x.md", FRESH_STORY)
    markers = {"x": srg.StoryMarker("x", "staleHASH00000000", "t.py", "test_x", 1)}
    result = classify_story(story, markers)
    assert result.status == STATUS_STORY_REGRESSION_STALE
    assert result.recorded_hash == "staleHASH00000000"


def test_classify_stale_when_no_recorded_hash(tmp_path: Path):
    story = _write(tmp_path / "story__x.md", FRESH_STORY)
    markers = {"x": srg.StoryMarker("x", None, "t.py", "test_x", 1)}
    result = classify_story(story, markers)
    assert result.status == STATUS_STORY_REGRESSION_STALE
    assert "no story_hash" in result.detail


def test_classify_ok_when_hash_matches(tmp_path: Path):
    story = _write(tmp_path / "story__x.md", FRESH_STORY)
    current = _story_content_hash(FRESH_STORY)
    markers = {"x": srg.StoryMarker("x", current, "t.py", "test_x", 1)}
    result = classify_story(story, markers)
    assert result.status == STATUS_STORY_REGRESSION_OK
    assert result.recorded_hash == current


def test_metadata_only_edit_is_not_stale(tmp_path: Path):
    # Adding only a pdd-story-prompts metadata comment must NOT change the hash.
    base = FRESH_STORY
    with_meta = "<!-- pdd-story-prompts: prompts/refund_python.prompt -->\n" + FRESH_STORY
    current = _story_content_hash(base)
    markers = {"x": srg.StoryMarker("x", current, "t.py", "test_x", 1)}
    story = _write(tmp_path / "story__x.md", with_meta)
    result = classify_story(story, markers)
    assert result.status == STATUS_STORY_REGRESSION_OK


# --------------------------------------------------------------------------- #
# evaluate_stories
# --------------------------------------------------------------------------- #

def test_evaluate_classifies_all_sorted(fixture_tree):
    _root, stories, tests = fixture_tree
    results = evaluate_stories(stories_dir=str(stories), tests_dir=str(tests))
    by_id = {r.story_id: r.status for r in results}
    assert [r.story_id for r in results] == ["checkout", "export", "refund"]
    assert by_id["refund"] == STATUS_STORY_REGRESSION_OK
    assert by_id["checkout"] == STATUS_STORY_REGRESSION_STALE
    assert by_id["export"] == STATUS_STORY_REGRESSION_MISSING


def test_evaluate_only_story_ids_scopes(fixture_tree):
    _root, stories, tests = fixture_tree
    results = evaluate_stories(
        stories_dir=str(stories), tests_dir=str(tests), only_story_ids=["export"]
    )
    assert [r.story_id for r in results] == ["export"]
    assert results[0].status == STATUS_STORY_REGRESSION_MISSING


# --------------------------------------------------------------------------- #
# changed_story_ids (offline git)
# --------------------------------------------------------------------------- #

def _git(repo: Path, *args: str) -> None:
    subprocess.run(
        ["git", "-C", str(repo), *args],
        check=True,
        capture_output=True,
        text=True,
    )


@pytest.mark.skipif(shutil.which("git") is None, reason="git not installed")
def test_changed_story_ids_detects_new_story(tmp_path: Path):
    repo = tmp_path / "repo"
    repo.mkdir()
    _git(repo, "init", "-q")
    _git(repo, "config", "user.email", "t@example.com")
    _git(repo, "config", "user.name", "t")
    _write(repo / "README.md", "base\n")
    _git(repo, "add", "-A")
    _git(repo, "commit", "-qm", "base")
    _git(repo, "branch", "-M", "main")
    # New, uncommitted story file in the working tree.
    _write(repo / "user_stories" / "story__newfeature.md", "# new\n")
    ids = changed_story_ids(repo, base_ref="main")
    assert ids is not None
    assert "newfeature" in ids


def test_changed_story_ids_returns_none_without_git_repo(tmp_path: Path):
    # Not a git repo and no base resolves -> scope unknown -> None.
    assert changed_story_ids(tmp_path) is None


# --------------------------------------------------------------------------- #
# config + mode resolution
# --------------------------------------------------------------------------- #

def test_config_default_is_warn(tmp_path: Path):
    assert load_story_regression_gate_config(tmp_path) == "warn"


def _write_pyproject(root: Path, value: str) -> None:
    _write(
        root / "pyproject.toml",
        f'[tool.pdd.checkup]\nstory_regression_gate = {value}\n',
    )


def test_config_reads_pyproject(tmp_path: Path):
    _write_pyproject(tmp_path, '"strict"')
    assert load_story_regression_gate_config(tmp_path) == "strict"


def test_config_boolean_false_is_off(tmp_path: Path):
    _write_pyproject(tmp_path, "false")
    assert load_story_regression_gate_config(tmp_path) == "off"


def test_config_boolean_true_ignored_defaults_warn(tmp_path: Path):
    _write_pyproject(tmp_path, "true")
    assert load_story_regression_gate_config(tmp_path) == "warn"


def test_config_unknown_value_ignored(tmp_path: Path):
    _write_pyproject(tmp_path, '"banana"')
    assert load_story_regression_gate_config(tmp_path) == "warn"


def test_resolve_disabled_is_off(tmp_path: Path):
    assert resolve_story_regression_gate_mode(disabled=True, project_root=tmp_path) == "off"


def test_resolve_cli_override_wins(tmp_path: Path):
    _write_pyproject(tmp_path, '"off"')
    assert (
        resolve_story_regression_gate_mode(cli_override="strict", project_root=tmp_path)
        == "strict"
    )


def test_resolve_invalid_cli_override_raises(tmp_path: Path):
    with pytest.raises(click.BadParameter):
        resolve_story_regression_gate_mode(cli_override="banana", project_root=tmp_path)


def test_resolve_falls_back_to_config(tmp_path: Path):
    _write_pyproject(tmp_path, '"strict"')
    assert resolve_story_regression_gate_mode(project_root=tmp_path) == "strict"


# --------------------------------------------------------------------------- #
# run_story_regression_gate
# --------------------------------------------------------------------------- #

def test_gate_off_skips_all_work(fixture_tree):
    root, stories, tests = fixture_tree
    result = run_story_regression_gate(
        project_root=root, mode="off", stories_dir=str(stories), tests_dir=str(tests)
    )
    assert isinstance(result, StoryRegressionGateResult)
    assert result.mode == "off"
    assert result.ok is True
    assert result.exit_code == 0
    assert result.results == ()


def test_gate_warn_reports_but_passes(fixture_tree):
    root, stories, tests = fixture_tree
    result = run_story_regression_gate(
        project_root=root,
        mode="warn",
        stories_dir=str(stories),
        tests_dir=str(tests),
        scope_to_diff=False,
    )
    assert result.ok is True
    assert result.exit_code == 0
    assert sorted(r.story_id for r in result.offending) == ["checkout", "export"]


def test_gate_strict_fails_on_offending(fixture_tree):
    root, stories, tests = fixture_tree
    result = run_story_regression_gate(
        project_root=root,
        mode="strict",
        stories_dir=str(stories),
        tests_dir=str(tests),
        scope_to_diff=False,
    )
    assert result.ok is False
    assert result.exit_code == 2
    assert sorted(r.story_id for r in result.offending) == ["checkout", "export"]


def test_gate_strict_passes_when_all_fresh(tmp_path: Path):
    stories = tmp_path / "user_stories"
    tests = tmp_path / "tests"
    _write(stories / "story__refund.md", FRESH_STORY)
    _write(
        tests / "test_ok.py",
        _test_module(_marked("refund", _story_content_hash(FRESH_STORY), "test_refund")),
    )
    result = run_story_regression_gate(
        project_root=tmp_path,
        mode="strict",
        stories_dir=str(stories),
        tests_dir=str(tests),
        scope_to_diff=False,
    )
    assert result.ok is True
    assert result.exit_code == 0
    assert result.offending == ()


# --------------------------------------------------------------------------- #
# determinism / public-safe
# --------------------------------------------------------------------------- #

def test_gate_decision_is_deterministic_without_secrets(fixture_tree, monkeypatch):
    root, stories, tests = fixture_tree
    for key in ("ANTHROPIC_API_KEY", "OPENAI_API_KEY", "PDD_CLOUD_API_KEY", "GEMINI_API_KEY"):
        monkeypatch.delenv(key, raising=False)

    def _run():
        return run_story_regression_gate(
            project_root=root,
            mode="strict",
            stories_dir=str(stories),
            tests_dir=str(tests),
            scope_to_diff=False,
        )

    first = _run()
    second = _run()
    assert first.ok == second.ok == False
    assert first.exit_code == second.exit_code == 2
    assert [r.status for r in first.results] == [r.status for r in second.results]
