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
    discover_all_story_markers,
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


def test_discover_all_keeps_every_claim(tmp_path: Path):
    # discover_story_markers collapses to first-wins; discover_all keeps both.
    _write(tmp_path / "test_a.py", _test_module(_marked("dup", "hashA", "test_a")))
    _write(tmp_path / "test_b.py", _test_module(_marked("dup", "hashB", "test_b")))
    all_markers = discover_all_story_markers(tmp_path)
    assert [m.story_hash for m in all_markers["dup"]] == ["hashA", "hashB"]


def test_evaluate_stale_duplicate_does_not_shadow_fresh(tmp_path: Path):
    """A story claimed by two tests — one stale, one fresh — is OK. A stale
    duplicate marker must not shadow a fresh sibling (regression for pdd#1857 G1,
    where a per-flow file's stale hash shadowed the fresh top_flows marker)."""
    stories = tmp_path / "user_stories"
    tests = tmp_path / "tests"
    _write(stories / "story__refund.md", FRESH_STORY)
    fresh_hash = _story_content_hash(FRESH_STORY)
    # Sorted-first file carries a STALE hash; sorted-later file the FRESH one.
    _write(tests / "test_a_stale.py", _test_module(_marked("refund", "0000000000000000", "test_stale")))
    _write(tests / "test_b_fresh.py", _test_module(_marked("refund", fresh_hash, "test_fresh")))

    by_id = {r.story_id: r for r in evaluate_stories(stories_dir=str(stories), tests_dir=str(tests))}
    assert by_id["refund"].status == STATUS_STORY_REGRESSION_OK
    assert by_id["refund"].recorded_hash == fresh_hash


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


# --------------------------------------------------------------------------- #
# Evidence honesty (issue #1889): static presence/freshness surfaces must never
# claim a test PASSED — the gate never executes test bodies.
# --------------------------------------------------------------------------- #

def test_module_docstring_does_not_claim_it_enforces_passing():
    """The module docstring must describe presence + freshness, not passing.

    The gate is AST/static: it checks marker presence and hash freshness and
    never runs a test body, so it cannot enforce that a test *passes*.
    """
    doc = srg.__doc__ or ""
    assert "passing, non-stale executable regression test" not in doc, (
        "Docstring overclaims: gate does not execute tests / prove passing."
    )


def test_classify_ok_detail_does_not_claim_the_test_passed(tmp_path: Path):
    """A fresh matching-hash marker whose test body is ``assert False`` still
    classifies OK (presence+freshness), but the human-facing detail must NOT
    imply the test passed — pass/fail is verified separately by the story lane.
    """
    story = _write(tmp_path / "story__x.md", FRESH_STORY)
    current = _story_content_hash(FRESH_STORY)
    # Marker records a fresh hash; the *body* deliberately fails.
    markers = {"x": srg.StoryMarker("x", current, "t.py", "test_x", 1)}
    result = classify_story(story, markers)
    assert result.status == STATUS_STORY_REGRESSION_OK  # value unchanged
    detail = result.detail.lower()
    assert result.detail != "Story has a fresh regression test.", (
        "detail must be reworded so it does not imply the test passed"
    )
    assert "verified separately" in detail, (
        f"detail should point to separate pass/fail verification, got: {result.detail!r}"
    )


def test_evaluate_story_regression_status_never_says_passing(tmp_path: Path):
    """The lightweight coverage evaluator's verdict value must be presence /
    freshness neutral: the literal word 'pass' is the overclaim (#1889 Bug 2).
    Holds for both legacy hashless markers and fresh markers with failing bodies.
    """
    from pdd.story_regression import build_story_map
    from pdd.story_regression_gate import STATUS_PASSING, evaluate_story_regression

    assert "pass" not in STATUS_PASSING, (
        f"the OK/present verdict value overclaims a pass: {STATUS_PASSING!r}"
    )

    stories = tmp_path / "user_stories"
    tests = tmp_path / "tests"
    story = _write(stories / "story__x.md", FRESH_STORY)
    # Legacy hashless marker, failing body: traceability only, no pass proof.
    _write(
        tests / "test_x.py",
        _test_module(
            '@pytest.mark.story(story_id="x")\ndef test_x():\n    assert False'
        ),
    )
    smap = build_story_map(tests)
    ev = evaluate_story_regression(story, tests_dir=tests, story_map=smap)
    assert ev.status == STATUS_PASSING
    assert "pass" not in ev.status


# --------------------------------------------------------------------------- #
# pdd#1889 Bug 1: the wired evaluator must share the full gate's acceptance
# logic -- accept marker ``story_hash=`` kwargs AND module constants, over the
# content-hash UNION bundle-hash set -- so it is not wrong in BOTH directions.
# --------------------------------------------------------------------------- #


def test_evaluate_story_regression_accepts_recorded_content_hash(tmp_path: Path):
    """Direction A (false STALE): a test that records the *content* hash (the
    form the behavioral generator emits, and the form documented in the module
    docstring) must be accepted by the wired evaluator even when a contract
    makes the bundle hash differ -- exactly as the full gate accepts it."""
    from pdd.story_regression import build_story_map
    from pdd.story_regression_gate import STATUS_PASSING, evaluate_story_regression

    stories = tmp_path / "user_stories"
    contracts = stories / "contracts"
    tests = tmp_path / "tests"
    story = _write(stories / "story__refund.md", FRESH_STORY)
    # A contract makes story_bundle_hash != _story_content_hash.
    _write(contracts / "refund.contract.md", "## Oracle\n\n- Refunds are accepted.\n")
    content_hash = _story_content_hash(FRESH_STORY)
    _write(
        tests / "test_refund.py",
        _test_module(
            f'STORY_HASH = "{content_hash}"',
            '@pytest.mark.story(story_id="refund", story_hash=STORY_HASH)\n'
            "def test_refund():\n    assert True",
        ),
    )
    smap = build_story_map(tests)
    ev = evaluate_story_regression(story, tests_dir=tests, story_map=smap)
    assert ev.status == STATUS_PASSING


def test_evaluate_story_regression_fresh_wins_over_earlier_stale_in_same_file(
    tmp_path: Path,
):
    """A file with two markers for the same story -- a STALE one listed first,
    a FRESH one second -- must be reported 'present' (any-fresh-wins), matching
    the full gate. Regression guard for collapsing the recorded-hash list to
    ``found[0]``, which would re-introduce exactly the evaluator divergence this
    change eliminates (pdd#1889)."""
    from pdd.story_regression import build_story_map
    from pdd.story_regression_gate import STATUS_PASSING, evaluate_story_regression

    stories = tmp_path / "user_stories"
    tests = tmp_path / "tests"
    story = _write(stories / "story__refund.md", FRESH_STORY)
    content_hash = _story_content_hash(FRESH_STORY)
    # Stale marker FIRST (source order drives AST scan order), fresh SECOND.
    _write(
        tests / "test_refund.py",
        _test_module(
            _marked("refund", "0000000000000000", "test_refund_stale"),
            _marked("refund", content_hash, "test_refund_fresh"),
        ),
    )
    smap = build_story_map(tests)
    ev = evaluate_story_regression(story, tests_dir=tests, story_map=smap)
    assert ev.status == STATUS_PASSING


def test_evaluate_story_regression_stale_on_bogus_marker_kwarg_hash(tmp_path: Path):
    """Direction B (false PASS): a test recording only a bogus ``story_hash=``
    marker kwarg (no module constant) is genuinely stale and must be reported
    stale -- the wired evaluator must not ignore marker kwargs and fall through
    to the legacy hashless 'present' verdict."""
    from pdd.story_regression import build_story_map
    from pdd.story_regression_gate import STATUS_STALE, evaluate_story_regression

    stories = tmp_path / "user_stories"
    tests = tmp_path / "tests"
    story = _write(stories / "story__refund.md", FRESH_STORY)
    _write(
        tests / "test_refund.py",
        _test_module(_marked("refund", "0000000000000000", "test_refund")),
    )
    smap = build_story_map(tests)
    ev = evaluate_story_regression(story, tests_dir=tests, story_map=smap)
    assert ev.status == STATUS_STALE


# --------------------------------------------------------------------------- #
# pdd#1889 Bug 2: a metadata-only prompt relink must not flip the bundle hash,
# so the gate cannot falsely stale a bundle-recording test after `pdd story link`.
# --------------------------------------------------------------------------- #


def test_metadata_only_relink_does_not_flip_bundle_hash(tmp_path: Path):
    from pdd.story_regression import build_story_map
    from pdd.story_regression_gate import STATUS_PASSING, evaluate_story_regression
    from pdd.story_test_generation import story_bundle_hash

    stories = tmp_path / "user_stories"
    contracts = stories / "contracts"
    tests = tmp_path / "tests"
    story = _write(
        stories / "story__refund.md",
        FRESH_STORY + "\n<!-- pdd-story-prompts: pdd/foo.prompt -->\n",
    )
    _write(contracts / "refund.contract.md", "## Oracle\n\n- Refunds are accepted.\n")

    before = story_bundle_hash(story)
    _write(
        tests / "test_refund.py",
        _test_module(
            f'PDD_STORY_HASH = "{before}"',
            '@pytest.mark.story(story_id="refund")\n'
            "def test_refund():\n    assert True",
        ),
    )
    smap = build_story_map(tests)
    assert (
        evaluate_story_regression(story, tests_dir=tests, story_map=smap).status
        == STATUS_PASSING
    )

    # Metadata-only relink: rewrite ONLY the pdd-story-prompts comment.
    story.write_text(
        FRESH_STORY + "\n<!-- pdd-story-prompts: pdd/bar.prompt, pdd/baz.prompt -->\n",
        encoding="utf-8",
    )
    after = story_bundle_hash(story)
    assert after == before, "metadata-only relink must not change the bundle hash"
    assert (
        evaluate_story_regression(story, tests_dir=tests, story_map=smap).status
        == STATUS_PASSING
    )


# --------------------------------------------------------------------------- #
# pdd#1889 P2 robustness — gate discovery / exit safety
# --------------------------------------------------------------------------- #

def test_discover_skips_non_utf8_file_without_crashing(tmp_path: Path):
    """G-F3: a test file that is not valid UTF-8 must be skipped, not crash the
    whole scan with a UnicodeDecodeError (a ValueError, not OSError)."""
    # A latin-1 byte (0xe9 = 'é') that is invalid UTF-8.
    (tmp_path / "test_latin1.py").write_bytes(
        b"# caf\xe9 latin-1\ndef test_x():\n    pass\n"
    )
    _write(tmp_path / "test_ok.py", _test_module(_marked("alpha", "abc123", "test_alpha")))
    # Must not raise; the readable marker is still discovered.
    markers = discover_story_markers(tmp_path)
    assert set(markers) == {"alpha"}
    all_markers = discover_all_story_markers(tmp_path)
    assert set(all_markers) == {"alpha"}


def test_evaluate_survives_non_utf8_test_file(tmp_path: Path):
    """G-F3 end-to-end: evaluate_stories must return a verdict even when an
    undecodable test file lives in the tests dir."""
    stories = tmp_path / "user_stories"
    tests = tmp_path / "tests"
    _write(stories / "story__refund.md", FRESH_STORY)
    tests.mkdir(parents=True, exist_ok=True)
    (tests / "test_latin1.py").write_bytes(
        b"# caf\xe9 latin-1\ndef test_x():\n    pass\n"
    )
    fresh = _story_content_hash(FRESH_STORY)
    _write(tests / "test_ok.py", _test_module(_marked("refund", fresh, "test_refund")))
    results = evaluate_stories(stories_dir=str(stories), tests_dir=str(tests))
    by_id = {r.story_id: r.status for r in results}
    assert by_id["refund"] == STATUS_STORY_REGRESSION_OK


def test_discover_finds_class_level_story_marker(tmp_path: Path):
    """G-F4: a @pytest.mark.story on a test CLASS (propagates to its methods)
    must be discovered, not reported missing."""
    src = (
        "import pytest\n\n"
        '@pytest.mark.story(story_id="clsflow", story_hash="clshash00")\n'
        "class TestClsFlow:\n"
        "    def test_one(self):\n"
        "        assert True\n"
    )
    _write(tmp_path / "test_cls.py", src)
    markers = discover_story_markers(tmp_path)
    assert "clsflow" in markers
    assert markers["clsflow"].story_hash == "clshash00"


def test_discover_finds_module_level_pytestmark_story(tmp_path: Path):
    """G-F4: a module-level ``pytestmark = pytest.mark.story(...)`` claims every
    test in the module and must be discovered."""
    src = (
        "import pytest\n\n"
        'pytestmark = pytest.mark.story(story_id="modflow", story_hash="modhash00")\n\n'
        "def test_one():\n    assert True\n"
    )
    _write(tmp_path / "test_mod.py", src)
    markers = discover_story_markers(tmp_path)
    assert "modflow" in markers
    assert markers["modflow"].story_hash == "modhash00"


def test_evaluate_discovers_nested_story(tmp_path: Path):
    """G-F5 (gate side): a story in a nested subdir must be discovered by the
    gate the same way the coverage path (rglob) already sees it."""
    stories = tmp_path / "user_stories"
    tests = tmp_path / "tests"
    _write(stories / "nested" / "story__baz.md", FRESH_STORY)
    fresh = _story_content_hash(FRESH_STORY)
    _write(tests / "test_baz.py", _test_module(_marked("baz", fresh, "test_baz")))
    results = evaluate_stories(stories_dir=str(stories), tests_dir=str(tests))
    by_id = {r.story_id: r.status for r in results}
    assert "baz" in by_id, "nested story must be discovered by the gate"
    assert by_id["baz"] == STATUS_STORY_REGRESSION_OK


def test_gate_honors_stories_dir_env_var_when_root_differs(tmp_path, monkeypatch):
    """G-F7: when stories_dir is None and project_root != cwd, the gate must
    still honor PDD_USER_STORIES_DIR instead of hardcoding root/user_stories —
    otherwise strict mode passes vacuously over zero stories."""
    root = tmp_path / "project"
    alt = root / "stories_alt"
    tests = root / "tests"
    _write(alt / "story__refund.md", FRESH_STORY)
    _write(tests / "test_noop.py", "def test_noop():\n    assert True\n")

    # cwd must differ from root to trigger the buggy hardcoded branch.
    outside = tmp_path / "elsewhere"
    outside.mkdir()
    monkeypatch.chdir(outside)
    monkeypatch.setenv("PDD_USER_STORIES_DIR", "stories_alt")

    result = run_story_regression_gate(
        project_root=root, mode="strict", scope_to_diff=False
    )
    # The story has no marker -> missing -> strict must FAIL (exit 2), not pass.
    assert result.results, "gate must evaluate the env-var stories dir, not zero stories"
    assert result.ok is False
    assert result.exit_code == 2
