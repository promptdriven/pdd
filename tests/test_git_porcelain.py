"""Failing tests for issue #1080 — structured git porcelain parser.

These tests target a new module ``pdd.git_porcelain`` that exposes a
structured parser for ``git status --porcelain=v1 -z`` output. Until the
module exists and behaves as specified, all tests in this file fail.

Tests 1 and 2 verify the parser handles staged renames (NUL-separated
new + old paths) and preserves paths containing spaces and quotes
verbatim. Test 12 is a regression guard for PR #1076 — it asserts that
the existing ``pdd.checkup_review_loop._git_changed_files`` helper
continues to surface BOTH sides of a staged rename as discrete entries.
"""
from __future__ import annotations

import subprocess
from pathlib import Path
from unittest.mock import patch

import pytest


# ---------------------------------------------------------------------------
# Helpers
# ---------------------------------------------------------------------------


def _completed(stdout, returncode: int = 0):
    """Build a CompletedProcess that subprocess.run mocks can return."""
    cp = subprocess.CompletedProcess(
        args=["git", "status", "--porcelain=v1", "-z"],
        returncode=returncode,
        stdout=stdout,
        stderr=b"" if isinstance(stdout, (bytes, bytearray)) else "",
    )
    return cp


# ---------------------------------------------------------------------------
# Test 1: structured porcelain parser handles staged rename (NUL-delimited)
# ---------------------------------------------------------------------------


def test_parse_porcelain_z_handles_staged_rename():
    """Parser must expose status, path, and old_path for a staged rename.

    ``git status --porcelain=v1 -z`` emits a renamed entry as the
    two-char status, a space, the NEW path, a NUL, then the OLD path,
    then a NUL. The structured parser must surface both sides.
    """
    from pdd.git_porcelain import parse_porcelain_z

    raw = b"R  prompts/new.prompt\x00prompts/old.prompt\x00 M other.py\x00"
    entries = list(parse_porcelain_z(raw))

    # Two entries: the rename and the modification.
    assert len(entries) == 2, f"expected 2 entries, got {entries!r}"

    rename = entries[0]
    modify = entries[1]

    # Behavioral access — no introspection / no key-presence reflection.
    assert rename.status == "R "
    assert rename.path == "prompts/new.prompt"
    assert rename.old_path == "prompts/old.prompt"

    assert modify.status == " M"
    assert modify.path == "other.py"
    assert modify.old_path is None


# ---------------------------------------------------------------------------
# Test 2: structured parser preserves paths with embedded spaces and quotes
# ---------------------------------------------------------------------------


def test_parse_porcelain_z_preserves_paths_with_spaces_and_quotes():
    """``-z`` output is NUL-terminated and never C-quoted; the parser
    must preserve embedded spaces and quote characters verbatim."""
    from pdd.git_porcelain import parse_porcelain_z

    raw = b'R  prompts/new name.prompt\x00prompts/old "name".prompt\x00'
    entries = list(parse_porcelain_z(raw))

    assert len(entries) == 1
    rec = entries[0]
    assert rec.path == "prompts/new name.prompt"
    assert rec.old_path == 'prompts/old "name".prompt'
    # No quoting artifacts.
    assert not rec.path.startswith('"')
    assert not rec.path.endswith('"')


# ---------------------------------------------------------------------------
# Test 12: checkup_review_loop rename regression (issue #1063 / PR #1076)
# ---------------------------------------------------------------------------


def test_checkup_review_loop_rename_regression(tmp_path, monkeypatch):
    """PR #1076 contract: ``_git_changed_files`` must surface BOTH sides
    of a staged rename as discrete entries (old + new). This must remain
    true after the structured parser migration."""
    pytest.importorskip("pdd.checkup_review_loop")
    from pdd.checkup_review_loop import _git_changed_files

    # Init a real git repo and stage a rename so we exercise the live
    # parser against real porcelain output (high fidelity).
    env = {
        "GIT_AUTHOR_NAME": "Test",
        "GIT_AUTHOR_EMAIL": "t@t",
        "GIT_COMMITTER_NAME": "Test",
        "GIT_COMMITTER_EMAIL": "t@t",
    }

    proj = tmp_path / "repo"
    proj.mkdir()
    (proj / "a.prompt").write_text("alpha")
    (proj / "b.prompt").write_text("beta")

    subprocess.run(["git", "init", str(proj)], check=True, capture_output=True, env={**__import__("os").environ, **env})
    subprocess.run(["git", "-C", str(proj), "add", "-A"], check=True, capture_output=True, env={**__import__("os").environ, **env})
    subprocess.run(
        ["git", "-C", str(proj), "commit", "-m", "initial"],
        check=True, capture_output=True, env={**__import__("os").environ, **env},
    )

    # Stage a rename
    subprocess.run(
        ["git", "-C", str(proj), "mv", "a.prompt", "a_renamed.prompt"],
        check=True, capture_output=True, env={**__import__("os").environ, **env},
    )

    changed = _git_changed_files(proj)

    # PR #1076 contract: BOTH old + new sides must be present.
    assert "a.prompt" in changed, (
        f"PR #1076 regression: old side missing from {changed!r}"
    )
    assert "a_renamed.prompt" in changed, (
        f"PR #1076 regression: new side missing from {changed!r}"
    )
    # And no fake combined literal.
    fake = "a.prompt -> a_renamed.prompt"
    assert fake not in changed, (
        f"fake combined path leaked into output: {changed!r}"
    )
