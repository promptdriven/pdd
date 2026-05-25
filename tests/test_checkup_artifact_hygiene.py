"""Regression tests for checkup-run artifact hygiene.

Step 6a of the agentic checkup for issue #1116 removed an untracked
empty ``new_file.txt`` left in the repo root by an earlier checkup run on
an unrelated issue. The artifact would reappear in ``git status`` and
clutter PR reviews. These tests pin the invariant that the worktree root
does not carry stray empty placeholder files.
"""
from __future__ import annotations

from pathlib import Path

import pytest


REPO_ROOT = Path(__file__).resolve().parent.parent

# Empty placeholder filenames that prior checkup / generator runs are known
# to have leaked into the worktree root. Keep this list short — each entry
# is a concrete artifact we have observed and explicitly do not want.
KNOWN_STRAY_ARTIFACTS = ("new_file.txt",)


@pytest.mark.parametrize("artifact_name", KNOWN_STRAY_ARTIFACTS)
def test_no_stray_artifact_at_repo_root(artifact_name: str) -> None:
    """The worktree root must not contain known stray checkup artifacts."""
    artifact = REPO_ROOT / artifact_name
    assert not artifact.exists(), (
        f"Stray checkup artifact found at repo root: {artifact}. "
        "Remove it — see issue #1116 step 6a."
    )


def test_no_empty_top_level_txt_artifacts() -> None:
    """No zero-byte ``*.txt`` files should sit at the worktree root.

    The empty ``new_file.txt`` artifact had size 0. Catching the broader
    empty-``.txt``-at-root pattern protects against the same class of
    leftover without forbidding legitimate documentation files.
    """
    offenders = [
        path
        for path in REPO_ROOT.glob("*.txt")
        if path.is_file() and path.stat().st_size == 0
    ]
    assert not offenders, (
        "Empty *.txt files found at repo root (likely stray checkup "
        f"artifacts): {[str(p) for p in offenders]}"
    )
