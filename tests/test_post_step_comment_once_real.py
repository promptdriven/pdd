"""Real-LLM / real-network test for ``post_step_comment_once``.

This test actually shells out to ``gh issue comment`` to post a real
comment on a real GitHub issue, then deletes it. Skipped by default;
to run:

    PDD_RUN_REAL_LLM_TESTS=1 PDD_REAL_GH_ISSUE_URL=https://github.com/<owner>/<repo>/issues/<N> \\
        pytest tests/test_post_step_comment_once_real.py -m real

Requires ``gh`` CLI on PATH and ``GH_TOKEN`` / authenticated session.
"""
from __future__ import annotations

import os
import re
import subprocess
from pathlib import Path

import pytest


_REAL_FLAG = os.environ.get("PDD_RUN_REAL_LLM_TESTS") == "1"
_REAL_URL = os.environ.get("PDD_REAL_GH_ISSUE_URL", "")

_URL_RE = re.compile(
    r"https://github\.com/(?P<owner>[^/]+)/(?P<repo>[^/]+)/issues/(?P<num>\d+)"
)


def _parse_url(url: str):
    m = _URL_RE.match(url)
    if not m:
        return None
    return m.group("owner"), m.group("repo"), int(m.group("num"))


def _gh_on_path() -> bool:
    try:
        return subprocess.run(
            ["which", "gh"], capture_output=True, text=True
        ).returncode == 0
    except (FileNotFoundError, OSError):
        return False


@pytest.mark.real
@pytest.mark.skipif(
    not _REAL_FLAG,
    reason="real-network test gated by PDD_RUN_REAL_LLM_TESTS=1",
)
@pytest.mark.skipif(
    not _REAL_URL,
    reason="requires PDD_REAL_GH_ISSUE_URL to point at a writable issue",
)
@pytest.mark.skipif(not _gh_on_path(), reason="gh CLI not on PATH")
def test_real_post_step_comment_once_round_trip(tmp_path: Path) -> None:
    """Post a real comment, find it, delete it. End-to-end."""
    parsed = _parse_url(_REAL_URL)
    if parsed is None:
        pytest.skip(f"PDD_REAL_GH_ISSUE_URL not a valid issue URL: {_REAL_URL!r}")
    owner, repo, issue_number = parsed

    from pdd.agentic_common import post_step_comment_once

    posted_steps: set = set()
    body = "## Trusted-comment helper round-trip test\n\nIf you see this, the helper works. (Auto-deletion follows.)"

    result = post_step_comment_once(
        repo_owner=owner,
        repo_name=repo,
        issue_number=issue_number,
        step_num=999_999,
        body=body,
        posted_steps=posted_steps,
        cwd=tmp_path,
    )

    assert result is True, "post_step_comment_once returned False on real post"
    assert 999_999 in posted_steps

    # Idempotency: a second call with the same step_num is a no-op.
    result_again = post_step_comment_once(
        repo_owner=owner,
        repo_name=repo,
        issue_number=issue_number,
        step_num=999_999,
        body="DIFFERENT BODY — should not be posted",
        posted_steps=posted_steps,
        cwd=tmp_path,
    )
    assert result_again is True

    # Discover the comment we just posted and delete it. We look at the
    # most recent issue comments and find ours by body prefix.
    list_proc = subprocess.run(
        [
            "gh", "api",
            f"repos/{owner}/{repo}/issues/{issue_number}/comments",
            "--paginate",
            "-q",
            ".[] | select(.body | startswith(\"## Trusted-comment helper\")) | .id",
        ],
        capture_output=True,
        text=True,
    )
    if list_proc.returncode != 0:
        pytest.fail(
            f"Failed to list comments for cleanup: rc={list_proc.returncode} "
            f"stderr={list_proc.stderr!r}"
        )
    comment_ids = [line.strip() for line in list_proc.stdout.splitlines() if line.strip()]
    assert comment_ids, "Expected at least one matching comment to delete"

    for cid in comment_ids:
        subprocess.run(
            [
                "gh", "api",
                f"repos/{owner}/{repo}/issues/comments/{cid}",
                "-X", "DELETE",
            ],
            capture_output=True,
            text=True,
            check=False,
        )
