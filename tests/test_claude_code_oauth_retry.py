"""Regression coverage for the release-note Claude OAuth retry boundary."""

from __future__ import annotations

import os
import subprocess
from pathlib import Path

import pytest
import yaml


RETRY_SCRIPT = Path("scripts/claude_code_oauth_retry.sh").resolve()
RELEASE_WORKFLOW = Path(".github/workflows/release.yml")
BACKFILL_WORKFLOW = Path(".github/workflows/backfill-release-notes.yml")
AUTH_DIAGNOSTIC = (
    "Your organization has disabled Claude subscription access for Claude Code."
)
TOKEN_NAMES = (
    "CLAUDE_CODE_OAUTH_TOKEN_1",
    "CLAUDE_CODE_OAUTH_TOKEN_2",
    "CLAUDE_CODE_OAUTH_TOKEN_3",
    "CLAUDE_CODE_OAUTH_TOKEN",
)


@pytest.fixture
def fake_claude(tmp_path: Path) -> Path:
    command = tmp_path / "fake-claude"
    command.write_text(
        """#!/usr/bin/env bash
set -u
printf '%s\n' "${CLAUDE_CODE_OAUTH_TOKEN:-no-token}" >>"$ATTEMPTS_FILE"
case "${CLAUDE_CODE_OAUTH_TOKEN:-no-token}" in
  zero-stdout)
    printf '%s\n' "$AUTH_DIAGNOSTIC"
    exit 0
    ;;
  zero-stderr)
    printf '%s\n' 'These notes must not be accepted.'
    printf '%s\n' "$AUTH_DIAGNOSTIC" >&2
    exit 0
    ;;
  nonzero-stdout)
    printf '%s\n' 'Authentication failed: expired credential'
    exit 23
    ;;
  nonzero-stderr)
    printf '%s\n' 'quota exceeded' >&2
    exit 24
    ;;
  fatal)
    printf '%s\n' 'render process failed unexpectedly' >&2
    exit 42
    ;;
  empty)
    exit 0
    ;;
  prose)
    printf '%s\n' 'This release improves authentication failure messages for users.'
    exit 0
    ;;
  good|no-token)
    printf '%s\n' 'A concise release summary.'
    exit 0
    ;;
  *)
    printf '%s\n' 'unexpected test token slot' >&2
    exit 99
    ;;
esac
"""
    )
    command.chmod(0o755)
    return command


def _run_wrapper(
    tmp_path: Path,
    fake_claude: Path,
    *tokens: str,
) -> tuple[subprocess.CompletedProcess[str], Path, list[str]]:
    output_file = tmp_path / "notes.md"
    attempts_file = tmp_path / "attempts"
    env = os.environ.copy()
    for name in TOKEN_NAMES:
        env.pop(name, None)
    env.update(
        {
            "ATTEMPTS_FILE": str(attempts_file),
            "AUTH_DIAGNOSTIC": AUTH_DIAGNOSTIC,
        }
    )
    env.update(dict(zip(TOKEN_NAMES, tokens, strict=False)))
    result = subprocess.run(
        [str(RETRY_SCRIPT), str(output_file), str(fake_claude)],
        input="release context\n",
        text=True,
        capture_output=True,
        check=False,
        env=env,
    )
    attempts = attempts_file.read_text().splitlines() if attempts_file.exists() else []
    return result, output_file, attempts


@pytest.mark.parametrize(
    "diagnostic_token",
    ["zero-stdout", "zero-stderr", "nonzero-stdout", "nonzero-stderr"],
)
def test_recognized_auth_or_quota_diagnostic_retries_next_token(
    tmp_path: Path,
    fake_claude: Path,
    diagnostic_token: str,
) -> None:
    result, output_file, attempts = _run_wrapper(
        tmp_path, fake_claude, diagnostic_token, "good"
    )

    assert result.returncode == 0, result.stderr
    assert output_file.read_text() == "A concise release summary.\n"
    assert attempts == [diagnostic_token, "good"]
    assert diagnostic_token not in result.stderr


def test_all_retryable_tokens_fail_without_returning_diagnostic_as_notes(
    tmp_path: Path,
    fake_claude: Path,
) -> None:
    result, output_file, attempts = _run_wrapper(
        tmp_path,
        fake_claude,
        "zero-stdout",
        "nonzero-stderr",
        "nonzero-stdout",
        "zero-stderr",
    )

    assert result.returncode != 0
    assert not output_file.exists() or output_file.read_text() == ""
    assert attempts == [
        "zero-stdout",
        "nonzero-stderr",
        "nonzero-stdout",
        "zero-stderr",
    ]
    assert all(token not in result.stderr for token in attempts)


def test_non_diagnostic_failure_keeps_status_and_does_not_rotate(
    tmp_path: Path,
    fake_claude: Path,
) -> None:
    result, output_file, attempts = _run_wrapper(
        tmp_path, fake_claude, "fatal", "good"
    )

    assert result.returncode == 42
    assert not output_file.exists() or output_file.read_text() == ""
    assert attempts == ["fatal"]


def test_empty_success_is_rejected(
    tmp_path: Path,
    fake_claude: Path,
) -> None:
    result, output_file, attempts = _run_wrapper(tmp_path, fake_claude, "empty", "good")

    assert result.returncode != 0
    assert not output_file.exists() or output_file.read_text() == ""
    assert attempts == ["empty"]


def test_non_diagnostic_prose_is_valid_notes(
    tmp_path: Path,
    fake_claude: Path,
) -> None:
    result, output_file, attempts = _run_wrapper(tmp_path, fake_claude, "prose")

    assert result.returncode == 0, result.stderr
    assert output_file.read_text() == (
        "This release improves authentication failure messages for users.\n"
    )
    assert attempts == ["prose"]


def test_no_configured_token_preserves_direct_command_fallback(
    tmp_path: Path,
    fake_claude: Path,
) -> None:
    result, output_file, attempts = _run_wrapper(tmp_path, fake_claude)

    assert result.returncode == 0, result.stderr
    assert output_file.read_text() == "A concise release summary.\n"
    assert attempts == ["no-token"]


def _workflow_step(path: Path, name: str) -> str:
    workflow = yaml.safe_load(path.read_text())
    jobs = workflow["jobs"]
    for job in jobs.values():
        for step in job.get("steps", []):
            if step.get("name") == name:
                return step["run"]
    raise AssertionError(f"Missing workflow step {name!r} in {path}")


def test_release_workflow_keeps_generated_notes_when_validation_fails() -> None:
    script = _workflow_step(RELEASE_WORKFLOW, "Rewrite release notes with Claude Code")
    wrapper_call = script.index("scripts/claude_code_oauth_retry.sh")
    safe_fallback = script.index("keeping auto-generated notes", wrapper_call)
    release_edit = script.index("gh release edit", safe_fallback)

    assert "if ! scripts/claude_code_oauth_retry.sh" in script
    assert wrapper_call < safe_fallback < release_edit


def test_backfill_workflow_does_not_edit_release_after_validation_failure() -> None:
    script = _workflow_step(
        BACKFILL_WORKFLOW, "Rewrite release notes with Claude Code"
    )
    wrapper_call = script.index("scripts/claude_code_oauth_retry.sh")
    release_edit = script.index("gh release edit", wrapper_call)

    assert "set -euo pipefail" in script
    assert wrapper_call < release_edit
