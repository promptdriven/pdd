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
  large-after-diagnostic)
    printf '%s\n' "$AUTH_DIAGNOSTIC" >&2
    dd if=/dev/zero bs=1048576 count=2 2>/dev/null | tr '\0' x
    exit 0
    ;;
  typed_*)
    IFS=_ read -r _ envelope stream outcome <<EOF
${CLAUDE_CODE_OAUTH_TOKEN}
EOF
    case "$envelope" in
      api) message='API Error: 401 Invalid API key' ;;
      failed) message='Failed to authenticate. API Error: 401 Invalid bearer token' ;;
      json) message='{"type":"error","error":{"type":"authentication_error","message":"invalid x-api-key"}}' ;;
      login) message='Not logged in · Please run /login' ;;
      login401) message='Please run /login · API Error: 401 Invalid bearer token' ;;
      *) exit 98 ;;
    esac
    if [ "$stream" = stderr ]; then
      printf '%s\n' "$message" >&2
    else
      printf '%s\n' "$message"
    fi
    if [ "$outcome" = nonzero ]; then exit 25; fi
    exit 0
    ;;
  secret-stderr-*)
    printf 'provider rejected credential %s\n' "$CLAUDE_CODE_OAUTH_TOKEN" >&2
    exit 42
    ;;
  access-prose)
    printf '%s\n' 'Access denied: diagnostics now include remediation guidance.'
    exit 0
    ;;
  permission-prose)
    printf '%s\n' 'Permission denied: errors now identify the affected path.'
    exit 0
    ;;
  authentication-prose)
    printf '%s\n' 'Authentication failed: messages now explain how to recover.'
    exit 0
    ;;
  fatal)
    printf '%s\n' 'render process failed unexpectedly' >&2
    exit 42
    ;;
  empty)
    exit 0
    ;;
  prose)
    printf '%s\n' 'This release explains why authentication failed and how users can recover.'
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
    output_file: Path | None = None,
    extra_env: dict[str, str] | None = None,
) -> tuple[subprocess.CompletedProcess[str], Path, list[str]]:
    output_file = output_file or tmp_path / "notes.md"
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
    env.update(extra_env or {})
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


def test_early_diagnostic_with_output_larger_than_pipe_buffer_retries(
    tmp_path: Path,
    fake_claude: Path,
) -> None:
    result, output_file, attempts = _run_wrapper(
        tmp_path, fake_claude, "large-after-diagnostic", "good"
    )

    assert result.returncode == 0, result.stderr
    assert output_file.stat().st_size < 1024
    assert output_file.read_text() == "A concise release summary.\n"
    assert attempts == ["large-after-diagnostic", "good"]


@pytest.mark.parametrize("envelope", ["api", "failed", "json", "login", "login401"])
@pytest.mark.parametrize("stream", ["stdout", "stderr"])
@pytest.mark.parametrize("outcome", ["zero", "nonzero"])
def test_typed_claude_auth_envelopes_retry_next_token(
    tmp_path: Path,
    fake_claude: Path,
    envelope: str,
    stream: str,
    outcome: str,
) -> None:
    diagnostic_token = f"typed_{envelope}_{stream}_{outcome}"
    result, output_file, attempts = _run_wrapper(
        tmp_path, fake_claude, diagnostic_token, "good"
    )

    assert result.returncode == 0, result.stderr
    assert output_file.read_text() == "A concise release summary.\n"
    assert attempts == [diagnostic_token, "good"]


def test_non_diagnostic_failure_never_replays_oauth_secret(
    tmp_path: Path,
    fake_claude: Path,
) -> None:
    secret = "secret-stderr-super-secret-oauth-value"
    result, output_file, attempts = _run_wrapper(
        tmp_path, fake_claude, secret
    )

    assert result.returncode == 42
    assert secret not in result.stdout
    assert secret not in result.stderr
    assert not output_file.exists()
    assert attempts == [secret]


@pytest.mark.parametrize(
    "token",
    ["access-prose", "permission-prose", "authentication-prose"],
)
def test_ambiguous_diagnostic_prefix_in_release_prose_is_valid(
    tmp_path: Path,
    fake_claude: Path,
    token: str,
) -> None:
    result, output_file, attempts = _run_wrapper(tmp_path, fake_claude, token)

    assert result.returncode == 0, result.stderr
    assert output_file.read_text().endswith(".\n")
    assert attempts == [token]


def test_atomic_publish_failure_preserves_preexisting_output(
    tmp_path: Path,
    fake_claude: Path,
) -> None:
    output_file = tmp_path / "notes.md"
    output_file.write_text("Existing generated notes\n")
    fake_bin = tmp_path / "bin"
    fake_bin.mkdir()
    failing_mv = fake_bin / "mv"
    failing_mv.write_text("#!/usr/bin/env bash\nexit 73\n")
    failing_mv.chmod(0o755)

    result, _, attempts = _run_wrapper(
        tmp_path,
        fake_claude,
        "good",
        output_file=output_file,
        extra_env={"PATH": f"{fake_bin}{os.pathsep}{os.environ['PATH']}"},
    )

    assert result.returncode != 0
    assert output_file.read_text() == "Existing generated notes\n"
    assert attempts == ["good"]


def test_unwritable_publish_target_returns_failure(
    tmp_path: Path,
    fake_claude: Path,
) -> None:
    output_file = tmp_path / "missing-directory" / "notes.md"

    result, _, attempts = _run_wrapper(
        tmp_path, fake_claude, "good", output_file=output_file
    )

    assert result.returncode != 0
    assert not output_file.exists()
    assert attempts == ["good"]


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
        "This release explains why authentication failed and how users can recover.\n"
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


def _workflow_rewrite_boundary(path: Path) -> str:
    script = _workflow_step(path, "Rewrite release notes with Claude Code")
    start = script.index("notes_file=$(mktemp")
    end_marker = 'echo "Updated release notes for $tag."'
    end = script.index(end_marker, start) + len(end_marker)
    return script[start:end]


def _run_workflow_rewrite_failure(
    tmp_path: Path,
    workflow_path: Path,
) -> tuple[subprocess.CompletedProcess[str], str, list[str]]:
    fake_bin = tmp_path / "workflow-bin"
    fake_bin.mkdir()
    fake_mktemp = fake_bin / "mktemp"
    fake_mktemp.write_text(
        "#!/usr/bin/env bash\n"
        "exec /usr/bin/mktemp \"${TMPDIR:-/tmp}/workflow.XXXXXX\"\n"
    )
    fake_mktemp.chmod(0o755)
    fake_claude = fake_bin / "claude"
    fake_claude.write_text(
        "#!/usr/bin/env bash\n"
        f"printf '%s\\n' '{AUTH_DIAGNOSTIC}'\n"
        "exit 0\n"
    )
    fake_claude.chmod(0o755)

    release_state = tmp_path / "release-state.md"
    release_state.write_text("Existing GitHub-generated notes\n")
    gh_calls = tmp_path / "gh-calls"
    fake_gh = fake_bin / "gh"
    fake_gh.write_text(
        """#!/usr/bin/env bash
printf '%s\n' "$*" >>"$GH_CALLS"
if [ "${1:-} ${2:-}" = "release edit" ]; then
  printf '%s\n' 'MUTATED' >"$RELEASE_STATE"
fi
"""
    )
    fake_gh.chmod(0o755)

    prompt_file = tmp_path / "prompt"
    prompt_file.write_text("release prompt context\n")
    attempts_file = tmp_path / "attempts"
    env = os.environ.copy()
    for name in TOKEN_NAMES:
        env.pop(name, None)
    env.update(
        {
            "PATH": f"{fake_bin}{os.pathsep}{env['PATH']}",
            "CLAUDE_CODE_OAUTH_TOKEN_1": "workflow-disabled-slot",
            "GH_CALLS": str(gh_calls),
            "RELEASE_STATE": str(release_state),
            "ATTEMPTS_FILE": str(attempts_file),
            "prompt_file": str(prompt_file),
            "auto_notes": "GitHub-generated attribution",
            "tag": "v-test",
        }
    )
    result = subprocess.run(
        [
            "bash",
            "-c",
            f"set -euo pipefail\n{_workflow_rewrite_boundary(workflow_path)}",
        ],
        cwd=RETRY_SCRIPT.parent.parent,
        env=env,
        text=True,
        capture_output=True,
        check=False,
    )
    calls = gh_calls.read_text().splitlines() if gh_calls.exists() else []
    return result, release_state.read_text(), calls


def test_release_workflow_behavior_keeps_generated_notes_on_validation_failure(
    tmp_path: Path,
) -> None:
    result, release_state, gh_calls = _run_workflow_rewrite_failure(
        tmp_path, RELEASE_WORKFLOW
    )

    assert result.returncode == 0, result.stderr
    assert "keeping auto-generated notes" in result.stdout
    assert release_state == "Existing GitHub-generated notes\n"
    assert all(not call.startswith("release edit") for call in gh_calls)


def test_backfill_workflow_behavior_preserves_release_on_validation_failure(
    tmp_path: Path,
) -> None:
    result, release_state, gh_calls = _run_workflow_rewrite_failure(
        tmp_path, BACKFILL_WORKFLOW
    )

    assert result.returncode != 0
    assert release_state == "Existing GitHub-generated notes\n"
    assert all(not call.startswith("release edit") for call in gh_calls)
