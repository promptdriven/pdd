"""Mocked end-to-end tests for agentic sync (`pdd sync <issue-url>`).

Unlike the unit suites (which patch ``run_agentic_task`` / ``AsyncSyncRunner``
in-process), these tests run the REAL CLI entry point as a subprocess and let
the full pipeline execute: issue fetch -> LLM module identification ->
dependency graph -> dry-run validation children -> fingerprint filter ->
runner/resume. Nothing is patched in-process; instead every external binary
the pipeline shells out to (``claude``, ``gh``, ``pdd`` children, and the
never-expected ``codex``/``gemini``/``agy``/``opencode``) is replaced by a
shim placed first on a restricted ``PATH``.

Billing safety (the whole point of this file):
  - subprocess env is built from scratch: no inherited API keys or tokens
  - ``HOME`` points at an empty temp dir: hides ``~/.codex/auth.json``,
    ``~/.gemini`` OAuth, litellm key files, and any real ``~/.pdd``
  - restricted ``PATH``: only the shim dir plus system dirs, so real
    ``claude``/``codex``/``gemini``/``gh`` binaries are unreachable
  - ``PDD_FORCE_LOCAL=1`` disables PDD-cloud endpoints and auto-submit
  - ``PDD_AGENTIC_PROVIDER=anthropic`` pins provider selection to the shim
  - tripwire shims fail loudly (exit 86) if any other provider is invoked

This covers the gap that no test exercised CLI -> run_agentic_sync ->
AsyncSyncRunner -> real child ``pdd sync`` subprocesses end to end.
"""

import json
import os
import shutil
import subprocess
import sys
import textwrap
from pathlib import Path

import pytest

pytestmark = [
    pytest.mark.timeout(600),
    pytest.mark.skipif(sys.platform == "win32", reason="POSIX shell shims"),
]

ISSUE_URL = "https://github.com/e2e-org/greeter-proj/issues/7"
REPO_ROOT = Path(__file__).resolve().parents[1]


def _is_relative_to(path: Path, parent: Path) -> bool:
    try:
        path.relative_to(parent)
        return True
    except ValueError:
        return False


# ---------------------------------------------------------------------------
# Harness construction
# ---------------------------------------------------------------------------

CLAUDE_SHIM = """#!/bin/sh
# Mock `claude` CLI. Speaks the protocol pdd/agentic_common.py expects:
#   claude -p - --dangerously-skip-permissions --output-format json
LOG_DIR="$E2E_LOG_DIR"
printf 'argv: %s\\n' "$*" >> "$LOG_DIR/claude_calls.log"
case "$1" in
  --version|-v) echo "1.0.0-mock"; exit 0;;
esac
PROMPT=$(cat)
printf '%s' "$PROMPT" > "$LOG_DIR/claude_prompt_$$.txt"
if [ "$CLAUDE_SHIM_MODE" = "fail" ]; then
  {PYTHON} -c 'import json; print(json.dumps({{"type": "result", "is_error": True, "result": "Mock provider failure injected for failure-path testing.", "total_cost_usd": 0.0}}))'
  exit 0
fi
if printf '%s' "$PROMPT" | grep -q "MODULES_TO_SYNC"; then
  RESULT='Analysis complete. The issue requests the greeter feature, which maps to greeter and its dependency textutil in architecture.json.

MODULES_TO_SYNC: ["greeter", "textutil"]
DEPS_VALID: true
DEPS_CORRECTIONS: []'
else
  RESULT='Mock agentic task completed successfully; no changes were required for this step. STATUS: SUCCESS'
fi
RESULT="$RESULT" {PYTHON} -c 'import json, os; print(json.dumps({{"type": "result", "subtype": "success", "is_error": False, "result": os.environ["RESULT"], "total_cost_usd": 0.0, "usage": {{"input_tokens": 512, "output_tokens": 128}}, "modelUsage": {{"claude-mock": {{}}}}}}))'
"""

GH_SHIM = """#!/bin/sh
# Mock `gh` CLI: serves the fixture issue, captures (never sends) writes.
LOG_DIR="$E2E_LOG_DIR"
ARGS="$*"
printf 'argv: %s\\n' "$ARGS" >> "$LOG_DIR/gh_calls.log"
case "$ARGS" in
  *--version*) echo "gh version 2.99.0-mock"; exit 0;;
esac
if printf '%s' "$ARGS" | grep -qE '(-X *POST|-X *PATCH|-f |--field )'; then
  printf '%s\\n' "$ARGS" >> "$LOG_DIR/gh_writes.log"
  echo '{"id": 999001, "html_url": "https://github.local/mock/comment/999001"}'
  exit 0
fi
case "$ARGS" in
  *issues/7/comments*) echo '[]'; exit 0;;
  *issues/7*) cat "$E2E_ISSUE_JSON"; exit 0;;
esac
echo '{}'
"""

TRIPWIRE_SHIM = """#!/bin/sh
echo "TRIPWIRE: {name} invoked: $*" >> "$E2E_LOG_DIR/TRIPWIRE.log"
exit 86
"""

PDD_SHIM = """#!/bin/sh
# Route child `pdd` invocations back to this test's interpreter.
printf 'pdd %s\\n' "$*" >> "$E2E_LOG_DIR/pdd_calls.log"
exec {PYTHON} -m pdd "$@"
"""


@pytest.fixture()
def harness(tmp_path):
    """Build the sandbox: shim bin dir, fake HOME, fixture project, env."""
    shim_bin = tmp_path / "shimbin"
    fake_home = tmp_path / "fakehome"
    log_dir = tmp_path / "logs"
    project = tmp_path / "project"
    for d in (shim_bin, fake_home, log_dir, project):
        d.mkdir()

    python = sys.executable
    (shim_bin / "claude").write_text(CLAUDE_SHIM.format(PYTHON=python))
    (shim_bin / "gh").write_text(GH_SHIM)
    (shim_bin / "pdd").write_text(PDD_SHIM.format(PYTHON=python))
    for name in ("codex", "gemini", "agy", "opencode"):
        (shim_bin / name).write_text(TRIPWIRE_SHIM.format(name=name))
    for f in shim_bin.iterdir():
        f.chmod(0o755)

    (fake_home / ".gitconfig").write_text(
        "[user]\n\tname = E2E Test\n\temail = e2e@test.local\n"
        "[init]\n\tdefaultBranch = main\n"
    )

    issue_json = tmp_path / "issue.json"
    issue_json.write_text(json.dumps({
        "number": 7,
        "title": "Sync the greeter feature",
        "state": "open",
        "html_url": ISSUE_URL,
        "user": {"login": "e2e-user"},
        "labels": [],
        "body": (
            "The greeter feature needs to be synchronized.\n\n"
            "FILES_MODIFIED:\n"
            "- prompts/greeter_python.prompt\n"
            "- prompts/textutil_python.prompt\n"
        ),
    }))

    # Fixture PDD project: two modules with one dependency edge.
    (project / "prompts").mkdir()
    (project / ".pddrc").write_text(textwrap.dedent("""\
        contexts:
          default:
            paths: ["**"]
            defaults:
              generate_output_path: "src/"
              test_output_path: "tests/"
              example_output_path: "examples/"
    """))
    (project / "architecture.json").write_text(json.dumps([
        {"filename": "textutil_python.prompt", "dependencies": []},
        {"filename": "greeter_python.prompt",
         "dependencies": ["textutil_python.prompt"]},
    ]))
    (project / "prompts" / "textutil_python.prompt").write_text(
        "Write a Python module `textutil` with a function "
        "`capitalize_name(name: str) -> str`.\n"
    )
    (project / "prompts" / "greeter_python.prompt").write_text(
        "Write a Python module `greeter` with a function "
        "`greet(name: str) -> str` using `capitalize_name` from `textutil`.\n"
    )

    env = {
        "PATH": f"{shim_bin}:/usr/bin:/bin:/usr/sbin:/sbin",
        "HOME": str(fake_home),
        "TMPDIR": str(tmp_path / "tmp"),
        "LANG": "en_US.UTF-8",
        "TERM": "dumb",
        "NO_COLOR": "1",
        "COLUMNS": "200",
        "E2E_LOG_DIR": str(log_dir),
        "E2E_ISSUE_JSON": str(issue_json),
        "PDD_FORCE_LOCAL": "1",
        "PDD_FORCE": "1",
        "PDD_AUTO_UPDATE": "false",
        "PDD_AGENTIC_PROVIDER": "anthropic",
        "PDD_MODULE_TIMEOUT_SECONDS": "120",
        "PDD_SUPPRESS_SETUP_REMINDER": "1",
        "LITELLM_CACHE_DISABLE": "1",
        "PYTHONUNBUFFERED": "1",
        "PYTHONPATH": str(REPO_ROOT),
    }
    (tmp_path / "tmp").mkdir()

    probe = subprocess.run(
        [
            sys.executable,
            "-c",
            (
                "import os, pathlib, pdd; "
                "print(pathlib.Path(pdd.__file__).resolve(), flush=True); "
                "os._exit(0)"
            ),
        ],
        cwd=project,
        env=env,
        capture_output=True,
        text=True,
        timeout=60,
    )
    assert probe.returncode == 0, probe.stdout + probe.stderr
    imported_pdd = Path(probe.stdout.strip()).resolve()
    assert _is_relative_to(imported_pdd, REPO_ROOT.resolve()), (
        "E2E subprocess imported pdd outside this checkout: "
        f"{imported_pdd}"
    )

    git_env = {**env, "GIT_CONFIG_GLOBAL": str(fake_home / ".gitconfig")}
    for cmd in (
        ["git", "init", "-q", "-b", "main"],
        ["git", "add", "-A"],
        ["git", "commit", "-qm", "fixture"],
        ["git", "checkout", "-qb", "work"],
    ):
        subprocess.run(cmd, cwd=project, env=git_env, check=True, timeout=60)

    class Harness:
        pass

    h = Harness()
    h.project = project
    h.log_dir = log_dir
    h.env = env
    h.git_env = git_env
    return h


def run_sync(h, *extra_args, shim_mode=None, timeout=420):
    """Invoke the real CLI entry point (`pdd sync <issue-url> ...`)."""
    env = dict(h.env)
    if shim_mode:
        env["CLAUDE_SHIM_MODE"] = shim_mode
    return subprocess.run(
        [sys.executable, "-m", "pdd", "--force", "--local",
         "sync", ISSUE_URL, "--no-steer", *extra_args],
        cwd=h.project, env=env, capture_output=True, text=True,
        timeout=timeout,
    )


def read_log(h, name):
    p = h.log_dir / name
    return p.read_text() if p.exists() else ""


def assert_no_billing(h):
    """No tripwire provider was ever invoked."""
    assert read_log(h, "TRIPWIRE.log") == "", (
        "a non-shimmed provider CLI was invoked: " + read_log(h, "TRIPWIRE.log")
    )


# ---------------------------------------------------------------------------
# Tests
# ---------------------------------------------------------------------------

def test_dry_run_pipeline_end_to_end(harness):
    """CLI -> issue fetch -> LLM identification -> dep graph -> child
    dry-run validation -> fingerprint filter -> report, hermetically."""
    result = run_sync(harness, "--dry-run", "--no-github-state")

    assert result.returncode == 0, result.stdout + result.stderr
    out = result.stdout
    assert "greeter" in out and "textutil" in out
    assert "Dry run complete" in out

    # Identification went through the claude shim exactly once.
    claude_prompts = [
        f for f in os.listdir(harness.log_dir) if f.startswith("claude_prompt_")
    ]
    assert len(claude_prompts) == 1
    prompt_text = (harness.log_dir / claude_prompts[0]).read_text()
    assert "MODULES_TO_SYNC" in prompt_text
    assert "Sync the greeter feature" in prompt_text  # issue content threaded

    # Issue was fetched via the gh shim; nothing was written to GitHub.
    assert "issues/7" in read_log(harness, "gh_calls.log")
    assert read_log(harness, "gh_writes.log") == ""

    # Real child dry-run validation subprocesses ran for both modules.
    pdd_calls = read_log(harness, "pdd_calls.log")
    assert (
        "--force --local sync greeter --dry-run --agentic --no-steer"
        in pdd_calls
    )
    assert (
        "--force --local sync textutil --dry-run --agentic --no-steer"
        in pdd_calls
    )

    assert_no_billing(harness)


def test_identification_failure_posts_error_comment(harness):
    """Provider failure aborts cleanly and the error comment is captured."""
    result = run_sync(harness, shim_mode="fail")

    assert result.returncode != 0
    assert "LLM failed to identify modules" in result.stdout
    # Error comment attempted through gh (captured by the shim, not sent).
    assert "PDD Agentic Sync - Error" in read_log(harness, "gh_writes.log")
    # No partial state was left behind.
    assert not (harness.project / ".pdd" / "agentic_sync_state.json").exists()
    assert_no_billing(harness)


def test_branch_diff_detection_skips_llm(harness):
    """A prompt change on the branch is detected deterministically:
    module identification must not call any provider."""
    prompt = harness.project / "prompts" / "greeter_python.prompt"
    prompt.write_text(prompt.read_text() + "# friendlier greeting\n")
    subprocess.run(
        ["git", "commit", "-qam", "tweak greeter prompt"],
        cwd=harness.project, env=harness.git_env, check=True, timeout=60,
    )

    result = run_sync(harness, "--dry-run", "--no-github-state")

    assert result.returncode == 0, result.stdout + result.stderr
    assert "Detected modules from branch diff" in result.stdout
    assert "greeter" in result.stdout
    assert read_log(harness, "claude_calls.log") == ""  # zero provider calls
    assert_no_billing(harness)


def test_branch_diff_scope_reconciled_with_issue_named_modules(harness):
    """Issue #1980 repro (from the #1868 E2E validation): the fixture issue
    explicitly names BOTH prompts (greeter and textutil) but the work branch
    diff touches only greeter. The old fast path silently synced greeter alone,
    dropping the greeter -> textutil dependency edge while reporting Success.
    The reconciled fast path must scope both modules — still deterministically,
    with zero provider calls."""
    prompt = harness.project / "prompts" / "greeter_python.prompt"
    prompt.write_text(prompt.read_text() + "# friendlier greeting\n")
    subprocess.run(
        ["git", "commit", "-qam", "tweak greeter prompt"],
        cwd=harness.project, env=harness.git_env, check=True, timeout=60,
    )

    result = run_sync(harness, "--dry-run", "--no-github-state")

    assert result.returncode == 0, result.stdout + result.stderr
    out = result.stdout
    assert "Detected modules from branch diff" in out
    # The issue-named module missing from the diff was added, loudly.
    assert "adding them to the sync scope" in out
    assert "textutil" in out

    # BOTH modules reached real child dry-run validation subprocesses.
    pdd_calls = read_log(harness, "pdd_calls.log")
    assert (
        "--force --local sync greeter --dry-run --agentic --no-steer"
        in pdd_calls
    )
    assert (
        "--force --local sync textutil --dry-run --agentic --no-steer"
        in pdd_calls
    )

    # Still the free path: no provider was ever invoked.
    assert read_log(harness, "claude_calls.log") == ""
    assert_no_billing(harness)


def test_resume_skips_succeeded_modules(harness):
    """A state file marking every identified module as succeeded lets the
    execution phase complete without any provider or LLM call, and the
    state file is cleaned up on success."""
    # Branch-diff detection finds ['greeter']; issue-scope reconciliation
    # (#1980) adds the issue-named 'textutil' — still no LLM.
    prompt = harness.project / "prompts" / "greeter_python.prompt"
    prompt.write_text(prompt.read_text() + "# friendlier greeting\n")
    subprocess.run(
        ["git", "commit", "-qam", "tweak greeter prompt"],
        cwd=harness.project, env=harness.git_env, check=True, timeout=60,
    )

    module_state = {
        "status": "success",
        "cost": 0.0,
        "completed_phases": [],
        "current_phase": None,
        "start_time": None,
        "end_time": None,
        "error": None,
    }
    state_dir = harness.project / ".pdd"
    state_dir.mkdir()
    (state_dir / "agentic_sync_state.json").write_text(json.dumps({
        "issue_url": ISSUE_URL,
        "modules": {
            "greeter": dict(module_state),
            "textutil": dict(module_state),
        },
    }))

    result = run_sync(harness, "--no-github-state")

    assert result.returncode == 0, result.stdout + result.stderr
    assert "Resuming: skipping 2 already-succeeded module(s)" in result.stdout
    assert "All 2 modules synced successfully" in result.stdout
    # State file removed after a fully successful run.
    assert not (state_dir / "agentic_sync_state.json").exists()
    assert_no_billing(harness)
