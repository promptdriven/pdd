"""
E2E tests for Issue #743: Anthropic OAuth auth failures must not be treated as
successful agentic task completions.

These tests exercise the full `run_agentic_bug_orchestrator()` workflow with the
real `run_agentic_task()` implementation. Only external boundaries are mocked:
- provider discovery / CLI lookup
- provider CLI subprocess responses

Bug on the current worktree:
- Anthropic JSON with `is_error: true` is parsed as success
- the orchestrator accepts the auth failure as a valid step result
- fallback providers are skipped, or single-provider runs advance until a later
  hard stop unrelated to the actual auth failure
"""

import json
import subprocess
from pathlib import Path
from unittest.mock import MagicMock, patch

import pytest

REAL_SUBPROCESS_RUN = subprocess.run


def _make_repo(tmp_path: Path) -> Path:
    repo_path = tmp_path / "repo"
    repo_path.mkdir()

    subprocess.run(
        ["git", "init", "-b", "main"],
        cwd=repo_path,
        check=True,
        capture_output=True,
    )
    subprocess.run(
        ["git", "config", "user.email", "test@example.com"],
        cwd=repo_path,
        check=True,
        capture_output=True,
    )
    subprocess.run(
        ["git", "config", "user.name", "Test User"],
        cwd=repo_path,
        check=True,
        capture_output=True,
    )

    (repo_path / "README.md").write_text("# Test Repo\n")
    subprocess.run(["git", "add", "."], cwd=repo_path, check=True, capture_output=True)
    subprocess.run(
        ["git", "commit", "-m", "Initial commit"],
        cwd=repo_path,
        check=True,
        capture_output=True,
    )
    return repo_path


@pytest.fixture(autouse=True)
def set_pdd_path(monkeypatch):
    import pdd

    monkeypatch.setenv("PDD_PATH", str(Path(pdd.__file__).parent))


@pytest.fixture
def git_repo(tmp_path):
    return _make_repo(tmp_path)


def _template_for_name(name: str) -> str:
    if "step1" in name:
        return "STEP1_DUPLICATE_CHECK for issue {issue_number}"
    if "step2" in name:
        return "STEP2_DOCS_CHECK uses {step1_output}"
    if "step3" in name:
        return "STEP3_TRIAGE uses {step2_output}"
    if "step4" in name:
        return "STEP4_REPRODUCE uses {step3_output}"
    if "step5_5" in name:
        return "STEP5_5_PROMPT_CLASSIFICATION uses {step5_output}"
    if "step5" in name:
        return "STEP5_ROOT_CAUSE uses {step4_output}"
    if "step6" in name:
        return "STEP6_TEST_PLAN uses {step5_5_output}"
    if "step7" in name:
        return "STEP7_GENERATE_UNIT_TEST uses {step6_output}"
    if "step8" in name:
        return "STEP8_VERIFY_UNIT_TEST uses {step7_output}"
    if "step9" in name:
        return "STEP9_GENERATE_E2E uses files {files_to_stage}"
    if "step10" in name:
        return "STEP10_CREATE_PR uses files {files_to_stage}"
    raise AssertionError(f"Unexpected template request: {name}")


def _extract_step_marker(*, cmd: list[str], cwd: Path, stdin_content: str | None) -> str:
    if stdin_content:
        prompt_text = stdin_content
    else:
        prompt_name = next(
            part.split("file ", 1)[1].split(" ", 1)[0]
            for part in cmd
            if "Read the file " in part
        )
        prompt_text = (cwd / prompt_name).read_text(encoding="utf-8")

    for line in prompt_text.splitlines():
        if line.startswith("STEP"):
            return line.split(" ", 1)[0]
    raise AssertionError(f"Could not find step marker in prompt: {prompt_text!r}")


def _google_output_for_step(step_marker: str) -> str:
    if step_marker == "STEP7_GENERATE_UNIT_TEST":
        return "Generated unit test.\nFILES_CREATED: tests/test_issue_743_unit.py"
    if step_marker == "STEP8_VERIFY_UNIT_TEST":
        return "PASS: Test catches the Anthropic OAuth failure."
    if step_marker == "STEP9_GENERATE_E2E":
        return "E2E_SKIP: Workflow-level fallback path already exercised in this regression."
    if step_marker == "STEP10_CREATE_PR":
        return "Created draft PR summary."
    return f"{step_marker} completed via Google fallback."


def _mock_provider_subprocess(call_log: list[str]):
    def side_effect(cmd, cwd=None, env=None, input=None, capture_output=None, text=None, timeout=None, **kwargs):
        if cmd and cmd[0] == "git":
            return REAL_SUBPROCESS_RUN(
                cmd,
                cwd=cwd,
                env=env,
                input=input,
                capture_output=capture_output,
                text=text,
                timeout=timeout,
                **kwargs,
            )

        provider = Path(cmd[0]).name
        call_log.append(provider)

        if provider == "mock-claude":
            result = MagicMock()
            result.returncode = 0
            result.stdout = json.dumps(
                {
                    "type": "result",
                    "subtype": "success",
                    "is_error": True,
                    "result": (
                        "Failed to authenticate. API Error: 401 "
                        "{\"type\":\"error\",\"error\":{\"type\":\"authentication_error\","
                        "\"message\":\"Invalid bearer token\"}}"
                    ),
                    "total_cost_usd": 0.0,
                }
            )
            result.stderr = ""
            return result

        if provider == "mock-gemini":
            step_marker = _extract_step_marker(cmd=cmd, cwd=Path(cwd), stdin_content=input)
            result = MagicMock()
            result.returncode = 0
            result.stdout = json.dumps(
                {
                    "response": _google_output_for_step(step_marker),
                    "stats": {
                        "models": {
                            "gemini-1.5-flash": {
                                "tokens": {"prompt": 1000, "candidates": 500, "cached": 0}
                            }
                        }
                    },
                }
            )
            result.stderr = ""
            return result

        raise AssertionError(f"Unexpected provider command: {cmd}")

    return side_effect


@pytest.mark.e2e
def test_bug_orchestrator_falls_back_to_google_on_claude_oauth_error(git_repo):
    from pdd.agentic_bug_orchestrator import run_agentic_bug_orchestrator

    call_log: list[str] = []

    def which_side_effect(binary_name: str) -> str | None:
        return {
            "claude": "/usr/bin/mock-claude",
            "gemini": "/usr/bin/mock-gemini",
        }.get(binary_name)

    with patch.dict(
        "os.environ",
        {"ANTHROPIC_API_KEY": "test-ant", "GEMINI_API_KEY": "test-gem"},
        clear=False,
    ), patch(
        "pdd.agentic_bug_orchestrator.load_prompt_template",
        side_effect=_template_for_name,
    ), patch(
        "pdd.agentic_bug_orchestrator.console",
    ), patch(
        "pdd.agentic_common.get_available_agents",
        return_value=["anthropic", "google"],
    ), patch(
        "pdd.agentic_common.get_agent_provider_preference",
        return_value=["anthropic", "google"],
    ), patch(
        "pdd.agentic_common._find_cli_binary",
        side_effect=which_side_effect,
    ), patch(
        "pdd.agentic_common.subprocess.run",
        side_effect=_mock_provider_subprocess(call_log),
    ), patch(
        "pdd.agentic_common.time.sleep",
    ):
        success, message, cost, model, files = run_agentic_bug_orchestrator(
            issue_url="https://github.com/promptdriven/pdd/issues/743",
            issue_content="Claude OAuth auth errors should trigger fallback instead of success.",
            repo_owner="promptdriven",
            repo_name="pdd",
            issue_number=743,
            issue_author="test-user",
            issue_title="bug: Anthropic OAuth auth failures skip fallback",
            cwd=git_repo,
            verbose=False,
            quiet=True,
            use_github_state=False,
        )

    assert success is True, (
        "Issue #743 E2E: the bug workflow should complete when Claude returns "
        "OAuth auth JSON and Google is available as fallback."
    )
    assert message == "Investigation complete"
    assert model == "google"
    assert "tests/test_issue_743_unit.py" in files
    assert "mock-gemini" in call_log, (
        "Google fallback should be invoked after the Claude auth failure."
    )
    assert cost > 0.0


@pytest.mark.e2e
def test_bug_orchestrator_aborts_after_three_steps_when_claude_auth_error_has_no_fallback(
    git_repo,
):
    from pdd.agentic_bug_orchestrator import run_agentic_bug_orchestrator

    def which_side_effect(binary_name: str) -> str | None:
        return {"claude": "/usr/bin/mock-claude"}.get(binary_name)

    with patch.dict(
        "os.environ",
        {"ANTHROPIC_API_KEY": "test-ant"},
        clear=False,
    ), patch(
        "pdd.agentic_bug_orchestrator.load_prompt_template",
        side_effect=_template_for_name,
    ), patch(
        "pdd.agentic_bug_orchestrator.console",
    ), patch(
        "pdd.agentic_common.get_available_agents",
        return_value=["anthropic"],
    ), patch(
        "pdd.agentic_common.get_agent_provider_preference",
        return_value=["anthropic"],
    ), patch(
        "pdd.agentic_common._find_cli_binary",
        side_effect=which_side_effect,
    ), patch(
        "pdd.agentic_common.subprocess.run",
        side_effect=_mock_provider_subprocess([]),
    ), patch(
        "pdd.agentic_common.time.sleep",
    ):
        success, message, cost, model, files = run_agentic_bug_orchestrator(
            issue_url="https://github.com/promptdriven/pdd/issues/743",
            issue_content="Claude OAuth auth errors should fail immediately when no fallback exists.",
            repo_owner="promptdriven",
            repo_name="pdd",
            issue_number=743,
            issue_author="test-user",
            issue_title="bug: Anthropic OAuth auth failures are misclassified",
            cwd=git_repo,
            verbose=False,
            quiet=True,
            use_github_state=False,
        )

    assert success is False
    assert "3 consecutive steps failed" in message
    assert "agent providers unavailable" in message
    assert cost == 0.0
    assert model == ""
    assert files == []
