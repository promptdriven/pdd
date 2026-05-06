from __future__ import annotations

import json
import os
import signal
import subprocess
import time
from pathlib import Path
from typing import Any
from unittest.mock import MagicMock, patch

import pytest

from pdd.agentic_common import (
    DEFAULT_TIMEOUT_SECONDS,
    JOB_TIMEOUT_MARGIN_SECONDS,
    MAX_ERROR_RESPONSE_NEWLINES,
    MIN_ATTEMPT_TIMEOUT_SECONDS,
    MIN_VALID_OUTPUT_LENGTH,
    TokenMatch,
    _calculate_anthropic_cost,
    _calculate_codex_cost,
    _calculate_gemini_cost,
    _codex_auth_failure_message,
    _find_cli_binary,
    _is_false_positive,
    _is_permanent_error,
    _log_agentic_interaction,
    _parse_opencode_jsonl,
    _parse_provider_json,
    _resolve_reasoning_effort,
    _run_with_provider,
    _subprocess_run,
    clear_agentic_progress,
    clear_workflow_state,
    classify_step_output,
    detect_control_token,
    get_agent_provider_preference,
    get_and_clear_agentic_interrupt_context,
    get_available_agents,
    get_job_deadline,
    post_final_comment,
    post_pr_comment,
    post_step_comment,
    run_agentic_task,
    save_workflow_state,
    set_agentic_progress,
    substitute_template_variables,
    validate_cached_state,
)


@pytest.fixture(autouse=True)
def clean_agentic_env(monkeypatch: pytest.MonkeyPatch, tmp_path: Path) -> None:
    keys = [
        "PDD_AGENTIC_PROVIDER",
        "ANTHROPIC_API_KEY",
        "GEMINI_API_KEY",
        "GOOGLE_API_KEY",
        "GOOGLE_GENAI_USE_VERTEXAI",
        "OPENAI_API_KEY",
        "PDD_CODEX_AUTH_AVAILABLE",
        "OPENROUTER_API_KEY",
        "GITHUB_TOKEN",
        "GROQ_API_KEY",
        "PDD_USER_FEEDBACK",
        "PDD_JOB_DEADLINE",
        "PDD_REASONING_EFFORT",
        "CODEX_REASONING_EFFORT",
        "CLAUDE_MODEL",
        "GEMINI_MODEL",
        "CODEX_MODEL",
        "OPENCODE_MODEL",
        "OPENCODE_AGENT",
        "OPENCODE_VARIANT",
    ]
    for key in keys:
        monkeypatch.delenv(key, raising=False)
    monkeypatch.chdir(tmp_path)


def _completed(stdout: str, returncode: int = 0, stderr: str = "") -> subprocess.CompletedProcess[str]:
    return subprocess.CompletedProcess(args=["agent"], returncode=returncode, stdout=stdout, stderr=stderr)


def test_provider_preference_default_and_env_override(monkeypatch: pytest.MonkeyPatch) -> None:
    assert get_agent_provider_preference() == ["anthropic", "google", "openai", "opencode"]

    monkeypatch.setenv("PDD_AGENTIC_PROVIDER", "opencode, openai,unknown")
    assert get_agent_provider_preference() == ["opencode", "openai"]


def test_available_agents_auth_rules(monkeypatch: pytest.MonkeyPatch, tmp_path: Path) -> None:
    auth_path = tmp_path / "auth.json"
    auth_path.write_text("{}", encoding="utf-8")

    def fake_find(name: str, config: dict[str, Any] | None = None) -> str | None:
        return f"/bin/{name}"

    monkeypatch.setattr("pdd.agentic_common._find_cli_binary", fake_find)
    monkeypatch.setattr("pdd.agentic_common._has_gemini_oauth_credentials", lambda: True)
    monkeypatch.setattr("pdd.agentic_common._OPENCODE_AUTH_PATH", auth_path)

    agents = get_available_agents()
    assert agents == ["anthropic", "google", "opencode"]

    monkeypatch.setenv("OPENAI_API_KEY", "sk-test")
    assert get_available_agents() == ["anthropic", "google", "openai", "opencode"]


def test_find_cli_binary_uses_pddrc_override(monkeypatch: pytest.MonkeyPatch, tmp_path: Path) -> None:
    cli = tmp_path / "custom-claude"
    cli.write_text("#!/bin/sh\n", encoding="utf-8")
    cli.chmod(0o755)
    (tmp_path / ".pddrc").write_text(f"agentic:\n  claude_path: {cli}\n", encoding="utf-8")
    monkeypatch.chdir(tmp_path)
    monkeypatch.setattr("shutil.which", lambda _name: None)

    assert _find_cli_binary("claude") == str(cli)


def test_subprocess_run_kills_process_group_on_timeout() -> None:
    proc = MagicMock()
    proc.pid = 12345
    proc.communicate.side_effect = subprocess.TimeoutExpired(cmd="agent", timeout=10)

    with patch("pdd.agentic_common.subprocess.Popen", return_value=proc), \
         patch("pdd.agentic_common.os.getpgid", return_value=12345), \
         patch("pdd.agentic_common.os.killpg") as killpg:
        with pytest.raises(subprocess.TimeoutExpired):
            _subprocess_run(["agent"], timeout=10)

    killpg.assert_called_once_with(12345, signal.SIGKILL)


def test_provider_json_parsing_and_costs() -> None:
    anthropic = {
        "result": "done",
        "modelUsage": {"claude-sonnet-4": {"costUSD": 0.25}},
    }
    assert _parse_provider_json("anthropic", anthropic) == (True, "done", 0.25)

    google = {
        "response": "ok",
        "stats": {"models": {"gemini-1.5-flash": {"tokens": {"prompt": 1000, "candidates": 1000}}}},
    }
    ok, text, cost = _parse_provider_json("google", google)
    assert ok is True
    assert text == "ok"
    assert cost == pytest.approx(_calculate_gemini_cost(google["stats"]))

    openai_jsonl = "\n".join([
        json.dumps({"type": "item.completed", "item": {"type": "agent_message", "text": "hello"}}),
        json.dumps({"type": "turn.completed", "usage": {"input_tokens": 1000, "output_tokens": 500}}),
    ])
    assert _parse_provider_json("openai", openai_jsonl) == (
        True,
        "hello",
        pytest.approx(_calculate_codex_cost({"input_tokens": 1000, "output_tokens": 500})),
    )


def test_anthropic_model_usage_tokens_estimated_when_total_cost_zero() -> None:
    cost = _calculate_anthropic_cost({
        "total_cost_usd": 0,
        "modelUsage": {
            "claude-sonnet-4-20250514": {
                "inputTokens": 1000,
                "outputTokens": 200,
                "cacheReadInputTokens": 500,
                "cacheCreationInputTokens": 300,
            }
        },
    })

    assert cost == pytest.approx(0.004875)


def test_openai_dict_parsing_extracts_agent_message_content_and_usage() -> None:
    ok, text, cost = _parse_provider_json(
        "openai",
        {
            "item": {
                "type": "agent_message",
                "content": [{"type": "output_text", "text": "hello from codex"}],
            },
            "usage": {"input_tokens": 1000, "output_tokens": 500},
        },
    )

    assert ok is True
    assert text == "hello from codex"
    assert cost == pytest.approx(_calculate_codex_cost({"input_tokens": 1000, "output_tokens": 500}))


def test_anthropic_is_error_is_failure() -> None:
    ok, text, cost = _parse_provider_json(
        "anthropic",
        {"is_error": True, "result": "Not logged in - Please run /login", "total_cost_usd": 0.0},
    )
    assert ok is False
    assert "Not logged in" in text
    assert cost == 0.0


def test_opencode_jsonl_parses_text_cost_and_errors() -> None:
    ok, text, cost, error = _parse_opencode_jsonl(
        '{"type":"text","part":{"text":"Hello "}}\n'
        '{"type":"text","part":{"text":"world"}}\n'
        '{"type":"step_finish","part":{"cost":0.01}}\n'
        '{"type":"step_finish","cost":0.02}\n'
    )
    assert ok is True
    assert text == "Hello world"
    assert cost == pytest.approx(0.03)
    assert error is None

    ok, text, cost, error = _parse_opencode_jsonl('{"type":"error","message":"model not found"}')
    assert ok is False
    assert text == ""
    assert cost == 0.0
    assert error == "model not found"

    assert _parse_provider_json("opencode", "") == (False, "", 0.0)


def test_false_positive_detection_is_anchored() -> None:
    assert _is_false_positive("", 0.0) is True
    assert _is_false_positive("short", 0.0) is True
    assert _is_false_positive("Error: rate limit exceeded", 0.01) is True
    assert _is_false_positive("Finding: code raises Error: for invalid input", 0.01) is False
    assert _is_false_positive("Error:\n\n\nSubstantive multi-paragraph finding", 0.01) is False
    assert MAX_ERROR_RESPONSE_NEWLINES == 3
    assert MIN_VALID_OUTPUT_LENGTH == 50


def test_run_agentic_task_uses_prompt_file_and_injects_feedback(
    monkeypatch: pytest.MonkeyPatch, tmp_path: Path
) -> None:
    monkeypatch.setenv("PDD_AGENTIC_PROVIDER", "anthropic")
    monkeypatch.setenv("PDD_USER_FEEDBACK", "Try a smaller patch")
    monkeypatch.setattr("pdd.agentic_common._find_cli_binary", lambda *_args, **_kwargs: "/bin/claude")

    seen_prompt_text = ""
    seen_instruction = ""

    def fake_run(cmd: list[str], **kwargs: Any) -> subprocess.CompletedProcess[str]:
        nonlocal seen_prompt_text, seen_instruction
        seen_instruction = kwargs["input"]
        prompt_path = Path(seen_instruction.split("Read the file ", 1)[1].split(" for instructions", 1)[0])
        seen_prompt_text = prompt_path.read_text(encoding="utf-8")
        return _completed(json.dumps({"result": "Task completed with enough detail to be valid.", "total_cost_usd": 0.01}))

    monkeypatch.setattr("pdd.agentic_common._subprocess_run", fake_run)

    success, output, cost, provider = run_agentic_task("Fix the bug", tmp_path, quiet=True)

    assert success is True
    assert provider == "anthropic"
    assert cost == pytest.approx(0.01)
    assert "Read the file" in seen_instruction
    assert "Fix the bug" in seen_prompt_text
    assert "User Feedback" in seen_prompt_text
    assert "Try a smaller patch" in seen_prompt_text
    assert not list(tmp_path.glob(".agentic_prompt_*.txt"))


def test_run_agentic_task_single_provider_retries_false_positive(
    monkeypatch: pytest.MonkeyPatch, tmp_path: Path
) -> None:
    monkeypatch.setattr("pdd.agentic_common.get_available_agents", lambda: ["anthropic"])
    monkeypatch.setattr("pdd.agentic_common.time.sleep", lambda _seconds: None)
    monkeypatch.setattr("pdd.agentic_common.random.uniform", lambda _a, _b: 0.5)
    calls: list[str] = []

    def fake_provider(*_args: Any, **_kwargs: Any) -> tuple[bool, str, float]:
        calls.append("call")
        if len(calls) == 1:
            return False, "", 0.0
        return True, "Recovered with a valid long response after retry.", 0.01

    monkeypatch.setattr("pdd.agentic_common._run_with_provider", fake_provider)

    success, output, _cost, provider = run_agentic_task("Do work", tmp_path, max_retries=2, quiet=True)

    assert success is True
    assert provider == "anthropic"
    assert "Recovered" in output
    assert len(calls) == 2


def test_run_agentic_task_multi_provider_falls_through_without_retry(
    monkeypatch: pytest.MonkeyPatch, tmp_path: Path
) -> None:
    monkeypatch.setattr("pdd.agentic_common.get_available_agents", lambda: ["anthropic", "google"])
    calls: list[str] = []

    def fake_provider(provider: str, *_args: Any, **_kwargs: Any) -> tuple[bool, str, float]:
        calls.append(provider)
        if provider == "anthropic":
            return False, "", 0.0
        return True, "Google produced a valid long response.", 0.01

    monkeypatch.setattr("pdd.agentic_common._run_with_provider", fake_provider)

    success, _output, _cost, provider = run_agentic_task("Do work", tmp_path, max_retries=3, quiet=True)

    assert success is True
    assert provider == "google"
    assert calls == ["anthropic", "google"]


def test_deadline_skips_attempt_when_budget_is_too_low(
    monkeypatch: pytest.MonkeyPatch, tmp_path: Path
) -> None:
    monkeypatch.setattr("pdd.agentic_common.get_available_agents", lambda: ["anthropic"])
    called = False

    def fake_provider(*_args: Any, **_kwargs: Any) -> tuple[bool, str, float]:
        nonlocal called
        called = True
        return True, "should not run", 0.0

    monkeypatch.setattr("pdd.agentic_common._run_with_provider", fake_provider)

    success, message, _cost, _provider = run_agentic_task(
        "Do work",
        tmp_path,
        deadline=time.time() + JOB_TIMEOUT_MARGIN_SECONDS + MIN_ATTEMPT_TIMEOUT_SECONDS - 1,
        quiet=True,
    )

    assert success is False
    assert "Deadline exceeded" in message
    assert called is False


def test_codex_reasoning_effort_config_precedes_exec(
    monkeypatch: pytest.MonkeyPatch, tmp_path: Path
) -> None:
    prompt = tmp_path / "prompt.txt"
    prompt.write_text("Do work", encoding="utf-8")
    monkeypatch.setenv("CODEX_REASONING_EFFORT", "xhigh")
    monkeypatch.setattr("pdd.agentic_common._find_cli_binary", lambda *_args, **_kwargs: "/bin/codex")
    captured_cmd: list[str] = []

    def fake_run(cmd: list[str], **_kwargs: Any) -> subprocess.CompletedProcess[str]:
        captured_cmd[:] = cmd
        return _completed(
            "\n".join([
                json.dumps({"type": "item.completed", "item": {"type": "agent_message", "text": "Valid Codex output."}}),
                json.dumps({"type": "turn.completed", "usage": {"input_tokens": 100, "output_tokens": 100}}),
            ])
        )

    monkeypatch.setattr("pdd.agentic_common._subprocess_run", fake_run)

    success, _output, _cost = _run_with_provider("openai", prompt, tmp_path, quiet=True)

    assert success is True
    assert captured_cmd.index("-c") < captured_cmd.index("exec")
    assert "model_reasoning_effort=xhigh" in captured_cmd


def test_control_token_detection_uses_splitlines_tail() -> None:
    output = "\r".join([f"line {i}" for i in range(40)] + ["all 12 tests pass"])
    match = detect_control_token(output, "ALL_TESTS_PASS")

    assert isinstance(match, TokenMatch)
    assert match.tier == "semantic"


def test_classify_step_output_uses_detection_before_llm() -> None:
    assert classify_step_output("Final status: all 12 tests pass", ["ALL_TESTS_PASS"], quiet=True) == "ALL_TESTS_PASS"


def test_codex_auth_failure_is_actionable_and_permanent() -> None:
    detail = "401 Unauthorized chatgpt.com/backend-api/codex/responses access token could not be refreshed"
    message = _codex_auth_failure_message(detail)

    assert message is not None
    assert "codex login" in message
    assert _is_permanent_error(message) is True
    assert _is_permanent_error("Not logged in - Please run /login") is True


def test_reasoning_time_uses_shared_boundaries() -> None:
    assert _resolve_reasoning_effort(0.3) == "low"
    assert _resolve_reasoning_effort(0.7) == "medium"
    assert _resolve_reasoning_effort(0.71) == "high"


def test_state_validation_template_and_progress_helpers() -> None:
    assert validate_cached_state(4, {"1": "ok", "2": "FAILED: bad", "3": "ok"}, quiet=True) == 1
    assert validate_cached_state(4, {"1": "ok", "2": "ok", "3": "FAILED: bad"}, [1, 2, 3, 4], quiet=True) == 2
    assert substitute_template_variables("A={a}; json={\"x\": 1}", {"a": 3}) == "A=3; json={\"x\": 1}"

    set_agentic_progress("bug", 2, 5, "Fix", ["Triage"])
    state = get_and_clear_agentic_interrupt_context()
    assert state is not None
    assert state["workflow"] == "bug"
    assert get_and_clear_agentic_interrupt_context() is None
    clear_agentic_progress()


def test_github_comment_helpers(monkeypatch: pytest.MonkeyPatch, tmp_path: Path) -> None:
    monkeypatch.setattr("pdd.agentic_common.shutil.which", lambda name: "/usr/bin/gh" if name == "gh" else None)
    calls: list[list[str]] = []

    def fake_run(cmd: list[str], **_kwargs: Any) -> subprocess.CompletedProcess[str]:
        calls.append(cmd)
        return _completed(json.dumps({"id": 123}))

    monkeypatch.setattr("pdd.agentic_common.subprocess.run", fake_run)

    assert post_step_comment("o", "r", 1, 1, 2, "desc", "output", tmp_path) is True
    assert post_pr_comment("o", "r", 2, "body", tmp_path) is True
    assert post_final_comment("o", "r", 1, "done", tmp_path) is True
    assert calls[0][:3] == ["gh", "issue", "comment"]
    assert calls[1][:3] == ["gh", "pr", "comment"]


def test_log_agentic_interaction_gates_success_by_verbose(
    monkeypatch: pytest.MonkeyPatch, tmp_path: Path
) -> None:
    import pdd.agentic_common as agentic_common

    monkeypatch.setattr(agentic_common, "_SESSION_LOG_PATH", None)
    monkeypatch.setattr(agentic_common, "_SESSION_LOG_BASE_CWD", None)
    monkeypatch.setattr(agentic_common, "_AGENTIC_SESSION_ID", None)

    _log_agentic_interaction({"success": True, "provider": "anthropic", "cwd": str(tmp_path)}, verbose=False)
    assert not list((tmp_path / ".pdd" / "agentic-logs").glob("*.jsonl"))

    _log_agentic_interaction({"success": False, "provider": "anthropic", "cwd": str(tmp_path)}, verbose=False)
    logs = list((tmp_path / ".pdd" / "agentic-logs").glob("*.jsonl"))
    assert len(logs) == 1
    assert '"success": false' in logs[0].read_text(encoding="utf-8")


def test_save_and_clear_workflow_state_local_first(monkeypatch: pytest.MonkeyPatch, tmp_path: Path) -> None:
    monkeypatch.setenv("PDD_NO_GITHUB_STATE", "1")
    state_dir = tmp_path / "state"

    result = save_workflow_state(
        repo_owner="o",
        repo_name="r",
        issue_number=7,
        workflow_type="bug",
        state={"last_completed_step": 3},
        state_dir=state_dir,
        cwd=tmp_path,
        use_github_state=False,
    )

    assert result is None
    local = state_dir / "bug_state_7.json"
    assert json.loads(local.read_text(encoding="utf-8"))["last_completed_step"] == 3

    clear_workflow_state(
        repo_owner="o",
        repo_name="r",
        issue_number=7,
        workflow_type="bug",
        state_dir=state_dir,
        cwd=tmp_path,
        use_github_state=False,
    )
    assert not local.exists()


def test_constants_match_prompt() -> None:
    assert DEFAULT_TIMEOUT_SECONDS == 600.0
    assert JOB_TIMEOUT_MARGIN_SECONDS == 120.0
    assert MIN_ATTEMPT_TIMEOUT_SECONDS == 60.0
