"""Provider-free story regression coverage for PDD issue #2422.

The primary cases call the public ``run_agentic_task`` API and replace only
provider discovery plus the CLI process/result boundary. No provider account,
credential, network service, or paid model is used.
"""

from __future__ import annotations

import io
import json
import os
import subprocess
from contextlib import ExitStack, nullcontext
from pathlib import Path
from typing import Any
from unittest.mock import patch

import pytest

import pdd.agentic_common as ac


pytestmark = [
    pytest.mark.timeout(60),
    pytest.mark.story(story_id="provider_attempt_outcome"),
]


def _zero_work_rejection() -> dict[str, Any]:
    """Sanitized shape observed from Claude CLI 2.1.263 at the real boundary."""
    return {
        "duration_api_ms": 0,
        "stop_reason": "stop_sequence",
        "session_id": "11111111-2222-4333-8444-555555555555",
        "total_cost_usd": 0,
        "usage": {
            "output_tokens_details": {"thinking_tokens": 0},
            "input_tokens": 0,
            "cache_creation_input_tokens": 0,
            "cache_read_input_tokens": 0,
            "output_tokens": 0,
            "server_tool_use": {
                "web_search_requests": 0,
                "web_fetch_requests": 0,
            },
            "service_tier": "standard",
            "cache_creation": {
                "ephemeral_1h_input_tokens": 0,
                "ephemeral_5m_input_tokens": 0,
            },
            "inference_geo": "",
            "iterations": [],
            "speed": "standard",
        },
        "modelUsage": {},
        "permission_denials": [],
        "terminal_reason": "api_error",
        "fast_mode_state": "off",
        "fast_mode_disabled_reason": "sdk_opt_in_required",
        "subagent_stats": {
            "spawned": 0,
            "requested": {"background": 0, "foreground": 0, "unset": 0},
            "started_in_background": 0,
            "max_depth": 0,
            "spawned_by_subagents": 0,
            "completed": 0,
            "failed": 0,
            "killed": {"parent": 0, "user": 0, "system": 0},
            "refused": {
                "depth_limit": 0,
                "concurrency_limit": 0,
                "budget": 0,
            },
            "by_type": {},
        },
        "is_error": True,
        # These are wrapper lifecycle fields, not evidence that inference ran.
        "num_turns": 1,
        "subtype": "success",
        "api_error_status": 403,
        "result": (
            "Failed to authenticate. API Error: 403 synthetic account has no "
            "access. Authorization: Bearer sk-syntheticsecret000000000000"
        ),
        "type": "result",
        "duration_ms": 65,
        "uuid": "aaaaaaaa-bbbb-4ccc-8ddd-eeeeeeeeeeee",
        "queued_turn_count": 0,
    }


def _zero_work_rejection_280() -> dict[str, Any]:
    """Sanitized 2.1.280 output from a local-only synthetic 403 API boundary.

    Compared with 2.1.263 using npm package integrity
    sha512-EZlX8jqNf+e7q9v+UoPbLYAbEGth7aDbcTytHzPYYohbP/fCfrjboCbcv85ZYGEq1Rq7Amm8hXLhuCKxLsabwA==.
    Both CLIs used --output-format json against ANTHROPIC_BASE_URL on loopback
    with a synthetic key; the 2.1.280 result adds result_index: 0.
    """
    envelope = _zero_work_rejection()
    envelope["result"] = "Failed to authenticate. API Error: 403 synthetic account has no access"
    envelope["result_index"] = 0
    return envelope


@pytest.fixture(autouse=True)
def _reset_provider_state(request):
    version_boundary = (
        nullcontext()
        if request.node.get_closest_marker("uses_real_cli_detector")
        else patch(
            "pdd.agentic_common._get_provider_cli_version",
            return_value="2.1.263 (Claude Code)",
        )
    )
    with version_boundary:
        ac._PROVIDER_CLI_VERSION_CACHE.clear()
        ac.reset_disabled_providers()
        yield
        ac.reset_disabled_providers()
        ac._PROVIDER_CLI_VERSION_CACHE.clear()


def _write_fake_claude_executable(tmp_path: Path) -> Path:
    """Create an offline Claude boundary that is still a real OS process."""
    cli_dir = tmp_path / "fake-bin"
    cli_dir.mkdir()
    cli_path = cli_dir / "claude"
    cli_path.write_text(
        """#!/bin/sh
if [ "${1-}" = "--version" ]; then
    printf '%s\\n' "$PDD_FAKE_CLAUDE_VERSION"
    printf '%s\\n' version >> "$PDD_FAKE_CLAUDE_EVENTS"
    exit 0
fi
while IFS= read -r _line; do :; done
printf '%s\\n' attempt >> "$PDD_FAKE_CLAUDE_EVENTS"
printf '%s\\n' "$PDD_FAKE_CLAUDE_PAYLOAD"
exit 1
""",
        encoding="utf-8",
    )
    cli_path.chmod(0o755)
    return cli_path


def _completed(stdout: str, *, returncode: int = 1, stderr: str = ""):
    return subprocess.CompletedProcess(
        ["synthetic-provider"], returncode, stdout=stdout, stderr=stderr
    )


def _spooled(stdout: str, *, returncode: int) -> ac._SpooledCompletedProcess:
    payload = stdout.encode()
    return ac._SpooledCompletedProcess(
        args=["codex"],
        returncode=returncode,
        stdout_file=io.BytesIO(payload),
        stderr_file=io.BytesIO(b""),
        stdout_bytes=len(payload),
        stderr_bytes=0,
        stdout_head=stdout,
        stdout_tail="",
        stderr_head="",
        stderr_tail="",
    )


def _opencode_step_start() -> dict[str, Any]:
    return {
        "type": "step_start",
        "timestamp": 1,
        "sessionID": "ses_synthetic",
        "part": {
            "id": "prt_start",
            "sessionID": "ses_synthetic",
            "messageID": "msg_synthetic",
            "type": "step-start",
        },
    }


def _opencode_tool_use() -> dict[str, Any]:
    return {
        "type": "tool_use",
        "timestamp": 2,
        "sessionID": "ses_synthetic",
        "part": {
            "id": "prt_tool",
            "sessionID": "ses_synthetic",
            "messageID": "msg_synthetic",
            "type": "tool",
            "callID": "call_synthetic",
            "tool": "synthetic-tool",
            "state": {"status": "completed"},
        },
    }


def _codex_current_item_pair(item_type: str) -> tuple[dict[str, Any], dict[str, Any]]:
    if item_type == "command_execution":
        base = {
            "id": "item_command",
            "type": item_type,
            "command": "true",
            "aggregated_output": "",
            "exit_code": None,
        }
        return (
            {**base, "status": "in_progress"},
            {**base, "status": "completed", "exit_code": 0},
        )
    if item_type == "file_change":
        base = {
            "id": "item_file",
            "type": item_type,
            "changes": [{"path": "synthetic.txt", "kind": "update"}],
        }
        completed = {**base, "status": "completed"}
        return (completed, completed)
    if item_type == "mcp_tool_call":
        base = {
            "id": "item_mcp",
            "type": item_type,
            "server": "synthetic-server",
            "tool": "synthetic-tool",
            "arguments": {},
        }
        return (
            {**base, "status": "in_progress", "result": None, "error": None},
            {
                **base,
                "status": "completed",
                "result": {"content": [], "structured_content": None},
                "error": None,
            },
        )
    if item_type == "collab_tool_call":
        base = {
            "id": "item_collab",
            "type": item_type,
            "tool": "spawn_agent",
            "sender_thread_id": "thread_parent",
            "receiver_thread_ids": ["thread_child"],
            "prompt": "synthetic task",
            "agents_states": {
                "thread_child": {"status": "running", "message": None}
            },
        }
        return (
            {**base, "status": "in_progress"},
            {**base, "status": "completed"},
        )
    if item_type == "web_search":
        item = {
            "id": "item_search",
            "type": item_type,
            "query": "synthetic",
            "action": {"type": "search", "query": "synthetic"},
        }
        return (item, item)
    raise AssertionError(f"unsupported synthetic item type: {item_type}")


def _run_public(
    tmp_path: Path,
    *,
    providers: list[str],
    boundary_result: Any,
    provider_preference: str | None = None,
    max_retries: int = 4,
    before_attempt=None,
    single_provider_attempt: bool = True,
    claude_version: str = "2.1.263 (Claude Code)",
):
    preference = provider_preference or ",".join(providers)
    with ExitStack() as stack:
        stack.enter_context(
            patch.dict(
                "os.environ",
                {"PDD_AGENTIC_PROVIDER": preference},
                clear=False,
            )
        )
        stack.enter_context(
            patch("pdd.agentic_common.get_available_agents", return_value=providers)
        )
        stack.enter_context(
            patch("pdd.agentic_common._find_cli_binary", return_value="/synthetic/cli")
        )
        stack.enter_context(
            patch(
                "pdd.agentic_common._get_google_cli_binary",
                return_value="/synthetic/google",
            )
        )
        stack.enter_context(
            patch("pdd.agentic_common._strip_anthropic_creds_for_claude_subprocess")
        )
        stack.enter_context(
            patch(
                "pdd.agentic_common._get_provider_cli_version",
                return_value=claude_version,
            )
        )
        stack.enter_context(
            patch("pdd.agentic_common._codex_gpt_5_6_version_error", return_value=None)
        )
        run_mock = stack.enter_context(
            patch("pdd.agentic_common._subprocess_run")
        )
        spooled_mock = stack.enter_context(
            patch("pdd.agentic_common._subprocess_run_spooled")
        )
        if isinstance(boundary_result, BaseException):
            run_mock.side_effect = boundary_result
            spooled_mock.side_effect = boundary_result
        else:
            run_mock.return_value = boundary_result
            spooled_mock.return_value = boundary_result
        result = ac.run_agentic_task(
            "synthetic provider boundary",
            tmp_path,
            quiet=True,
            max_retries=max_retries,
            before_attempt=before_attempt,
            single_provider_attempt=single_provider_attempt,
            background_safe=True,
        )
    return result, run_mock, spooled_mock


def _receipt_dict(result: ac.AgenticTaskResult) -> dict[str, Any]:
    receipt = result.provider_attempt_receipt
    assert receipt is not None
    return result.to_dict()["provider_attempt_receipt"]


def test_complete_private_envelope_returns_not_started_and_blocks_fallback(tmp_path):
    raw = json.dumps(_zero_work_rejection(), separators=(",", ":"))
    assert len(raw) > 500
    assert raw.index('"api_error_status"') > 500
    attempts: list[tuple[str, int]] = []

    result, run_mock, _ = _run_public(
        tmp_path,
        providers=["anthropic", "google"],
        boundary_result=_completed(raw),
        before_attempt=lambda provider, attempt: attempts.append((provider, attempt)),
    )

    assert result.success is False
    assert run_mock.call_count == 1
    assert attempts == [("anthropic", 1)]
    assert _receipt_dict(result) == {
        "schema_version": "pdd.provider_attempt.v1",
        "provider": "anthropic",
        "attempt_number": 1,
        "failure_kind": "credential_or_account",
        "work_disposition": "not_started",
    }
    assert len(result.output_text) <= 500
    assert "sk-syntheticsecret" not in result.output_text
    assert "11111111-2222-4333-8444-555555555555" not in result.output_text
    assert "aaaaaaaa-bbbb-4ccc-8ddd-eeeeeeeeeeee" not in result.output_text
    assert '"duration_api_ms"' not in result.output_text


@pytest.mark.parametrize(
    "single_provider_attempt,expected_attempts",
    [(True, [("anthropic", 1)]), (False, [("anthropic", 1), ("google", 1)])],
)
def test_claude_280_rejection_rotation_and_retry(
    tmp_path, single_provider_attempt, expected_attempts
):
    attempts: list[tuple[str, int]] = []
    result, run_mock, _ = _run_public(
        tmp_path,
        providers=["anthropic", "google"],
        boundary_result=_completed(json.dumps(_zero_work_rejection_280())),
        claude_version="2.1.280 (Claude Code)",
        max_retries=7,
        single_provider_attempt=single_provider_attempt,
        before_attempt=lambda provider, attempt: attempts.append((provider, attempt)),
    )
    assert result.success is False
    assert attempts == expected_attempts
    assert run_mock.call_count == len(expected_attempts)
    if single_provider_attempt:
        assert _receipt_dict(result)["work_disposition"] == "not_started"
        assert _receipt_dict(result)["failure_kind"] == "credential_or_account"


@pytest.mark.parametrize(
    "mutation",
    [
        lambda data: data.pop("result_index"),
        lambda data: data.__setitem__("result_index", 1),
        lambda data: data.__setitem__("result_index", True),
        lambda data: data.__setitem__("result_index", -1),
        lambda data: data.__setitem__("future_activity", 0),
        lambda data: data["usage"].__setitem__("future_tokens", 0),
    ],
    ids=["missing-index", "second-result", "boolean-index", "negative-index", "new-field", "new-usage"],
)
def test_claude_280_unreviewed_or_substituted_envelope_is_ambiguous(mutation):
    envelope = _zero_work_rejection_280()
    mutation(envelope)
    with patch("pdd.agentic_common._get_provider_cli_version", return_value="2.1.280 (Claude Code)"):
        receipt = ac._create_provider_attempt_receipt(
            "anthropic", 1, 1, json.dumps(envelope), ""
        )
    assert receipt.work_disposition == "ambiguous"


def test_claude_280_envelope_rejected_under_263_version():
    receipt = ac._create_provider_attempt_receipt(
        "anthropic", 1, 1, json.dumps(_zero_work_rejection_280()), ""
    )
    assert receipt.work_disposition == "ambiguous"


@pytest.mark.parametrize("change", ["tokens", "cost", "queue"])
def test_claude_280_positive_work_overrides_credential_failure(change):
    envelope = _zero_work_rejection_280()
    if change == "tokens":
        envelope["usage"]["input_tokens"] = 1
    elif change == "cost":
        envelope["total_cost_usd"] = 0.01
    else:
        envelope["queued_turn_count"] = 1
    with patch("pdd.agentic_common._get_provider_cli_version", return_value="2.1.280 (Claude Code)"):
        receipt = ac._create_provider_attempt_receipt(
            "anthropic", 1, 1, json.dumps(envelope), ""
        )
    assert receipt.work_disposition == "started_or_billable"


def test_claude_280_contradictory_stderr_is_ambiguous():
    with patch("pdd.agentic_common._get_provider_cli_version", return_value="2.1.280 (Claude Code)"):
        receipt = ac._create_provider_attempt_receipt(
            "anthropic", 1, 1, json.dumps(_zero_work_rejection_280()), "connection reset"
        )
    assert receipt.work_disposition == "ambiguous"


@pytest.mark.parametrize("boundary", [{"timed_out": True}, {"output_complete": False}])
def test_claude_280_cancelled_or_partial_output_is_ambiguous(boundary):
    with patch("pdd.agentic_common._get_provider_cli_version", return_value="2.1.280 (Claude Code)"):
        receipt = ac._create_provider_attempt_receipt(
            "anthropic", 1, 1, json.dumps(_zero_work_rejection_280()), "", **boundary
        )
    assert receipt.work_disposition == "ambiguous"


def test_claude_280_complete_401_is_not_started():
    envelope = _zero_work_rejection_280()
    envelope["api_error_status"] = 401
    envelope["result"] = "Failed to authenticate. API Error: 401 synthetic invalid key"
    with patch("pdd.agentic_common._get_provider_cli_version", return_value="2.1.280 (Claude Code)"):
        receipt = ac._create_provider_attempt_receipt(
            "anthropic", 1, 1, json.dumps(envelope), ""
        )
    assert (receipt.failure_kind, receipt.work_disposition) == (
        "credential_or_account", "not_started"
    )


def test_single_attempt_unstructured_diagnostic_never_echoes_private_text(tmp_path):
    private_text = (
        "authentication failed password=hunter2 "
        "session_id=sess_sensitive request_id=req_01JPRIVATE"
    )
    result, _, _ = _run_public(
        tmp_path,
        providers=["anthropic"],
        boundary_result=_completed("", stderr=private_text),
    )
    assert result.provider_attempt_receipt.work_disposition == "ambiguous"
    assert len(result.output_text) <= 500
    for private_value in ("hunter2", "sess_sensitive", "req_01JPRIVATE"):
        assert private_value not in result.output_text


@pytest.mark.parametrize(
    "mutation",
    [
        lambda data: data["usage"].__setitem__("input_tokens", 1),
        lambda data: data.__setitem__("total_cost_usd", 0.01),
        lambda data: data.__setitem__("duration_api_ms", 1),
        lambda data: data["usage"]["server_tool_use"].__setitem__(
            "web_search_requests", 1
        ),
        lambda data: data["subagent_stats"].__setitem__("spawned", 1),
        lambda data: data.__setitem__("queued_turn_count", 1),
        lambda data: data["usage"].__setitem__("iterations", [{"type": "task"}]),
        lambda data: data.__setitem__(
            "modelUsage", {"synthetic-model": {"costUSD": 0.01}}
        ),
    ],
    ids=[
        "tokens",
        "cost",
        "api-duration",
        "server-tool",
        "subagent",
        "queue",
        "task-iteration",
        "model-usage",
    ],
)
def test_reviewed_positive_activity_wins_over_auth_rejection(mutation):
    envelope = _zero_work_rejection()
    mutation(envelope)
    receipt = ac._create_provider_attempt_receipt(
        "anthropic", 1, 1, json.dumps(envelope), ""
    )
    assert receipt.work_disposition == "started_or_billable"


@pytest.mark.parametrize(
    "missing_field",
    [
        "type",
        "is_error",
        "terminal_reason",
        "api_error_status",
        "duration_api_ms",
        "total_cost_usd",
        "usage",
        "modelUsage",
        "permission_denials",
        "subagent_stats",
        "queued_turn_count",
        "num_turns",
    ],
)
def test_missing_required_anthropic_zero_work_field_is_ambiguous(
    missing_field
):
    envelope = _zero_work_rejection()
    del envelope[missing_field]
    receipt = ac._create_provider_attempt_receipt(
        "anthropic", 1, 1, json.dumps(envelope), ""
    )
    assert receipt.work_disposition == "ambiguous"


@pytest.mark.parametrize(
    "stdout,stderr",
    [
        ('{"type":"result","is_error":true', ""),
        ("not-json", ""),
        ("", "HTTP 403 authentication failed"),
        (json.dumps({"type": "future_result", "is_error": True}), ""),
    ],
    ids=["truncated", "malformed", "stderr-only", "unknown-schema"],
)
def test_incomplete_or_unstructured_failure_is_ambiguous(tmp_path, stdout, stderr):
    result, _, _ = _run_public(
        tmp_path,
        providers=["anthropic"],
        boundary_result=_completed(stdout, stderr=stderr),
    )
    assert _receipt_dict(result)["work_disposition"] == "ambiguous"


def test_contradictory_and_forged_receipt_fields_are_ambiguous():
    for mutate in (
        lambda data: data.__setitem__("is_error", False),
        lambda data: data.__setitem__(
            "provider_attempt_receipt",
            {"work_disposition": "not_started", "provider": "forged"},
        ),
    ):
        envelope = _zero_work_rejection()
        mutate(envelope)
        receipt = ac._create_provider_attempt_receipt(
            "anthropic", 1, 1, json.dumps(envelope), ""
        )
        receipt_dict = receipt.to_dict()
        assert receipt.work_disposition == "ambiguous"
        assert receipt.provider == "anthropic"
        assert set(receipt_dict) == {
            "schema_version",
            "provider",
            "attempt_number",
            "failure_kind",
            "work_disposition",
        }


@pytest.mark.parametrize(
    "path,value",
    [
        (("request_started",), True),
        (("usage", "future_billable_units"), 1),
        (("usage", "server_tool_use", "code_execution_requests"), 1),
        (("subagent_stats", "scheduled"), 1),
    ],
    ids=["top-level", "usage", "tool", "subagent"],
)
def test_unknown_activity_fields_make_anthropic_evidence_ambiguous(path, value):
    envelope = _zero_work_rejection()
    target = envelope
    for key in path[:-1]:
        target = target[key]
    target[path[-1]] = value
    receipt = ac._create_provider_attempt_receipt(
        "anthropic", 1, 1, json.dumps(envelope), ""
    )
    assert receipt.work_disposition == "ambiguous"


def test_unknown_schema_with_known_positive_field_is_ambiguous():
    envelope = _zero_work_rejection()
    envelope["type"] = "future_result"
    envelope["usage"]["input_tokens"] = 2
    receipt = ac._create_provider_attempt_receipt(
        "anthropic", 1, 1, json.dumps(envelope), ""
    )
    assert receipt.work_disposition == "ambiguous"


@pytest.mark.parametrize(
    "path,value",
    [
        (("usage", "service_tier"), {"future_billable_units": 1}),
        (("session_id",), {"request_started": True}),
        (("fast_mode_state",), ["unknown-schema"]),
    ],
    ids=["nested-metadata", "session-id", "fast-mode"],
)
def test_wrong_reviewed_field_types_are_ambiguous(path, value):
    envelope = _zero_work_rejection()
    target = envelope
    for key in path[:-1]:
        target = target[key]
    target[path[-1]] = value
    receipt = ac._create_provider_attempt_receipt(
        "anthropic", 1, 1, json.dumps(envelope), ""
    )
    assert receipt.work_disposition == "ambiguous"


@pytest.mark.parametrize(
    "version",
    ["2.1.264 (Claude Code)", "2.1.281 (Claude Code)", "2.1.263.1", "2.1.263-beta", "2.1.263"],
)
def test_unreviewed_anthropic_cli_version_is_ambiguous(version):
    with patch(
        "pdd.agentic_common._get_provider_cli_version", return_value=version
    ):
        receipt = ac._create_provider_attempt_receipt(
            "anthropic", 1, 1, json.dumps(_zero_work_rejection()), ""
        )
    assert receipt.work_disposition == "ambiguous"


@pytest.mark.parametrize("bad_value", [float("nan"), float("inf"), float("-inf")])
def test_nonstandard_anthropic_numbers_are_ambiguous(bad_value):
    envelope = _zero_work_rejection()
    envelope["duration_ms"] = bad_value
    receipt = ac._create_provider_attempt_receipt(
        "anthropic", 1, 1, json.dumps(envelope), ""
    )
    assert receipt.work_disposition == "ambiguous"


def test_duplicate_anthropic_json_keys_are_ambiguous():
    raw = json.dumps(_zero_work_rejection(), separators=(",", ":"))
    contradictory = '{"usage":{"input_tokens":9},' + raw[1:]
    receipt = ac._create_provider_attempt_receipt(
        "anthropic", 1, 1, contradictory, ""
    )
    assert receipt.work_disposition == "ambiguous"


def test_duplicate_anthropic_success_bypass_is_demoted_at_public_boundary(tmp_path):
    raw = json.dumps(_zero_work_rejection(), separators=(",", ":"))
    contradictory = raw[:-1] + ',"is_error":false}'
    result, _, _ = _run_public(
        tmp_path,
        providers=["anthropic"],
        boundary_result=_completed(contradictory, returncode=0),
    )
    assert result.success is False
    assert result.provider_attempt_receipt.work_disposition == "ambiguous"
    assert "sk-syntheticsecret" not in result.output_text


def test_contradictory_stderr_prevents_not_started():
    receipt = ac._create_provider_attempt_receipt(
        "anthropic",
        1,
        1,
        json.dumps(_zero_work_rejection()),
        "connection reset after request acceptance",
    )
    assert receipt.work_disposition == "ambiguous"


def test_explicit_incomplete_capture_and_unknown_provider_fail_closed():
    raw = json.dumps(_zero_work_rejection())
    incomplete = ac._create_provider_attempt_receipt(
        "anthropic", 1, 1, raw, "", output_complete=False
    )
    unknown = ac._create_provider_attempt_receipt(
        "provider-name-from-untrusted-output", 1, 1, raw, ""
    )
    assert incomplete.work_disposition == "ambiguous"
    assert unknown.work_disposition == "ambiguous"
    assert unknown.provider == "unknown"


@pytest.mark.parametrize(
    "exc",
    [
        subprocess.TimeoutExpired(
            ["synthetic"], 1, output=b'{"usage":{"input_tokens":0}', stderr=b""
        ),
        ConnectionResetError("synthetic reset"),
    ],
    ids=["timeout-with-partial-output", "connection-reset"],
)
def test_timeout_and_reset_are_ambiguous(tmp_path, exc):
    result, _, _ = _run_public(
        tmp_path,
        providers=["anthropic"],
        boundary_result=exc,
    )
    receipt = result.provider_attempt_receipt
    assert receipt is not None
    assert receipt.failure_kind == "transport"
    assert receipt.work_disposition == "ambiguous"


@pytest.mark.parametrize("provider", ["google", "opencode"])
def test_other_standard_provider_schemas_do_not_borrow_anthropic_proof(
    tmp_path, provider
):
    with patch.dict("os.environ", {"OPENCODE_MODEL": "synthetic/model"}, clear=False):
        result, _, _ = _run_public(
            tmp_path,
            providers=[provider],
            boundary_result=_completed(json.dumps(_zero_work_rejection())),
        )
    receipt = result.provider_attempt_receipt
    assert receipt is not None
    assert receipt.provider == provider
    assert receipt.work_disposition == "ambiguous"


def test_google_reviewed_positive_stats_yield_started_or_billable(tmp_path):
    envelope = {
        "type": "error",
        "message": "synthetic failure",
        "stats": {
            "models": {
                "synthetic-model": {"tokens": {"prompt": 1, "candidates": 0}}
            }
        },
    }
    result, _, _ = _run_public(
        tmp_path,
        providers=["google"],
        boundary_result=_completed(json.dumps(envelope)),
    )
    assert result.provider_attempt_receipt.work_disposition == "started_or_billable"


def test_google_unknown_positive_field_does_not_claim_started():
    receipt = ac._create_provider_attempt_receipt(
        "google",
        1,
        1,
        json.dumps(
            {
                "type": "error",
                "stats": {"models": {"synthetic": {"future_counter": 1}}},
            }
        ),
        "",
    )
    assert receipt.work_disposition == "ambiguous"


def test_google_unknown_schema_with_known_tokens_is_ambiguous():
    receipt = ac._create_provider_attempt_receipt(
        "google",
        1,
        1,
        json.dumps(
            {
                "type": "future_result",
                "stats": {
                    "models": {"synthetic": {"tokens": {"prompt": 1}}}
                },
            }
        ),
        "",
    )
    assert receipt.work_disposition == "ambiguous"


def test_google_unhashable_failure_type_remains_ambiguous(tmp_path):
    result, _, _ = _run_public(
        tmp_path,
        providers=["google"],
        boundary_result=_completed(
            json.dumps({"type": [], "stats": {"models": {}}}),
            returncode=1,
        ),
    )
    assert result.success is False
    assert result.provider_attempt_receipt.work_disposition == "ambiguous"


def test_interactive_pty_failure_attaches_ambiguous_receipt(tmp_path):
    with patch.dict(
        "os.environ",
        {"PDD_CLAUDE_CODE_MODE": "interactive", "PDD_AGENTIC_PROVIDER": "anthropic"},
        clear=False,
    ), patch(
        "pdd.agentic_common.get_available_agents", return_value=["anthropic"]
    ), patch(
        "pdd.agentic_common._find_cli_binary", return_value="/synthetic/claude"
    ), patch(
        "pdd.agentic_common._strip_anthropic_creds_for_claude_subprocess"
    ), patch(
        "pdd.agentic_common._run_claude_interactive_with_mcp",
        return_value=ac._ProviderRunResult(
            False,
            "synthetic PTY failure request_id=req_PRIVATE session_id=sess_PRIVATE",
            0,
            None,
        ),
    ) as pty_boundary:
        result = ac.run_agentic_task(
            "synthetic PTY boundary",
            tmp_path,
            quiet=True,
            single_provider_attempt=True,
        )
    assert pty_boundary.call_count == 1
    assert result.provider_attempt_receipt.provider == "anthropic"
    assert result.provider_attempt_receipt.work_disposition == "ambiguous"
    assert "req_PRIVATE" not in result.output_text
    assert "sess_PRIVATE" not in result.output_text


def test_interactive_pty_positive_usage_yields_started_or_billable(tmp_path):
    usage = {
        "claude": [
            {
                "model": "synthetic-model",
                "input_tokens": 1,
                "output_tokens": 0,
                "cached_input_tokens": 0,
                "cache_creation_input_tokens": 0,
            }
        ]
    }
    with patch.dict(
        "os.environ",
        {"PDD_CLAUDE_CODE_MODE": "interactive", "PDD_AGENTIC_PROVIDER": "anthropic"},
        clear=False,
    ), patch(
        "pdd.agentic_common.get_available_agents", return_value=["anthropic"]
    ), patch(
        "pdd.agentic_common._find_cli_binary", return_value="/synthetic/claude"
    ), patch(
        "pdd.agentic_common._strip_anthropic_creds_for_claude_subprocess"
    ), patch(
        "pdd.agentic_common._run_claude_interactive_with_mcp",
        return_value=ac._ProviderRunResult(
            False, "synthetic PTY failure", 0, None, usage
        ),
    ):
        result = ac.run_agentic_task(
            "synthetic PTY boundary",
            tmp_path,
            quiet=True,
            single_provider_attempt=True,
        )
    assert result.provider_attempt_receipt.work_disposition == "started_or_billable"


def test_receipt_none_and_tuple_compatibility_for_success_and_ordinary_run(tmp_path):
    success_envelope = {
        "type": "result",
        "result": "A sufficiently long successful synthetic provider response.",
        "total_cost_usd": 0.25,
        "usage": {"input_tokens": 2, "output_tokens": 3},
        "modelUsage": {"synthetic-model": {}},
    }
    successful, _, _ = _run_public(
        tmp_path,
        providers=["anthropic"],
        boundary_result=_completed(json.dumps(success_envelope), returncode=0),
    )
    assert successful.provider_attempt_receipt is None
    assert successful.to_dict()["provider_attempt_receipt"] is None
    success, output, cost, provider = successful
    assert success is True
    assert output == success_envelope["result"]
    assert cost == pytest.approx(0.25)
    assert provider == "anthropic"
    assert len(successful) == 5
    assert successful[4] == successful.usage

    ordinary, _, _ = _run_public(
        tmp_path,
        providers=["anthropic"],
        boundary_result=_completed(json.dumps(_zero_work_rejection())),
        max_retries=1,
        single_provider_attempt=False,
    )
    assert ordinary.provider_attempt_receipt is None
    assert ordinary.to_dict()["provider_attempt_receipt"] is None


def test_false_positive_work_and_provider_environment_fail_closed(tmp_path):
    worked_but_empty = {
        "type": "result",
        "result": "",
        "total_cost_usd": 0.1,
        "usage": {"input_tokens": 1, "output_tokens": 0},
        "modelUsage": {"synthetic-model": {"costUSD": 0.1}},
    }
    demoted, _, _ = _run_public(
        tmp_path,
        providers=["anthropic"],
        boundary_result=_completed(json.dumps(worked_but_empty), returncode=0),
        max_retries=1,
    )
    assert demoted.provider_attempt_receipt.work_disposition == "started_or_billable"

    with patch.dict(
        "os.environ", {"PDD_AGENTIC_PROVIDER": "anthropic"}, clear=False
    ), patch(
        "pdd.agentic_common.get_available_agents", return_value=["anthropic"]
    ), patch(
        "pdd.agentic_common._run_with_provider",
        return_value=ac._ProviderRunResult(
            False,
            "Provider runtime requires interactive configuration.",
            0,
            None,
            provider_environment_reason="trust_prompt",
        ),
    ):
        environment = ac.run_agentic_task(
            "synthetic provider environment",
            tmp_path,
            quiet=True,
            single_provider_attempt=True,
        )
    assert environment.provider_environment_failure == (
        "anthropic",
        "trust_prompt",
    )
    assert environment.provider_attempt_receipt.work_disposition == "ambiguous"


def test_single_attempt_false_positive_diagnostic_does_not_echo_private_ids(tmp_path):
    envelope = {
        "type": "result",
        "result": "request_id=req_PRIVATE session_id=sess_PRIVATE",
        "total_cost_usd": 0,
        "usage": {"input_tokens": 0, "output_tokens": 0},
        "modelUsage": {},
    }
    result, _, _ = _run_public(
        tmp_path,
        providers=["anthropic"],
        boundary_result=_completed(json.dumps(envelope), returncode=0),
    )
    assert result.success is False
    assert result.provider_attempt_receipt.work_disposition == "ambiguous"
    assert "req_PRIVATE" not in result.output_text
    assert "sess_PRIVATE" not in result.output_text


@pytest.mark.uses_real_cli_detector
@pytest.mark.parametrize(
    ("version", "failure_kind", "work_disposition"),
    [
        (
            "2.1.263 (Claude Code)",
            "credential_or_account",
            "not_started",
        ),
        (
            "2.1.280 (Claude Code)",
            "credential_or_account",
            "not_started",
        ),
        (
            "2.1.119 (Claude Code)",
            "unknown",
            "ambiguous",
        ),
    ],
)
def test_fake_claude_executable_exercises_public_receipt_end_to_end(
    tmp_path,
    version,
    failure_kind,
    work_disposition,
):
    """Exercise discovery, process capture, classification, and serialization."""
    fake_cli = _write_fake_claude_executable(tmp_path)
    fake_home = tmp_path / "home"
    fake_home.mkdir()
    event_log = tmp_path / "claude-events.log"
    raw = json.dumps(
        _zero_work_rejection_280() if "2.1.280" in version else _zero_work_rejection(),
        separators=(",", ":"),
    )
    isolated_env = {
        "HOME": str(fake_home),
        "PATH": str(fake_cli.parent),
        "PDD_AGENTIC_PROVIDER": "anthropic",
        "PDD_AUTO_UPDATE": "false",
        "PDD_FAKE_CLAUDE_EVENTS": str(event_log),
        "PDD_FAKE_CLAUDE_PAYLOAD": raw,
        "PDD_FAKE_CLAUDE_VERSION": version,
    }

    with patch.dict(os.environ, isolated_env, clear=True):
        result = ac.run_agentic_task(
            "synthetic black-box receipt check",
            tmp_path,
            quiet=True,
            max_retries=7,
            single_provider_attempt=True,
            background_safe=True,
        )

    assert event_log.read_text(encoding="utf-8").splitlines() == [
        "attempt",
        "version",
    ]
    assert result.success is False

    serialized = result.to_dict()
    assert serialized["provider_attempt_receipt"] == {
        "schema_version": "pdd.provider_attempt.v1",
        "provider": "anthropic",
        "attempt_number": 1,
        "failure_kind": failure_kind,
        "work_disposition": work_disposition,
    }
    assert len(result.output_text) <= 500

    serialized_text = json.dumps(serialized, sort_keys=True)
    for private_value in (
        "sk-syntheticsecret",
        "11111111-2222-4333-8444-555555555555",
        "aaaaaaaa-bbbb-4ccc-8ddd-eeeeeeeeeeee",
        '"duration_api_ms"',
    ):
        assert private_value not in result.output_text
        assert private_value not in serialized_text
