"""Tests for the tolerant session-log parser and proxy reconciliation."""

import json

from harness.context_snapshots.session_parser import parse_session_log, reconcile


def _write_session(tmp_path, events):
    path = tmp_path / "session.jsonl"
    path.write_text("\n".join(json.dumps(e) for e in events) + "\n")
    return path


def test_extracts_usage_and_tool_calls(tmp_path):
    events = [
        {"type": "session_meta", "payload": {"id": "abc"}},
        {
            "type": "event_msg",
            "payload": {
                "type": "token_count",
                "usage": {"input_tokens": 1200, "output_tokens": 40},
            },
        },
        {
            "type": "response_item",
            "payload": {"type": "function_call", "name": "shell"},
        },
        {
            "type": "response_item",
            "payload": {"type": "custom_tool_call", "name": "apply_patch"},
        },
        {
            "type": "event_msg",
            "payload": {
                "type": "token_count",
                "usage": {"input_tokens": 2500, "output_tokens": 60},
            },
        },
    ]
    summary = parse_session_log(_write_session(tmp_path, events))
    assert summary.parsed_lines == 5
    assert summary.malformed_lines == 0
    assert summary.request_count_estimate == 2
    assert summary.cumulative_input_tokens == 3700
    assert "shell" in summary.tool_call_names
    assert "apply_patch" in summary.tool_call_names


def test_malformed_lines_counted_not_fatal(tmp_path):
    path = tmp_path / "session.jsonl"
    path.write_text('{"type": "ok"}\nnot json at all\n{"type": "also_ok"}\n')
    summary = parse_session_log(path)
    assert summary.line_count == 3
    assert summary.parsed_lines == 2
    assert summary.malformed_lines == 1


def test_unknown_event_types_recorded(tmp_path):
    events = [{"type": "wormhole_sync", "payload": {}}]
    summary = parse_session_log(_write_session(tmp_path, events))
    assert "wormhole_sync" in summary.unknown_event_types


def test_reconcile_consistent(tmp_path):
    events = [
        {"usage": {"input_tokens": 1000, "output_tokens": 10}},
        {"usage": {"input_tokens": 2000, "output_tokens": 10}},
    ]
    summary = parse_session_log(_write_session(tmp_path, events))
    problems = reconcile(
        proxy_input_tokens_total=3000, proxy_request_count=2, session=summary
    )
    assert problems == []


def test_reconcile_flags_token_drift(tmp_path):
    events = [{"usage": {"input_tokens": 5000, "output_tokens": 10}}]
    summary = parse_session_log(_write_session(tmp_path, events))
    problems = reconcile(
        proxy_input_tokens_total=3000, proxy_request_count=1, session=summary
    )
    assert any("mismatch" in p for p in problems)


def test_reconcile_flags_bypassed_traffic(tmp_path):
    events = [
        {"usage": {"input_tokens": 100, "output_tokens": 1}},
        {"usage": {"input_tokens": 100, "output_tokens": 1}},
        {"usage": {"input_tokens": 100, "output_tokens": 1}},
    ]
    summary = parse_session_log(_write_session(tmp_path, events))
    problems = reconcile(
        proxy_input_tokens_total=300, proxy_request_count=2, session=summary
    )
    assert any("bypass" in p for p in problems)
