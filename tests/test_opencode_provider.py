"""Focused behavior tests for OpenCode provider integration (Issue #798).

Covers detection, model translation/resolution, JSONL output parsing, cost
parsing, _run_with_provider routing, and cli_detector wiring. Aligned with
the spec in pdd/prompts/agentic_common_python.prompt and the README's
PDD_AGENTIC_PROVIDER=opencode contract.
"""
from __future__ import annotations

import json
import os
import subprocess
from pathlib import Path
from unittest.mock import MagicMock, patch

import pytest

from pdd.agentic_common import (
    CLI_COMMANDS,
    _DEFAULT_PROVIDER_PREFERENCE,
    _PROVIDER_MODEL_ENV,
    _has_opencode_credentials,
    _opencode_auth_file_has_credentials,
    _parse_opencode_jsonl,
    _resolve_opencode_model,
    _run_with_provider,
    _translate_to_opencode_model,
    get_agent_provider_preference,
    get_available_agents,
)
from pdd import cli_detector


# ---------------------------------------------------------------------------
# Static wiring
# ---------------------------------------------------------------------------

def test_opencode_in_default_provider_preference():
    assert "opencode" in _DEFAULT_PROVIDER_PREFERENCE


def test_opencode_in_cli_commands():
    assert CLI_COMMANDS.get("opencode") == "opencode"


def test_opencode_provider_model_env():
    assert _PROVIDER_MODEL_ENV.get("opencode") == "OPENCODE_MODEL"


def test_pdd_agentic_provider_opencode_token_recognized():
    with patch.dict(os.environ, {"PDD_AGENTIC_PROVIDER": "opencode"}, clear=False):
        assert get_agent_provider_preference() == ["opencode"]


# ---------------------------------------------------------------------------
# Model translation
# ---------------------------------------------------------------------------

@pytest.mark.parametrize(
    "given,expected",
    [
        ("github_copilot/gpt-5", "github-copilot/gpt-5"),
        ("gemini/gemini-3-flash", "google/gemini-3-flash"),
        ("anthropic/claude-sonnet-4-6", "anthropic/claude-sonnet-4-6"),  # passthrough
        ("openrouter/openai/gpt-5.3-codex", "openrouter/openai/gpt-5.3-codex"),  # passthrough
        ("claude-sonnet-4-6", "anthropic/claude-sonnet-4-6"),  # bare anthropic
        ("gpt-5", "openai/gpt-5"),  # bare openai
    ],
)
def test_translate_to_opencode_model(given, expected):
    assert _translate_to_opencode_model(given) == expected


def test_resolve_opencode_model_from_env():
    assert _resolve_opencode_model({"OPENCODE_MODEL": "anthropic/claude-sonnet-4-6"}) == "anthropic/claude-sonnet-4-6"


def test_resolve_opencode_model_unset_returns_none():
    assert _resolve_opencode_model({}) is None


# ---------------------------------------------------------------------------
# JSONL parsing
# ---------------------------------------------------------------------------

def _jsonl(*events):
    return "\n".join(json.dumps(e) for e in events)


def test_parse_opencode_jsonl_text_and_cost():
    stdout = _jsonl(
        {"type": "step_start"},
        {"type": "text", "part": {"text": "Hello "}},
        {"type": "text", "part": {"text": "world."}},
        {"type": "step_finish", "part": {"cost": 0.0125, "usage": {"input_tokens": 100, "output_tokens": 50}}},
        {"type": "session.end", "model": "anthropic/claude-sonnet-4-6"},
    )
    parsed = _parse_opencode_jsonl(stdout)
    assert parsed["text"] == "Hello world."
    assert parsed["cost"] == pytest.approx(0.0125)
    assert parsed["cost_reported"] is True
    assert parsed["error"] == ""
    assert parsed["model"] == "anthropic/claude-sonnet-4-6"
    assert parsed["tokens"]["input"] == 100
    assert parsed["tokens"]["output"] == 50


def test_parse_opencode_jsonl_multiple_step_finish_costs_sum():
    stdout = _jsonl(
        {"type": "text", "part": {"text": "a"}},
        {"type": "step_finish", "part": {"cost": 0.01}},
        {"type": "text", "part": {"text": "b"}},
        {"type": "step_finish", "part": {"cost": 0.02}},
    )
    parsed = _parse_opencode_jsonl(stdout)
    assert parsed["text"] == "ab"
    assert parsed["cost"] == pytest.approx(0.03)
    assert parsed["cost_reported"] is True


def test_parse_opencode_jsonl_error_event():
    stdout = _jsonl(
        {"type": "text", "part": {"text": "partial"}},
        {"type": "error", "message": "provider not configured"},
    )
    parsed = _parse_opencode_jsonl(stdout)
    assert parsed["error"] == "provider not configured"


def test_parse_opencode_jsonl_no_cost_reported():
    stdout = _jsonl(
        {"type": "text", "part": {"text": "x"}},
        {"type": "step_finish", "part": {}},
    )
    parsed = _parse_opencode_jsonl(stdout)
    assert parsed["cost"] == 0.0
    assert parsed["cost_reported"] is False


def test_parse_opencode_jsonl_ignores_non_json_lines():
    stdout = "not json\n" + json.dumps({"type": "text", "part": {"text": "ok"}}) + "\nalso not json\n"
    parsed = _parse_opencode_jsonl(stdout)
    assert parsed["text"] == "ok"


def test_parse_opencode_jsonl_empty():
    parsed = _parse_opencode_jsonl("")
    assert parsed["text"] == ""
    assert parsed["cost"] == 0.0
    assert parsed["cost_reported"] is False


# ---------------------------------------------------------------------------
# Credential detection
# ---------------------------------------------------------------------------

def test_opencode_auth_file_with_provider_data(tmp_path):
    auth = tmp_path / "auth.json"
    auth.write_text(json.dumps({"anthropic": {"type": "api", "key": "sk-..."}}), encoding="utf-8")
    assert _opencode_auth_file_has_credentials(auth) is True


def test_opencode_auth_file_empty_dict_is_not_credential(tmp_path):
    auth = tmp_path / "auth.json"
    auth.write_text("{}", encoding="utf-8")
    assert _opencode_auth_file_has_credentials(auth) is False


def test_opencode_auth_file_missing(tmp_path):
    assert _opencode_auth_file_has_credentials(tmp_path / "nope.json") is False


def test_has_opencode_credentials_via_env(monkeypatch, tmp_path):
    # Ensure no auth.json or config files exist.
    monkeypatch.setattr(Path, "home", lambda: tmp_path)
    monkeypatch.chdir(tmp_path)
    monkeypatch.delenv("OPENCODE_CONFIG", raising=False)
    # Clear all backing-provider env vars to a known state, then set one.
    for k in (
        "ANTHROPIC_API_KEY", "OPENAI_API_KEY", "GEMINI_API_KEY", "GOOGLE_API_KEY",
        "OPENROUTER_API_KEY", "GITHUB_TOKEN", "XAI_API_KEY", "DEEPSEEK_API_KEY",
        "MISTRAL_API_KEY", "COHERE_API_KEY", "MOONSHOT_API_KEY", "AZURE_API_KEY",
    ):
        monkeypatch.delenv(k, raising=False)
    monkeypatch.setenv("ANTHROPIC_API_KEY", "sk-ant-test")
    assert _has_opencode_credentials(cwd=tmp_path) is True


def test_has_opencode_credentials_no_signals(monkeypatch, tmp_path):
    monkeypatch.setattr(Path, "home", lambda: tmp_path)
    monkeypatch.chdir(tmp_path)
    monkeypatch.delenv("OPENCODE_CONFIG", raising=False)
    for k in (
        "ANTHROPIC_API_KEY", "OPENAI_API_KEY", "GEMINI_API_KEY", "GOOGLE_API_KEY",
        "OPENROUTER_API_KEY", "GITHUB_TOKEN", "XAI_API_KEY", "DEEPSEEK_API_KEY",
        "MISTRAL_API_KEY", "COHERE_API_KEY", "MOONSHOT_API_KEY", "AZURE_API_KEY",
        "AZURE_AI_API_KEY", "AWS_ACCESS_KEY_ID", "GROQ_API_KEY", "TOGETHERAI_API_KEY",
        "FIREWORKS_AI_API_KEY", "FIREWORKS_API_KEY", "PERPLEXITYAI_API_KEY",
        "REPLICATE_API_KEY", "DEEPINFRA_API_KEY", "ZAI_API_KEY", "DASHSCOPE_API_KEY",
        "MINIMAX_API_KEY", "OLLAMA_HOST", "LMSTUDIO_HOST",
    ):
        monkeypatch.delenv(k, raising=False)
    assert _has_opencode_credentials(cwd=tmp_path) is False


def test_opencode_model_env_alone_is_not_a_credential(monkeypatch, tmp_path):
    """OPENCODE_MODEL is a model knob, not a credential."""
    monkeypatch.setattr(Path, "home", lambda: tmp_path)
    monkeypatch.chdir(tmp_path)
    monkeypatch.delenv("OPENCODE_CONFIG", raising=False)
    for k in (
        "ANTHROPIC_API_KEY", "OPENAI_API_KEY", "GEMINI_API_KEY", "GOOGLE_API_KEY",
        "OPENROUTER_API_KEY", "GITHUB_TOKEN", "XAI_API_KEY", "DEEPSEEK_API_KEY",
        "MISTRAL_API_KEY", "COHERE_API_KEY", "MOONSHOT_API_KEY", "AZURE_API_KEY",
        "AZURE_AI_API_KEY", "AWS_ACCESS_KEY_ID", "GROQ_API_KEY", "TOGETHERAI_API_KEY",
        "FIREWORKS_AI_API_KEY", "FIREWORKS_API_KEY", "PERPLEXITYAI_API_KEY",
        "REPLICATE_API_KEY", "DEEPINFRA_API_KEY", "ZAI_API_KEY", "DASHSCOPE_API_KEY",
        "MINIMAX_API_KEY", "OLLAMA_HOST", "LMSTUDIO_HOST",
    ):
        monkeypatch.delenv(k, raising=False)
    monkeypatch.setenv("OPENCODE_MODEL", "anthropic/claude-sonnet-4-6")
    assert _has_opencode_credentials(cwd=tmp_path) is False


# ---------------------------------------------------------------------------
# get_available_agents
# ---------------------------------------------------------------------------

def test_get_available_agents_includes_opencode_when_credentials_present(monkeypatch):
    """opencode CLI present + ANTHROPIC_API_KEY -> opencode in available agents."""
    # Make _find_cli_binary return a path only for opencode.
    def _fake_find(name, *args, **kwargs):
        return "/usr/local/bin/opencode" if name == "opencode" else None

    with (
        patch("pdd.agentic_common._find_cli_binary", side_effect=_fake_find),
        patch.dict(os.environ, {"ANTHROPIC_API_KEY": "sk-ant-test"}, clear=True),
        patch("pdd.agentic_common._has_gemini_oauth_credentials", return_value=False),
        patch("pdd.agentic_common._has_codex_auth_file", return_value=False),
    ):
        agents = get_available_agents()
    assert "opencode" in agents


def test_get_available_agents_excludes_opencode_when_cli_missing(monkeypatch):
    with (
        patch("pdd.agentic_common._find_cli_binary", return_value=None),
        patch.dict(os.environ, {"ANTHROPIC_API_KEY": "sk-ant-test"}, clear=True),
        patch("pdd.agentic_common._has_gemini_oauth_credentials", return_value=False),
        patch("pdd.agentic_common._has_codex_auth_file", return_value=False),
    ):
        agents = get_available_agents()
    assert "opencode" not in agents


def test_get_available_agents_excludes_opencode_when_no_credentials(monkeypatch):
    def _fake_find(name, *args, **kwargs):
        return "/usr/local/bin/opencode" if name == "opencode" else None

    with (
        patch("pdd.agentic_common._find_cli_binary", side_effect=_fake_find),
        patch.dict(os.environ, {}, clear=True),
        patch("pdd.agentic_common._has_gemini_oauth_credentials", return_value=False),
        patch("pdd.agentic_common._has_codex_auth_file", return_value=False),
        patch("pdd.agentic_common._has_opencode_credentials", return_value=False),
    ):
        agents = get_available_agents()
    assert "opencode" not in agents


# ---------------------------------------------------------------------------
# _run_with_provider routing
# ---------------------------------------------------------------------------

def test_run_with_provider_opencode_unknown_returns_actionable_error(tmp_path):
    """No OPENCODE_MODEL -> fail fast with an actionable message."""
    prompt_file = tmp_path / "prompt.txt"
    prompt_file.write_text("do thing", encoding="utf-8")
    with (
        patch("pdd.agentic_common._find_cli_binary", return_value="/usr/local/bin/opencode"),
        patch.dict(os.environ, {}, clear=True),
    ):
        success, msg, cost, model = _run_with_provider(
            "opencode", prompt_file, tmp_path, timeout=5, quiet=True,
        )
    assert success is False
    assert "OPENCODE_MODEL" in msg
    assert cost == 0.0


def test_run_with_provider_opencode_routes_to_opencode_run(tmp_path):
    """OpenCode route invokes `opencode run --format json --model ...` and
    parses JSONL output (text + cost)."""
    prompt_file = tmp_path / "prompt.txt"
    prompt_file.write_text("instructions go here", encoding="utf-8")

    # Mock the JSONL stdout the CLI would emit.
    fake_stdout = "\n".join([
        json.dumps({"type": "step_start"}),
        json.dumps({"type": "text", "part": {"text": "Hi."}}),
        json.dumps({"type": "step_finish", "part": {"cost": 0.0042}}),
        json.dumps({"type": "session.end", "model": "anthropic/claude-sonnet-4-6"}),
    ])
    fake_proc = MagicMock(returncode=0, stdout=fake_stdout, stderr="")

    with (
        patch("pdd.agentic_common._find_cli_binary", return_value="/usr/local/bin/opencode"),
        patch("pdd.agentic_common._subprocess_run", return_value=fake_proc) as run_mock,
        patch.dict(
            os.environ,
            {"OPENCODE_MODEL": "anthropic/claude-sonnet-4-6"},
            clear=True,
        ),
    ):
        success, output, cost, model = _run_with_provider(
            "opencode", prompt_file, tmp_path, timeout=10, quiet=True,
        )

    assert success is True
    assert output == "Hi."
    assert cost == pytest.approx(0.0042)

    # Verify the command shape: opencode run --dir <cwd> --format json
    # --dangerously-skip-permissions --model ...
    invoked_cmd = run_mock.call_args.args[0]
    assert invoked_cmd[0] == "/usr/local/bin/opencode"
    assert invoked_cmd[1] == "run"
    assert "--format" in invoked_cmd and "json" in invoked_cmd
    assert "--model" in invoked_cmd
    model_idx = invoked_cmd.index("--model")
    assert invoked_cmd[model_idx + 1] == "anthropic/claude-sonnet-4-6"
    # Prompt content must NOT be passed as a single argv element.
    assert "instructions go here" not in invoked_cmd
    # The trailing -- separator is present.
    assert "--" in invoked_cmd


def test_run_with_provider_opencode_passes_agent_and_variant(tmp_path):
    prompt_file = tmp_path / "prompt.txt"
    prompt_file.write_text("x", encoding="utf-8")
    fake_stdout = json.dumps({"type": "text", "part": {"text": "ok"}})
    fake_proc = MagicMock(returncode=0, stdout=fake_stdout, stderr="")

    with (
        patch("pdd.agentic_common._find_cli_binary", return_value="/usr/local/bin/opencode"),
        patch("pdd.agentic_common._subprocess_run", return_value=fake_proc) as run_mock,
        patch.dict(
            os.environ,
            {
                "OPENCODE_MODEL": "anthropic/claude-sonnet-4-6",
                "OPENCODE_AGENT": "build",
                "OPENCODE_VARIANT": "thinking",
            },
            clear=True,
        ),
    ):
        _run_with_provider("opencode", prompt_file, tmp_path, timeout=10, quiet=True)

    invoked_cmd = run_mock.call_args.args[0]
    assert "--agent" in invoked_cmd and "build" in invoked_cmd
    assert "--variant" in invoked_cmd and "thinking" in invoked_cmd


def test_run_with_provider_opencode_propagates_error_event(tmp_path):
    prompt_file = tmp_path / "prompt.txt"
    prompt_file.write_text("x", encoding="utf-8")
    fake_stdout = "\n".join([
        json.dumps({"type": "text", "part": {"text": "partial output"}}),
        json.dumps({"type": "error", "message": "provider not configured"}),
    ])
    fake_proc = MagicMock(returncode=0, stdout=fake_stdout, stderr="")

    with (
        patch("pdd.agentic_common._find_cli_binary", return_value="/usr/local/bin/opencode"),
        patch("pdd.agentic_common._subprocess_run", return_value=fake_proc),
        patch.dict(
            os.environ,
            {"OPENCODE_MODEL": "anthropic/claude-sonnet-4-6"},
            clear=True,
        ),
    ):
        success, output, cost, model = _run_with_provider(
            "opencode", prompt_file, tmp_path, timeout=10, quiet=True,
        )

    assert success is False
    assert "provider not configured" in output


def test_run_with_provider_opencode_cli_missing(tmp_path):
    prompt_file = tmp_path / "prompt.txt"
    prompt_file.write_text("x", encoding="utf-8")
    with (
        patch("pdd.agentic_common._find_cli_binary", return_value=None),
        patch.dict(
            os.environ,
            {"OPENCODE_MODEL": "anthropic/claude-sonnet-4-6"},
            clear=True,
        ),
    ):
        success, msg, cost, model = _run_with_provider(
            "opencode", prompt_file, tmp_path, timeout=5, quiet=True,
        )
    assert success is False
    assert "opencode" in msg.lower() and "not found" in msg.lower()
    assert cost == 0.0


# ---------------------------------------------------------------------------
# cli_detector wiring
# ---------------------------------------------------------------------------

def test_cli_detector_has_opencode_entries():
    assert cli_detector._CLI_COMMANDS.get("opencode") == "opencode"
    assert cli_detector._CLI_DISPLAY_NAMES.get("opencode") == "OpenCode CLI"
    assert "opencode-ai" in cli_detector._INSTALL_COMMANDS.get("opencode", "")
    assert cli_detector.PROVIDER_DISPLAY.get("opencode") == "OpenCode"


def test_cli_detector_table_order_includes_opencode():
    providers = [row[0] for row in cli_detector._TABLE_ORDER]
    assert "opencode" in providers
    cli_names = [row[1] for row in cli_detector._TABLE_ORDER]
    assert "opencode" in cli_names


def test_cli_detector_has_provider_oauth_opencode_with_creds(monkeypatch, tmp_path):
    """auth.json with provider data -> _has_provider_oauth('opencode') True."""
    monkeypatch.setattr(Path, "home", lambda: tmp_path)
    auth_dir = tmp_path / ".local" / "share" / "opencode"
    auth_dir.mkdir(parents=True)
    (auth_dir / "auth.json").write_text(
        json.dumps({"anthropic": {"type": "api", "key": "sk-..."}}),
        encoding="utf-8",
    )
    assert cli_detector._has_provider_oauth("opencode") is True


def test_cli_detector_has_provider_oauth_opencode_without_creds(monkeypatch, tmp_path):
    monkeypatch.setattr(Path, "home", lambda: tmp_path)
    assert cli_detector._has_provider_oauth("opencode") is False
