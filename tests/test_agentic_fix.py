import os
import shutil
from pathlib import Path

import pandas as pd
import pytest

from pdd.agentic_fix import run_agentic_fix


def _df():
    return pd.DataFrame(
        [
            {"provider": "anthropic", "model": "claude-3",   "api_key": "ANTHROPIC_API_KEY"},
            {"provider": "google",    "model": "gemini-pro", "api_key": "GOOGLE_API_KEY"},
            {"provider": "openai",    "model": "gpt-4",      "api_key": "OPENAI_API_KEY"},
        ]
    )


def _prep_files(tmp_path: Path):
    prompt = tmp_path / "prompt.txt"
    code   = tmp_path / "code.py"
    testf  = tmp_path / "test_file.py"
    err    = tmp_path / "error.log"
    prompt.write_text("prompt", encoding="utf-8")
    code.write_text("print('bug')\n", encoding="utf-8")
    testf.write_text("assert True\n", encoding="utf-8")
    err.write_text("", encoding="utf-8")
    return str(prompt), str(code), str(testf), str(err)


@pytest.fixture
def patch_env(monkeypatch):
    monkeypatch.setenv("PDD_PATH", ".")
    monkeypatch.setenv("ANTHROPIC_API_KEY", "x")
    monkeypatch.setenv("GOOGLE_API_KEY", "x")
    monkeypatch.setenv("OPENAI_API_KEY", "x")
    monkeypatch.setenv("PDD_AGENTIC_LOGLEVEL", "quiet")


def test_run_agentic_fix_success_via_harvest(monkeypatch, tmp_path, patch_env):
    p_prompt, p_code, p_test, p_err = _prep_files(tmp_path)

    # Force model CSV to our in-test DF
    monkeypatch.setattr("pdd.agentic_fix._load_model_data", lambda _: _df())

    # Minimal prompt template (we just need .format(...) to succeed)
    monkeypatch.setattr(
        "pdd.agentic_fix.load_prompt_template",
        lambda name: "{code_abs}{test_abs}{begin}{end}{prompt_content}{code_content}{test_content}{error_content}",
    )

    # Pretend CLIs exist so selection proceeds
    monkeypatch.setattr("shutil.which", lambda _: "/usr/bin/shim")

    # Short-circuit harvest path to succeed — NOTE: correct symbol (no leading underscore)
    monkeypatch.setattr("pdd.agentic_fix.try_harvest_then_verify", lambda *a, **k: True)

    ok, msg, cost, model = run_agentic_fix(p_prompt, p_code, p_test, p_err)
    assert ok is True
    assert "successful" in msg.lower()
    assert cost > 0.0
    assert model.startswith("agentic-")


def test_run_agentic_fix_handles_no_keys(monkeypatch, tmp_path):
    p_prompt, p_code, p_test, p_err = _prep_files(tmp_path)
    # Force model CSV to in-test DF
    monkeypatch.setattr("pdd.agentic_fix._load_model_data", lambda _: _df())

    # Remove all relevant keys
    monkeypatch.delenv("ANTHROPIC_API_KEY", raising=False)
    monkeypatch.delenv("GEMINI_API_KEY", raising=False)
    monkeypatch.delenv("GOOGLE_API_KEY", raising=False)
    monkeypatch.delenv("OPENAI_API_KEY", raising=False)

    ok, msg, cost, model = run_agentic_fix(
        prompt_file=str(p_prompt),
        code_file=str(p_code),
        unit_test_file=str(p_test),
        error_log_file=str(p_err),
    )
    assert ok is False
    assert "No configured agent API keys" in msg


AGENTS = [
    ("anthropic", "ANTHROPIC_API_KEY", "claude"),
    ("google",    "GOOGLE_API_KEY",    "gemini"),  # allow GEMINI_API_KEY alias
    ("openai",    "OPENAI_API_KEY",    "codex"),
]


def _has_cli(cmd: str) -> bool:
    return shutil.which(cmd) is not None


def _mk_files(tmp_path: Path):
    p_prompt = tmp_path / "prompt.txt"
    p_code   = tmp_path / "code.py"
    p_test   = tmp_path / "test_dummy.py"
    p_err    = tmp_path / "error.log"
    p_prompt.write_text("Generate a simple function.", encoding="utf-8")
    p_code.write_text("def f():\n    return 1/0\n", encoding="utf-8")
    p_test.write_text("def test_ok(): assert True\n", encoding="utf-8")
    p_err.write_text("ZeroDivisionError", encoding="utf-8")
    return p_prompt, p_code, p_test, p_err


@pytest.mark.parametrize("provider,env_key,cli", AGENTS)
def test_run_agentic_fix_real_call_when_available(provider, env_key, cli, tmp_path, monkeypatch):
    # Only run if API key (or Gemini alias for Google) + CLI are present
    detected_key = os.getenv(env_key)
    if provider == "google" and not detected_key:
        detected_key = os.getenv("GEMINI_API_KEY")

    if not detected_key or not _has_cli(cli):
        pytest.skip(f"{provider} not available (missing API key and/or '{cli}' CLI).")

    # Ensure the model CSV used by the code matches our expected env var names
    monkeypatch.setattr("pdd.agentic_fix._load_model_data", lambda _: _df())

    # Prefer only this provider: drop others
    for k in ("ANTHROPIC_API_KEY", "GOOGLE_API_KEY", "GEMINI_API_KEY", "OPENAI_API_KEY"):
        if k != env_key:
            monkeypatch.delenv(k, raising=False)

    # Re-apply the cached key to the env var our CSV expects
    if provider == "google":
        monkeypatch.setenv("GOOGLE_API_KEY", detected_key)
    else:
        monkeypatch.setenv(env_key, detected_key)

    monkeypatch.setenv("PDD_PATH", ".")
    # Keep local verification off (agents may run on remote infra)
    monkeypatch.setenv("PDD_AGENTIC_VERIFY", "0")
    monkeypatch.setenv("PDD_AGENTIC_LOGLEVEL", "quiet")
    monkeypatch.setenv("PDD_AGENTIC_TIMEOUT", "120")
    monkeypatch.setenv("PDD_AGENTIC_VERIFY_TIMEOUT", "60")

    p_prompt, p_code, p_test, p_err = _mk_files(tmp_path)

    ok, msg, cost, model = run_agentic_fix(
        prompt_file=str(p_prompt),
        code_file=str(p_code),
        unit_test_file=str(p_test),
        error_log_file=str(p_err),
    )

    # Don’t require success; just verify the chosen agent tag
    assert model.startswith(f"agentic-{provider}")
