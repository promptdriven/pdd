import os
import sys
import stat
import shutil
import subprocess
from pathlib import Path

import pandas as pd
import pytest

from pdd.agentic_fix import run_agentic_fix

# --- Shared mini project content ---
PROMPT = "Handle missing 'name' key gracefully."
BUGGY = """import json
from pathlib import Path

def get_greeting():
    cfg = Path(__file__).parent / 'config.json'
    with cfg.open('r') as f:
        config = json.load(f)
    # fragile: KeyError if 'name' missing
    name = config['user']['name']
    return f'Hello, {name}!'
"""
TESTS = """import unittest
from src import utils

class TestGreeting(unittest.TestCase):
    def test_get_greeting(self):
        msg = utils.get_greeting()
        assert "Hello" in msg
"""
CONFIG = '{"user": {"email": "test@example.com"}}'
ERRLOG = "KeyError: 'name'"

@pytest.fixture
def mini_project(tmp_path):
    root = tmp_path
    (root / "prompts").mkdir()
    (root / "src").mkdir()
    (root / "tests").mkdir()
    # project files
    (root / "prompts" / "utils.prompt").write_text(PROMPT, encoding="utf-8")
    (root / "src" / "utils.py").write_text(BUGGY, encoding="utf-8")
    (root / "src" / "config.json").write_text(CONFIG, encoding="utf-8")
    (root / "tests" / "test_utils.py").write_text(TESTS, encoding="utf-8")
    (root / "error.log").write_text(ERRLOG, encoding="utf-8")
    # .pdd with llm_model.csv (we’ll monkeypatch loader anyway; still nice to have)
    (root / ".pdd").mkdir()
    (root / ".pdd" / "llm_model.csv").write_text(
        "provider,model,api_key\ngoogle,gemini-pro,GOOGLE_API_KEY\nopenai,gpt-4,OPENAI_API_KEY\n",
        encoding="utf-8",
    )
    return root


def _df_google_openai():
    return pd.DataFrame.from_records(
        [
            {"provider": "google", "model": "gemini-pro", "api_key": "GOOGLE_API_KEY"},
            {"provider": "openai", "model": "gpt-4", "api_key": "OPENAI_API_KEY"},
        ]
    )


def _harvested_code(name_default: str = "Guest") -> str:
    return f"""import json
from pathlib import Path

def get_greeting():
    cfg = Path(__file__).parent / 'config.json'
    with cfg.open('r') as f:
        config = json.load(f)
    # use .get with default
    name = (config.get("user") or {{}}).get("name", "{name_default}")
    return f'Hello, {{name}}!'
"""


def _patch_env_and_loader(monkeypatch):
    # Present GOOGLE_API_KEY so google is considered available
    monkeypatch.setenv("GOOGLE_API_KEY", "DUMMY")
    # OPENAI_API_KEY present too (for tests that need skipping codex)
    monkeypatch.setenv("OPENAI_API_KEY", "DUMMY_OPENAI")
    # Make the loader return our controlled dataframe
    monkeypatch.setattr("pdd.agentic_fix._load_model_data", lambda _: _df_google_openai(), raising=True)


# -------------------------------
# 1) Absolute-path harvest applies
# -------------------------------
def test_harvest_applies_with_absolute_markers(mini_project, monkeypatch):
    from pdd import agentic_fix as AF

    _patch_env_and_loader(monkeypatch)

    # Pretend gemini CLI exists
    monkeypatch.setattr(shutil, "which", lambda bin: "/usr/bin/gemini" if bin == "gemini" else None)

    # Build absolute markers the same way the SUT does (resolve)
    code_path = (mini_project / "src" / "utils.py").resolve()
    begin = f"<<<BEGIN_FILE:{code_path}>>>"
    end = f"<<<END_FILE:{code_path}>>>"
    stdout_with_markers = f"{begin}\n{_harvested_code('World')}{end}\n"

    real_run = subprocess.run

    def fake_run(cmd, **kwargs):
        # The agent invocation
        if isinstance(cmd, (list, tuple)) and cmd[:2] == ["gemini", "implement"]:
            return subprocess.CompletedProcess(cmd, 0, stdout=stdout_with_markers, stderr="")
        # Pytest verification should be real
        return real_run(cmd, **kwargs)

    monkeypatch.setattr("subprocess.run", fake_run, raising=True)

    # Run inside the temp project
    monkeypatch.chdir(mini_project)
    ok, msg = run_agentic_fix(
        prompt_file="prompts/utils.prompt",
        code_file="src/utils.py",
        unit_test_file="tests/test_utils.py",
        error_log_file="error.log",
    )

    assert ok, f"Expected success, got: {msg}"
    fixed = (mini_project / "src" / "utils.py").read_text(encoding="utf-8")
    assert 'get("name", "World")' in fixed
    # run the test file again to be extra sure
    res = subprocess.run([sys.executable, "-m", "pytest", "tests/test_utils.py", "-q"], capture_output=True, text=True)
    assert res.returncode == 0, f"Downstream tests failed:\n{res.stdout}\n{res.stderr}"


# ------------------------------------------------------
# 2) Path-variant harvesting: relative path & filename-only
# ------------------------------------------------------
@pytest.mark.parametrize("variant", ["relative", "filename"])
def test_harvest_path_variants(mini_project, monkeypatch, variant):
    from pdd import agentic_fix as AF

    _patch_env_and_loader(monkeypatch)
    monkeypatch.setattr(shutil, "which", lambda bin: "/usr/bin/gemini" if bin == "gemini" else None)

    code_abs = (mini_project / "src" / "utils.py").resolve()
    if variant == "relative":
        marker_path = str(mini_project / "src" / "utils.py")
    else:
        marker_path = "utils.py"

    begin = f"<<<BEGIN_FILE:{marker_path}>>>"
    end = f"<<<END_FILE:{marker_path}>>>"
    stdout_with_markers = f"{begin}\n{_harvested_code('Guest')}{end}\n"

    real_run = subprocess.run

    def fake_run(cmd, **kwargs):
        if isinstance(cmd, (list, tuple)) and cmd[:2] == ["gemini", "implement"]:
            return subprocess.CompletedProcess(cmd, 0, stdout=stdout_with_markers, stderr="")
        return real_run(cmd, **kwargs)

    monkeypatch.setattr("subprocess.run", fake_run, raising=True)
    monkeypatch.chdir(mini_project)

    ok, msg = run_agentic_fix(
        prompt_file="prompts/utils.prompt",
        code_file="src/utils.py",
        unit_test_file="tests/test_utils.py",
        error_log_file="error.log",
    )
    assert ok, f"Harvest for variant {variant} should succeed. Msg: {msg}"
    fixed = (mini_project / "src" / "utils.py").read_text(encoding="utf-8")
    assert 'get("name", "Guest")' in fixed


# ---------------------------------------------------------
# 3) Timeout on first agent & missing CLI for the next agent
# ---------------------------------------------------------
def test_timeout_and_missing_cli_path(mini_project, monkeypatch):
    """
    Simulate gemini timing out and codex missing from PATH.
    Expect overall failure with a useful message (but no crash).
    """
    from pdd import agentic_fix as AF

    _patch_env_and_loader(monkeypatch)

    def fake_which(bin):
        if bin == "gemini":
            return "/usr/bin/gemini"
        if bin == "codex":
            return None  # not in PATH
        return None

    monkeypatch.setattr(shutil, "which", fake_which, raising=True)

    real_run = subprocess.run

    def fake_run(cmd, **kwargs):
        # Raise timeout for gemini agent call
        if isinstance(cmd, (list, tuple)) and cmd[:2] == ["gemini", "implement"]:
            raise subprocess.TimeoutExpired(cmd=cmd, timeout=kwargs.get("timeout", 60))
        return real_run(cmd, **kwargs)

    monkeypatch.setattr("subprocess.run", fake_run, raising=True)
    monkeypatch.chdir(mini_project)

    ok, msg = run_agentic_fix(
        prompt_file="prompts/utils.prompt",
        code_file="src/utils.py",
        unit_test_file="tests/test_utils.py",
        error_log_file="error.log",
    )
    assert not ok, "Should report failure when first agent times out and second is missing."
    assert "timed out" in msg.lower() or "failed" in msg.lower()
