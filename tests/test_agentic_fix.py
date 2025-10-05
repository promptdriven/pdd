# tests/test_agentic_e2e.py
import os
import shutil
import multiprocessing as mp
from pathlib import Path

import pytest

from pdd.agentic_fix import run_agentic_fix


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


def _make_mini_project(root: Path):
    (root / "prompts").mkdir()
    (root / "src").mkdir()
    (root / "tests").mkdir()
    # use *_python.prompt to be consistent with your other suite
    (root / "prompts" / "utils_python.prompt").write_text(PROMPT, encoding="utf-8")
    (root / "src" / "utils.py").write_text(BUGGY, encoding="utf-8")
    (root / "src" / "config.json").write_text(CONFIG, encoding="utf-8")
    (root / "tests" / "test_utils.py").write_text(TESTS, encoding="utf-8")
    (root / "error.log").write_text(ERRLOG, encoding="utf-8")


def _worker(q, prompt_file, code_file, unit_test_file, error_log_file):
    try:
        ok, msg = run_agentic_fix(
            prompt_file=prompt_file,
            code_file=code_file,
            unit_test_file=unit_test_file,
            error_log_file=error_log_file,
        )
        q.put((ok, msg))
    except Exception as e:
        q.put((False, f"exception: {e!r}"))


def _run_with_timeout(seconds: int, *args):
    q = mp.Queue()
    p = mp.Process(target=_worker, args=(q, *args))
    p.start()
    p.join(seconds)
    if p.is_alive():
        p.terminate()
        p.join(5)
        return False, "timeout"
    return q.get() if not q.empty() else (False, "no-result")


def _has_cli(name: str) -> bool:
    return shutil.which(name) is not None


@pytest.mark.e2e
def test_real_gemini_agent(tmp_path, monkeypatch):
    """Real-agent test for Google's Gemini CLI."""
    if not os.getenv("GOOGLE_API_KEY") and not os.getenv("GEMINI_API_KEY"):
        pytest.skip("No GOOGLE_API_KEY/GEMINI_API_KEY in environment.")
    if not _has_cli("gemini"):
        pytest.skip("Gemini CLI not found in PATH (need `gemini`).")

    # Prefer Google; remove others
    monkeypatch.delenv("ANTHROPIC_API_KEY", raising=False)
    monkeypatch.delenv("OPENAI_API_KEY", raising=False)
    if not os.getenv("GOOGLE_API_KEY") and os.getenv("GEMINI_API_KEY"):
        monkeypatch.setenv("GOOGLE_API_KEY", os.environ["GEMINI_API_KEY"])

    # logging
    monkeypatch.setenv("PDD_AGENTIC_LOGLEVEL", os.getenv("PDD_AGENTIC_LOGLEVEL", "normal"))
    monkeypatch.setenv("PDD_AGENTIC_MAX_LOG_LINES", os.getenv("PDD_AGENTIC_MAX_LOG_LINES", "2000"))
    monkeypatch.setenv("PDD_AGENTIC_TIMEOUT", os.getenv("PDD_AGENTIC_TIMEOUT", "180"))
    monkeypatch.setenv("PDD_AGENTIC_VERIFY_TIMEOUT", os.getenv("PDD_AGENTIC_VERIFY_TIMEOUT", "90"))
    monkeypatch.setenv("NO_COLOR", "1")
    monkeypatch.setenv("CLICOLOR", "0")
    monkeypatch.setenv("CLICOLOR_FORCE", "0")

    project = tmp_path
    _make_mini_project(project)
    monkeypatch.chdir(project)

    ok, msg = _run_with_timeout(
        180,
        "prompts/utils_python.prompt", "src/utils.py", "tests/test_utils.py", "error.log"
    )
    if msg == "timeout":
        pytest.xfail("Gemini run hit hard timeout.")
    assert ok, f"Gemini should succeed via agent. msg={msg}"
    fixed = (project / "src" / "utils.py").read_text(encoding="utf-8")
    assert ".get(" in fixed and "['name']" not in fixed


@pytest.mark.e2e
def test_real_claude_agent(tmp_path, monkeypatch):
    """Real-agent test for Anthropic's Claude CLI."""
    if not os.getenv("ANTHROPIC_API_KEY"):
        pytest.skip("No ANTHROPIC_API_KEY in environment.")
    if not _has_cli("claude"):
        pytest.skip("Claude CLI not found in PATH (need `claude`).")

    # Prefer Anthropic; remove others
    monkeypatch.delenv("GOOGLE_API_KEY", raising=False)
    monkeypatch.delenv("GEMINI_API_KEY", raising=False)
    monkeypatch.delenv("OPENAI_API_KEY", raising=False)

    # logging
    monkeypatch.setenv("PDD_AGENTIC_LOGLEVEL", os.getenv("PDD_AGENTIC_LOGLEVEL", "normal"))
    monkeypatch.setenv("PDD_AGENTIC_MAX_LOG_LINES", os.getenv("PDD_AGENTIC_MAX_LOG_LINES", "2000"))
    monkeypatch.setenv("PDD_AGENTIC_TIMEOUT", os.getenv("PDD_AGENTIC_TIMEOUT", "180"))
    monkeypatch.setenv("PDD_AGENTIC_VERIFY_TIMEOUT", os.getenv("PDD_AGENTIC_VERIFY_TIMEOUT", "90"))
    monkeypatch.setenv("NO_COLOR", "1")
    monkeypatch.setenv("CLICOLOR", "0")
    monkeypatch.setenv("CLICOLOR_FORCE", "0")

    project = tmp_path
    _make_mini_project(project)
    monkeypatch.chdir(project)

    ok, msg = _run_with_timeout(
        180,
        "prompts/utils_python.prompt", "src/utils.py", "tests/test_utils.py", "error.log"
    )
    if msg == "timeout":
        pytest.xfail("Claude run hit hard timeout.")
    assert ok, f"Claude should succeed via agent. msg={msg}"
    fixed = (project / "src" / "utils.py").read_text(encoding="utf-8")

    # Accept either dict.get(...) or try/except guarding KeyError
    assert (".get(" in fixed) or ("except KeyError" in fixed), \
        "Agent must either use dict.get(...) or guard KeyError with try/except."

    # Optional extra sanity: the function actually returns a greeting
    import importlib.util
    spec = importlib.util.spec_from_file_location("utils", project / "src" / "utils.py")
    mod = importlib.util.module_from_spec(spec); spec.loader.exec_module(mod)
    assert "Hello" in mod.get_greeting()


@pytest.mark.e2e
def test_real_codex_agent(tmp_path, monkeypatch):
    """Real-agent test for OpenAI Codex-style CLI (codex)."""
    if not os.getenv("OPENAI_API_KEY"):
        pytest.skip("No OPENAI_API_KEY in environment.")
    if not _has_cli("codex"):
        pytest.skip("Codex CLI not found in PATH (need `codex`).")

    # Prefer OpenAI; remove others
    monkeypatch.delenv("GOOGLE_API_KEY", raising=False)
    monkeypatch.delenv("GEMINI_API_KEY", raising=False)
    monkeypatch.delenv("ANTHROPIC_API_KEY", raising=False)

    # tighter verify for codex
    monkeypatch.setenv("PDD_AGENTIC_LOGLEVEL", os.getenv("PDD_AGENTIC_LOGLEVEL", "normal"))
    monkeypatch.setenv("PDD_AGENTIC_MAX_LOG_LINES", os.getenv("PDD_AGENTIC_MAX_LOG_LINES", "2000"))
    monkeypatch.setenv("PDD_AGENTIC_TIMEOUT", os.getenv("PDD_AGENTIC_TIMEOUT", "150"))
    monkeypatch.setenv("PDD_AGENTIC_VERIFY_TIMEOUT", os.getenv("PDD_AGENTIC_VERIFY_TIMEOUT", "60"))
    monkeypatch.setenv("NO_COLOR", "1")
    monkeypatch.setenv("CLICOLOR", "0")
    monkeypatch.setenv("CLICOLOR_FORCE", "0")

    project = tmp_path
    _make_mini_project(project)
    monkeypatch.chdir(project)

    ok, msg = _run_with_timeout(
        180,
        "prompts/utils_python.prompt", "src/utils.py", "tests/test_utils.py", "error.log"
    )
    if msg == "timeout":
        pytest.xfail("Codex run hit hard timeout.")
    assert ok, f"OpenAI/Codex should succeed via agent. msg={msg}"
    fixed = (project / "src" / "utils.py").read_text(encoding="utf-8")
    assert ".get(" in fixed and "['name']" not in fixed
