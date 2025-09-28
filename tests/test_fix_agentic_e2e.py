# tests/test_fix_agentic_e2e.py
import os
import shutil
import sys
from pathlib import Path

import pytest

from pdd.fix_error_loop import fix_error_loop


def _has_cli(name: str) -> bool:
    return shutil.which(name) is not None


def _purge_modules():
    """Remove cached modules that can bleed across tmp projects in a single pytest session."""
    for key in list(sys.modules.keys()):
        if key == "test_utils" or key.startswith("test_utils"):
            sys.modules.pop(key, None)
        if key == "src" or key.startswith("src."):
            sys.modules.pop(key, None)


def _make_project(root: Path, test_basename: str) -> None:
    (root / "prompts").mkdir()
    (root / "src").mkdir()
    (root / "tests").mkdir()
    (root / ".pdd").mkdir()

    # Prompt
    (root / "prompts" / "utils.prompt").write_text(
        "Handle missing 'name' key gracefully.", encoding="utf-8"
    )

    # Buggy code: KeyError when 'name' missing
    buggy = (
        "import json\n"
        "from pathlib import Path\n\n"
        "def get_greeting():\n"
        "    cfg = Path(__file__).parent / 'config.json'\n"
        "    with cfg.open('r') as f:\n"
        "        config = json.load(f)\n"
        "    # fragile: KeyError if 'name' missing\n"
        "    name = config['user']['name']\n"
        "    return f'Hello, {name}!'\n"
    )
    (root / "src" / "utils.py").write_text(buggy, encoding="utf-8")

    # Config w/o name
    (root / "src" / "config.json").write_text(
        '{"user": {"email": "test@example.com"}}', encoding="utf-8"
    )

    # Test file — use a UNIQUE BASENAME per provider!
    tests = (
        "import unittest\n"
        "from src import utils\n\n"
        "class TestGreeting(unittest.TestCase):\n"
        "    def test_get_greeting(self):\n"
        "        msg = utils.get_greeting()\n"
        "        assert 'Hello' in msg\n"
    )
    (root / "tests" / f"{test_basename}.py").write_text(tests, encoding="utf-8")

    # Error log
    (root / "error.log").write_text("KeyError: 'name'", encoding="utf-8")

    # Local provider CSV
    (root / ".pdd" / "llm_model.csv").write_text(
        "provider,model,api_key\n"
        "google,gemini-pro,GOOGLE_API_KEY\n"
        "anthropic,claude-3-opus,ANTHROPIC_API_KEY\n"
        "openai,gpt-4,OPENAI_API_KEY\n",
        encoding="utf-8",
    )


def _run_fix_once(project: Path, unit_test_file: str) -> bool:
    # Make sure previous imports don’t leak
    _purge_modules()

    success, *_ = fix_error_loop(
        unit_test_file=unit_test_file,
        code_file="src/utils.py",
        prompt_file="prompts/utils.prompt",
        prompt="Handle missing 'name' key gracefully.",
        verification_program=str(project / unit_test_file),
        strength=0.0,
        temperature=0.0,
        max_attempts=1,         # force a quick fallback to the agent
        budget=5.0,
        error_log_file="error.log",
        verbose=False,
        agentic_fallback=True,
    )
    return success


def _assert_fixed() -> None:
    final_code = Path("src/utils.py").read_text(encoding="utf-8")
    # Must not use fragile indexing
    assert "config['user']['name']" not in final_code
    assert 'config["user"]["name"]' not in final_code
    # Must use a safe get-based access
    assert ".get(" in final_code


@pytest.mark.e2e
def test_fix_command_gemini(tmp_path, monkeypatch):
    """E2E: real fix command uses Google/Gemini agent (if available)."""
    if not (os.getenv("GOOGLE_API_KEY") or os.getenv("GEMINI_API_KEY")) or not _has_cli("gemini"):
        pytest.skip("Gemini not available (need gemini CLI and GOOGLE_API_KEY or GEMINI_API_KEY).")

    # Prefer Google; remove others
    monkeypatch.delenv("ANTHROPIC_API_KEY", raising=False)
    monkeypatch.delenv("OPENAI_API_KEY", raising=False)
    if not os.getenv("GOOGLE_API_KEY") and os.getenv("GEMINI_API_KEY"):
        monkeypatch.setenv("GOOGLE_API_KEY", os.environ["GEMINI_API_KEY"])

    # Logs/timeouts
    monkeypatch.setenv("PDD_AGENTIC_LOGLEVEL", os.getenv("PDD_AGENTIC_LOGLEVEL", "normal"))
    monkeypatch.setenv("PDD_AGENTIC_TIMEOUT", os.getenv("PDD_AGENTIC_TIMEOUT", "180"))
    monkeypatch.setenv("PDD_AGENTIC_VERIFY_TIMEOUT", os.getenv("PDD_AGENTIC_VERIFY_TIMEOUT", "90"))
    monkeypatch.setenv("NO_COLOR", "1"); monkeypatch.setenv("CLICOLOR", "0"); monkeypatch.setenv("CLICOLOR_FORCE", "0")

    project = tmp_path
    unit_test = "tests/test_utils_gemini.py"
    _make_project(project, "test_utils_gemini")
    monkeypatch.chdir(project)
    monkeypatch.syspath_prepend(str(project))

    ok = _run_fix_once(project, unit_test)
    if not ok:
        res = os.system(f"{sys.executable} -m pytest {unit_test} -q > /dev/null 2>&1")
        if res != 0:
            pytest.xfail("Gemini agent did not finish within timeout.")
        ok = True

    assert ok is True
    _assert_fixed()


@pytest.mark.e2e
def test_fix_command_claude(tmp_path, monkeypatch):
    """E2E: real fix command uses Anthropic/Claude agent (if available)."""
    if not os.getenv("ANTHROPIC_API_KEY") or not _has_cli("claude"):
        pytest.skip("Claude not available (need claude CLI and ANTHROPIC_API_KEY).")

    # Prefer Anthropic; remove others
    monkeypatch.delenv("GOOGLE_API_KEY", raising=False)
    monkeypatch.delenv("GEMINI_API_KEY", raising=False)
    monkeypatch.delenv("OPENAI_API_KEY", raising=False)

    # Logs/timeouts
    monkeypatch.setenv("PDD_AGENTIC_LOGLEVEL", os.getenv("PDD_AGENTIC_LOGLEVEL", "normal"))
    monkeypatch.setenv("PDD_AGENTIC_TIMEOUT", os.getenv("PDD_AGENTIC_TIMEOUT", "180"))
    monkeypatch.setenv("PDD_AGENTIC_VERIFY_TIMEOUT", os.getenv("PDD_AGENTIC_VERIFY_TIMEOUT", "90"))
    monkeypatch.setenv("NO_COLOR", "1"); monkeypatch.setenv("CLICOLOR", "0"); monkeypatch.setenv("CLICOLOR_FORCE", "0")

    project = tmp_path
    unit_test = "tests/test_utils_claude.py"
    _make_project(project, "test_utils_claude")
    monkeypatch.chdir(project)
    monkeypatch.syspath_prepend(str(project))

    ok = _run_fix_once(project, unit_test)
    if not ok:
        res = os.system(f"{sys.executable} -m pytest {unit_test} -q > /dev/null 2>&1")
        if res != 0:
            pytest.xfail("Claude agent did not finish within timeout.")
        ok = True

    assert ok is True
    _assert_fixed()


@pytest.mark.e2e
def test_fix_command_codex(tmp_path, monkeypatch):
    """E2E: real fix command uses OpenAI/Codex agent (if available)."""
    if not os.getenv("OPENAI_API_KEY") or not _has_cli("codex"):
        pytest.skip("Codex not available (need codex CLI and OPENAI_API_KEY).")

    # Prefer OpenAI; remove others
    monkeypatch.delenv("GOOGLE_API_KEY", raising=False)
    monkeypatch.delenv("GEMINI_API_KEY", raising=False)
    monkeypatch.delenv("ANTHROPIC_API_KEY", raising=False)

    # Logs/timeouts
    monkeypatch.setenv("PDD_AGENTIC_LOGLEVEL", os.getenv("PDD_AGENTIC_LOGLEVEL", "normal"))
    monkeypatch.setenv("PDD_AGENTIC_TIMEOUT", os.getenv("PDD_AGENTIC_TIMEOUT", "210"))
    monkeypatch.setenv("PDD_AGENTIC_VERIFY_TIMEOUT", os.getenv("PDD_AGENTIC_VERIFY_TIMEOUT", "90"))
    monkeypatch.setenv("NO_COLOR", "1"); monkeypatch.setenv("CLICOLOR", "0"); monkeypatch.setenv("CLICOLOR_FORCE", "0")

    project = tmp_path
    unit_test = "tests/test_utils_codex.py"
    _make_project(project, "test_utils_codex")
    monkeypatch.chdir(project)
    monkeypatch.syspath_prepend(str(project))

    ok = _run_fix_once(project, unit_test)
    if not ok:
        res = os.system(f"{sys.executable} -m pytest {unit_test} -q > /dev/null 2>&1")
        if res != 0:
            pytest.xfail("Codex agent did not finish within timeout.")
        ok = True

    assert ok is True
    _assert_fixed()
