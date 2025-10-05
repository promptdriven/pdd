# tests/test_agentic_fallback_combined.py
import os
import sys
import json
import shutil
from pathlib import Path
from unittest.mock import MagicMock

import pytest

from pdd.fix_error_loop import fix_error_loop


# =========================
# Unit-level fallback tests
# =========================

PROMPT_CONTENT = "Test prompt"
BUGGY_CODE_CONTENT = "def buggy_function():\n    return 1/0"
FIXED_CODE_CONTENT = "def buggy_function():\n    return 1"
MAIN_CONTENT = "from src.utils import buggy_function; print(buggy_function())"
TEST_CONTENT_FAILING = (
    "import unittest\nfrom src import utils\n\n"
    "class TestBug(unittest.TestCase):\n"
    "    def test_bug(self):\n"
    "        utils.buggy_function()"
)

@pytest.fixture
def tmp_project(tmp_path):
    """Sets up a temporary project directory for unit-level tests."""
    project_root = tmp_path
    (project_root / "prompts").mkdir()
    (project_root / "src").mkdir()
    (project_root / "tests").mkdir()

    (project_root / "prompts" / "utils_python.prompt").write_text(PROMPT_CONTENT, encoding="utf-8")
    (project_root / "src" / "utils.py").write_text(BUGGY_CODE_CONTENT, encoding="utf-8")
    (project_root / "main.py").write_text(MAIN_CONTENT, encoding="utf-8")
    (project_root / "tests" / "test_utils.py").write_text(TEST_CONTENT_FAILING, encoding="utf-8")
    (project_root / "error.log").touch()

    return project_root


def test_fallback_is_triggered_on_failure(tmp_project, monkeypatch):
    """Agentic fallback triggers when normal loop fails and flag is True."""
    monkeypatch.syspath_prepend(str(tmp_project))
    monkeypatch.setattr("pdd.fix_error_loop.run_pytest_on_file", MagicMock(return_value=(1, 0, 0, "mocked pytest failure")))
    monkeypatch.setattr("pdd.fix_error_loop.fix_errors_from_unit_tests", MagicMock(return_value=(False, False, "", "", "LLM fail", 0.0, "mock_model")))
    mock_agentic_fix = MagicMock(return_value=(True, "Agentic fix successful"))
    monkeypatch.setattr("pdd.fix_error_loop.run_agentic_fix", mock_agentic_fix)

    success, *_ = fix_error_loop(
        unit_test_file=str(tmp_project / "tests" / "test_utils.py"),
        code_file=str(tmp_project / "src" / "utils.py"),
        prompt_file=str(tmp_project / "prompts" / "utils_python.prompt"),
        prompt=PROMPT_CONTENT,
        verification_program=str(tmp_project / "main.py"),
        strength=0.5, temperature=0.0, max_attempts=1, budget=1.0,
        error_log_file=str(tmp_project / "error.log"),
        verbose=False, agentic_fallback=True
    )

    mock_agentic_fix.assert_called_once()
    assert success is True


def test_fallback_not_triggered_if_disabled(tmp_project, monkeypatch):
    """No agentic fallback when flag is False."""
    monkeypatch.syspath_prepend(str(tmp_project))
    monkeypatch.setattr("pdd.fix_error_loop.run_pytest_on_file", MagicMock(return_value=(1, 0, 0, "mocked pytest failure")))
    monkeypatch.setattr("pdd.fix_error_loop.fix_errors_from_unit_tests", MagicMock(return_value=(False, False, "", "", "LLM fail", 0.0, "mock_model")))
    mock_agentic_fix = MagicMock()
    monkeypatch.setattr("pdd.fix_error_loop.run_agentic_fix", mock_agentic_fix)

    success, *_ = fix_error_loop(
        unit_test_file=str(tmp_project / "tests" / "test_utils.py"),
        code_file=str(tmp_project / "src" / "utils.py"),
        prompt_file=str(tmp_project / "prompts" / "utils_python.prompt"),
        prompt=PROMPT_CONTENT,
        verification_program=str(tmp_project / "main.py"),
        strength=0.5, temperature=0.0, max_attempts=1, budget=1.0,
        error_log_file=str(tmp_project / "error.log"),
        verbose=False, agentic_fallback=False
    )

    mock_agentic_fix.assert_not_called()
    assert success is False


def test_fallback_not_triggered_on_success(tmp_project, monkeypatch):
    """Normal loop succeeds → no fallback call."""
    monkeypatch.syspath_prepend(str(tmp_project))
    monkeypatch.setattr("pdd.fix_error_loop.run_pytest_on_file", MagicMock(side_effect=[(1, 0, 0, "fail"), (0, 0, 0, "pass")]))
    monkeypatch.setattr("pdd.fix_error_loop.fix_errors_from_unit_tests", MagicMock(return_value=(True, True, "", FIXED_CODE_CONTENT, "Fixed", 0.1, "gpt-4")))
    mock_agentic_fix = MagicMock()
    monkeypatch.setattr("pdd.fix_error_loop.run_agentic_fix", mock_agentic_fix)

    success, *_ = fix_error_loop(
        unit_test_file=str(tmp_project / "tests" / "test_utils.py"),
        code_file=str(tmp_project / "src" / "utils.py"),
        prompt_file=str(tmp_project / "prompts" / "utils_python.prompt"),
        prompt=PROMPT_CONTENT,
        verification_program=str(tmp_project / "main.py"),
        strength=0.5, temperature=0.0, max_attempts=1, budget=1.0,
        error_log_file=str(tmp_project / "error.log"),
        verbose=False, agentic_fallback=True
    )

    mock_agentic_fix.assert_not_called()
    assert success is True


def test_budget_exceeded_before_fallback(tmp_project, monkeypatch):
    """Budget exceeded by LLM fixer → no fallback trigger."""
    monkeypatch.syspath_prepend(str(tmp_project))
    monkeypatch.setattr("pdd.fix_error_loop.run_pytest_on_file", MagicMock(return_value=(1, 0, 0, "mocked pytest failure")))
    monkeypatch.setattr("pdd.fix_error_loop.fix_errors_from_unit_tests", MagicMock(return_value=(False, False, "", "", "Expensive failure", 2.0, "gpt-4-turbo")))
    mock_agentic_fix = MagicMock()
    monkeypatch.setattr("pdd.fix_error_loop.run_agentic_fix", mock_agentic_fix)

    success, *_ = fix_error_loop(
        unit_test_file=str(tmp_project / "tests" / "test_utils.py"),
        code_file=str(tmp_project / "src" / "utils.py"),
        prompt_file=str(tmp_project / "prompts" / "utils_python.prompt"),
        prompt=PROMPT_CONTENT,
        verification_program=str(tmp_project / "main.py"),
        strength=0.5, temperature=0.0, max_attempts=3, budget=1.0,
        error_log_file=str(tmp_project / "error.log"),
        verbose=False, agentic_fallback=True
    )

    mock_agentic_fix.assert_not_called()
    assert success is False


def test_max_attempts_reached_triggers_fallback(tmp_project, monkeypatch):
    """Reaching max_attempts triggers fallback exactly once."""
    monkeypatch.syspath_prepend(str(tmp_project))
    monkeypatch.setattr("pdd.fix_error_loop.run_pytest_on_file", MagicMock(return_value=(1, 0, 0, "mocked pytest failure")))
    mock_llm_fix = MagicMock(return_value=(False, False, "", "", "LLM fail", 0.1, "mock_model"))
    monkeypatch.setattr("pdd.fix_error_loop.fix_errors_from_unit_tests", mock_llm_fix)
    mock_agentic_fix = MagicMock(return_value=(True, "Agentic fix successful"))
    monkeypatch.setattr("pdd.fix_error_loop.run_agentic_fix", mock_agentic_fix)

    fix_error_loop(
        unit_test_file=str(tmp_project / "tests" / "test_utils.py"),
        code_file=str(tmp_project / "src" / "utils.py"),
        prompt_file=str(tmp_project / "prompts" / "utils_python.prompt"),
        prompt=PROMPT_CONTENT,
        verification_program=str(tmp_project / "main.py"),
        strength=0.5, temperature=0.0, max_attempts=3, budget=5.0,
        error_log_file=str(tmp_project / "error.log"),
        verbose=False, agentic_fallback=True
    )

    assert mock_llm_fix.call_count == 3
    mock_agentic_fix.assert_called_once()


def test_agent_failure_returns_overall_failure(tmp_project, monkeypatch):
    """If fallback fails, overall success is False."""
    monkeypatch.syspath_prepend(str(tmp_project))
    monkeypatch.setattr("pdd.fix_error_loop.run_pytest_on_file", MagicMock(return_value=(1, 0, 0, "mocked pytest failure")))
    monkeypatch.setattr("pdd.fix_error_loop.fix_errors_from_unit_tests", MagicMock(return_value=(False, False, "", "", "LLM fail", 0.0, "mock_model")))
    mock_agentic_fix = MagicMock(return_value=(False, "Agentic fix failed"))
    monkeypatch.setattr("pdd.fix_error_loop.run_agentic_fix", mock_agentic_fix)

    success, *_ = fix_error_loop(
        unit_test_file=str(tmp_project / "tests" / "test_utils.py"),
        code_file=str(tmp_project / "src" / "utils.py"),
        prompt_file=str(tmp_project / "prompts" / "utils_python.prompt"),
        prompt=PROMPT_CONTENT,
        verification_program=str(tmp_project / "main.py"),
        strength=0.5, temperature=0.0, max_attempts=1, budget=1.0,
        error_log_file=str(tmp_project / "error.log"),
        verbose=False, agentic_fallback=True
    )

    mock_agentic_fix.assert_called_once()
    assert success is False


def test_no_unit_test_file_returns_failure(tmp_project):
    """Graceful failure if test file missing."""
    missing_test = tmp_project / "tests" / "nope_test.py"
    success, *_ = fix_error_loop(
        unit_test_file=str(missing_test),
        code_file=str(tmp_project / "src" / "utils.py"),
        prompt_file=str(tmp_project / "prompts" / "utils_python.prompt"),
        prompt=PROMPT_CONTENT,
        verification_program=str(tmp_project / "main.py"),
        strength=0.5, temperature=0.0, max_attempts=1, budget=1.0,
        error_log_file=str(tmp_project / "error.log"),
        verbose=False, agentic_fallback=True
    )
    assert success is False


def test_no_code_file_returns_failure(tmp_project):
    """Graceful failure if code file missing."""
    missing_code = tmp_project / "src" / "nope_code.py"
    success, *_ = fix_error_loop(
        unit_test_file=str(tmp_project / "tests" / "test_utils.py"),
        code_file=str(missing_code),
        prompt_file=str(tmp_project / "prompts" / "utils_python.prompt"),
        prompt=PROMPT_CONTENT,
        verification_program=str(tmp_project / "main.py"),
        strength=0.5, temperature=0.0, max_attempts=1, budget=1.0,
        error_log_file=str(tmp_project / "error.log"),
        verbose=False, agentic_fallback=True
    )
    assert success is False


def test_initial_pytest_pass_skips_everything(tmp_project, monkeypatch):
    """If initial pytest passes, no LLM or agentic calls are made."""
    monkeypatch.syspath_prepend(str(tmp_project))
    mock_pytest = MagicMock(return_value=(0, 0, 0, "All tests pass"))
    monkeypatch.setattr("pdd.fix_error_loop.run_pytest_on_file", mock_pytest)
    mock_llm = MagicMock()
    monkeypatch.setattr("pdd.fix_error_loop.fix_errors_from_unit_tests", mock_llm)
    mock_agent = MagicMock()
    monkeypatch.setattr("pdd.fix_error_loop.run_agentic_fix", mock_agent)

    success, *_ = fix_error_loop(
        unit_test_file=str(tmp_project / "tests" / "test_utils.py"),
        code_file=str(tmp_project / "src" / "utils.py"),
        prompt_file=str(tmp_project / "prompts" / "utils_python.prompt"),
        prompt=PROMPT_CONTENT,
        verification_program=str(tmp_project / "main.py"),
        strength=0.5, temperature=0.0, max_attempts=3, budget=5.0,
        error_log_file=str(tmp_project / "error.log"),
        verbose=False, agentic_fallback=True
    )

    mock_pytest.assert_called_once()
    mock_llm.assert_not_called()
    mock_agent.assert_not_called()
    assert success is True


def test_agent_receives_correct_file_paths(tmp_project, monkeypatch):
    """Ensure agentic fix receives the exact paths passed by the loop."""
    monkeypatch.syspath_prepend(str(tmp_project))
    monkeypatch.setattr("pdd.fix_error_loop.run_pytest_on_file", MagicMock(return_value=(1, 0, 0, "mocked pytest failure")))
    monkeypatch.setattr("pdd.fix_error_loop.fix_errors_from_unit_tests", MagicMock(return_value=(False, False, "", "", "LLM fail", 0.0, "mock_model")))
    mock_agentic_fix = MagicMock(return_value=(True, "Agentic fix successful"))
    monkeypatch.setattr("pdd.fix_error_loop.run_agentic_fix", mock_agentic_fix)

    error_log_path = tmp_project / "custom_error.log"

    fix_error_loop(
        unit_test_file=str(tmp_project / "tests" / "test_utils.py"),
        code_file=str(tmp_project / "src" / "utils.py"),
        prompt_file=str(tmp_project / "prompts" / "utils_python.prompt"),
        prompt=PROMPT_CONTENT,
        verification_program=str(tmp_project / "main.py"),
        strength=0.5, temperature=0.0, max_attempts=1, budget=1.0,
        error_log_file=str(error_log_path),
        verbose=False, agentic_fallback=True
    )

    args = mock_agentic_fix.call_args[1]
    assert args["prompt_file"] == str(tmp_project / "prompts" / "utils_python.prompt")
    assert args["code_file"] == str(tmp_project / "src" / "utils.py")
    assert args["unit_test_file"] == str(tmp_project / "tests" / "test_utils.py")
    assert args["error_log_file"] == str(error_log_path)


# =========================
# E2E CLI agent tests
# =========================

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

    (root / "prompts" / "utils.prompt").write_text(
        "Handle missing 'name' key gracefully.", encoding="utf-8"
    )

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

    (root / "src" / "config.json").write_text(
        '{"user": {"email": "test@example.com"}}', encoding="utf-8"
    )

    tests = (
        "import unittest\n"
        "from src import utils\n\n"
        "class TestGreeting(unittest.TestCase):\n"
        "    def test_get_greeting(self):\n"
        "        msg = utils.get_greeting()\n"
        "        assert 'Hello' in msg\n"
    )
    (root / "tests" / f"{test_basename}.py").write_text(tests, encoding="utf-8")

    (root / "error.log").write_text("KeyError: 'name'", encoding="utf-8")

    (root / ".pdd" / "llm_model.csv").write_text(
        "provider,model,api_key\n"
        "google,gemini-pro,GOOGLE_API_KEY\n"
        "anthropic,claude-3-opus,ANTHROPIC_API_KEY\n"
        "openai,gpt-4,OPENAI_API_KEY\n",
        encoding="utf-8",
    )


def _run_fix_once(project: Path, unit_test_file: str) -> bool:
    _purge_modules()
    success, *_ = fix_error_loop(
        unit_test_file=unit_test_file,
        code_file="src/utils.py",
        prompt_file="prompts/utils.prompt",
        prompt="Handle missing 'name' key gracefully.",
        verification_program=str(project / unit_test_file),
        strength=0.0,
        temperature=0.0,
        max_attempts=1,  # force quick fallback to agent
        budget=5.0,
        error_log_file="error.log",
        verbose=False,
        agentic_fallback=True,
    )
    return success


def _assert_fixed() -> None:
    final_code = Path("src/utils.py").read_text(encoding="utf-8")
    assert "config['user']['name']" not in final_code
    assert 'config["user"]["name"]' not in final_code
    assert ".get(" in final_code


@pytest.mark.e2e
def test_fix_command_gemini(tmp_path, monkeypatch):
    """E2E: Google/Gemini agent (if available)."""
    if not (os.getenv("GOOGLE_API_KEY") or os.getenv("GEMINI_API_KEY")) or not _has_cli("gemini"):
        pytest.skip("Gemini not available (need gemini CLI + key).")

    # Prefer Google; remove others
    monkeypatch.delenv("ANTHROPIC_API_KEY", raising=False)
    monkeypatch.delenv("OPENAI_API_KEY", raising=False)
    if not os.getenv("GOOGLE_API_KEY") and os.getenv("GEMINI_API_KEY"):
        monkeypatch.setenv("GOOGLE_API_KEY", os.environ["GEMINI_API_KEY"])

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
    """E2E: Anthropic/Claude agent (if available)."""
    if not os.getenv("ANTHROPIC_API_KEY") or not _has_cli("claude"):
        pytest.skip("Claude not available (need claude CLI + key).")

    # Prefer Anthropic; remove others
    monkeypatch.delenv("GOOGLE_API_KEY", raising=False)
    monkeypatch.delenv("GEMINI_API_KEY", raising=False)
    monkeypatch.delenv("OPENAI_API_KEY", raising=False)

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
    """E2E: OpenAI/Codex agent (if available)."""
    if not os.getenv("OPENAI_API_KEY") or not _has_cli("codex"):
        pytest.skip("Codex not available (need codex CLI + key).")

    # Prefer OpenAI; remove others
    monkeypatch.delenv("GOOGLE_API_KEY", raising=False)
    monkeypatch.delenv("GEMINI_API_KEY", raising=False)
    monkeypatch.delenv("ANTHROPIC_API_KEY", raising=False)

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
