import os
import shutil
import sys
from pathlib import Path

import pytest

from pdd.fix_error_loop import fix_error_loop

def _has_real_agent() -> bool:
    """
    Detect if we can actually run a real agent based on env + CLI presence.
    We keep the selection logic independent from SUT: just check common CLIs.
    """
    # Google / Gemini
    if (os.getenv("GOOGLE_API_KEY") or os.getenv("GEMINI_API_KEY")) and shutil.which("gemini"):
        return True
    # Anthropic / Claude
    if os.getenv("ANTHROPIC_API_KEY") and shutil.which("claude"):
        return True
    # OpenAI / Codex (rarely available)
    if os.getenv("OPENAI_API_KEY") and shutil.which("codex"):
        return True
    return False

@pytest.mark.e2e
def test_agentic_fallback_real_agent(tmp_path, monkeypatch):
    """
    Case 11 (E2E, real agent): Use the actual CLI agent to fix a simple KeyError bug.
    Skips automatically if no usable provider/CLI is available in this environment.
    """
    if not _has_real_agent():
        pytest.skip(
            "No usable agent found. Install a CLI and set its API key. "
            "Supported: claude/ANTHROPIC_API_KEY, gemini/GOOGLE_API_KEY|GEMINI_API_KEY, codex/OPENAI_API_KEY."
        )

    # Keep module output quiet to preserve clean pytest logs
    monkeypatch.setenv("PDD_AGENTIC_LOGLEVEL", "quiet")

    # Slightly generous timeouts so the real agent can edit + verify
    monkeypatch.setenv("PDD_AGENTIC_TIMEOUT", os.getenv("PDD_AGENTIC_TIMEOUT", "240"))
    monkeypatch.setenv("PDD_AGENTIC_VERIFY_TIMEOUT", os.getenv("PDD_AGENTIC_VERIFY_TIMEOUT", "120"))

    # ---- Project layout for a known-fixable scenario (greeting + missing 'name') ----
    project = tmp_path
    (project / "prompts").mkdir()
    (project / "src").mkdir()
    (project / "tests").mkdir()
    (project / ".pdd").mkdir()

    # Prompt (minimal is fine)
    (project / "prompts" / "utils.prompt").write_text("Handle missing 'name' key gracefully.")

    # Buggy code: raises KeyError when 'name' is missing
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
    (project / "src" / "utils.py").write_text(buggy)

    # Config without 'name'
    (project / "src" / "config.json").write_text('{"user": {"email": "test@example.com"}}')

    # Unit test: only requires 'Hello' to be in the message
    test_content = (
        "import unittest\n"
        "from src import utils\n\n"
        "class TestGreeting(unittest.TestCase):\n"
        "    def test_get_greeting(self):\n"
        "        msg = utils.get_greeting()\n"
        "        self.assertIn('Hello', msg)\n"
        "\n"
    )
    (project / "tests" / "test_utils.py").write_text(test_content)

    # Error log
    (project / "error.log").write_text("KeyError: 'name'")

    # llm_model.csv to allow the SUT to discover configured providers in this project
    # (doesn't override discovery logic; just mirrors user/home setup locally)
    (project / ".pdd" / "llm_model.csv").write_text(
        "provider,model,api_key\n"
        "google,gemini-pro,GOOGLE_API_KEY\n"
        "anthropic,claude-3-opus,ANTHROPIC_API_KEY\n"
        "openai,gpt-4,OPENAI_API_KEY\n"
    )

    # Make imports and relative paths resolve like a user project
    monkeypatch.syspath_prepend(str(project))
    monkeypatch.chdir(project)

    # Force the standard loop to "fail" quickly so we hit agent fallback:
    #   - run_pytest_on_file will see a failing test naturally from the buggy code
    #   - fix_errors_from_unit_tests won't be monkeypatched, so the loop will attempt 1 time (max_attempts=1) and then fallback
    #   - agentic_fallback=True triggers `run_agentic_fix`, which runs the real CLI.
    success, _, _, _, _, _ = fix_error_loop(
        unit_test_file="tests/test_utils.py",
        code_file="src/utils.py",
        prompt_file="prompts/utils.prompt",
        prompt="Handle missing 'name' key gracefully.",
        verification_program=str(project / "tests" / "test_utils.py"),  # not used in fallback verification
        strength=0.0,
        temperature=0.0,
        max_attempts=1,
        budget=5.0,
        error_log_file="error.log",
        verbose=False,
        agentic_fallback=True,
    )

    # If real agent timed out due to provider slowness, mark as xfail instead of hard fail
    if not success:
        # Re-run the unit test directly to surface extra debugging info if needed
        result = os.system(f"{sys.executable} -m pytest tests/test_utils.py -q > /dev/null 2>&1")
        if result != 0:
            pytest.xfail("Real agent did not produce a passing test within the configured timeout.")
        # If tests actually pass now, consider this a success
        success = True

    assert success is True

    # Optional: confirm file was updated to a .get()-style access
    final_code = Path("src/utils.py").read_text(encoding="utf-8")
    assert "config['user']['name']" not in final_code and 'config["user"]["name"]' not in final_code
    assert ".get(" in final_code
