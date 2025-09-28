import os
import shutil
import subprocess
import sys
from pathlib import Path
import time

import pytest

# ---- Opt-in to real-agent tests so CI stays fast ----
if not os.getenv("RUN_REAL_AGENT_E2E"):
    pytest.skip("Set RUN_REAL_AGENT_E2E=1 to run the real-agent E2E test.", allow_module_level=True)

from pdd.agentic_fix import run_agentic_fix, AGENT_PROVIDER_PREFERENCE  # noqa: E402

# ---- Minimal fixtures (tiny files => faster prompts) ----
PROMPT_CONTENT = "Handle missing 'name' key gracefully.\n"
BUGGY_CODE_CONTENT = (
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
CONFIG_CONTENT = '{"user": {"email": "test@example.com"}}\n'
TEST_CONTENT_FAILING = (
    "import unittest\n"
    "from src import utils\n\n"
    "class TestGreeting(unittest.TestCase):\n"
    "    def test_get_greeting(self):\n"
    "        msg = utils.get_greeting()\n"
    "        self.assertIn('Hello', msg)\n"
)
ERROR_LOG_CONTENT = "KeyError: 'name'\n"  # keep tiny; large logs slow CLIs

# Preflight helper (does NOT change production discovery logic)
PROVIDER_CLI = {"anthropic": "claude", "google": "gemini", "openai": "codex"}
ENV_FOR_PROVIDER = {"anthropic": "ANTHROPIC_API_KEY", "google": "GOOGLE_API_KEY", "openai": "OPENAI_API_KEY"}


def _has_usable_provider():
    """Only to decide whether to skip; production discovery still happens inside run_agentic_fix."""
    for provider in AGENT_PROVIDER_PREFERENCE:
        cli = PROVIDER_CLI.get(provider)
        if not cli:
            continue
        if shutil.which(cli) is None:
            continue
        env_name = ENV_FOR_PROVIDER.get(provider)
        if env_name and os.getenv(env_name):
            return True
    return False


@pytest.fixture(scope="session", autouse=True)
def warmup_agent():
    """Best-effort warmup; reduces cold start without changing discovery logic."""
    for cli in ("claude", "gemini", "codex"):
        path = shutil.which(cli)
        if not path:
            continue
        try:
            subprocess.run([path, "--help"], stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL, timeout=8)
        except Exception:
            pass


@pytest.fixture
def e2e_project(tmp_path):
    """Create a tiny project tree compatible with run_agentic_fix()."""
    root = tmp_path
    (root / "prompts").mkdir()
    src_dir = root / "src"
    src_dir.mkdir()
    tests_dir = root / "tests"
    tests_dir.mkdir()
    pdd_dir = root / ".pdd"
    pdd_dir.mkdir()

    (root / "prompts" / "utils.prompt").write_text(PROMPT_CONTENT, encoding="utf-8")
    (src_dir / "__init__.py").write_text("", encoding="utf-8")
    (src_dir / "utils.py").write_text(BUGGY_CODE_CONTENT, encoding="utf-8")

    # Put config where the buggy code expects it; also at root (some agents may rewrite paths)
    (src_dir / "config.json").write_text(CONFIG_CONTENT, encoding="utf-8")
    (root / "config.json").write_text(CONFIG_CONTENT, encoding="utf-8")

    (tests_dir / "test_utils.py").write_text(TEST_CONTENT_FAILING, encoding="utf-8")
    (root / "error.log").write_text(ERROR_LOG_CONTENT, encoding="utf-8")

    # CSV used by production discovery (names match common env vars)
    (pdd_dir / "llm_model.csv").write_text(
        "provider,model,api_key\n"
        "google,gemini-1.5-pro,GOOGLE_API_KEY\n"
        "anthropic,claude-3-5-sonnet,ANTHROPIC_API_KEY\n"
        "openai,gpt-4o,OPENAI_API_KEY\n",
        encoding="utf-8",
    )
    return root


def _patch_global_timeout(monkeypatch, seconds: int):
    """
    Add a hard timeout to subprocess.run used by the SUT, WITHOUT recursion.
    We patch the dotted path inside pdd.agentic_fix and also our local subprocess.run
    for consistency in the re-run step.
    """
    original_run = subprocess.run

    def run_with_timeout(*args, **kwargs):
        kwargs.setdefault("timeout", seconds)
        return original_run(*args, **kwargs)

    monkeypatch.setattr("pdd.agentic_fix.subprocess.run", run_with_timeout, raising=False)
    monkeypatch.setattr("subprocess.run", run_with_timeout, raising=False)


# -----------------------------
# 1) FAST SMOKE (infra only)
# -----------------------------
@pytest.mark.e2e
def test_agentic_fix_real_cli_smoke(e2e_project, monkeypatch):
    """
    Call the real agent via production discovery and assert success flag only.
    Validates: CSV load -> env detection -> command build -> subprocess exec -> success handling.
    """
    if not _has_usable_provider():
        pytest.skip(
            "No usable agent found. Install a CLI and set its API key. "
            "Supported: claude/ANTHROPIC_API_KEY, gemini/GOOGLE_API_KEY, codex/OPENAI_API_KEY."
        )

    # Keep smoke test tight
    soft_cap = int(os.getenv("AGENT_E2E_SOFT_MAX_SECS", "150"))
    _patch_global_timeout(monkeypatch, int(os.getenv("AGENT_E2E_TIMEOUT", "90")))
    monkeypatch.chdir(e2e_project)

    t0 = time.time()
    success, message = run_agentic_fix(
        prompt_file="prompts/utils.prompt",
        code_file="src/utils.py",
        unit_test_file="tests/test_utils.py",
        error_log_file="error.log",
    )
    elapsed = time.time() - t0

    assert success is True, f"Agentic fix reported failure. Message: {message}"
    assert elapsed <= soft_cap, f"Real-agent smoke test too slow: {elapsed:.1f}s > {soft_cap}s"


# -----------------------------------
# 2) FULL BEHAVIOR (opt-in & slower)
# -----------------------------------
@pytest.mark.e2e
def test_agentic_fix_real_cli_behavior(e2e_project, monkeypatch):
    """
    Uses real agent. After success, re-runs the user's unit test to ensure the bug is truly fixed.
    Only runs if RUN_AGENT_BEHAVIOR=1 is set.
    """
    if not os.getenv("RUN_AGENT_BEHAVIOR"):
        pytest.skip("Set RUN_AGENT_BEHAVIOR=1 to run the full behavior check.")

    if not _has_usable_provider():
        pytest.skip(
            "No usable agent found. Install a CLI and set its API key. "
            "Supported: claude/ANTHROPIC_API_KEY, gemini/GOOGLE_API_KEY, codex/OPENAI_API_KEY."
        )

    # Give the real agent more time for a code edit
    agent_timeout = int(os.getenv("AGENT_E2E_TIMEOUT", "240"))
    test_timeout = int(os.getenv("AGENT_E2E_TEST_TIMEOUT", "120"))
    _patch_global_timeout(monkeypatch, agent_timeout)
    monkeypatch.chdir(e2e_project)

    success, message = run_agentic_fix(
        prompt_file="prompts/utils.prompt",
        code_file="src/utils.py",
        unit_test_file="tests/test_utils.py",
        error_log_file="error.log",
    )

    # Provider/network slowness should not fail CI: xfail on timeout
    if not success and "timed out" in (message or "").lower():
        pytest.xfail(f"Agent CLI timed out: {message}")

    assert success is True, f"Agentic fix reported failure. Message: {message}"

    # Ground truth: user's unit test must pass now
    if str(e2e_project) not in sys.path:
        sys.path.insert(0, str(e2e_project))

    result = subprocess.run(
        [sys.executable, "-m", "pytest", "tests/test_utils.py", "-q"],
        capture_output=True,
        text=True,
        timeout=test_timeout,
    )
    assert result.returncode == 0, (
        "Downstream unit test still fails after agentic fix.\n"
        f"stdout:\n{result.stdout}\n\nstderr:\n{result.stderr}"
    )
