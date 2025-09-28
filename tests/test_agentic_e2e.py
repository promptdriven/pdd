import os
import shutil
import subprocess
import sys
from pathlib import Path
import time

import pytest

# ---- Opt-in to real-agent test so CI stays fast ----
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
# keep logs tiny; big logs slow CLIs
ERROR_LOG_CONTENT = "KeyError: 'name'\n"

PROVIDER_CLI = {"anthropic": "claude", "google": "gemini", "openai": "codex"}
ENV_FOR_PROVIDER = {"anthropic": "ANTHROPIC_API_KEY", "google": "GOOGLE_API_KEY", "openai": "OPENAI_API_KEY"}


def _has_usable_provider():
    """
    Preflight so we can skip with a helpful message if nothing is configured.
    This does NOT alter production discovery logic; run_agentic_fix does the real work.
    """
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
    """
    Best-effort warmup; reduces cold-start latency for common CLIs.
    Does not alter agent discovery logic.
    """
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
    """
    Create a tiny project tree compatible with run_agentic_fix() without altering
    production agent selection logic.
    """
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


def _patch_global_timeout(monkeypatch):
    """
    Add a hard timeout to subprocess.run used by the SUT,
    WITHOUT causing recursion.
    """
    original_run = subprocess.run
    real_timeout = int(os.getenv("AGENT_E2E_TIMEOUT", "90"))  # keep it tight for speed

    def run_with_timeout(*args, **kwargs):
        kwargs.setdefault("timeout", real_timeout)
        return original_run(*args, **kwargs)

    # Patch the function that pdd.agentic_fix will call (dotted path!)
    monkeypatch.setattr("pdd.agentic_fix.subprocess.run", run_with_timeout, raising=False)
    # Optional: keep our test's subprocess calls consistent too
    monkeypatch.setattr("subprocess.run", run_with_timeout, raising=False)


@pytest.mark.e2e
def test_agentic_fix_real_cli_smoke(e2e_project, monkeypatch):
    """
    SMOKE (fastest): call the real agent via production-discovery, assert success flag only.
    This validates: CSV load -> env detection -> command build -> subprocess exec -> success handling.
    """
    if not _has_usable_provider():
        pytest.skip(
            "No usable agent found. Install a CLI and set its API key. "
            "Supported: claude/ANTHROPIC_API_KEY, gemini/GOOGLE_API_KEY, codex/OPENAI_API_KEY."
        )

    _patch_global_timeout(monkeypatch)
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
    # Optional soft guard: fail if it took egregiously long (adjust as you like)
    max_seconds = int(os.getenv("AGENT_E2E_SOFT_MAX_SECS", "150"))
    assert elapsed <= max_seconds, f"Real-agent smoke test too slow: {elapsed:.1f}s > {max_seconds}s"


@pytest.mark.e2e
def test_agentic_fix_real_cli_behavior(e2e_project, monkeypatch):
    """
    FULL BEHAVIOR (opt-in): only runs if RUN_AGENT_BEHAVIOR=1 is set.
    Uses real agent. After success, re-runs the user's unit test to ensure the bug is truly fixed.
    """
    if not os.getenv("RUN_AGENT_BEHAVIOR"):
        pytest.skip("Set RUN_AGENT_BEHAVIOR=1 to run the full behavior check.")

    if not _has_usable_provider():
        pytest.skip(
            "No usable agent found. Install a CLI and set its API key. "
            "Supported: claude/ANTHROPIC_API_KEY, gemini/GOOGLE_API_KEY, codex/OPENAI_API_KEY."
        )

    _patch_global_timeout(monkeypatch)
    monkeypatch.chdir(e2e_project)

    success, message = run_agentic_fix(
        prompt_file="prompts/utils.prompt",
        code_file="src/utils.py",
        unit_test_file="tests/test_utils.py",
        error_log_file="error.log",
    )
    assert success is True, f"Agentic fix reported failure. Message: {message}"

    # Ground truth: user's test must pass (agent actually fixed the bug)
    if str(e2e_project) not in sys.path:
        sys.path.insert(0, str(e2e_project))

    rerun_timeout = int(os.getenv("AGENT_E2E_TEST_TIMEOUT", "90"))
    result = subprocess.run(
        [sys.executable, "-m", "pytest", "tests/test_utils.py", "-q"],
        capture_output=True,
        text=True,
        timeout=rerun_timeout,
    )
    assert result.returncode == 0, (
        "Downstream unit test still fails after agentic fix.\n"
        f"stdout:\n{result.stdout}\n\nstderr:\n{result.stderr}"
    )
