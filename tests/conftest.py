"""Project-level pytest configuration hooks."""

import os
import sys
from pathlib import Path
from typing import Any

import pytest
from dotenv import load_dotenv
from pdd.llm_invoke import InsufficientCreditsError


# Load environment variables from .env early in collection
load_dotenv()

# Store the original PDD_PATH at module load time for restoration
_ORIGINAL_PDD_PATH = os.environ.get('PDD_PATH')

# Store original streams at module load time for restoration
_ORIGINAL_STDOUT = sys.stdout
_ORIGINAL_STDERR = sys.stderr


_ORIGINAL_GIT_WORK_TREE = os.environ.get('GIT_WORK_TREE')


_E2E_FIX_ORIGINAL_ATTRS: dict[str, Any] | None = None
_E2E_FIX_ATTRS_TO_RESTORE = (
    "run_agentic_task",
    "load_prompt_template",
    "console",
    "load_workflow_state",
    "save_workflow_state",
    "clear_workflow_state",
    "_get_file_hashes",
    "_detect_changed_files",
    "_detect_meaningful_changes",
    "_commit_and_push",
    "_check_e2e_environment",
    "classify_step_output",
    "post_final_comment",
    "_run_step11_code_cleanup",
    "run_ci_validation_loop",
)


@pytest.fixture(autouse=True)
def restore_agentic_e2e_fix_orchestrator_mocks():
    """Restore orchestrator globals that heavily mocked tests replace.

    The public CI unit-test job runs many orchestrator regression modules in
    shared xdist workers. If a mock of file-change detection leaks past one
    test, later end-to-end tests can think a fix was applied and skip their
    no-progress guards. Keep the cleanup centralized so those tests remain
    order-independent.
    """
    global _E2E_FIX_ORIGINAL_ATTRS

    try:
        import pdd.agentic_e2e_fix_orchestrator as orchestrator
    except ImportError:
        yield
        return

    if _E2E_FIX_ORIGINAL_ATTRS is None:
        _E2E_FIX_ORIGINAL_ATTRS = {
            attr: getattr(orchestrator, attr)
            for attr in _E2E_FIX_ATTRS_TO_RESTORE
            if hasattr(orchestrator, attr)
        }

    yield

    for attr, original in _E2E_FIX_ORIGINAL_ATTRS.items():
        setattr(orchestrator, attr, original)


@pytest.fixture(autouse=True)
def preserve_cwd():
    """Restore cwd after each test so xdist workers don't leak temp dirs.

    Several tests intentionally chdir into throwaway workspaces. When one of
    those tests leaves the worker process outside the repository, later tests
    that read committed relative paths such as ``pdd/data/llm_model.csv`` fail
    order-dependently in the full public CI run.
    """
    original_cwd = os.getcwd()
    yield
    try:
        os.chdir(original_cwd)
    except FileNotFoundError:
        os.chdir(Path(__file__).resolve().parents[1])


@pytest.fixture(autouse=True)
def preserve_git_work_tree():
    """Clear GIT_WORK_TREE during tests to avoid interfering with git init in temp dirs."""
    os.environ.pop('GIT_WORK_TREE', None)
    yield
    if _ORIGINAL_GIT_WORK_TREE is not None:
        os.environ['GIT_WORK_TREE'] = _ORIGINAL_GIT_WORK_TREE
    else:
        os.environ.pop('GIT_WORK_TREE', None)


@pytest.fixture(autouse=True)
def _isolate_claude_oauth_probe(monkeypatch):
    """Default the Issue #813 OAuth probe to False so tests are CI-portable.

    On developer machines and CI runners that have ``claude`` installed and
    logged in via Max/Pro, the probe in ``_strip_anthropic_creds_for_claude_subprocess``
    would otherwise pop ANTHROPIC_API_KEY out of the subprocess env and break
    legacy tests that assert the key survives (e.g. ``test_environment_sanitization``).

    Tests that exercise the strip behavior re-patch ``_claude_has_oauth_login``
    or ``_probe_claude_auth_status`` to True/non-empty in their own scope.
    """
    monkeypatch.setattr("pdd.agentic_common._claude_has_oauth_login", lambda: False)


@pytest.fixture(autouse=True)
def _isolate_codex_auth_file(monkeypatch):
    """Default ``_has_codex_auth_file`` to False (Issue #813 round-6).

    Developer machines often have ``~/.codex/auth.json`` from a real
    ``codex login``. Without this fixture, ``test_get_available_agents_*``
    tests that assume "no auth signal" pick up the dev's real codex
    login and incorrectly report openai available, breaking
    deterministic test runs across environments.
    """
    monkeypatch.setattr("pdd.agentic_common._has_codex_auth_file", lambda: False)


@pytest.fixture(autouse=True)
def preserve_pdd_path():
    """Ensure PDD_PATH is restored after each test to prevent test pollution.

    Always restores to the original PDD_PATH that was present when conftest loaded,
    regardless of what other fixtures or tests did during the test.
    """
    yield
    # Always restore original PDD_PATH after each test
    if _ORIGINAL_PDD_PATH is not None:
        os.environ['PDD_PATH'] = _ORIGINAL_PDD_PATH
    elif 'PDD_PATH' in os.environ:
        # Original was None but test set it - remove it
        del os.environ['PDD_PATH']


@pytest.fixture(autouse=True)
def restore_standard_streams():
    """Ensure sys.stdout/stderr are restored after each test to prevent pollution.

    CLI code may wrap streams with OutputCapture for core dump functionality.
    If early exits (ctx.exit(0)) bypass normal cleanup, streams remain wrapped.
    This fixture provides defense-in-depth by restoring original streams.
    """
    yield
    # Restore if streams were replaced (indicates incomplete cleanup)
    # Import here to avoid circular imports at module load time
    try:
        from pdd.core.cli import OutputCapture
        if isinstance(sys.stdout, OutputCapture):
            sys.stdout = _ORIGINAL_STDOUT
        if isinstance(sys.stderr, OutputCapture):
            sys.stderr = _ORIGINAL_STDERR
    except ImportError:
        # If OutputCapture can't be imported, fall back to simple check
        if sys.stdout is not _ORIGINAL_STDOUT:
            sys.stdout = _ORIGINAL_STDOUT
        if sys.stderr is not _ORIGINAL_STDERR:
            sys.stderr = _ORIGINAL_STDERR


def pytest_addoption(parser: pytest.Parser) -> None:
    """Expose the legacy ``--run-all`` flag expected by our tooling."""

    parser.addoption(
        "--run-all",
        action="store_true",
        default=False,
        help="Run the full suite including slow or integration tests.",
    )
    parser.addoption(
        "--durable-max-parallel",
        action="store",
        type=int,
        default=None,
        help="Override durable sync runner concurrency in durable verification tests.",
    )


@pytest.fixture
def durable_max_parallel(request: pytest.FixtureRequest) -> int | None:
    """Return the optional durable runner concurrency override."""

    return request.config.getoption("--durable-max-parallel")


def pytest_configure(config: pytest.Config) -> None:
    """Configure pytest: mirror --run-all flag.

    Note: JWT auto-population was removed to prevent browser popups during
    test runs (especially from test explorers like VS Code/PyCharm).
    Tests needing auth should mock it or use PDD_JWT_TOKEN env var.
    """
    run_all: Any = config.getoption("--run-all")
    if run_all:
        os.environ["PDD_RUN_ALL_TESTS"] = "1"
    else:
        os.environ.setdefault("PDD_RUN_ALL_TESTS", "0")


@pytest.hookimpl(hookwrapper=True)
def pytest_runtest_makereport(item: pytest.Item, call):
    """Convert InsufficientCreditsError failures to skips.

    The cloud batch test account may run out of credits, causing tests that call
    the production LLM endpoint to fail with InsufficientCreditsError. These are
    infrastructure failures, not code bugs — convert to skip rather than fail.
    """
    outcome = yield
    report = outcome.get_result()
    if report.when == "call" and report.failed and call.excinfo is not None:
        if call.excinfo.errisinstance(InsufficientCreditsError):
            report.outcome = "skipped"
            report.wasxfail = ""
            report.longrepr = f"Skipped: Insufficient credits for cloud LLM call"


# Ignore non-suite assets under tests/ during collection.
# `tests/fixtures/` contains fixture source trees used by higher-level tests;
# some of those fixtures intentionally include broken `test_*.py` files.
# They must never be collected as part of the main pytest suite.
collect_ignore_glob = [
    "csv/*",
    "fixtures/*",
]


# --- Common fixtures for CLI tests ---
from click.testing import CliRunner


@pytest.fixture
def create_dummy_files(tmp_path):
    """Fixture to create dummy files for testing."""
    files = {}
    def _create_files(*filenames, content="dummy content"):
        for name in filenames:
            file_path = tmp_path / name
            file_path.parent.mkdir(parents=True, exist_ok=True)
            file_path.write_text(content)
            files[name] = file_path
        return files
    return _create_files


@pytest.fixture
def runner():
    """Fixture to provide a CliRunner for testing Click commands."""
    return CliRunner()
