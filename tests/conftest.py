"""Project-level pytest configuration hooks."""

import os
import sys
from typing import Any

import pytest
from dotenv import load_dotenv


# Load environment variables from .env early in collection
load_dotenv()

# Store the original PDD_PATH at module load time for restoration
_ORIGINAL_PDD_PATH = os.environ.get('PDD_PATH')

# Store original streams at module load time for restoration
_ORIGINAL_STDOUT = sys.stdout
_ORIGINAL_STDERR = sys.stderr


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
def _reset_quiet_mode():
    """Ensure quiet mode doesn't leak between tests."""
    import logging
    pdd_logger = logging.getLogger("pdd.llm_invoke")
    root_logger = logging.getLogger()
    # Capture state before test
    pdd_level = pdd_logger.level
    pdd_handler_levels = [(h, h.level) for h in pdd_logger.handlers]
    root_level = root_logger.level
    root_handler_levels = [(h, h.level) for h in root_logger.handlers]
    old_last_resort = logging.lastResort
    old_pdd_quiet = os.environ.get("PDD_QUIET")
    yield
    from pdd import quiet
    quiet.disable_quiet_mode()
    # Restore env var
    if old_pdd_quiet is None:
        os.environ.pop("PDD_QUIET", None)
    else:
        os.environ["PDD_QUIET"] = old_pdd_quiet
    # Restore logger levels and handler levels
    pdd_logger.setLevel(pdd_level)
    for handler, level in pdd_handler_levels:
        handler.setLevel(level)
    root_logger.setLevel(root_level)
    for handler, level in root_handler_levels:
        handler.setLevel(level)
    if old_last_resort is not None:
        logging.lastResort = old_last_resort
    elif logging.lastResort is None:
        logging.lastResort = logging.StreamHandler()


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


# Ignore CSV-driven assets under tests/csv during collection
collect_ignore_glob = [
    "csv/*",
]


# --- Common fixtures for CLI tests ---
from pathlib import Path
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
