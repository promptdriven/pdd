"""Project-level pytest configuration hooks."""

import os
from typing import Any

import pytest
from dotenv import load_dotenv


# Load environment variables from .env early in collection
load_dotenv()

# Store the original PDD_PATH at module load time for restoration
_ORIGINAL_PDD_PATH = os.environ.get('PDD_PATH')


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


def pytest_addoption(parser: pytest.Parser) -> None:
    """Expose the legacy ``--run-all`` flag expected by our tooling."""

    parser.addoption(
        "--run-all",
        action="store_true",
        default=False,
        help="Run the full suite including slow or integration tests.",
    )


def pytest_configure(config: pytest.Config) -> None:
    """Configure pytest: populate JWT cache and mirror --run-all flag.

    JWT cache population runs only in master process (not xdist workers)
    to ensure cache is ready before workers spawn. This prevents multiple
    keyring password prompts when running tests with pytest-xdist.
    """
    # --- Populate JWT cache (master process only) ---
    # With xdist, session-scoped fixtures run once per worker, causing race
    # conditions. pytest_configure runs in master BEFORE workers spawn.
    if not hasattr(config, 'workerinput'):
        # We're in master process (or running without xdist)
        try:
            from pdd.get_jwt_token import _get_cached_jwt
            from pdd.core.cloud import CloudConfig

            # Only fetch JWT if cache is empty/expired
            if not _get_cached_jwt():
                CloudConfig.get_jwt_token()
        except Exception:
            # Auth failure is fine - tests needing JWT will fail appropriately
            pass

    # --- Mirror --run-all into PDD_RUN_ALL_TESTS ---
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
