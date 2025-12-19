"""Project-level pytest configuration hooks."""

import os
from typing import Any

import pytest
from dotenv import load_dotenv


# Load environment variables from .env early in collection
load_dotenv()


def pytest_addoption(parser: pytest.Parser) -> None:
    """Expose the legacy ``--run-all`` flag expected by our tooling."""

    parser.addoption(
        "--run-all",
        action="store_true",
        default=False,
        help="Run the full suite including slow or integration tests.",
    )


def pytest_configure(config: pytest.Config) -> None:
    """Mirror ``--run-all`` into ``PDD_RUN_ALL_TESTS`` for compatibility."""

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
