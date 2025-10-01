"""Project-level pytest configuration hooks."""

import os
from typing import Any

import pytest


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

