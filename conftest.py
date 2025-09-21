"""
Configuration file for pytest.

This file defines pytest collection behavior, particularly
which directories to ignore during test discovery.
"""
import os
from dotenv import load_dotenv


def pytest_addoption(parser):
    """Add custom CLI options for pytest."""
    parser.addoption(
        "--run-all",
        action="store_true",
        default=False,
        help="Run the full suite, including integration tests that hit live resources.",
    )


def pytest_configure(config):
    """Propagate --run-all to the shared environment flag for import-time checks."""
    if config.getoption("--run-all"):
        os.environ["PDD_RUN_ALL_TESTS"] = "1"

# Load environment variables from .env file
load_dotenv()

# Directories or files to ignore during test collection
collect_ignore_glob = [
    "tests/csv/*",
] 
