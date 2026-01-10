"""
Pytest configuration for server tests.

IMPORTANT: Due to module-level sys.modules interactions between test files,
server tests should be run in THREE separate pytest invocations:

    # 1. Run test_app.py alone (12 tests)
    pytest tests/server/test_app.py -v

    # 2. Run other non-route tests (98 tests, 2 expected failures)
    pytest tests/server --ignore=tests/server/routes --ignore=tests/server/test_app.py -v

    # 3. Run route tests (85 tests)
    pytest tests/server/routes -v

Or use the simplified two-command approach:
    # Non-route tests (some test_app failures expected when run together)
    pytest tests/server --ignore=tests/server/routes -v

    # Route tests
    pytest tests/server/routes -v

Running `pytest tests/server/` directly will cause failures because pytest imports
ALL test files during collection, causing module pollution.
"""

import sys


def _cleanup_server_modules():
    """Remove all pdd.server modules from sys.modules."""
    mods_to_remove = [k for k in list(sys.modules.keys()) if k.startswith("pdd.server")]
    for mod in mods_to_remove:
        if mod in sys.modules:
            del sys.modules[mod]


def pytest_configure(config):
    """Called at the very start before any collection."""
    _cleanup_server_modules()


def pytest_unconfigure(config):
    """Called after all tests complete."""
    _cleanup_server_modules()
