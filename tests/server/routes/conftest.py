"""
Pytest configuration for route tests.

This conftest provides fixtures that set up mock modules for testing
pdd.server.routes without polluting sys.modules during collection.

IMPORTANT: We use REAL pdd.server.models and pdd.server.security modules.
We only mock modules that don't exist or cause circular import issues.

NOTE: Top-level imports from pdd.server.* are avoided to prevent module
pollution during pytest collection.
"""

import sys
import types
from unittest.mock import MagicMock

import pytest


def _get_model_classes():
    """Import model classes lazily to avoid collection-time pollution."""
    from pdd.server.models import (
        FileTreeNode,
        FileContent,
        WriteFileRequest,
        WriteResult,
        FileMetadata,
        JobHandle,
        JobResult,
        JobStatus,
        CommandRequest,
        ServerConfig,
        ServerStatus,
    )
    return {
        'FileTreeNode': FileTreeNode,
        'FileContent': FileContent,
        'WriteFileRequest': WriteFileRequest,
        'WriteResult': WriteResult,
        'FileMetadata': FileMetadata,
        'JobHandle': JobHandle,
        'JobResult': JobResult,
        'JobStatus': JobStatus,
        'CommandRequest': CommandRequest,
        'ServerConfig': ServerConfig,
        'ServerStatus': ServerStatus,
    }


def _get_security_classes():
    """Import security classes lazily to avoid collection-time pollution."""
    from pdd.server.security import (
        PathValidator,
        SecurityError,
    )
    return {
        'PathValidator': PathValidator,
        'SecurityError': SecurityError,
    }


# ============================================================================
# Fixture to setup and teardown mocks (only for modules that need mocking)
# ============================================================================

_saved_modules = {}
_mocks_installed = False


def _setup_route_mocks():
    """Install mock modules into sys.modules for modules that need mocking."""
    global _saved_modules, _mocks_installed

    if _mocks_installed:
        return

    # Only mock modules that cause issues during route imports
    # DO NOT mock pdd.server.models or pdd.server.security - they work fine
    modules_to_mock = [
        "pdd.server.jobs",
        "pdd.server.routes.websocket",
    ]

    for mod_name in modules_to_mock:
        if mod_name in sys.modules:
            _saved_modules[mod_name] = sys.modules[mod_name]

    # Mock jobs module - it may have circular imports or missing dependencies
    m_jobs = types.ModuleType("pdd.server.jobs")
    m_jobs.JobManager = MagicMock()
    m_jobs.Job = MagicMock()
    m_jobs.JobCallbacks = MagicMock()
    m_jobs.JobStatus = _get_model_classes()['JobStatus']  # Use real JobStatus
    sys.modules["pdd.server.jobs"] = m_jobs

    # Mock websocket module - it may have complex dependencies
    m_ws = types.ModuleType("pdd.server.routes.websocket")
    m_ws.ConnectionManager = MagicMock()
    m_ws.create_websocket_routes = MagicMock()
    m_ws.router = MagicMock()
    sys.modules["pdd.server.routes.websocket"] = m_ws

    _mocks_installed = True


def _teardown_route_mocks():
    """Remove mock modules and restore originals."""
    global _saved_modules, _mocks_installed

    if not _mocks_installed:
        return

    # Remove mocked modules
    for mod_name in ["pdd.server.jobs", "pdd.server.routes.websocket"]:
        if mod_name in sys.modules:
            del sys.modules[mod_name]

    # Restore saved modules
    for mod_name, mod in _saved_modules.items():
        sys.modules[mod_name] = mod

    _saved_modules = {}
    _mocks_installed = False


@pytest.fixture(scope="module")
def route_test_environment():
    """
    Module-scoped fixture that sets up minimal mocks for route tests.

    Only mocks modules that cause import issues (jobs, websocket).
    Uses real pdd.server.models and pdd.server.security.

    Note: NOT autouse - tests must explicitly depend on this or on
    files_module/commands_module which depend on this.
    """
    _setup_route_mocks()
    yield
    _teardown_route_mocks()


# ============================================================================
# Shared fixtures for route tests
# ============================================================================

@pytest.fixture
def security_error_class():
    """Provides the SecurityError class for tests."""
    return _get_security_classes()['SecurityError']


@pytest.fixture
def path_validator_class():
    """Provides the PathValidator class for tests."""
    return _get_security_classes()['PathValidator']


@pytest.fixture
def job_status_enum():
    """Provides the JobStatus enum for tests."""
    return _get_model_classes()['JobStatus']
