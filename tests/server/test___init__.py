"""
Test Plan for pdd/server/__init__.py

1. **Module Exports Verification**
   - Goal: Ensure that the `__init__.py` file correctly exposes the required components.
   - Strategy: Use a pytest fixture to mock all submodules (`.app`, `.executor`, etc.) and inject them into `sys.modules`. Then reload `pdd.server` to ensure it imports these specific mocks.
   - Rationale: This isolates the test from the actual implementation of submodules and prevents import errors.

2. **Version and Constants Verification**
   - Goal: Verify `__version__` and global constants.
   - Strategy: Assert values on the reloaded module.

3. **Import Integrity**
   - Goal: Ensure `__all__` is complete and accurate.
   - Strategy: Compare `__all__` list against expected set of symbols.
"""

import sys
import pytest
import importlib
from unittest.mock import MagicMock, patch

@pytest.fixture
def mock_environment():
    """
    Creates mocks for all submodules required by pdd.server and patches sys.modules.
    Returns a tuple: (mock_objects_dict, sys_modules_patch_dict)
    """
    # Create mocks for the submodules
    mock_app = MagicMock()
    mock_app.create_app = MagicMock(name="create_app")
    mock_app.run_server = MagicMock(name="run_server")

    mock_executor = MagicMock()
    mock_executor.execute_pdd_command = MagicMock(name="execute_pdd_command")

    mock_jobs = MagicMock()
    mock_jobs.Job = MagicMock(name="Job")
    mock_jobs.JobManager = MagicMock(name="JobManager")

    mock_models = MagicMock()
    mock_models.ServerConfig = MagicMock(name="ServerConfig")
    mock_models.ServerStatus = MagicMock(name="ServerStatus")

    mock_websocket = MagicMock()
    mock_websocket.ConnectionManager = MagicMock(name="ConnectionManager")

    mock_security = MagicMock()
    mock_security.PathValidator = MagicMock(name="PathValidator")
    mock_security.SecurityError = MagicMock(name="SecurityError")

    # Dictionary of mocks to access in tests
    mock_objects = {
        "app": mock_app,
        "executor": mock_executor,
        "jobs": mock_jobs,
        "models": mock_models,
        "websocket": mock_websocket,
        "security": mock_security,
    }

    # Dictionary to patch sys.modules
    # We must mock the full hierarchy to ensure relative imports work
    modules_patch = {
        "pdd.server.app": mock_app,
        "pdd.server.executor": mock_executor,
        "pdd.server.jobs": mock_jobs,
        "pdd.server.models": mock_models,
        "pdd.server.routes": MagicMock(),
        "pdd.server.routes.websocket": mock_websocket,
        "pdd.server.security": mock_security,
    }

    return mock_objects, modules_patch

@pytest.fixture
def server_pkg(mock_environment):
    """
    Fixture that patches sys.modules, imports/reloads pdd.server, 
    and returns the module and the mocks.
    """
    mock_objects, modules_patch = mock_environment
    
    with patch.dict(sys.modules, modules_patch):
        # Import pdd.server. If it was already imported by another test, 
        # we MUST reload it to ensure it binds to our new mocks.
        import pdd.server
        importlib.reload(pdd.server)
        
        yield pdd.server, mock_objects

# --- Tests ---

def test_version_exists(server_pkg):
    """Verify that the package has a version string."""
    pkg, _ = server_pkg
    assert hasattr(pkg, "__version__")
    assert isinstance(pkg.__version__, str)
    assert pkg.__version__ == "0.1.0"

def test_constants_exist(server_pkg):
    """Verify global constants are exported."""
    pkg, _ = server_pkg
    assert pkg.DEFAULT_HOST == "127.0.0.1"
    assert pkg.DEFAULT_PORT == 9876
    assert pkg.API_VERSION == "v1"

def test_all_exports_are_present(server_pkg):
    """
    Verify that every symbol listed in __all__ is actually available 
    in the module namespace.
    """
    pkg, _ = server_pkg
    for name in pkg.__all__:
        assert hasattr(pkg, name), f"{name} is in __all__ but not in module namespace"

def test_app_exports(server_pkg):
    """Verify exports from .app submodule."""
    pkg, mocks = server_pkg
    assert pkg.create_app is mocks["app"].create_app
    assert pkg.run_server is mocks["app"].run_server

def test_executor_exports(server_pkg):
    """Verify exports from .executor submodule."""
    pkg, mocks = server_pkg
    assert pkg.execute_pdd_command is mocks["executor"].execute_pdd_command

def test_jobs_exports(server_pkg):
    """Verify exports from .jobs submodule."""
    pkg, mocks = server_pkg
    assert pkg.Job is mocks["jobs"].Job
    assert pkg.JobManager is mocks["jobs"].JobManager

def test_models_exports(server_pkg):
    """Verify exports from .models submodule."""
    pkg, mocks = server_pkg
    assert pkg.ServerConfig is mocks["models"].ServerConfig
    assert pkg.ServerStatus is mocks["models"].ServerStatus

def test_security_exports(server_pkg):
    """Verify exports from .security submodule."""
    pkg, mocks = server_pkg
    assert pkg.PathValidator is mocks["security"].PathValidator
    assert pkg.SecurityError is mocks["security"].SecurityError

def test_websocket_exports(server_pkg):
    """Verify exports from .routes.websocket submodule."""
    pkg, mocks = server_pkg
    assert pkg.ConnectionManager is mocks["websocket"].ConnectionManager

def test_all_list_completeness(server_pkg):
    """
    Verify that __all__ contains exactly the expected list of public symbols.
    """
    pkg, _ = server_pkg
    expected_symbols = {
        "create_app",
        "run_server",
        "ServerConfig",
        "ServerStatus",
        "Job",
        "JobManager",
        "PathValidator",
        "SecurityError",
        "ConnectionManager",
        "execute_pdd_command",
        "DEFAULT_HOST",
        "DEFAULT_PORT",
        "API_VERSION",
    }
    
    actual_symbols = set(pkg.__all__)
    assert actual_symbols == expected_symbols