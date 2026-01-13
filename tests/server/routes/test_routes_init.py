import sys
import pytest
from unittest.mock import MagicMock, patch
from pathlib import Path
import importlib

# --- Test Plan ---
#
# 1. Objective: Verify that `pdd.server.routes` correctly exposes the required routers.
#
# 2. Code Analysis:
#    - The module performs relative imports:
#      - `from .files import router as files_router`
#      - `from .commands import router as commands_router`
#      - `from .websocket import router as websocket_router`
#    - It defines `__all__` to export these three aliases.
#
# 3. Strategy:
#    - Since this is an `__init__.py` file relying on sibling modules that might not exist
#      in the test environment or should be isolated, we must mock the submodules
#      (`pdd.server.routes.files`, `pdd.server.routes.commands`, `pdd.server.routes.websocket`).
#    - We will use `sys.modules` patching to inject these mocks before importing the module under test.
#    - We will verify that the imported module has the expected attributes pointing to our mocks.
#    - We will verify the content of `__all__`.
#
# 4. Z3 Formal Verification:
#    - This module contains only declarative import/export logic.
#    - There is no algorithmic complexity, state transitions, or constraints suitable for SMT solving.
#    - Therefore, Z3 tests are not applicable and will be omitted in favor of structural unit tests.
#
# 5. Edge Cases:
#    - Missing submodules: Verified by the fact that we must mock them for the test to pass.
#    - Missing `router` attribute in submodules: Verified implicitly; if our mock lacks it, import fails.

# --- Tests ---

def test_routes_module_exports():
    """
    Test that pdd.server.routes imports specific routers from submodules
    and exports them via __all__.
    """
    # 1. Create mocks for the dependencies
    mock_architecture_module = MagicMock()
    mock_auth_module = MagicMock()
    mock_files_module = MagicMock()
    mock_commands_module = MagicMock()
    mock_websocket_module = MagicMock()
    mock_prompts_module = MagicMock()

    # 2. Define the 'router' objects that should be imported
    mock_architecture_router = MagicMock(name="architecture_router_obj")
    mock_auth_router = MagicMock(name="auth_router_obj")
    mock_files_router = MagicMock(name="files_router_obj")
    mock_commands_router = MagicMock(name="commands_router_obj")
    mock_websocket_router = MagicMock(name="websocket_router_obj")
    mock_prompts_router = MagicMock(name="prompts_router_obj")

    mock_architecture_module.router = mock_architecture_router
    mock_auth_module.router = mock_auth_router
    mock_files_module.router = mock_files_router
    mock_commands_module.router = mock_commands_router
    mock_websocket_module.router = mock_websocket_router
    mock_prompts_module.router = mock_prompts_router

    # 3. Patch sys.modules to simulate the existence of the submodules
    # We use a dict to update sys.modules temporarily
    module_patches = {
        "pdd.server.routes.architecture": mock_architecture_module,
        "pdd.server.routes.auth": mock_auth_module,
        "pdd.server.routes.files": mock_files_module,
        "pdd.server.routes.commands": mock_commands_module,
        "pdd.server.routes.websocket": mock_websocket_module,
        "pdd.server.routes.prompts": mock_prompts_module,
    }

    with patch.dict(sys.modules, module_patches):
        # 4. Import the module under test
        # We must ensure it's reloaded if it was already imported, to pick up our mocks
        if "pdd.server.routes" in sys.modules:
            del sys.modules["pdd.server.routes"]

        import pdd.server.routes as routes_module

        # 5. Assertions

        # Verify attributes exist and point to the correct mock objects
        assert hasattr(routes_module, "architecture_router")
        assert routes_module.architecture_router is mock_architecture_router

        assert hasattr(routes_module, "auth_router")
        assert routes_module.auth_router is mock_auth_router

        assert hasattr(routes_module, "files_router")
        assert routes_module.files_router is mock_files_router

        assert hasattr(routes_module, "commands_router")
        assert routes_module.commands_router is mock_commands_router

        assert hasattr(routes_module, "websocket_router")
        assert routes_module.websocket_router is mock_websocket_router

        assert hasattr(routes_module, "prompts_router")
        assert routes_module.prompts_router is mock_prompts_router

        # Verify __all__ definition
        assert hasattr(routes_module, "__all__")
        expected_all = ["architecture", "auth", "files", "commands", "prompts", "architecture_router", "auth_router", "files_router", "commands_router", "websocket_router", "prompts_router"]
        assert sorted(routes_module.__all__) == sorted(expected_all)

def test_routes_import_failure():
    """
    Verify that the module fails to import if a required submodule attribute (router) is missing.
    This ensures the code is actually looking for 'router' and not just importing the module.
    """
    # Mock a module that exists but lacks the 'router' attribute
    bad_mock_module = MagicMock(spec=[])  # Empty spec, no attributes

    module_patches = {
        "pdd.server.routes.architecture": MagicMock(),
        "pdd.server.routes.auth": bad_mock_module,
        "pdd.server.routes.files": MagicMock(),
        # We don't strictly need the others for this specific failure test
        "pdd.server.routes.commands": MagicMock(),
        "pdd.server.routes.websocket": MagicMock(),
        "pdd.server.routes.prompts": MagicMock(),
    }

    with patch.dict(sys.modules, module_patches):
        if "pdd.server.routes" in sys.modules:
            del sys.modules["pdd.server.routes"]

        # Expect an ImportError because 'router' cannot be imported from 'files'
        with pytest.raises(ImportError):
            import pdd.server.routes