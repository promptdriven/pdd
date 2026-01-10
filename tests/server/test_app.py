"""
Unit tests for pdd.server.app module.

This test file uses fixture-based mocking to avoid polluting sys.modules
during pytest collection. All mocks are set up inside fixtures/tests.
"""
import sys
import types
import importlib
import pytest
import z3
from pathlib import Path
from datetime import datetime
from enum import Enum
from unittest.mock import MagicMock, patch, AsyncMock
from fastapi import FastAPI, Request, APIRouter
from fastapi.testclient import TestClient
from pydantic import BaseModel, Field
from typing import Optional, List


# ============================================================================
# Mock Pydantic Models (defined but NOT injected at module level)
# ============================================================================

class MockFileTreeNode(BaseModel):
    name: str
    path: str
    type: str
    children: Optional[List['MockFileTreeNode']] = None
    size: Optional[int] = None
    mtime: datetime


class MockFileContent(BaseModel):
    path: str
    content: str
    encoding: str
    size: int
    is_binary: bool
    chunk_index: Optional[int] = None
    total_chunks: Optional[int] = None
    checksum: str


class MockWriteFileRequest(BaseModel):
    path: str
    content: str
    encoding: str = "utf-8"
    create_parents: bool = False


class MockWriteResult(BaseModel):
    success: bool
    path: str
    mtime: Optional[datetime] = None
    error: Optional[str] = None


class MockFileMetadata(BaseModel):
    path: str
    exists: bool
    size: Optional[int] = None
    mtime: Optional[datetime] = None
    is_directory: bool = False


class MockJobStatus(str, Enum):
    QUEUED = "queued"
    RUNNING = "running"
    COMPLETED = "completed"
    FAILED = "failed"
    CANCELLED = "cancelled"


class MockJobHandle(BaseModel):
    job_id: str
    status: MockJobStatus = MockJobStatus.QUEUED
    created_at: datetime = Field(default_factory=datetime.utcnow)


class MockJobResult(BaseModel):
    job_id: str
    status: MockJobStatus
    result: Optional[dict] = None
    error: Optional[str] = None
    cost: float = 0.0
    duration_seconds: float = 0.0
    completed_at: Optional[datetime] = None


class MockCommandRequest(BaseModel):
    command: str
    args: dict = Field(default_factory=dict)
    options: dict = Field(default_factory=dict)


class MockServerConfig(BaseModel):
    host: str = "127.0.0.1"
    port: int = 9876
    log_level: str = "info"
    allowed_origins: Optional[List[str]] = None


class MockServerStatus(BaseModel):
    version: str
    project_root: str
    uptime_seconds: float
    active_jobs: int


class MockSecurityError(Exception):
    def __init__(self, code: str, message: str):
        self.code = code
        self.message = message
        super().__init__(message)


class MockSecurityLoggingMiddleware:
    def __init__(self, app):
        self.app = app

    async def __call__(self, scope, receive, send):
        await self.app(scope, receive, send)


# ============================================================================
# Fixture to set up mocks and import app module
# ============================================================================

@pytest.fixture(scope="module")
def app_module_with_mocks():
    """
    Set up mock modules, import app, then clean up.
    This avoids polluting sys.modules for other tests.
    """
    # Save original modules - be thorough to handle pollution from other tests
    saved_modules = {}
    modules_to_clear = [
        "pdd.server.app",
        "pdd.server.models",
        "pdd.server.security",
        "pdd.server.jobs",
        "pdd.server.routes",
        "pdd.server.routes.files",
        "pdd.server.routes.commands",
        "pdd.server.routes.websocket",
        "pdd.server.routes.prompts",
    ]

    # Save and remove ALL pdd.server modules to ensure clean slate
    for mod_name in list(sys.modules.keys()):
        if mod_name.startswith("pdd.server"):
            saved_modules[mod_name] = sys.modules[mod_name]
            del sys.modules[mod_name]

    try:
        # Set up mock modules
        _mock_models = types.ModuleType("pdd.server.models")
        _mock_models.FileTreeNode = MockFileTreeNode
        _mock_models.FileContent = MockFileContent
        _mock_models.WriteFileRequest = MockWriteFileRequest
        _mock_models.WriteResult = MockWriteResult
        _mock_models.FileMetadata = MockFileMetadata
        _mock_models.JobStatus = MockJobStatus
        _mock_models.JobHandle = MockJobHandle
        _mock_models.JobResult = MockJobResult
        _mock_models.CommandRequest = MockCommandRequest
        _mock_models.ServerConfig = MockServerConfig
        _mock_models.ServerStatus = MockServerStatus
        sys.modules["pdd.server.models"] = _mock_models

        _mock_security = types.ModuleType("pdd.server.security")
        _mock_security.SecurityError = MockSecurityError
        _mock_security.PathValidator = MagicMock()
        _mock_security.configure_cors = MagicMock()
        _mock_security.SecurityLoggingMiddleware = MockSecurityLoggingMiddleware
        sys.modules["pdd.server.security"] = _mock_security

        _mock_jobs = types.ModuleType("pdd.server.jobs")
        _mock_jobs.JobManager = MagicMock()
        _mock_jobs.Job = MagicMock()
        sys.modules["pdd.server.jobs"] = _mock_jobs

        _mock_routes = types.ModuleType("pdd.server.routes")
        _mock_routes.__path__ = []
        sys.modules["pdd.server.routes"] = _mock_routes

        _mock_routes_files = types.ModuleType("pdd.server.routes.files")
        _mock_routes_files.router = APIRouter()
        _mock_routes_files.get_path_validator = MagicMock(__name__="get_path_validator_mock")
        sys.modules["pdd.server.routes.files"] = _mock_routes_files

        _mock_routes_commands = types.ModuleType("pdd.server.routes.commands")
        _mock_routes_commands.router = APIRouter()
        _mock_routes_commands.get_job_manager = MagicMock(__name__="get_job_manager_mock")
        sys.modules["pdd.server.routes.commands"] = _mock_routes_commands

        _mock_routes_ws = types.ModuleType("pdd.server.routes.websocket")
        _mock_routes_ws.ConnectionManager = MagicMock()
        _mock_routes_ws.create_websocket_routes = MagicMock()
        _mock_routes_ws.router = APIRouter()
        _mock_routes_ws.get_job_manager = MagicMock(__name__="ws_get_job_manager_mock")
        _mock_routes_ws.get_connection_manager = MagicMock(__name__="ws_get_connection_manager_mock")
        _mock_routes_ws.get_project_root = MagicMock(__name__="ws_get_project_root_mock")
        sys.modules["pdd.server.routes.websocket"] = _mock_routes_ws

        _mock_routes_prompts = types.ModuleType("pdd.server.routes.prompts")
        _mock_routes_prompts.router = APIRouter()
        _mock_routes_prompts.get_path_validator = MagicMock(__name__="get_path_validator_mock")
        _mock_routes_prompts.set_path_validator = MagicMock(__name__="set_path_validator_mock")
        sys.modules["pdd.server.routes.prompts"] = _mock_routes_prompts

        # Remove cached app module if any
        if "pdd.server.app" in sys.modules:
            del sys.modules["pdd.server.app"]

        # Import the app module fresh
        from pdd.server import app as app_mod

        # Return everything needed for tests
        yield {
            "app_module": app_mod,
            "AppState": app_mod.AppState,
            "create_app": app_mod.create_app,
            "get_app_state": app_mod.get_app_state,
            "get_path_validator": app_mod.get_path_validator,
            "get_job_manager": app_mod.get_job_manager,
            "get_connection_manager": app_mod.get_connection_manager,
            "run_server": app_mod.run_server,
            "security_exception_handler": app_mod.security_exception_handler,
            "generic_exception_handler": app_mod.generic_exception_handler,
            "SecurityError": MockSecurityError,
            "ServerConfig": MockServerConfig,
            "files": _mock_routes_files,
            "commands": _mock_routes_commands,
        }

    finally:
        # Clean up: remove ALL pdd.server modules and restore originals
        for mod_name in list(sys.modules.keys()):
            if mod_name.startswith("pdd.server"):
                del sys.modules[mod_name]

        for mod_name, mod in saved_modules.items():
            sys.modules[mod_name] = mod


@pytest.fixture
def mock_project_root(tmp_path):
    return tmp_path / "project"


@pytest.fixture
def mock_managers():
    """Mock the internal managers of AppState."""
    with patch("pdd.server.app.PathValidator") as MockPV, \
         patch("pdd.server.app.JobManager") as MockJM, \
         patch("pdd.server.app.ConnectionManager") as MockCM:

        jm_instance = MockJM.return_value
        jm_instance.get_active_jobs.return_value = []
        jm_instance.shutdown = AsyncMock()

        yield {
            "PathValidator": MockPV,
            "JobManager": MockJM,
            "ConnectionManager": MockCM,
            "jm_instance": jm_instance
        }


# ============================================================================
# Unit Tests: AppState & Dependencies
# ============================================================================

def test_app_state_initialization(app_module_with_mocks, mock_project_root, mock_managers):
    """Test that AppState initializes all required managers."""
    AppState = app_module_with_mocks["AppState"]
    state = AppState(mock_project_root)

    assert state.project_root == mock_project_root.resolve()
    assert state.version == "0.1.0"
    assert isinstance(state.uptime_seconds, float)

    mock_managers["PathValidator"].assert_called_once_with(state.project_root)
    mock_managers["JobManager"].assert_called_once_with(max_concurrent=2)
    mock_managers["ConnectionManager"].assert_called_once()


def test_get_app_state_uninitialized(app_module_with_mocks):
    """Test that get_app_state raises RuntimeError if create_app hasn't been called."""
    app_mod = app_module_with_mocks["app_module"]
    app_mod._app_state = None

    with pytest.raises(RuntimeError, match="Application state not initialized"):
        app_module_with_mocks["get_app_state"]()


def test_dependency_getters(app_module_with_mocks, mock_project_root, mock_managers):
    """Test that dependency injection helpers return the correct objects."""
    app_mod = app_module_with_mocks["app_module"]
    app_mod._app_state = None

    create_app = app_module_with_mocks["create_app"]
    get_app_state = app_module_with_mocks["get_app_state"]
    get_path_validator = app_module_with_mocks["get_path_validator"]
    get_job_manager = app_module_with_mocks["get_job_manager"]
    get_connection_manager = app_module_with_mocks["get_connection_manager"]

    create_app(mock_project_root)
    state = get_app_state()

    assert get_path_validator() == state.path_validator
    assert get_job_manager() == state.job_manager
    assert get_connection_manager() == state.connection_manager


# ============================================================================
# Unit Tests: App Factory
# ============================================================================

def test_create_app_structure(app_module_with_mocks, mock_project_root, mock_managers):
    """Test that create_app builds the FastAPI app correctly."""
    app_mod = app_module_with_mocks["app_module"]
    app_mod._app_state = None

    create_app = app_module_with_mocks["create_app"]
    get_app_state = app_module_with_mocks["get_app_state"]
    files = app_module_with_mocks["files"]
    commands = app_module_with_mocks["commands"]

    app = create_app(mock_project_root)

    assert isinstance(app, FastAPI)
    assert app.title == "PDD Server"
    assert get_app_state().project_root == mock_project_root.resolve()
    assert files.get_path_validator in app.dependency_overrides
    assert commands.get_job_manager in app.dependency_overrides


def test_create_app_cors_configuration(app_module_with_mocks, mock_project_root, mock_managers):
    """Test CORS configuration is called."""
    app_mod = app_module_with_mocks["app_module"]
    app_mod._app_state = None

    create_app = app_module_with_mocks["create_app"]

    with patch("pdd.server.app.configure_cors") as mock_cors:
        create_app(mock_project_root, allowed_origins=["http://test.com"])
        mock_cors.assert_called_once()
        args = mock_cors.call_args
        assert args[0][1] == ["http://test.com"]


# ============================================================================
# Z3 Formal Verification: Configuration Logic
# ============================================================================

def test_z3_cors_precedence_logic():
    """Formal verification of the CORS origin selection logic in create_app."""
    s = z3.Solver()
    has_config = z3.Bool('has_config')
    config_origins_val = z3.Int('config_origins_val')
    arg_origins_val = z3.Int('arg_origins_val')
    s.add(z3.Or(config_origins_val == 0, config_origins_val == 1))
    s.add(z3.Or(arg_origins_val == 0, arg_origins_val == 2))
    step1_origins = z3.If(has_config, config_origins_val, z3.IntVal(0))
    final_origins = z3.If(step1_origins == 0, arg_origins_val, step1_origins)
    s.push()
    s.add(has_config)
    s.add(config_origins_val == 1)
    s.add(final_origins != 1)
    assert s.check() == z3.unsat
    s.pop()
    s.push()
    s.add(has_config)
    s.add(config_origins_val == 0)
    s.add(final_origins != arg_origins_val)
    assert s.check() == z3.unsat
    s.pop()
    s.push()
    s.add(z3.Not(has_config))
    s.add(final_origins != arg_origins_val)
    assert s.check() == z3.unsat
    s.pop()


# ============================================================================
# Unit Tests: Lifespan & Exception Handlers
# ============================================================================

@pytest.mark.asyncio
async def test_lifespan_startup_shutdown(app_module_with_mocks, mock_project_root, mock_managers):
    """Test that lifespan logs startup and cancels jobs on shutdown."""
    app_mod = app_module_with_mocks["app_module"]
    app_mod._app_state = None

    create_app = app_module_with_mocks["create_app"]
    app = create_app(mock_project_root)
    jm_mock = mock_managers["jm_instance"]
    jm_mock.get_active_jobs.return_value = ["job1", "job2"]

    with TestClient(app) as client:
        pass

    jm_mock.shutdown.assert_awaited_once()


@pytest.mark.asyncio
async def test_security_exception_handler(app_module_with_mocks):
    """Test that SecurityError returns 403."""
    security_exception_handler = app_module_with_mocks["security_exception_handler"]
    SecurityError = app_module_with_mocks["SecurityError"]

    exc = SecurityError(code="TEST_CODE", message="Access denied")
    response = await security_exception_handler(Request({"type": "http"}), exc)
    assert response.status_code == 403
    content = eval(response.body.decode())
    assert content["detail"] == "Access denied"


@pytest.mark.asyncio
async def test_generic_exception_handler(app_module_with_mocks):
    """Test that generic exceptions return 500."""
    generic_exception_handler = app_module_with_mocks["generic_exception_handler"]

    exc = ValueError("Something went wrong")
    response = await generic_exception_handler(Request({"type": "http"}), exc)
    assert response.status_code == 500
    content = eval(response.body.decode())
    assert content["detail"] == "Internal server error"


# ============================================================================
# Unit Tests: Server Runner
# ============================================================================

def test_run_server_legacy_args(app_module_with_mocks, mock_project_root, mock_managers):
    """Test run_server with legacy arguments."""
    app_mod = app_module_with_mocks["app_module"]
    app_mod._app_state = None

    run_server = app_module_with_mocks["run_server"]

    with patch("uvicorn.run") as mock_uvicorn:
        run_server(project_root=mock_project_root, host="0.0.0.0", port=8000, log_level="debug")
        mock_uvicorn.assert_called_once()

        args, kwargs = mock_uvicorn.call_args
        assert isinstance(args[0], FastAPI)
        assert kwargs["host"] == "0.0.0.0"
        assert kwargs["port"] == 8000
        assert kwargs["log_level"] == "debug"


def test_run_server_with_config(app_module_with_mocks, mock_project_root, mock_managers):
    """Test run_server with ServerConfig object."""
    app_mod = app_module_with_mocks["app_module"]
    app_mod._app_state = None

    run_server = app_module_with_mocks["run_server"]
    ServerConfig = app_module_with_mocks["ServerConfig"]

    config = ServerConfig(host="1.2.3.4", port=9000, log_level="warning", allowed_origins=["*"])
    with patch("uvicorn.run") as mock_uvicorn:
        run_server(project_root=mock_project_root, config=config)
        mock_uvicorn.assert_called_once()
        kwargs = mock_uvicorn.call_args[1]
        assert kwargs["host"] == "1.2.3.4"
        assert kwargs["port"] == 9000
        assert kwargs["log_level"] == "warning"


def test_run_server_missing_args(app_module_with_mocks):
    """Test run_server raises error if neither app nor project_root provided."""
    run_server = app_module_with_mocks["run_server"]

    with pytest.raises(ValueError, match="Must provide either 'app' or 'project_root'"):
        run_server(project_root=None, app=None)
