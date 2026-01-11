"""
Tests for pdd.server.routes.websocket module.

This test file uses fixture-based mocking to avoid polluting sys.modules
during pytest collection.
"""

import sys
import types
import json
import asyncio
import time
from unittest.mock import MagicMock, AsyncMock, patch, ANY
from datetime import datetime
from enum import Enum
import pytest


# ============================================================================
# Local mock classes (not installed to sys.modules at module level)
# ============================================================================

class MockPydanticModel:
    def model_dump_json(self):
        d = {k: v for k, v in self.__dict__.items() if not k.startswith('_')}
        return json.dumps(d, default=str)


class WSMessage(MockPydanticModel):
    def __init__(self, type, data=None, **kwargs):
        self.type = type
        self.data = data
        for k, v in kwargs.items():
            setattr(self, k, v)


class StdoutMessage(WSMessage):
    def __init__(self, data, raw, timestamp):
        super().__init__(type="stdout", data=data, raw=raw, timestamp=timestamp)


class StderrMessage(WSMessage):
    def __init__(self, data, raw, timestamp):
        super().__init__(type="stderr", data=data, raw=raw, timestamp=timestamp)


class ProgressMessage(WSMessage):
    def __init__(self, current, total, message, timestamp):
        super().__init__(type="progress", data=None, current=current, total=total, message=message, timestamp=timestamp)


class JobStatus(Enum):
    QUEUED = "queued"
    RUNNING = "running"
    COMPLETED = "completed"
    FAILED = "failed"
    CANCELLED = "cancelled"


class Job:
    def __init__(self, id, status=JobStatus.RUNNING, result=None, cost=0.0):
        self.id = id
        self.status = status
        self.result = result
        self.cost = cost


class JobManager:
    pass


class ServerConfig:
    """Mock ServerConfig for testing."""
    pass


class ServerStatus:
    """Mock ServerStatus for testing."""
    pass


# ============================================================================
# Fixture to set up mocks and import module under test
# ============================================================================

@pytest.fixture(scope="module")
def websocket_module():
    """
    Set up mocks and import the websocket module.
    This fixture ensures mocking happens at test execution time, not collection time.
    """
    # Save existing modules - include all pdd.server modules to avoid pollution
    saved_modules = {}
    for mod_name in list(sys.modules.keys()):
        if mod_name.startswith("pdd.server"):
            saved_modules[mod_name] = sys.modules[mod_name]
            del sys.modules[mod_name]

    # Create mock models module with all required classes
    mock_models = types.ModuleType("pdd.server.models")
    mock_models.WSMessage = WSMessage
    mock_models.StdoutMessage = StdoutMessage
    mock_models.StderrMessage = StderrMessage
    mock_models.ProgressMessage = ProgressMessage
    mock_models.JobStatus = JobStatus
    mock_models.ServerConfig = ServerConfig
    mock_models.ServerStatus = ServerStatus
    sys.modules["pdd.server.models"] = mock_models

    # Create mock jobs module
    mock_jobs = types.ModuleType("pdd.server.jobs")
    mock_jobs.JobManager = JobManager
    mock_jobs.Job = Job
    mock_jobs.JobStatus = JobStatus  # websocket.py imports JobStatus as JobStatusEnum
    sys.modules["pdd.server.jobs"] = mock_jobs

    # Mock pdd.server as a package (must have __path__ to be a package)
    import pdd
    mock_server = types.ModuleType("pdd.server")
    mock_server.__path__ = [str(pdd.__path__[0]) + "/server"]  # Make it a package
    mock_server.app = MagicMock()
    mock_server.models = mock_models
    mock_server.jobs = mock_jobs
    sys.modules["pdd.server"] = mock_server
    sys.modules["pdd.server.app"] = MagicMock()
    sys.modules["pdd.server.security"] = MagicMock()
    sys.modules["pdd.server.executor"] = MagicMock()

    # Mock routes as a package
    mock_routes = types.ModuleType("pdd.server.routes")
    mock_routes.__path__ = [str(pdd.__path__[0]) + "/server/routes"]  # Make it a package
    sys.modules["pdd.server.routes"] = mock_routes

    # Mock sibling route modules to prevent import errors
    sys.modules["pdd.server.routes.files"] = MagicMock()
    sys.modules["pdd.server.routes.commands"] = MagicMock()
    sys.modules["pdd.server.routes.prompts"] = MagicMock()
    sys.modules["pdd.server.routes.exec"] = MagicMock()

    # Now import the module under test
    from pdd.server.routes.websocket import (
        clean_ansi,
        ConnectionManager,
        AsyncFileEventHandler,
        websocket_job_stream,
        websocket_watch,
        emit_job_output,
        emit_job_progress,
        emit_job_complete,
        manager as global_manager
    )

    yield {
        "clean_ansi": clean_ansi,
        "ConnectionManager": ConnectionManager,
        "AsyncFileEventHandler": AsyncFileEventHandler,
        "websocket_job_stream": websocket_job_stream,
        "websocket_watch": websocket_watch,
        "emit_job_output": emit_job_output,
        "emit_job_progress": emit_job_progress,
        "emit_job_complete": emit_job_complete,
        "global_manager": global_manager,
        # Also provide our mock classes for tests to use
        "WSMessage": WSMessage,
        "StdoutMessage": StdoutMessage,
        "StderrMessage": StderrMessage,
        "ProgressMessage": ProgressMessage,
        "JobStatus": JobStatus,
        "Job": Job,
    }

    # Cleanup: remove all pdd.server mocks and restore saved modules
    for mod_name in list(sys.modules.keys()):
        if mod_name.startswith("pdd.server"):
            del sys.modules[mod_name]
    for mod_name, mod in saved_modules.items():
        sys.modules[mod_name] = mod


# ============================================================================
# Tests
# ============================================================================

class TestUtilities:
    def test_clean_ansi(self, websocket_module):
        """Test ANSI code stripping."""
        clean_ansi = websocket_module["clean_ansi"]
        text = "\x1b[31mHello\x1b[0m World"
        assert clean_ansi(text) == "Hello World"
        text = "\x1b[1;32mSuccess\x1b[0m"
        assert clean_ansi(text) == "Success"
        text = "Plain text"
        assert clean_ansi(text) == "Plain text"


@pytest.mark.asyncio
class TestConnectionManager:
    async def test_lifecycle(self, websocket_module):
        ConnectionManager = websocket_module["ConnectionManager"]
        manager = ConnectionManager()
        ws = AsyncMock()
        await manager.connect(ws)
        assert ws in manager.active_connections
        ws.accept.assert_called_once()
        await manager.subscribe_to_job(ws, "job-1")
        assert ws in manager.job_subscriptions["job-1"]
        await manager.subscribe_to_watch(ws)
        assert ws in manager.watch_subscriptions
        manager.disconnect(ws, "job-1")
        assert ws not in manager.active_connections
        assert "job-1" not in manager.job_subscriptions
        assert ws not in manager.watch_subscriptions

    async def test_broadcast_job_message(self, websocket_module):
        ConnectionManager = websocket_module["ConnectionManager"]
        WSMessage = websocket_module["WSMessage"]
        manager = ConnectionManager()
        ws1 = AsyncMock()
        ws2 = AsyncMock()
        ws3 = AsyncMock()
        manager.job_subscriptions["job-1"] = [ws1]
        manager.job_subscriptions["job-2"] = [ws3]
        msg = WSMessage(type="test", data="foo")
        await manager.broadcast_job_message("job-1", msg)
        ws1.send_text.assert_called_once()
        ws2.send_text.assert_not_called()
        ws3.send_text.assert_not_called()
        sent_json = ws1.send_text.call_args[0][0]
        assert '"type": "test"' in sent_json
        assert '"data": "foo"' in sent_json

    async def test_broadcast_cleanup_on_error(self, websocket_module):
        ConnectionManager = websocket_module["ConnectionManager"]
        WSMessage = websocket_module["WSMessage"]
        manager = ConnectionManager()
        ws_alive = AsyncMock()
        ws_dead = AsyncMock()
        ws_dead.send_text.side_effect = Exception("Connection closed")
        manager.active_connections = [ws_alive, ws_dead]
        manager.job_subscriptions["job-1"] = [ws_alive, ws_dead]
        msg = WSMessage(type="test")
        await manager.broadcast_job_message("job-1", msg)
        assert ws_alive in manager.job_subscriptions["job-1"]
        assert ws_dead not in manager.job_subscriptions["job-1"]

    async def test_broadcast_file_change(self, websocket_module):
        ConnectionManager = websocket_module["ConnectionManager"]
        WSMessage = websocket_module["WSMessage"]
        manager = ConnectionManager()
        ws = AsyncMock()
        manager.watch_subscriptions.append(ws)
        msg = WSMessage(type="file_change")
        await manager.broadcast_file_change(msg)
        ws.send_text.assert_called_once()


class TestAsyncFileEventHandler:
    def test_debounce_logic(self, websocket_module):
        """Test that rapid events are debounced."""
        AsyncFileEventHandler = websocket_module["AsyncFileEventHandler"]
        WSMessage = websocket_module["WSMessage"]
        loop = MagicMock()
        queue = MagicMock()
        handler = AsyncFileEventHandler(loop, queue)
        event = MagicMock()
        event.is_directory = False
        event.src_path = "/tmp/test.txt"

        # First event
        with patch("time.time", return_value=100.0):
            handler.on_modified(event)
            loop.call_soon_threadsafe.assert_called()
            args = loop.call_soon_threadsafe.call_args[0]
            assert args[0] == queue.put_nowait
            assert isinstance(args[1], WSMessage)

        loop.reset_mock()

        # Second event (too soon)
        with patch("time.time", return_value=100.05):
            handler.on_modified(event)
            loop.call_soon_threadsafe.assert_not_called()

        # Third event (after debounce)
        with patch("time.time", return_value=100.2):
            handler.on_modified(event)
            loop.call_soon_threadsafe.assert_called()

    def test_event_types(self, websocket_module):
        """Test different event types trigger queue put."""
        AsyncFileEventHandler = websocket_module["AsyncFileEventHandler"]
        loop = MagicMock()
        queue = MagicMock()
        handler = AsyncFileEventHandler(loop, queue)
        event = MagicMock(is_directory=False, src_path="foo")

        with patch("time.time", side_effect=[100, 200, 300]):
            handler.on_created(event)
            handler.on_deleted(event)
            handler.on_modified(event)

        assert loop.call_soon_threadsafe.call_count == 3


@pytest.mark.asyncio
class TestWebsocketJobStream:
    async def test_job_not_found(self, websocket_module):
        websocket_job_stream = websocket_module["websocket_job_stream"]
        ws = AsyncMock()
        job_manager = MagicMock()
        job_manager.get_job.return_value = None
        await websocket_job_stream(ws, "job-missing", job_manager)
        ws.close.assert_called_with(code=1008, reason="Job not found")

    async def test_job_already_completed(self, websocket_module):
        websocket_job_stream = websocket_module["websocket_job_stream"]
        Job = websocket_module["Job"]
        JobStatus = websocket_module["JobStatus"]
        ws = AsyncMock()
        job_manager = MagicMock()
        job = Job("job-1", status=JobStatus.COMPLETED, result={"foo": "bar"})
        job_manager.get_job.return_value = job

        await websocket_job_stream(ws, "job-1", job_manager)

        ws.send_text.assert_called_once()
        sent_data = ws.send_text.call_args[0][0]
        assert '"type": "complete"' in sent_data
        assert '"result": {"foo": "bar"}' in sent_data
        ws.close.assert_called_once()

    async def test_stream_interaction_cancel(self, websocket_module):
        websocket_job_stream = websocket_module["websocket_job_stream"]
        Job = websocket_module["Job"]
        JobStatus = websocket_module["JobStatus"]
        ws = AsyncMock()
        job_manager = MagicMock()
        job_manager.cancel = AsyncMock()
        job = Job("job-1", status=JobStatus.RUNNING)
        job_manager.get_job.return_value = job

        ws.receive_text.side_effect = [
            json.dumps({"type": "cancel"}),
            Exception("Disconnect")
        ]

        try:
            await websocket_job_stream(ws, "job-1", job_manager)
        except Exception:
            pass

        job_manager.cancel.assert_called_with("job-1")

    async def test_stream_interaction_input(self, websocket_module):
        websocket_job_stream = websocket_module["websocket_job_stream"]
        Job = websocket_module["Job"]
        JobStatus = websocket_module["JobStatus"]
        ws = AsyncMock()
        job_manager = MagicMock()
        job = Job("job-1", status=JobStatus.RUNNING)
        job_manager.get_job.return_value = job

        ws.receive_text.side_effect = [
            json.dumps({"type": "input", "data": "yes\n"}),
            Exception("Disconnect")
        ]

        try:
            await websocket_job_stream(ws, "job-1", job_manager)
        except Exception:
            pass

        assert ws.receive_text.call_count == 2


@pytest.mark.asyncio
class TestWebsocketWatch:
    @patch("pdd.server.routes.websocket.Observer")
    async def test_watch_flow(self, MockObserver, websocket_module):
        websocket_watch = websocket_module["websocket_watch"]
        ws = AsyncMock()
        project_root = MagicMock()
        project_root.__truediv__.return_value.resolve.return_value.exists.return_value = True
        project_root.__truediv__.return_value.resolve.return_value.is_dir.return_value = True

        observer_instance = MockObserver.return_value

        ws.receive_text.side_effect = [
            json.dumps({"paths": ["src"]}),
            Exception("Stop Loop")
        ]

        try:
            await websocket_watch(ws, project_root)
        except Exception:
            pass

        observer_instance.schedule.assert_called()
        observer_instance.start.assert_called()
        observer_instance.stop.assert_called()


@pytest.mark.asyncio
class TestEmitHelpers:
    async def test_emit_job_output(self, websocket_module):
        emit_job_output = websocket_module["emit_job_output"]
        with patch("pdd.server.routes.websocket.manager") as mock_mgr:
            mock_mgr.broadcast_job_message = AsyncMock()
            await emit_job_output("job-1", "stdout", "test")
            args = mock_mgr.broadcast_job_message.call_args[0]
            assert args[0] == "job-1"
            assert type(args[1]).__name__ == "StdoutMessage"
            assert args[1].data == "test"

    async def test_emit_job_progress(self, websocket_module):
        emit_job_progress = websocket_module["emit_job_progress"]
        with patch("pdd.server.routes.websocket.manager") as mock_mgr:
            mock_mgr.broadcast_job_message = AsyncMock()
            await emit_job_progress("job-1", 50, 100, "halfway")
            args = mock_mgr.broadcast_job_message.call_args[0]
            assert args[0] == "job-1"
            assert type(args[1]).__name__ == "ProgressMessage"
            assert args[1].current == 50

    async def test_emit_job_complete(self, websocket_module):
        emit_job_complete = websocket_module["emit_job_complete"]
        with patch("pdd.server.routes.websocket.manager") as mock_mgr:
            mock_mgr.broadcast_job_message = AsyncMock()
            await emit_job_complete("job-1", {"res": 1}, True, 0.5)
            args = mock_mgr.broadcast_job_message.call_args[0]
            assert args[0] == "job-1"
            assert args[1].type == "complete"
            assert args[1].data["success"] is True
            assert args[1].data["cost"] == 0.5
