"""
Tests for pdd.sync_state_emitter module.

Tests the SyncStateEmitter class which writes structured JSON state
to a temp file for cross-process communication between the sync
subprocess and the server/frontend.
"""

import json
import os
import tempfile
import time
from unittest.mock import patch

import pytest

from pdd.sync_state_emitter import SyncStateEmitter


@pytest.fixture
def state_file(tmp_path):
    """Provide a temp file path for state output."""
    return str(tmp_path / "sync_state.json")


@pytest.fixture
def emitter(state_file):
    """Create an emitter that writes to a known temp file."""
    with patch.dict(os.environ, {"PDD_SYNC_STATE_FILE": state_file}):
        em = SyncStateEmitter(basename="calculator", budget=5.0)
    return em


def read_state(state_file):
    """Read and parse the state file."""
    with open(state_file, 'r') as f:
        return json.load(f)


class TestSyncStateEmitterInit:
    """Tests for SyncStateEmitter initialization."""

    def test_init_with_basename_and_budget(self, state_file):
        """Test initialization stores basename and budget."""
        with patch.dict(os.environ, {"PDD_SYNC_STATE_FILE": state_file}):
            emitter = SyncStateEmitter(basename="calculator", budget=5.0)
        assert emitter._basename == "calculator"
        assert emitter._budget == 5.0

    def test_init_with_none_budget(self, state_file):
        """Test initialization with no budget."""
        with patch.dict(os.environ, {"PDD_SYNC_STATE_FILE": state_file}):
            emitter = SyncStateEmitter(basename="my_module", budget=None)
        assert emitter._basename == "my_module"
        assert emitter._budget is None

    def test_init_sets_start_time(self, state_file):
        """Test that start time is set on initialization."""
        before = time.time()
        with patch.dict(os.environ, {"PDD_SYNC_STATE_FILE": state_file}):
            emitter = SyncStateEmitter(basename="test", budget=1.0)
        after = time.time()
        assert before <= emitter._start_time <= after

    def test_init_last_operation_is_none(self, state_file):
        """Test that last operation starts as None."""
        with patch.dict(os.environ, {"PDD_SYNC_STATE_FILE": state_file}):
            emitter = SyncStateEmitter(basename="test", budget=1.0)
        assert emitter._last_operation is None

    def test_init_uses_env_var_for_state_file(self, state_file):
        """Test that PDD_SYNC_STATE_FILE env var is used."""
        with patch.dict(os.environ, {"PDD_SYNC_STATE_FILE": state_file}):
            emitter = SyncStateEmitter(basename="test", budget=1.0)
        assert emitter._state_file == state_file

    def test_init_fallback_to_pid_based_path(self):
        """Test fallback path when env var is not set."""
        with patch.dict(os.environ, {}, clear=True):
            # Remove PDD_SYNC_STATE_FILE if it exists
            os.environ.pop("PDD_SYNC_STATE_FILE", None)
            emitter = SyncStateEmitter(basename="test", budget=1.0)
        expected = os.path.join(tempfile.gettempdir(), f'pdd_sync_state_{os.getpid()}.json')
        assert emitter._state_file == expected


class TestEmitSyncStart:
    """Tests for emit_sync_start method."""

    def test_emit_sync_start_writes_file(self, emitter, state_file):
        """Test that sync_start writes the state file."""
        paths = {
            "prompt": "prompts/calculator.prompt",
            "code": "src/calculator.py",
            "example": "examples/calculator_example.py",
            "tests": "tests/test_calculator.py",
        }
        emitter.emit_sync_start(paths=paths)
        assert os.path.exists(state_file)

    def test_emit_sync_start_json_payload(self, emitter, state_file):
        """Test that sync_start contains correct JSON data."""
        paths = {
            "prompt": "prompts/calculator.prompt",
            "code": "src/calculator.py",
            "example": "examples/calculator_example.py",
            "tests": "tests/test_calculator.py",
        }
        emitter.emit_sync_start(paths=paths)
        state = read_state(state_file)
        assert state["operation"] == "initializing"
        assert state["basename"] == "calculator"
        assert state["budget"] == 5.0
        assert state["paths"] == paths
        assert state["elapsedSeconds"] == 0
        assert state["cost"] == 0
        assert state["colors"] == {}
        assert state["status"] == "running"


class TestEmitStateUpdate:
    """Tests for emit_state_update method."""

    def test_emit_state_update_fields(self, emitter, state_file):
        """Test that state_update has correct fields."""
        emitter.emit_state_update(
            operation="generate",
            cost=0.42,
            paths={"prompt": "p.prompt", "code": "c.py", "example": "e.py", "tests": "t.py"},
        )
        state = read_state(state_file)
        assert state["operation"] == "generate"
        assert state["cost"] == 0.42
        assert state["status"] == "running"
        assert state["basename"] == "calculator"
        assert state["budget"] == 5.0

    def test_emit_state_update_with_colors(self, emitter, state_file):
        """Test that colors are included when provided."""
        colors = {"prompt": "purple", "code": "cyan", "example": "green", "tests": "magenta"}
        emitter.emit_state_update(
            operation="test",
            cost=1.0,
            paths={"prompt": "p", "code": "c", "example": "e", "tests": "t"},
            colors=colors,
        )
        state = read_state(state_file)
        assert state["colors"] == colors

    def test_emit_state_update_without_colors(self, emitter, state_file):
        """Test that empty colors dict is used when not provided."""
        emitter.emit_state_update(
            operation="fix",
            cost=0.5,
            paths={"prompt": "p", "code": "c", "example": "e", "tests": "t"},
        )
        state = read_state(state_file)
        assert state["colors"] == {}

    def test_emit_state_update_elapsed_time(self, emitter, state_file):
        """Test that elapsed time is computed from start."""
        emitter._start_time = time.time() - 10.0  # Simulate 10 seconds elapsed
        emitter.emit_state_update(
            operation="generate",
            cost=0.0,
            paths={"prompt": "p", "code": "c", "example": "e", "tests": "t"},
        )
        state = read_state(state_file)
        assert state["elapsedSeconds"] >= 10.0

    def test_emit_state_update_updates_last_operation(self, emitter, state_file):
        """Test that last_operation is updated on each emit."""
        assert emitter._last_operation is None
        emitter.emit_state_update(
            operation="generate",
            cost=0.0,
            paths={"prompt": "p", "code": "c", "example": "e", "tests": "t"},
        )
        assert emitter._last_operation == "generate"

    def test_emit_state_update_cost_rounded(self, emitter, state_file):
        """Test that cost is rounded to 4 decimal places."""
        emitter.emit_state_update(
            operation="test",
            cost=0.123456789,
            paths={"prompt": "p", "code": "c", "example": "e", "tests": "t"},
        )
        state = read_state(state_file)
        assert state["cost"] == 0.1235

    def test_emit_state_update_includes_budget(self, state_file):
        """Test that budget is included in the payload."""
        with patch.dict(os.environ, {"PDD_SYNC_STATE_FILE": state_file}):
            emitter = SyncStateEmitter(basename="calc", budget=3.5)
        emitter.emit_state_update(
            operation="fix",
            cost=1.0,
            paths={"prompt": "p", "code": "c", "example": "e", "tests": "t"},
        )
        state = read_state(state_file)
        assert state["budget"] == 3.5

    def test_emit_state_update_overwrites_previous(self, emitter, state_file):
        """Test that each update overwrites the previous state."""
        emitter.emit_state_update(
            operation="generate",
            cost=0.1,
            paths={"prompt": "p", "code": "c", "example": "e", "tests": "t"},
        )
        emitter.emit_state_update(
            operation="test",
            cost=0.5,
            paths={"prompt": "p", "code": "c", "example": "e", "tests": "t"},
        )
        state = read_state(state_file)
        assert state["operation"] == "test"
        assert state["cost"] == 0.5


class TestEmitSyncComplete:
    """Tests for emit_sync_complete method."""

    def test_emit_sync_complete_success(self, emitter, state_file):
        """Test sync_complete with success=True."""
        emitter._last_operation = "test"
        emitter.emit_sync_complete(cost=2.5, success=True)
        state = read_state(state_file)
        assert state["status"] == "completed"
        assert state["cost"] == 2.5
        assert state["operation"] == "test"

    def test_emit_sync_complete_failure(self, emitter, state_file):
        """Test sync_complete with success=False."""
        emitter._last_operation = "fix"
        emitter.emit_sync_complete(cost=1.0, success=False)
        state = read_state(state_file)
        assert state["status"] == "failed"

    def test_emit_sync_complete_no_last_operation(self, emitter, state_file):
        """Test sync_complete when no operation was tracked."""
        emitter.emit_sync_complete(cost=0.0, success=True)
        state = read_state(state_file)
        assert state["operation"] == "done"

    def test_emit_sync_complete_includes_elapsed(self, emitter, state_file):
        """Test sync_complete includes elapsed time."""
        emitter._start_time = time.time() - 60.0  # 60 seconds ago
        emitter.emit_sync_complete(cost=3.0, success=True)
        state = read_state(state_file)
        assert state["elapsedSeconds"] >= 60.0

    def test_emit_sync_complete_empty_paths(self, emitter, state_file):
        """Test sync_complete writes empty paths."""
        emitter.emit_sync_complete(cost=1.0, success=True)
        state = read_state(state_file)
        assert state["paths"] == {}
        assert state["colors"] == {}


class TestAtomicWrite:
    """Tests for atomic file writing behavior."""

    def test_write_is_atomic(self, emitter, state_file):
        """Test that writes use atomic rename (no partial reads)."""
        # Write state
        emitter.emit_state_update(
            operation="generate",
            cost=0.1,
            paths={"prompt": "p", "code": "c", "example": "e", "tests": "t"},
        )
        # Verify no .tmp file left behind
        assert not os.path.exists(state_file + '.tmp')
        # Verify state file is valid JSON
        state = read_state(state_file)
        assert state["operation"] == "generate"

    def test_write_uses_compact_json(self, emitter, state_file):
        """Test that JSON uses compact separators (no extra spaces)."""
        emitter.emit_state_update(
            operation="generate",
            cost=0.1,
            paths={"prompt": "p", "code": "c", "example": "e", "tests": "t"},
        )
        with open(state_file, 'r') as f:
            content = f.read()
        # Compact JSON should not have ": " (space after colon)
        assert ": " not in content

    def test_write_handles_oserror_gracefully(self, state_file):
        """Test that OSError during write is silently handled."""
        with patch.dict(os.environ, {"PDD_SYNC_STATE_FILE": "/nonexistent/path/state.json"}):
            emitter = SyncStateEmitter(basename="test", budget=1.0)
        # Should not raise
        emitter.emit_state_update(
            operation="generate",
            cost=0.1,
            paths={"prompt": "p", "code": "c", "example": "e", "tests": "t"},
        )


class TestCleanup:
    """Tests for cleanup method."""

    def test_cleanup_removes_file(self, emitter, state_file):
        """Test that cleanup removes the state file."""
        emitter.emit_sync_start(paths={"prompt": "p", "code": "c", "example": "e", "tests": "t"})
        assert os.path.exists(state_file)
        emitter.cleanup()
        assert not os.path.exists(state_file)

    def test_cleanup_handles_missing_file(self, emitter, state_file):
        """Test that cleanup handles already-removed file gracefully."""
        # File doesn't exist yet - should not raise
        emitter.cleanup()


class TestFullWorkflow:
    """Integration tests for full sync workflow."""

    def test_full_sync_lifecycle(self, emitter, state_file):
        """Test complete lifecycle: start → updates → complete → cleanup."""
        paths = {"prompt": "p", "code": "c", "example": "e", "tests": "t"}

        # Start
        emitter.emit_sync_start(paths=paths)
        state = read_state(state_file)
        assert state["status"] == "running"
        assert state["operation"] == "initializing"

        # Generate
        emitter.emit_state_update(
            operation="generate", cost=0.3, paths=paths,
            colors={"prompt": "purple", "code": "cyan"},
        )
        state = read_state(state_file)
        assert state["operation"] == "generate"
        assert state["cost"] == 0.3

        # Test
        emitter.emit_state_update(
            operation="test", cost=0.7, paths=paths,
            colors={"prompt": "green", "code": "green", "tests": "magenta"},
        )
        state = read_state(state_file)
        assert state["operation"] == "test"
        assert state["cost"] == 0.7

        # Complete
        emitter.emit_sync_complete(cost=0.7, success=True)
        state = read_state(state_file)
        assert state["status"] == "completed"
        assert state["operation"] == "test"

        # Cleanup
        emitter.cleanup()
        assert not os.path.exists(state_file)

    def test_server_can_read_during_sync(self, emitter, state_file):
        """Test that the state file can be read while emitter is writing updates."""
        paths = {"prompt": "p", "code": "c", "example": "e", "tests": "t"}

        emitter.emit_sync_start(paths=paths)

        # Simulate server reading the file (like the job status endpoint does)
        for op, cost in [("generate", 0.1), ("test", 0.3), ("fix", 0.5)]:
            emitter.emit_state_update(operation=op, cost=cost, paths=paths)
            # Server reads the file
            state = read_state(state_file)
            assert state["operation"] == op
            assert state["cost"] == cost
            assert state["status"] == "running"
