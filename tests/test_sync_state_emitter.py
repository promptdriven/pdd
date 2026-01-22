"""
Tests for pdd.sync_state_emitter module.

Tests the SyncStateEmitter class which outputs structured JSON state
to stdout with @@PDD_SYNC_STATE@@ markers for frontend parsing.
"""

import json
import time
from io import StringIO
from unittest.mock import patch

import pytest

from pdd.sync_state_emitter import SyncStateEmitter


MARKER = "@@PDD_SYNC_STATE@@"


class TestSyncStateEmitterInit:
    """Tests for SyncStateEmitter initialization."""

    def test_init_with_basename_and_budget(self):
        """Test initialization stores basename and budget."""
        emitter = SyncStateEmitter(basename="calculator", budget=5.0)
        assert emitter._basename == "calculator"
        assert emitter._budget == 5.0

    def test_init_with_none_budget(self):
        """Test initialization with no budget."""
        emitter = SyncStateEmitter(basename="my_module", budget=None)
        assert emitter._basename == "my_module"
        assert emitter._budget is None

    def test_init_sets_start_time(self):
        """Test that start time is set on initialization."""
        before = time.time()
        emitter = SyncStateEmitter(basename="test", budget=1.0)
        after = time.time()
        assert before <= emitter._start_time <= after

    def test_init_last_operation_is_none(self):
        """Test that last operation starts as None."""
        emitter = SyncStateEmitter(basename="test", budget=1.0)
        assert emitter._last_operation is None


class TestEmitSyncStart:
    """Tests for emit_sync_start method."""

    def test_emit_sync_start_outputs_marker(self):
        """Test that sync_start outputs the correct marker prefix."""
        emitter = SyncStateEmitter(basename="calculator", budget=5.0)
        with patch('builtins.print') as mock_print:
            emitter.emit_sync_start(paths={
                "prompt": "prompts/calculator.prompt",
                "code": "src/calculator.py",
                "example": "examples/calculator_example.py",
                "tests": "tests/test_calculator.py",
            })
            output = mock_print.call_args[0][0]
            assert output.startswith(MARKER)

    def test_emit_sync_start_json_payload(self):
        """Test that sync_start contains correct JSON data."""
        emitter = SyncStateEmitter(basename="calculator", budget=5.0)
        with patch('builtins.print') as mock_print:
            paths = {
                "prompt": "prompts/calculator.prompt",
                "code": "src/calculator.py",
                "example": "examples/calculator_example.py",
                "tests": "tests/test_calculator.py",
            }
            emitter.emit_sync_start(paths=paths)
            output = mock_print.call_args[0][0]
            payload = json.loads(output[len(MARKER):])
            assert payload["type"] == "sync_start"
            assert payload["basename"] == "calculator"
            assert payload["budget"] == 5.0
            assert payload["paths"] == paths
            assert payload["elapsedSeconds"] == 0

    def test_emit_sync_start_flushes(self):
        """Test that print is called with flush=True."""
        emitter = SyncStateEmitter(basename="test", budget=1.0)
        with patch('builtins.print') as mock_print:
            emitter.emit_sync_start(paths={"prompt": "", "code": "", "example": "", "tests": ""})
            assert mock_print.call_args[1].get("flush") is True


class TestEmitStateUpdate:
    """Tests for emit_state_update method."""

    def test_emit_state_update_type(self):
        """Test that state_update has correct type field."""
        emitter = SyncStateEmitter(basename="calc", budget=5.0)
        with patch('builtins.print') as mock_print:
            emitter.emit_state_update(
                operation="generate",
                cost=0.42,
                paths={"prompt": "p.prompt", "code": "c.py", "example": "e.py", "tests": "t.py"},
            )
            output = mock_print.call_args[0][0]
            payload = json.loads(output[len(MARKER):])
            assert payload["type"] == "state_update"
            assert payload["operation"] == "generate"
            assert payload["cost"] == 0.42
            assert payload["status"] == "running"

    def test_emit_state_update_with_colors(self):
        """Test that colors are included when provided."""
        emitter = SyncStateEmitter(basename="calc", budget=5.0)
        colors = {"prompt": "purple", "code": "cyan", "example": "green", "tests": "magenta"}
        with patch('builtins.print') as mock_print:
            emitter.emit_state_update(
                operation="test",
                cost=1.0,
                paths={"prompt": "p", "code": "c", "example": "e", "tests": "t"},
                colors=colors,
            )
            output = mock_print.call_args[0][0]
            payload = json.loads(output[len(MARKER):])
            assert payload["colors"] == colors

    def test_emit_state_update_without_colors(self):
        """Test that empty colors dict is used when not provided."""
        emitter = SyncStateEmitter(basename="calc", budget=5.0)
        with patch('builtins.print') as mock_print:
            emitter.emit_state_update(
                operation="fix",
                cost=0.5,
                paths={"prompt": "p", "code": "c", "example": "e", "tests": "t"},
            )
            output = mock_print.call_args[0][0]
            payload = json.loads(output[len(MARKER):])
            assert payload["colors"] == {}

    def test_emit_state_update_elapsed_time(self):
        """Test that elapsed time is computed from start."""
        emitter = SyncStateEmitter(basename="calc", budget=5.0)
        emitter._start_time = time.time() - 10.0  # Simulate 10 seconds elapsed
        with patch('builtins.print') as mock_print:
            emitter.emit_state_update(
                operation="generate",
                cost=0.0,
                paths={"prompt": "p", "code": "c", "example": "e", "tests": "t"},
            )
            output = mock_print.call_args[0][0]
            payload = json.loads(output[len(MARKER):])
            assert payload["elapsedSeconds"] >= 10.0

    def test_emit_state_update_updates_last_operation(self):
        """Test that last_operation is updated on each emit."""
        emitter = SyncStateEmitter(basename="calc", budget=5.0)
        assert emitter._last_operation is None
        with patch('builtins.print'):
            emitter.emit_state_update(
                operation="generate",
                cost=0.0,
                paths={"prompt": "p", "code": "c", "example": "e", "tests": "t"},
            )
        assert emitter._last_operation == "generate"

    def test_emit_state_update_cost_rounded(self):
        """Test that cost is rounded to 4 decimal places."""
        emitter = SyncStateEmitter(basename="calc", budget=5.0)
        with patch('builtins.print') as mock_print:
            emitter.emit_state_update(
                operation="test",
                cost=0.123456789,
                paths={"prompt": "p", "code": "c", "example": "e", "tests": "t"},
            )
            output = mock_print.call_args[0][0]
            payload = json.loads(output[len(MARKER):])
            assert payload["cost"] == 0.1235

    def test_emit_state_update_includes_budget(self):
        """Test that budget is included in the payload."""
        emitter = SyncStateEmitter(basename="calc", budget=3.5)
        with patch('builtins.print') as mock_print:
            emitter.emit_state_update(
                operation="fix",
                cost=1.0,
                paths={"prompt": "p", "code": "c", "example": "e", "tests": "t"},
            )
            output = mock_print.call_args[0][0]
            payload = json.loads(output[len(MARKER):])
            assert payload["budget"] == 3.5


class TestEmitSyncComplete:
    """Tests for emit_sync_complete method."""

    def test_emit_sync_complete_success(self):
        """Test sync_complete with success=True."""
        emitter = SyncStateEmitter(basename="calc", budget=5.0)
        emitter._last_operation = "test"
        with patch('builtins.print') as mock_print:
            emitter.emit_sync_complete(cost=2.5, success=True)
            output = mock_print.call_args[0][0]
            payload = json.loads(output[len(MARKER):])
            assert payload["type"] == "sync_complete"
            assert payload["status"] == "completed"
            assert payload["cost"] == 2.5
            assert payload["operation"] == "test"

    def test_emit_sync_complete_failure(self):
        """Test sync_complete with success=False."""
        emitter = SyncStateEmitter(basename="calc", budget=5.0)
        emitter._last_operation = "fix"
        with patch('builtins.print') as mock_print:
            emitter.emit_sync_complete(cost=1.0, success=False)
            output = mock_print.call_args[0][0]
            payload = json.loads(output[len(MARKER):])
            assert payload["status"] == "failed"

    def test_emit_sync_complete_no_last_operation(self):
        """Test sync_complete when no operation was tracked."""
        emitter = SyncStateEmitter(basename="calc", budget=5.0)
        with patch('builtins.print') as mock_print:
            emitter.emit_sync_complete(cost=0.0, success=True)
            output = mock_print.call_args[0][0]
            payload = json.loads(output[len(MARKER):])
            assert payload["operation"] == "done"

    def test_emit_sync_complete_includes_elapsed(self):
        """Test sync_complete includes elapsed time."""
        emitter = SyncStateEmitter(basename="calc", budget=5.0)
        emitter._start_time = time.time() - 60.0  # 60 seconds ago
        with patch('builtins.print') as mock_print:
            emitter.emit_sync_complete(cost=3.0, success=True)
            output = mock_print.call_args[0][0]
            payload = json.loads(output[len(MARKER):])
            assert payload["elapsedSeconds"] >= 60.0


class TestMarkerFormat:
    """Tests for the marker format and JSON output."""

    def test_marker_constant(self):
        """Test that the MARKER constant is correct."""
        assert SyncStateEmitter.MARKER == "@@PDD_SYNC_STATE@@"

    def test_output_is_single_line(self):
        """Test that each emit produces a single line."""
        emitter = SyncStateEmitter(basename="test", budget=5.0)
        with patch('builtins.print') as mock_print:
            emitter.emit_sync_start(paths={"prompt": "p", "code": "c", "example": "e", "tests": "t"})
            output = mock_print.call_args[0][0]
            assert "\n" not in output

    def test_json_is_compact(self):
        """Test that JSON uses compact separators (no spaces)."""
        emitter = SyncStateEmitter(basename="test", budget=5.0)
        with patch('builtins.print') as mock_print:
            emitter.emit_sync_start(paths={"prompt": "p", "code": "c", "example": "e", "tests": "t"})
            output = mock_print.call_args[0][0]
            json_part = output[len(MARKER):]
            # Compact JSON should not have ": " (space after colon)
            assert ": " not in json_part

    def test_parseable_from_stream(self):
        """Test that marker lines can be detected and parsed from a stream of text."""
        emitter = SyncStateEmitter(basename="calc", budget=5.0)
        lines = []
        with patch('builtins.print', side_effect=lambda *a, **kw: lines.append(a[0])):
            emitter.emit_sync_start(paths={"prompt": "p", "code": "c", "example": "e", "tests": "t"})
            emitter.emit_state_update(operation="generate", cost=0.1, paths={"prompt": "p", "code": "c", "example": "e", "tests": "t"})
            emitter.emit_sync_complete(cost=0.5, success=True)

        # Simulate mixed output stream
        mixed_output = [
            "Running sync in headless mode...",
            lines[0],
            "[2024-01-01] Operation: generate",
            lines[1],
            "Some other output",
            lines[2],
        ]

        parsed_states = []
        for line in mixed_output:
            if line.startswith(MARKER):
                parsed_states.append(json.loads(line[len(MARKER):]))

        assert len(parsed_states) == 3
        assert parsed_states[0]["type"] == "sync_start"
        assert parsed_states[1]["type"] == "state_update"
        assert parsed_states[2]["type"] == "sync_complete"
