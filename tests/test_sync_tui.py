"""
Tests for Terminal UI resize handling in pdd sync (Issue #236).

This test file verifies that the SyncApp class properly handles terminal
resize events during `pdd sync` execution. The bug manifests as severe
UI corruption (overlapping text, repeated values, unreadable output) when
the terminal window is resized while sync is running.

Root cause:
- The SyncApp class is missing an explicit `on_resize` event handler
- Without this handler, the RichLog widget and animation content are not
  re-rendered when the terminal dimensions change
- The custom animation loop runs every 50ms, but this is insufficient for
  immediate resize response
- Textual applications require explicit `on_resize` handlers to properly
  refresh custom content during resize events

This test is expected to FAIL until the bug is fixed by implementing
an `on_resize` method that:
1. Updates internal `_log_width` to reflect new terminal dimensions
2. Updates `os.environ["COLUMNS"]` for Rich Console width
3. Calls `self.log_widget.refresh()` to re-render log content
4. Triggers `self.update_animation()` for immediate animation redraw
"""

import pytest
import threading
import os
import asyncio
from unittest.mock import MagicMock, patch
from textual.widgets import RichLog, Static
from textual.events import Resize
from textual.geometry import Size


@pytest.mark.asyncio
async def test_sync_app_on_resize():
    """
    Verifies that the SyncApp class properly handles terminal resize events.

    This test simulates a terminal resize and verifies that:
    1. The `on_resize` method exists and can be called
    2. Internal `_log_width` is updated to new terminal width (accounting for UI offset)
    3. `os.environ["COLUMNS"]` is updated to match new log width
    4. `log_widget.refresh()` is called to force log re-rendering
    5. `update_animation()` is called for immediate animation redraw

    Without the fix, this test will fail because:
    - The `on_resize` method does not exist (AttributeError)
    - The UI state is not updated on resize, causing corruption

    Related to Issue #236: Terminal UI break when terminal is resized during pdd sync
    """
    # Import with textual.work mocked to avoid decorator issues in tests
    with patch("textual.work", lambda **kwargs: (lambda func: func)):
        from pdd.sync_tui import SyncApp

    # Mock a simple worker function
    def mock_worker():
        return {"success": True}

    # Setup shared refs and stop_event as required by SyncApp
    refs = [[""]] * 10  # 10 empty refs for the various state references
    stop_event = threading.Event()

    app = SyncApp(
        "test", 1.0, mock_worker,
        *refs, stop_event=stop_event
    )

    # Mock Textual UI components to avoid full rendering and focus on resize logic
    app.log_widget = MagicMock(spec=RichLog)
    app.animation_view = MagicMock(spec=Static)
    app.query_one = MagicMock(return_value=app.animation_view)

    # Set initial _log_width and os.environ["COLUMNS"]
    initial_width = 80
    app._log_width = initial_width
    os.environ["COLUMNS"] = str(initial_width)

    # Simulate mounting the app (necessary for on_resize to be called on a mounted widget)
    # We need to simulate enough of the app lifecycle for on_resize to be relevant
    with patch.object(app, 'mount') as mock_mount, \
         patch.object(app, 'call_after_refresh') as mock_call_after_refresh:
        # Manually call on_mount setup steps that on_resize might depend on
        with patch.object(app, 'run_worker_task'), patch.object(app, 'exit'):
            # Manually set the event loop to prevent "App is not running" RuntimeError
            app._loop = asyncio.get_running_loop()
            app.on_mount()

            # Simulate a resize event
            new_width = 100
            new_height = 30

            # Create a mock resize event
            resize_event = Resize(app, Size(new_width, new_height))

            # CRITICAL TEST: This will fail because SyncApp has no on_resize method
            # Expected AttributeError: 'SyncApp' object has no attribute 'on_resize'
            app.on_resize(resize_event)

            # After the fix is implemented, these assertions should verify correct behavior:

            # 1. Verify _log_width is updated (new_width - 6 for UI offset)
            expected_log_width = max(20, new_width - 6)
            assert app._log_width == expected_log_width, \
                f"Expected _log_width to be {expected_log_width}, but got {app._log_width}"

            # 2. Verify os.environ["COLUMNS"] is updated to match new log width
            assert os.environ["COLUMNS"] == str(expected_log_width), \
                f"Expected COLUMNS to be {expected_log_width}, but got {os.environ['COLUMNS']}"

            # 3. Verify log_widget.refresh() is called to redraw the log
            app.log_widget.refresh.assert_called_once()

            # 4. Verify animation_view.update() is called (via update_animation)
            # Note: update_animation calls animation_view.update(), so we verify it was called
            app.animation_view.update.assert_called()

    # Clean up os.environ["COLUMNS"] to avoid side effects on other tests
    os.environ["COLUMNS"] = "80"  # Reset to a default value


@pytest.mark.asyncio
async def test_sync_app_on_resize_multiple_consecutive():
    """
    Verifies that multiple consecutive resize events are handled correctly.

    This tests that the on_resize handler can be called multiple times in
    succession (simulating rapid terminal resizing) without issues.
    """
    with patch("textual.work", lambda **kwargs: (lambda func: func)):
        from pdd.sync_tui import SyncApp

    def mock_worker():
        return {"success": True}

    refs = [[""]] * 10
    stop_event = threading.Event()

    app = SyncApp("test", 1.0, mock_worker, *refs, stop_event=stop_event)

    app.log_widget = MagicMock(spec=RichLog)
    app.animation_view = MagicMock(spec=Static)
    app.query_one = MagicMock(return_value=app.animation_view)

    app._log_width = 80
    os.environ["COLUMNS"] = "80"

    with patch.object(app, 'mount'), \
         patch.object(app, 'call_after_refresh'), \
         patch.object(app, 'run_worker_task'), \
         patch.object(app, 'exit'):
        app._loop = asyncio.get_running_loop()
        app.on_mount()

        # Simulate multiple consecutive resizes
        resize_widths = [100, 120, 80, 60, 140]

        for width in resize_widths:
            resize_event = Resize(app, Size(width, 30))
            app.on_resize(resize_event)

            expected_log_width = max(20, width - 6)
            assert app._log_width == expected_log_width, \
                f"After resize to {width}, expected _log_width={expected_log_width}, got {app._log_width}"
            assert os.environ["COLUMNS"] == str(expected_log_width)

        # Verify refresh was called for each resize
        assert app.log_widget.refresh.call_count == len(resize_widths)

    os.environ["COLUMNS"] = "80"


@pytest.mark.asyncio
async def test_sync_app_on_resize_minimum_dimensions():
    """
    Verifies that resize to minimal terminal dimensions is handled gracefully.

    This tests edge case handling when the terminal is resized to very small
    dimensions, ensuring the minimum width logic (max(20, width - 6)) works.
    """
    with patch("textual.work", lambda **kwargs: (lambda func: func)):
        from pdd.sync_tui import SyncApp

    def mock_worker():
        return {"success": True}

    refs = [[""]] * 10
    stop_event = threading.Event()

    app = SyncApp("test", 1.0, mock_worker, *refs, stop_event=stop_event)

    app.log_widget = MagicMock(spec=RichLog)
    app.animation_view = MagicMock(spec=Static)
    app.query_one = MagicMock(return_value=app.animation_view)

    app._log_width = 80
    os.environ["COLUMNS"] = "80"

    with patch.object(app, 'mount'), \
         patch.object(app, 'call_after_refresh'), \
         patch.object(app, 'run_worker_task'), \
         patch.object(app, 'exit'):
        app._loop = asyncio.get_running_loop()
        app.on_mount()

        # Test very small terminal width (should use minimum of 20)
        resize_event = Resize(app, Size(10, 20))
        app.on_resize(resize_event)

        # Width of 10 - 6 = 4, but minimum is 20
        assert app._log_width == 20, \
            f"Expected minimum _log_width of 20, got {app._log_width}"
        assert os.environ["COLUMNS"] == "20"

        app.log_widget.refresh.assert_called()

    os.environ["COLUMNS"] = "80"
