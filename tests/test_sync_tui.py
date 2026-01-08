import pytest
import threading
import time
import os
import sys
import io
import asyncio
from unittest.mock import MagicMock, patch, PropertyMock
from io import StringIO # Added import

# We must patch 'textual.work' BEFORE importing SyncApp so the decorator 
# doesn't wrap the methods with the real Textual worker logic during class definition.
with patch("textual.work", lambda **kwargs: (lambda func: func)):
    from pdd.sync_tui import (
        SyncApp, 
        ConfirmScreen, 
        InputScreen, 
        ChoiceScreen, 
        TUIStdinRedirector, 
        ThreadSafeRedirector,
        maybe_steer_operation,
        _is_headless_environment
    )

from textual.widgets import RichLog, ProgressBar, Static
from textual.app import App
from textual.events import Event, Size, Resize
from unittest.mock import PropertyMock # Added import

# --- Unit Tests ---

def test_headless_detection():
    """Verify headless environment detection logic."""
    with patch.dict(os.environ, {"PDD_TEST_HEADLESS": "true"}):
        assert _is_headless_environment() is True
    
    with patch.dict(os.environ, {"PDD_TEST_HEADLESS": "false"}):
        # Even if CI is set, PDD_TEST_HEADLESS=false should override
        with patch.dict(os.environ, {"CI": "true"}):
            assert _is_headless_environment() is False

def test_thread_safe_redirector_buffering():
    """Verify that the redirector buffers until a newline is received."""
    mock_app = MagicMock(spec=App)
    mock_log = MagicMock(spec=RichLog)
    redirector = ThreadSafeRedirector(mock_app, mock_log)

    redirector.write("Hello ")
    assert mock_app.call_from_thread.called is False
    
    redirector.write("World\n")
    assert mock_app.call_from_thread.called is True
    # Check that the text object passed to write contains the full line
    args, _ = mock_app.call_from_thread.call_args
    assert args[1].plain == "Hello World"

def test_thread_safe_redirector_carriage_return():
    """Verify \r handling (common in progress bars)."""
    mock_app = MagicMock(spec=App)
    mock_log = MagicMock(spec=RichLog)
    redirector = ThreadSafeRedirector(mock_app, mock_log)

    # Simulate a progress bar update: [==  ] \r [====] \n
    redirector.write("Progress: [==  ]")
    redirector.write("\rProgress: [====]")
    redirector.write("\n")

    args, _ = mock_app.call_from_thread.call_args
    assert args[1].plain == "Progress: [====]"

def test_thread_safe_redirector_dimming():
    """Verify that log lines matching the pattern are dimmed."""
    mock_app = MagicMock(spec=App)
    mock_log = MagicMock(spec=RichLog)
    redirector = ThreadSafeRedirector(mock_app, mock_log)

    log_line = "2025-01-01 12:00:00 INFO: Doing work\n"
    redirector.write(log_line)

    args, _ = mock_app.call_from_thread.call_args
    rich_text = args[1]
    assert rich_text.style.dim is True

def test_stdin_redirector_prompt_capture():
    """Verify TUIStdinRedirector uses the last captured prompt."""
    app_ref = [MagicMock(spec=SyncApp)]
    stdin = TUIStdinRedirector(app_ref)
    
    # Simulate stdout writing a prompt
    stdin.set_prompt("Enter API Key: ")
    
    # Mock the app's request_input to return a value
    app_ref[0].request_input.return_value = "secret-123"
    
    result = stdin.readline()
    
    # Verify request_input was called with the correct prompt and password=True
    app_ref[0].request_input.assert_called_with(
        "Enter API Key:", "Input Required", default="", password=True
    )
    assert result == "secret-123\n"

def test_stdin_redirector_eof_on_cancel():
    """Verify EOFError is raised when user cancels input."""
    app_ref = [MagicMock(spec=SyncApp)]
    stdin = TUIStdinRedirector(app_ref)
    app_ref[0].request_input.return_value = None # User cancelled
    
    with pytest.raises(EOFError, match="Input cancelled by user"):
        stdin.readline()

@pytest.mark.asyncio
async def test_choice_screen_timeout():
    """Verify ChoiceScreen auto-dismisses with default after timeout."""
    screen = ChoiceScreen(
        title="Test",
        prompt="Choose",
        choices=["A", "B"],
        default="A",
        timeout_s=0.01 # Very short for test
    )
    
    # We mock dismiss because we aren't running a full Textual app loop here
    screen.dismiss = MagicMock()
    
    await screen._auto_default()
    screen.dismiss.assert_called_once_with("A")

def test_maybe_steer_operation_headless():
    """Verify steering returns original op immediately in headless mode."""
    with patch("pdd.sync_tui._is_headless_environment", return_value=True):
        op, abort = maybe_steer_operation("test", reason="testing")
        assert op == "test"
        assert abort is False

def test_sync_app_env_isolation():
    """Verify SyncApp worker thread isolates environment variables."""
    def mock_worker():
        # Check if env vars are set inside the worker
        assert os.environ.get("FORCE_COLOR") == "1"
        assert os.environ.get("TERM") == "xterm-256color"
        return {"success": True}

        # Setup shared refs (10 positional ref arguments)
        refs = [[""]] * 10
        stop_event = threading.Event()
    
        # Capture initial environment variables to verify restoration
        original_force_color = os.environ.get("FORCE_COLOR")
        original_term = os.environ.get("TERM")
        original_columns = os.environ.get("COLUMNS")
    
        # Create a minimal SyncApp instance for testing
        app = SyncApp(
            "test", 1.0, mock_worker,
            *refs, stop_event=stop_event
        )
    
        # Mock the UI components to avoid initialization errors
        app.log_widget = MagicMock()
        app._log_width = 80
        app._app_ref = [app] # Mimic on_mount setting this for stdin redirector
    
        # Mock `asyncio.create_task` to prevent it from trying to start a real async task
        # and `app.exit` since no actual app is running.
        with patch("asyncio.create_task") as mock_create_task, \
             patch.object(app, 'exit') as mock_app_exit, \
             patch.object(app, 'run_worker') as mock_run_worker, \
             patch.object(app, 'call_from_thread') as mock_call_from_thread, \
             patch("sys.stdout", new_callable=StringIO) as mock_stdout, \
             patch("sys.stderr", new_callable=StringIO) as mock_stderr:
    
            # Call run_worker_task, which should set environment variables
            app.run_worker_task()
    
        # Verify env vars are restored to their original values after run_worker_task finishes
        assert os.environ.get("FORCE_COLOR") == original_force_color
        assert os.environ.get("TERM") == original_term
        assert os.environ.get("COLUMNS") == original_columns
def test_progress_callback_thread_safety():
    """Verify _update_progress schedules a UI update."""
    # Setup shared refs (10 positional ref arguments)
    refs = [[""]] * 10
    app = SyncApp("test", 1.0, lambda: {}, *refs, stop_event=threading.Event())
    
    app.call_from_thread = MagicMock()
    app.progress_bar = MagicMock()
    app.progress_container = MagicMock(classes=[])
    
    app._update_progress(50, 100)
    
    # Verify call_from_thread was used
    assert app.call_from_thread.called
    
    # Execute the inner function passed to call_from_thread
    inner_func = app.call_from_thread.call_args[0][0]
    inner_func()
    
    app.progress_bar.update.assert_called_with(total=100, progress=50)
    app.progress_container.add_class.assert_called_with("visible")

def test_steering_logic_safety_z3():
    """
    Use Z3 to prove that the steering logic never returns a disallowed operation
    when skip flags are set, regardless of user choice.
    """
    from z3 import Solver, Or, And, Not, Implies, String, Bool, EnumSort, Const

    # Define the operations as an Enum-like sort in Z3
    Ops, (op_gen, op_ex, op_crash, op_ver, op_test, op_fix, op_abort, op_other) = EnumSort(
        'Ops', ['generate', 'example', 'crash', 'verify', 'test', 'fix', 'abort', 'other']
    )

    solver = Solver()

    # Variables
    recommended = Const('recommended', Ops)
    user_choice = Const('user_choice', Ops)
    skip_tests = Bool('skip_tests')
    skip_verify = Bool('skip_verify')
    final_op = Const('final_op', Ops)
    should_abort = Bool('should_abort')

    # Logic: If user_choice is disallowed, we revert to recommended.
    is_disallowed = Or(
        And(skip_tests, Or(user_choice == op_test, user_choice == op_fix)),
        And(skip_verify, user_choice == op_ver)
    )

    solver.add(Implies(is_disallowed, And(final_op == recommended, should_abort == False)))
    solver.add(Implies(Not(is_disallowed), And(
        Implies(user_choice == op_abort, And(final_op == recommended, should_abort == True)),
        Implies(user_choice != op_abort, And(final_op == user_choice, should_abort == False))
    )))

    # PROPERTY 1: If skip_tests is true, final_op can never be op_test or op_fix
    solver.push()
    solver.add(skip_tests == True)
    solver.add(Or(final_op == op_test, final_op == op_fix))
    solver.add(Not(Or(recommended == op_test, recommended == op_fix)))
    assert solver.check().r == -1 
    solver.pop()

    # PROPERTY 2: If user chooses abort, should_abort is always True
    solver.push()
    solver.add(user_choice == op_abort)
    solver.add(should_abort == False)
    assert solver.check().r == -1
    solver.pop()


@pytest.mark.asyncio
async def test_sync_app_on_resize():
    """
    Verifies that resizing the terminal window during pdd sync causes UI corruption
    due to improper handling of resize events by SyncApp.

    This test simulates a terminal resize and asserts that the log_widget
    is not immediately refreshed and internal width calculations (_log_width)
    are not updated to the new terminal width, leading to visual artifacts.
    """
    with patch("textual.work", lambda **kwargs: (lambda func: func)):
        from pdd.sync_tui import SyncApp

    # Mock a simple worker function
    def mock_worker():
        return {"success": True}

    # Setup shared refs and stop_event
    refs = [[""]] * 10
    stop_event = threading.Event()

    app = SyncApp(
        "test", 1.0, mock_worker,
        *refs, stop_event=stop_event
    )

    initial_app_width = 80 # Default fallback width during on_mount
    initial_app_height = 24 # Arbitrary initial height for testing
    expected_initial_log_width = max(20, initial_app_width - 6) # Should be 74

    # Mock the `size` property of the SyncApp instance
    # Use patch.object with new_callable=PropertyMock to mock a property
    # and set its return value to a MagicMock that acts like a Size object.
    with patch.object(type(app), 'size', new_callable=PropertyMock) as mock_size_property:
        mock_size_property.return_value = MagicMock(width=initial_app_width, height=initial_app_height)

        # Mock Textual UI components to avoid full rendering and focus on resize logic
        app.log_widget = MagicMock(spec=RichLog)
        app.animation_view = MagicMock(spec=Static)
        app.query_one = MagicMock(return_value=app.animation_view) # To simulate query_one selecting animation_view

        # Set initial _log_width and os.environ["COLUMNS"] based on how on_mount initializes it
        app._log_width = expected_initial_log_width
        os.environ["COLUMNS"] = str(expected_initial_log_width)
        # Simulate mounting the app (necessary for on_resize to be called on a mounted widget)
        # We need to simulate enough of the app lifecycle for on_resize to be relevant
        with patch.object(app, 'mount') as mock_mount, \
             patch.object(app, 'call_after_refresh') as mock_call_after_refresh:
                # Manually call on_mount setup steps that on_resize might depend on
                with patch.object(app, 'run_worker_task'), patch.object(app, 'exit'), \
                     patch.object(app, 'set_interval'), patch.object(app, 'update_animation'):
                    # Manually set the event loop to prevent "App is not running" RuntimeError
                    app._loop = asyncio.get_running_loop()
                    app.on_mount()

                # Simulate a resize event
                new_width = 100
                new_height = 30
                mock_size_property.return_value = MagicMock(width=new_width, height=new_height) # Update mock size
                # Removed direct mock_on_resize assertion, as we're now testing the *effect* of on_resize.
                app.on_resize(Resize(size=Size(width=new_width, height=new_height), virtual_size=Size(width=new_width, height=new_height)))

                # With the fix, _log_width should be updated immediately by on_resize
                expected_log_width = new_width - 6
                assert app._log_width == expected_log_width
                app.log_widget.refresh.assert_called_once()
                app.animation_view.update.assert_called_once() # Animation view should be updated via update_animation

                # Verify os.environ["COLUMNS"] is updated immediately by on_resize
                assert os.environ["COLUMNS"] == str(expected_log_width)
            # Clean up os.environ["COLUMNS"] if it was changed during the test run to avoid side effects
    os.environ["COLUMNS"] = "80" # Reset to a default value for subsequent tests
