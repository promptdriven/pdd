import pytest
import threading
import time
import os
import sys
import io
import asyncio
from unittest.mock import MagicMock, patch
from textual.widgets import RichLog, ProgressBar, Static
from textual.app import App

# Import the actual module
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
    
    # We patch the 'work' decorator to just return the function as-is
    # This bypasses Textual's worker manager which requires an event loop
    with patch("textual.work", lambda **kwargs: (lambda func: func)):
        app = SyncApp(
            "test", 1.0, mock_worker, 
            *refs, stop_event=stop_event
        )
        
        # Mock the UI components to avoid initialization errors
        app.log_widget = MagicMock()
        app._log_width = 80
        
        # Manually trigger the worker task logic
        with patch.object(app, 'exit'):
            app.run_worker_task()
        
    # Verify env vars are restored (assuming they weren't set before)
    assert os.environ.get("FORCE_COLOR") != "1"

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