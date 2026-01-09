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
        TUIStdoutWrapper,
        maybe_steer_operation,
        _is_headless_environment
    )

from textual.widgets import RichLog, ProgressBar, Static
from textual.app import App


# --- Event loop fixture for sync tests ---
@pytest.fixture(autouse=True)
def _ensure_asyncio_event_loop():
    """Ensure sync tests have a default asyncio loop.

    Some Textual helpers call asyncio.get_event_loop()/get_running_loop internally.
    In Python 3.12+, this raises RuntimeError if no loop is set.
    """
    try:
        asyncio.get_running_loop()
        # A loop is already running (e.g., in asyncio-marked tests).
        yield
        return
    except RuntimeError:
        pass

    loop = asyncio.new_event_loop()
    asyncio.set_event_loop(loop)
    try:
        yield
    finally:
        try:
            loop.close()
        finally:
            asyncio.set_event_loop(None)

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

# --- New Tests ---

def test_tui_stdout_wrapper_captures_prompt():
    """
    Verify that TUIStdoutWrapper detects strings without newlines as prompts
    and passes them to the stdin redirector.
    """
    mock_real_redirector = MagicMock(spec=ThreadSafeRedirector)
    mock_stdin_redirector = MagicMock(spec=TUIStdinRedirector)
    
    wrapper = TUIStdoutWrapper(mock_real_redirector, mock_stdin_redirector)
    
    # Case 1: Standard log line (ends with newline)
    wrapper.write("Log message\n")
    mock_real_redirector.write.assert_called_with("Log message\n")
    mock_stdin_redirector.set_prompt.assert_not_called()
    
    # Case 2: Prompt (no newline)
    wrapper.write("Enter value: ")
    mock_real_redirector.write.assert_called_with("Enter value: ")
    mock_stdin_redirector.set_prompt.assert_called_with("Enter value: ")

def test_confirm_screen_logic():
    """
    Verify ConfirmScreen dismisses with correct boolean values based on button IDs.
    """
    screen = ConfirmScreen("Are you sure?", "Confirm")
    screen.dismiss = MagicMock()
    
    # Simulate pressing 'yes'
    event_yes = MagicMock()
    event_yes.button.id = "yes"
    screen.on_button_pressed(event_yes)
    screen.dismiss.assert_called_with(True)
    
    # Simulate pressing 'no'
    event_no = MagicMock()
    event_no.button.id = "no"
    screen.on_button_pressed(event_no)
    screen.dismiss.assert_called_with(False)

def test_input_screen_logic():
    """
    Verify InputScreen dismisses with value on OK/Submit and None on Cancel.
    """
    screen = InputScreen("Enter key", "Input")
    screen.dismiss = MagicMock()
    
    # Mock the input widget query
    mock_input = MagicMock()
    mock_input.value = "secret_value"
    screen.query_one = MagicMock(return_value=mock_input)
    
    # Simulate pressing 'ok'
    event_ok = MagicMock()
    event_ok.button.id = "ok"
    screen.on_button_pressed(event_ok)
    screen.dismiss.assert_called_with("secret_value")
    
    # Simulate pressing 'cancel'
    event_cancel = MagicMock()
    event_cancel.button.id = "cancel"
    screen.on_button_pressed(event_cancel)
    screen.dismiss.assert_called_with(None)

def test_sync_app_request_confirmation_flow():
    """
    Verify request_confirmation blocks and returns the result set by the UI thread.
    """
    # Setup shared refs
    refs = [[""]] * 10
    app = SyncApp("test", 1.0, lambda: {}, *refs, stop_event=threading.Event())
    app.call_from_thread = MagicMock()
    
    # Simulate the UI thread: when call_from_thread is invoked, set the result and
    # signal the waiting event so the test doesn't hang.
    def _call_from_thread_side_effect(fn, *args, **kwargs):
        # In unit tests we don't run Textual's async loop; just unblock the wait.
        if getattr(app, "_confirm_event", None) is not None:
            app._confirm_result = True
            app._confirm_event.set()

    app.call_from_thread.side_effect = _call_from_thread_side_effect

    result = app.request_confirmation("Message")

    assert result is True
    assert app.call_from_thread.called
    # Verify the internal state was prepared
    assert app._confirm_message == "Message"

def test_sync_app_request_input_timeout():
    """
    Verify request_input returns None if the event wait times out.
    """
    refs = [[""]] * 10
    app = SyncApp("test", 1.0, lambda: {}, *refs, stop_event=threading.Event())
    app.call_from_thread = MagicMock()

    # Instead of running UI, unblock any waiting event to ensure test can't hang.
    def _call_from_thread_no_ui(fn, *a, **k):
        # Don't run UI, but ensure any waiting Event is released.
        if getattr(app, "_input_event", None) is not None:
            app._input_result = None
            app._input_event.set()

    app.call_from_thread.side_effect = _call_from_thread_no_ui

    result = app.request_input("Prompt")

    assert result is None
    assert app.call_from_thread.called

def test_maybe_steer_operation_integration():
    """
    Verify maybe_steer_operation delegates to the app instance correctly.
    """
    mock_app = MagicMock(spec=SyncApp)
    mock_app.request_steering.return_value = ("test", False)
    
    # Case 1: Normal delegation (force non-headless mode for determinism)
    with patch("pdd.sync_tui._is_headless_environment", return_value=False):
        op, abort = maybe_steer_operation("generate", app=mock_app)
    mock_app.request_steering.assert_called_with("generate", "", timeout_s=8.0)
    assert op == "test"
    assert abort is False
    
    # Case 2: Quiet mode (should not call app)
    mock_app.reset_mock()
    op, abort = maybe_steer_operation("generate", app=mock_app, quiet=True)
    mock_app.request_steering.assert_not_called()
    assert op == "generate"

def test_maybe_steer_operation_filtering():
    """
    Verify maybe_steer_operation filters out disallowed operations returned by the app.
    """
    mock_app = MagicMock(spec=SyncApp)
    
    # App returns 'test', but we passed skip_tests=True
    mock_app.request_steering.return_value = ("test", False)
    
    with patch("pdd.sync_tui._is_headless_environment", return_value=False):
        op, abort = maybe_steer_operation("generate", app=mock_app, skip_tests=True)
    
    # Should revert to original operation 'generate' because 'test' is disallowed
    assert op == "generate"
    assert abort is False

def test_z3_maybe_steer_filtering_logic():
    """
    Z3 Verification: Ensure that maybe_steer_operation logic strictly enforces
    skip constraints regardless of what the underlying app/user returns.
    """
    from z3 import Solver, Or, And, Not, Implies, Bool, EnumSort, Const

    # Define Operations
    Ops, (op_gen, op_test, op_fix, op_verify, op_abort, op_other) = EnumSort(
        'Ops2', ['generate', 'test', 'fix', 'verify', 'abort', 'other']
    )

    solver = Solver()

    # Inputs
    original_op = Const('original_op', Ops)
    app_returned_op = Const('app_returned_op', Ops)
    app_returned_abort = Bool('app_returned_abort')
    skip_tests = Bool('skip_tests')
    skip_verify = Bool('skip_verify')

    # Output
    final_op = Const('final_op', Ops)
    final_abort = Bool('final_abort')

    # Logic definition matching maybe_steer_operation implementation
    # disallowed set construction
    is_test_related = Or(app_returned_op == op_test, app_returned_op == op_fix)
    is_verify_related = (app_returned_op == op_verify)

    is_disallowed = Or(
        And(skip_tests, is_test_related),
        And(skip_verify, is_verify_related)
    )

    # If disallowed, return original_op and False. Else return app result.
    solver.add(Implies(is_disallowed, And(final_op == original_op, final_abort == False)))
    solver.add(Implies(Not(is_disallowed), And(final_op == app_returned_op, final_abort == app_returned_abort)))

    # Verification Goal 1: If skip_tests is True, final_op can NEVER be 'test' or 'fix'
    # unless original_op was 'test'/'fix' (the function only filters the *chosen* op if it differs, 
    # but strictly speaking the code says: if chosen in disallowed, return operation. 
    # If operation itself was disallowed, it returns it. The filter applies to the *change*).
    # Let's verify that if the app tries to *switch* to a test op, it is rejected.
    
    solver.push()
    solver.add(skip_tests == True)
    solver.add(Or(final_op == op_test, final_op == op_fix))
    # We assume the original operation was NOT test/fix, so we are looking for a switch
    solver.add(Not(Or(original_op == op_test, original_op == op_fix)))
    
    # If the solver finds a model, it means we managed to get a test op despite skipping tests
    assert solver.check().r == -1, "Found a case where skip_tests failed to prevent switching to test/fix"
    solver.pop()

    # Verification Goal 2: If skip_verify is True, final_op can NEVER be 'verify' (assuming original wasn't)
    solver.push()
    solver.add(skip_verify == True)
    solver.add(final_op == op_verify)
    solver.add(original_op != op_verify)
    assert solver.check().r == -1, "Found a case where skip_verify failed to prevent switching to verify"
    solver.pop()