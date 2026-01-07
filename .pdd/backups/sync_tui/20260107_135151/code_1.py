import sys
import os
import threading
import time
import asyncio
from typing import List, Optional, Callable, Any, Dict

from textual.app import App, ComposeResult
from textual.containers import Container, Vertical
from textual.widgets import Header, Footer, Log, Static, Label, Input, Button
from textual.screen import ModalScreen
from textual.worker import Worker
from textual import work
from textual.binding import Binding
from rich.console import Console
from rich.text import Text
from rich.panel import Panel
from rich.align import Align

# Import animation modules based on provided context
# Note: In a real deployment, ensure these paths are reachable
try:
    from pdd.sync_animation import sync_animation
    from pdd.logo_animation import start_logo_animation, stop_logo_animation
except ImportError:
    # Fallback mocks for development if pdd package isn't installed
    def sync_animation(*args, **kwargs): pass
    def start_logo_animation(): pass
    def stop_logo_animation(): pass

# --- Shared State Constants ---
DEFAULT_TIMEOUT = 10.0

# --- Helper: Headless Detection ---
def _is_headless_environment() -> bool:
    """Detects if running in a CI/CD or non-interactive environment."""
    if os.environ.get("CI") or os.environ.get("GITHUB_ACTIONS"):
        return True
    if not sys.stdin.isatty():
        return True
    return False

# --- Modal Screens ---

class ConfirmScreen(ModalScreen[bool]):
    """A modal screen for Yes/No confirmation."""
    
    CSS = """
    ConfirmScreen {
        align: center middle;
    }
    #dialog {
        grid-size: 2;
        grid-gutter: 1 2;
        grid-rows: 1fr 3;
        padding: 0 1;
        width: 60;
        height: 11;
        border: thick $background 80%;
        background: $surface;
    }
    #question {
        column-span: 2;
        height: 1fr;
        width: 1fr;
        content-align: center middle;
    }
    Button {
        width: 100%;
    }
    """

    def __init__(self, message: str):
        super().__init__()
        self.message = message

    def compose(self) -> ComposeResult:
        yield Container(
            Label(self.message, id="question"),
            Button("Yes", variant="success", id="yes"),
            Button("No", variant="error", id="no"),
            id="dialog",
        )

    def on_button_pressed(self, event: Button.Pressed) -> None:
        if event.button.id == "yes":
            self.dismiss(True)
        else:
            self.dismiss(False)


class InputScreen(ModalScreen[str]):
    """A modal screen for text input."""

    CSS = """
    InputScreen {
        align: center middle;
    }
    #dialog {
        padding: 0 1;
        width: 60;
        height: 11;
        border: thick $background 80%;
        background: $surface;
    }
    #prompt {
        height: 1fr;
        width: 1fr;
        content-align: center middle;
    }
    Input {
        width: 100%;
        margin: 1 0;
    }
    """

    def __init__(self, prompt: str, password: bool = False):
        super().__init__()
        self.prompt_text = prompt
        self.password = password

    def compose(self) -> ComposeResult:
        yield Container(
            Label(self.prompt_text, id="prompt"),
            Input(password=self.password, id="input"),
            id="dialog",
        )

    def on_input_submitted(self, event: Input.Submitted) -> None:
        self.dismiss(event.value)


class ChoiceScreen(ModalScreen[str]):
    """A modal screen for selecting from a list of options."""

    CSS = """
    ChoiceScreen {
        align: center middle;
    }
    #dialog {
        width: 60;
        height: auto;
        max-height: 80%;
        border: thick $background 80%;
        background: $surface;
        padding: 1 2;
    }
    #title {
        text-align: center;
        dock: top;
        margin-bottom: 1;
    }
    Button {
        width: 100%;
        margin-bottom: 1;
    }
    """

    BINDINGS = [
        Binding("1", "select_idx(0)", "Select 1"),
        Binding("2", "select_idx(1)", "Select 2"),
        Binding("3", "select_idx(2)", "Select 3"),
        Binding("4", "select_idx(3)", "Select 4"),
        Binding("5", "select_idx(4)", "Select 5"),
        Binding("6", "select_idx(5)", "Select 6"),
        Binding("7", "select_idx(6)", "Select 7"),
        Binding("8", "select_idx(7)", "Select 8"),
        Binding("9", "select_idx(8)", "Select 9"),
    ]

    def __init__(self, title: str, choices: List[str], default: Optional[str] = None, timeout: float = 0):
        super().__init__()
        self.title_text = title
        self.choices = choices
        self.default = default
        self.timeout_val = timeout
        self.timer = None

    def compose(self) -> ComposeResult:
        yield Container(
            Label(self.title_text, id="title"),
            *[Button(f"{i+1}. {c}", id=c) for i, c in enumerate(self.choices)],
            id="dialog",
        )

    def on_mount(self) -> None:
        if self.timeout_val > 0 and self.default:
            self.timer = self.set_timer(self.timeout_val, self.action_timeout_select)

    def action_timeout_select(self) -> None:
        self.dismiss(self.default)

    def action_select_idx(self, idx: int) -> None:
        if 0 <= idx < len(self.choices):
            self.dismiss(self.choices[idx])

    def on_button_pressed(self, event: Button.Pressed) -> None:
        self.dismiss(event.button.id)


# --- IO Redirectors ---

class TUIStdoutWrapper:
    """
    Redirects stdout/stderr to the Textual Log widget.
    Detects prompts (strings without newlines) to contextually aid input.
    """
    def __init__(self, app: "SyncApp", original_stream, is_stderr=False):
        self.app = app
        self.original_stream = original_stream
        self.is_stderr = is_stderr
        self.last_partial_line = ""

    def write(self, text: str):
        # Pass through to original stream if needed for debugging, 
        # but usually we want to capture it entirely.
        # self.original_stream.write(text) 
        
        if not text:
            return

        # Handle carriage returns for progress bars (simple heuristic)
        if '\r' in text:
            # In a RichLog, handling \r perfectly is hard without a dedicated Progress widget.
            # We'll strip it and just log the latest state to avoid clutter, 
            # or replace with newline to show history.
            text = text.replace('\r', '\n')

        # Check if this is a prompt (no newline at end)
        if not text.endswith('\n'):
            self.last_partial_line += text
            # We don't write partial lines immediately to the log to avoid fragmentation,
            # but we store it. If input() is called next, we use this as the prompt.
        else:
            # It's a complete line (or finishes one)
            full_text = self.last_partial_line + text
            self.last_partial_line = ""
            
            # Thread-safe update to UI
            self.app.write_to_log(full_text.rstrip(), self.is_stderr)

    def flush(self):
        self.original_stream.flush()
        if self.last_partial_line:
            self.app.write_to_log(self.last_partial_line, self.is_stderr)
            self.last_partial_line = ""

    def isatty(self):
        return False # We are capturing, not a real TTY


class TUIStdinWrapper:
    """
    Redirects stdin to trigger a Textual Input modal.
    """
    def __init__(self, app: "SyncApp", stdout_wrapper: TUIStdoutWrapper):
        self.app = app
        self.stdout_wrapper = stdout_wrapper

    def readline(self):
        # Determine prompt from the last partial output of stdout
        prompt = self.stdout_wrapper.last_partial_line
        self.stdout_wrapper.last_partial_line = "" # Consume it
        
        # Request input from UI (blocking call from worker thread perspective)
        return self.app.request_input(prompt)

    def read(self, size=-1):
        return self.readline()


# --- Main Application ---

class SyncApp(App):
    """
    The main Textual application for PDD Sync.
    """
    CSS = """
    Screen {
        layout: vertical;
    }
    #header-container {
        height: 10;
        dock: top;
        border-bottom: solid $primary;
    }
    #log-container {
        height: 1fr;
        border: solid $secondary;
    }
    RichLog {
        height: 1fr;
        background: $surface;
    }
    """

    BINDINGS = [("q", "quit", "Quit")]

    def __init__(self, worker_func: Callable, shared_state: Dict[str, Any]):
        super().__init__()
        self.worker_func = worker_func
        self.shared_state = shared_state
        
        # Animation State
        self.logo_active = True
        self.sync_anim_thread = None
        self.stop_event = threading.Event()
        
        # IO State
        self._input_response = None
        self._input_event = threading.Event()
        
        # Widgets
        self.rich_log = Log(highlight=True, markup=True)
        self.header_static = Static("")

    def compose(self) -> ComposeResult:
        yield Header()
        yield Container(self.header_static, id="header-container")
        yield Container(self.rich_log, id="log-container")
        yield Footer()

    def on_mount(self) -> None:
        # Start the background worker
        self.run_worker_task()
        # Start the animation loop
        self.set_interval(0.1, self.update_animation)

    @work(thread=True)
    def run_worker_task(self):
        """Runs the provided sync logic in a separate thread with IO redirection."""
        
        # 1. Setup IO Redirection
        original_stdout = sys.stdout
        original_stderr = sys.stderr
        original_stdin = sys.stdin

        stdout_wrapper = TUIStdoutWrapper(self, original_stdout)
        stderr_wrapper = TUIStdoutWrapper(self, original_stderr, is_stderr=True)
        stdin_wrapper = TUIStdinWrapper(self, stdout_wrapper)

        sys.stdout = stdout_wrapper
        sys.stderr = stderr_wrapper
        sys.stdin = stdin_wrapper

        # Set COLUMNS to ensure Rich renders correctly inside the log
        # We estimate width based on the app, defaulting to 100 if not yet mounted fully
        os.environ["COLUMNS"] = "100" 

        # 2. Start Logo Animation (Background)
        start_logo_animation()
        
        # 3. Start Sync Animation Logic (Background Thread)
        # We need to adapt the shared state dict to the list-refs expected by sync_animation
        self.sync_anim_thread = threading.Thread(
            target=sync_animation,
            args=(
                self.shared_state['current_function'], # List[str]
                self.stop_event,
                self.shared_state['basename'],
                self.shared_state['current_cost'],     # List[float]
                self.shared_state['budget'],
                self.shared_state['prompt_color'],     # List[str]
                self.shared_state['code_color'],       # List[str]
                self.shared_state['example_color'],    # List[str]
                self.shared_state['tests_color'],      # List[str]
                self.shared_state['prompt_path'],      # List[str]
                self.shared_state['code_path'],        # List[str]
                self.shared_state['example_path'],     # List[str]
                self.shared_state['tests_path']        # List[str]
            ),
            daemon=True
        )
        self.sync_anim_thread.start()

        try:
            # 4. Run the actual worker function
            # Wait a moment for logo to form before starting heavy work
            time.sleep(3.0) 
            self.logo_active = False # Switch UI to sync view
            stop_logo_animation()
            
            self.worker_func()
            
        except Exception as e:
            self.write_to_log(f"[bold red]Error in worker:[/bold red] {e}", is_stderr=True)
        finally:
            # 5. Cleanup
            self.stop_event.set() # Stop sync animation
            if self.sync_anim_thread:
                self.sync_anim_thread.join(timeout=2)
            
            sys.stdout = original_stdout
            sys.stderr = original_stderr
            sys.stdin = original_stdin
            
            self.write_to_log("[bold green]Sync process finished. Press 'q' to exit.[/bold green]")

    def update_animation(self):
        """Called periodically to update the header visual."""
        if self.logo_active:
            # While logo is active, the logo_animation module handles the screen.
            # However, since we are inside a Textual app, the logo_animation module's 
            # direct print to stdout might conflict or be hidden if not handled carefully.
            # For this integration, we assume logo_animation writes to a buffer or we 
            # display a placeholder. 
            # *Correction based on requirements*: The requirement says "Integrate with... logo_animation".
            # Since logo_animation takes over the screen, we might just show a loading text here
            # until we switch to the sync view.
            self.header_static.update(Panel(Align.center("Initializing PDD Sync...", vertical="middle")))
        else:
            # Render the Sync Status Box
            # We construct a Rich renderable based on shared state
            cost = self.shared_state['current_cost'][0]
            func = self.shared_state['current_function'][0]
            
            status_text = Text()
            status_text.append("Operation: ", style="bold white")
            status_text.append(f"{func.upper()}\n", style="bold cyan")
            status_text.append("Cost: ", style="bold white")
            status_text.append(f"${cost:.4f}", style="bold green")
            
            self.header_static.update(Panel(status_text, title="Sync Status", border_style="blue"))

    # --- Thread-Safe UI Methods ---

    def write_to_log(self, message: str, is_stderr: bool = False):
        """Writes to the RichLog widget from a thread."""
        if is_stderr:
            style = "bold red"
            # Wrap in style tags if not already present (simple check)
            if not message.startswith("["): 
                message = f"[{style}]{message}[/{style}]"
        
        self.call_from_thread(self.rich_log.write, message)

    def request_input(self, prompt: str) -> str:
        """
        Blocking call (for the worker thread) to get user input via Modal.
        """
        self._input_response = None
        self._input_event.clear()
        
        def show_modal():
            self.push_screen(InputScreen(prompt), self._handle_input_result)
            
        self.call_from_thread(show_modal)
        self._input_event.wait()
        return self._input_response

    def _handle_input_result(self, result: str):
        self._input_response = result
        self._input_event.set()

    def request_confirmation(self, message: str) -> bool:
        """Blocking call for Yes/No."""
        self._input_response = None
        self._input_event.clear()
        
        def show_modal():
            self.push_screen(ConfirmScreen(message), self._handle_input_result)
            
        self.call_from_thread(show_modal)
        self._input_event.wait()
        return bool(self._input_response)

    def request_choice(self, title: str, choices: List[str], default: str, timeout: float) -> str:
        """Blocking call for selection."""
        self._input_response = None
        self._input_event.clear()
        
        def show_modal():
            self.push_screen(ChoiceScreen(title, choices, default, timeout), self._handle_input_result)
            
        self.call_from_thread(show_modal)
        self._input_event.wait()
        return str(self._input_response)


# --- Steering Logic ---

def maybe_steer_operation(
    app: Optional[SyncApp], 
    current_op: str, 
    options: List[str] = ["generate", "test", "fix", "abort"],
    default: str = "test",
    timeout: float = DEFAULT_TIMEOUT
) -> str:
    """
    Prompts the user to choose the next operation.
    
    Args:
        app: The running SyncApp instance (or None if headless).
        current_op: The operation that just finished.
        options: List of valid next operations.
        default: The default operation if timeout occurs.
        timeout: Seconds to wait before auto-selecting default.
        
    Returns:
        The selected operation string.
    """
    
    # 1. Headless Check
    if _is_headless_environment() or app is None:
        print(f"Headless mode: Auto-selecting '{default}' after '{current_op}'")
        return default

    # 2. Interactive Steering
    # We are inside the worker thread here. We call into the App to show the modal.
    selection = app.request_choice(
        title=f"Operation '{current_op}' complete. Next step?",
        choices=options,
        default=default,
        timeout=timeout
    )
    
    return selection


# --- Entry Point Wrapper ---

def run_sync_tui(worker_func: Callable, shared_state: Dict[str, Any]):
    """
    Launches the TUI and runs the worker_func within it.
    """
    if _is_headless_environment():
        # Just run the worker directly without TUI
        print("Running in headless mode (no TUI).")
        worker_func()
    else:
        app = SyncApp(worker_func, shared_state)
        app.run()

# --- Example Usage (for testing this module directly) ---
if __name__ == "__main__":
    # Mock Shared State
    state = {
        'current_function': ["init"],
        'basename': "demo_project",
        'current_cost': [0.0],
        'budget': 5.0,
        'prompt_color': ["blue"],
        'code_color': ["cyan"],
        'example_color': ["green"],
        'tests_color': ["yellow"],
        'prompt_path': ["./prompt.txt"],
        'code_path': ["./src/main.py"],
        'example_path': ["./examples/ex1.py"],
        'tests_path': ["./tests/test_main.py"]
    }

    def mock_worker():
        print("Worker started.")
        time.sleep(1)
        print("Generating code...")
        state['current_function'][0] = "generate"
        state['current_cost'][0] += 0.05
        time.sleep(2)
        
        # Test Input
        name = input("Enter project name: ")
        print(f"Project name set to: {name}")
        
        # Test Steering
        # Note: In a real app, we'd pass the 'app' instance to the worker or make it globally available
        # For this test, we can't easily access 'app' inside this closure without a global or passing it in.
        # In the real integration, the orchestrator calling this would have access to the app instance.
        print("Steering would happen here in real flow.")
        
        print("Worker finished.")

    run_sync_tui(mock_worker, state)