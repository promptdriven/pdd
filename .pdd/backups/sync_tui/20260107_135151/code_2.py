import sys
import os
import threading
import time
import asyncio
from typing import List, Optional, Callable, Any, Dict

from textual.app import App, ComposeResult
from textual.containers import Container, Vertical
from textual.widgets import Header, Footer, Log, Static, Label, Input, Button, ProgressBar
from textual.screen import ModalScreen
from textual.worker import Worker
from textual import work
from textual.binding import Binding
from rich.console import Console
from rich.text import Text
from rich.panel import Panel
from rich.align import Align

# Import animation modules based on provided context
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


class ChoiceScreen(ModalScreen[int]):
    """A modal screen for selecting from a list of options. Returns the index of the selection."""

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

    def __init__(self, title: str, choices: List[str], default: int = 0, timeout: float = 0):
        super().__init__()
        self.title_text = title
        self.choices = choices
        self.default = default
        self.timeout_val = timeout
        self.timer = None

    def compose(self) -> ComposeResult:
        # Use index as ID for buttons to avoid issues with spaces/special chars in choice text
        yield Container(
            Label(self.title_text, id="title"),
            *[Button(f"{i+1}. {c}", id=str(i)) for i, c in enumerate(self.choices)],
            id="dialog",
        )

    def on_mount(self) -> None:
        if self.timeout_val > 0:
            self.timer = self.set_timer(self.timeout_val, self.action_timeout_select)

    def action_timeout_select(self) -> None:
        self.dismiss(self.default)

    def action_select_idx(self, idx: int) -> None:
        if 0 <= idx < len(self.choices):
            self.dismiss(idx)

    def on_button_pressed(self, event: Button.Pressed) -> None:
        # Button ID is the index string
        try:
            idx = int(event.button.id)
            self.dismiss(idx)
        except (ValueError, TypeError):
            pass


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
        if not text:
            return

        # Handle carriage returns for progress bars (simple heuristic)
        if '\r' in text:
            text = text.replace('\r', '\n')

        # Check if this is a prompt (no newline at end)
        if not text.endswith('\n'):
            self.last_partial_line += text
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
        return False


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
    #progress-container {
        height: auto;
        padding: 0 1;
        margin: 1 0;
    }
    ProgressBar {
        width: 100%;
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

    def __init__(self, basename: str, budget: float, worker_func: Callable, 
                 function_name_ref: List[str], cost_ref: List[float], 
                 paths: Dict[str, List[str]], colors: Dict[str, List[str]], 
                 stop_event: threading.Event):
        super().__init__()
        self.basename = basename
        self.budget = budget
        self.worker_func = worker_func
        self.function_name_ref = function_name_ref
        self.cost_ref = cost_ref
        self.paths = paths
        self.colors = colors
        self.stop_event = stop_event
        
        # Animation State
        self.logo_active = True
        self.sync_anim_thread = None
        
        # IO State
        self._input_response = None
        self._input_event = threading.Event()
        
        # Widgets
        self.rich_log = Log(highlight=True, markup=True)
        self.header_static = Static("")
        self.progress_bar = ProgressBar(total=100, show_eta=False)

    def compose(self) -> ComposeResult:
        yield Header()
        yield Container(self.header_static, id="header-container")
        yield Container(self.progress_bar, id="progress-container")
        yield Container(self.rich_log, id="log-container")
        yield Footer()

    def on_mount(self) -> None:
        # Start the background worker
        self.run_worker_task()
        # Start the animation loop
        self.set_interval(0.1, self.update_animation)

    def on_unmount(self) -> None:
        self.stop_event.set()

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
        os.environ["COLUMNS"] = "100" 

        # 2. Start Logo Animation (Background)
        start_logo_animation()
        
        # 3. Start Sync Animation Logic (Background Thread)
        self.sync_anim_thread = threading.Thread(
            target=sync_animation,
            args=(
                self.function_name_ref,
                self.stop_event,
                self.basename,
                self.cost_ref,
                self.budget,
                self.colors.get('prompt', ['blue']),
                self.colors.get('code', ['green']),
                self.colors.get('example', ['yellow']),
                self.colors.get('tests', ['magenta']),
                self.paths.get('prompt', []),
                self.paths.get('code', []),
                self.paths.get('example', []),
                self.paths.get('tests', [])
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
            
            result = self.worker_func()
            # Pass the result back to the main thread exit
            self.call_from_thread(self.exit, result)
            
        except Exception as e:
            self.write_to_log(f"[bold red]Error in worker:[/bold red] {e}", is_stderr=True)
            self.call_from_thread(self.exit, None)
        finally:
            # 5. Cleanup
            self.stop_event.set() # Stop sync animation
            if self.sync_anim_thread:
                self.sync_anim_thread.join(timeout=2)
            
            sys.stdout = original_stdout
            sys.stderr = original_stderr
            sys.stdin = original_stdin
            
            self.write_to_log("[bold green]Sync process finished.[/bold green]")

    def update_animation(self):
        """Called periodically to update the header visual."""
        if self.logo_active:
            self.header_static.update(Panel(Align.center("Initializing PDD Sync...", vertical="middle")))
        else:
            # Render the Sync Status Box
            cost = self.cost_ref[0]
            func = self.function_name_ref[0]
            
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
            if not message.startswith("["): 
                message = f"[{style}]{message}[/{style}]"
        
        self.call_from_thread(self.rich_log.write, message)

    def update_progress(self, current: int, total: int):
        """Updates the progress bar."""
        self.call_from_thread(self.progress_bar.update, total=total, progress=current)

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
        return str(self._input_response)

    def _handle_input_result(self, result: Any):
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

    def request_choice(self, prompt: str, options: List[str], default_index: int = 0, timeout_s: float = 10.0) -> int:
        """Blocking call for selection. Returns the index of the selected option."""
        self._input_response = None
        self._input_event.clear()
        
        def show_modal():
            self.push_screen(ChoiceScreen(prompt, options, default_index, timeout_s), self._handle_input_result)
            
        self.call_from_thread(show_modal)
        self._input_event.wait()
        
        # Result is already an int index from ChoiceScreen
        try:
            return int(self._input_response)
        except (ValueError, TypeError):
            return default_index


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
    """
    
    # 1. Headless Check
    if _is_headless_environment() or app is None:
        print(f"Headless mode: Auto-selecting '{default}' after '{current_op}'")
        return default

    # 2. Interactive Steering
    try:
        default_idx = options.index(default)
    except ValueError:
        default_idx = 0

    selection_idx = app.request_choice(
        prompt=f"Operation '{current_op}' complete. Next step?",
        options=options,
        default_index=default_idx,
        timeout_s=timeout
    )
    
    if 0 <= selection_idx < len(options):
        return options[selection_idx]
    return default


# --- Entry Point Wrapper ---

def run_sync_tui(worker_func: Callable, **kwargs):
    """
    Launches the TUI and runs the worker_func within it.
    Accepts kwargs to pass to SyncApp constructor.
    """
    if _is_headless_environment():
        # Just run the worker directly without TUI
        print("Running in headless mode (no TUI).")
        worker_func()
    else:
        app = SyncApp(worker_func=worker_func, **kwargs)
        app.run()

def show_exit_animation():
    """
    Displays a final exit animation in the standard terminal.
    """
    # Placeholder for exit animation logic
    print("\n--- PDD Sync Session Ended ---")

if __name__ == "__main__":
    # Example usage for testing
    pass