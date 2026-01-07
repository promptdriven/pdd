import sys
import os
import time
import threading
import queue
import re
from typing import List, Optional, Dict, Any, Callable, Union

from rich.console import Console
from rich.text import Text
from rich.panel import Panel
from rich.align import Align
from rich.style import Style
from rich.layout import Layout
from rich.live import Live

from textual.app import App, ComposeResult
from textual.containers import Vertical, Horizontal, Center

from textual.widgets import Static, RichLog, ProgressBar, Label, Button, Input
from textual.screen import ModalScreen
from textual.binding import Binding
from textual import work
from textual.message import Message

# -----------------------------------------------------------------------------
# Mock Imports / Assumptions based on Prompt Context
# In a real scenario, these would be: from pdd.utils import ...
# -----------------------------------------------------------------------------

try:
    # Assuming these exist based on prompt requirements
    from pdd.sync_animation import _render_animation_frame, AnimationState
    from pdd.logo_animation import ASCII_LOGO_ART
except ImportError:
    # Fallbacks for standalone testing if modules aren't present
    ASCII_LOGO_ART = "PDD SYNC"
    
    class AnimationState:
        def __init__(self, *args):
            pass
    
    def _render_animation_frame(*args, **kwargs):
        return Panel("Syncing...", title="PDD Sync")

# -----------------------------------------------------------------------------
# Redirectors
# -----------------------------------------------------------------------------

class ThreadSafeRedirector:
    """
    Redirects stdout/stderr to a Textual RichLog widget in a thread-safe manner.
    Handles ANSI codes, carriage returns for progress bars, and timestamp dimming.
    """
    def __init__(self, app: App, log_widget: RichLog, is_stderr: bool = False):
        self.app = app
        self.log_widget = log_widget
        self.is_stderr = is_stderr
        self.buffer = ""
        self.ansi_escape = re.compile(r'\x1B(?:[@-Z\\-_]|\[[0-?]* [ -/]*[@-~])')
        self.timestamp_pattern = re.compile(r'^\d{4}-\d{2}-\d{2} \d{2}:\d{2}:\d{2}')

    def write(self, string: str) -> None:
        if not string:
            return

        # Handle carriage returns (simple progress bar handling)
        # If we see a \r, we effectively want to discard what came before it in the buffer
        # or treat it as a line update. For RichLog, we usually just append.
        # However, to prevent log spam from progress bars, we can filter.
        if '\r' in string:
            parts = string.split('\r')
            string = parts[-1]  # Keep content after last \r

        self.buffer += string
        
        if '\n' in self.buffer:
            lines = self.buffer.split('\n')
            # Keep the last part in buffer if it didn't end with newline
            if self.buffer.endswith('\n'):
                self.buffer = ""
            else:
                self.buffer = lines.pop()

            for line in lines:
                self._write_line(line)

    def _write_line(self, line: str) -> None:
        # Clean ANSI for text processing if needed, but RichLog handles ANSI mostly.
        # However, Text.from_ansi is safer for Textual widgets.
        text = Text.from_ansi(line)
        
        # Dim timestamps
        plain_text = text.plain
        if self.timestamp_pattern.match(plain_text):
            # Apply dim style to the timestamp part (first 19 chars)
            text.stylize("dim", 0, 19)
        
        if self.is_stderr:
            text.stylize("red")

        self.app.call_from_thread(self.log_widget.write, text)

    def flush(self) -> None:
        if self.buffer:
            self._write_line(self.buffer)
            self.buffer = ""

    def isatty(self) -> bool:
        return True


class TUIStdinRedirector:
    """
    Redirects stdin requests to TUI modals.
    Captures the last prompt printed to stdout to display in the modal.
    """
    def __init__(self, app: 'SyncApp'):
        self.app = app
        self.last_prompt = ""

    def write(self, string: str) -> None:
        # Often prompts are written to stdout/stderr without a newline
        # We capture this to show in the input modal
        self.last_prompt = string

    def flush(self) -> None:
        pass

    def readline(self) -> str:
        if not self.app.is_running:
            raise EOFError("App is not running")

        # Detect password request
        is_password = False
        lower_prompt = self.last_prompt.lower()
        if "key" in lower_prompt or "api" in lower_prompt or "password" in lower_prompt:
            is_password = True

        # Request input from UI thread
        try:
            result = self.app.request_input(self.last_prompt, password=is_password)
            if result is None:
                raise EOFError("Input cancelled")
            return result + "\n"
        except Exception:
            raise EOFError("Input failed")

# -----------------------------------------------------------------------------
# Modals
# -----------------------------------------------------------------------------

class ConfirmScreen(ModalScreen[bool]):
    """Modal for Yes/No confirmation."""
    
    CSS = """
    ConfirmScreen {
        align: center middle;
        background: $surface 50%;
    }
    #dialog {
        padding: 1 2;
        width: 40;
        height: auto;
        border: thick $primary;
        background: $surface;
    }
    #question {
        content-align: center middle;
        margin-bottom: 1;
    }
    #buttons {
        width: 100%;
        align: center middle;
    }
    Button {
        margin: 0 1;
    }
    """

    BINDINGS = [
        ("y", "submit_yes", "Yes"),
        ("n", "submit_no", "No"),
        ("enter", "submit_yes", "Yes"),
        ("escape", "submit_no", "No"),
    ]

    def __init__(self, prompt: str):
        super().__init__()
        self.prompt_text = prompt

    def compose(self) -> ComposeResult:
        with Vertical(id="dialog"):
            yield Label(self.prompt_text, id="question")
            with Horizontal(id="buttons"):
                yield Button("Yes", variant="success", id="yes")
                yield Button("No", variant="error", id="no")

    def on_button_pressed(self, event: Button.Pressed) -> None:
        if event.button.id == "yes":
            self.dismiss(True)
        else:
            self.dismiss(False)

    def action_submit_yes(self) -> None:
        self.dismiss(True)

    def action_submit_no(self) -> None:
        self.dismiss(False)


class InputScreen(ModalScreen[Optional[str]]):
    """Modal for text input."""

    CSS = """
    InputScreen {
        align: center middle;
        background: $surface 50%;
    }
    #dialog {
        padding: 1 2;
        width: 60;
        height: auto;
        border: thick $primary;
        background: $surface;
    }
    Label {
        margin-bottom: 1;
    }
    """

    def __init__(self, prompt: str, password: bool = False):
        super().__init__()
        self.prompt_text = prompt
        self.password = password

    def compose(self) -> ComposeResult:
        with Vertical(id="dialog"):
            yield Label(self.prompt_text)
            yield Input(password=self.password, id="input")

    def on_mount(self) -> None:
        self.query_one(Input).focus()

    def on_input_submitted(self, event: Input.Submitted) -> None:
        self.dismiss(event.value)


class OptionPickerScreen(ModalScreen[int]):
    """Modal for selecting from a list of options with timeout."""

    CSS = """
    OptionPickerScreen {
        align: center middle;
        background: $surface 50%;
    }
    #dialog {
        padding: 1 2;
        width: 70;
        height: auto;
        border: thick $accent;
        background: $surface;
    }
    #prompt {
        text-align: center;
        text-style: bold;
        margin-bottom: 1;
    }
    #timer {
        text-align: center;
        color: $text-muted;
        margin-top: 1;
    }
    OptionButton {
        width: 100%;
        margin-bottom: 1;
    }
    """

    def __init__(self, prompt: str, options: List[str], default_index: int, timeout_s: float):
        super().__init__()
        self.prompt_text = prompt
        self.options = options
        self.default_index = default_index
        self.timeout_s = timeout_s
        self.remaining = timeout_s
        self.timer: Optional[Any] = None

    def compose(self) -> ComposeResult:
        with Vertical(id="dialog"):
            yield Label(self.prompt_text, id="prompt")
            
            for idx, opt in enumerate(self.options):
                label = f"{idx+1}. {opt}"
                if idx == self.default_index:
                    label += " (Default)"
                variant = "primary" if idx == self.default_index else "default"
                yield Button(label, variant=variant, id=f"opt_{idx}")

            yield Label(f"Auto-selecting default in {self.remaining:.1f}s...", id="timer")

    def on_mount(self) -> None:
        self.timer = self.set_interval(0.1, self.update_timer)
        # Bind number keys
        for i in range(1, min(10, len(self.options) + 1)):
            self.bind(str(i), f"select_option({i-1})")
        self.bind("enter", "select_default")

    def update_timer(self) -> None:
        self.remaining -= 0.1
        if self.remaining <= 0:
            self.dismiss(self.default_index)
        else:
            self.query_one("#timer", Label).update(f"Auto-selecting default in {self.remaining:.1f}s...")

    def on_button_pressed(self, event: Button.Pressed) -> None:
        idx = int(event.button.id.split("_")[1])
        self.dismiss(idx)

    def action_select_option(self, idx: int) -> None:
        if 0 <= idx < len(self.options):
            self.dismiss(idx)

    def action_select_default(self) -> None:
        self.dismiss(self.default_index)

# -----------------------------------------------------------------------------
# Main Application
# -----------------------------------------------------------------------------

class SyncApp(App):
    CSS = """
    Screen {
        layout: vertical;
    }
    #animation-container {
        height: 14;
        border-bottom: solid $primary;
        padding: 1;
        align: center middle;
    }
    #progress-container {
        height: auto;
        padding: 0 1;
        display: none; /* Hidden by default */
    }
    RichLog {
        height: 1fr;
        border-top: solid $secondary;
        background: $surface;
    }
    """

    def __init__(
        self, 
        basename: str, 
        budget: Optional[float], 
        worker_func: Callable, 
        shared_state: Dict[str, Any],
        colors: Dict[str, Any],
        stop_event: threading.Event,
        progress_callback_ref: Optional[List[Callable]] = None
    ):
        super().__init__()
        self.basename = basename
        self.budget = budget
        self.worker_func = worker_func
        self.shared_state = shared_state
        self.colors = colors
        self.stop_event = stop_event
        self.progress_callback_ref = progress_callback_ref
        
        # Animation State
        self.logo_phase = True
        self.logo_start_time = 0.0
        self.LOGO_DURATION = 3.0 # Seconds for logo before sync UI
        
        # Worker Result
        self.worker_result = {}

    def compose(self) -> ComposeResult:
        with Vertical():
            with Center(id="animation-container"):
                yield Static(id="animation-display")
            
            with Vertical(id="progress-container"):
                yield Label("Processing...", id="progress-label")
                yield ProgressBar(total=100, show_eta=False, id="progress-bar")
            
            yield RichLog(highlight=True, markup=True, id="log")

    def on_mount(self) -> None:
        self.logo_start_time = time.time()
        self.set_interval(0.1, self.update_animation)
        
        # Setup progress callback if requested
        if self.progress_callback_ref is not None:
            self.progress_callback_ref.append(self.update_progress)

        # Start the worker
        self.run_worker_task()

    def update_progress(self, current: int, total: int, description: str = "") -> None:
        """Thread-safe progress update."""
        self.call_from_thread(self._update_progress_ui, current, total, description)

    def _update_progress_ui(self, current: int, total: int, description: str) -> None:
        container = self.query_one("#progress-container")
        bar = self.query_one("#progress-bar", ProgressBar)
        label = self.query_one("#progress-label", Label)
        
        if total > 0:
            container.styles.display = "block"
            bar.update(total=total, progress=current)
            label.update(description)
        else:
            container.styles.display = "none"

    def update_animation(self) -> None:
        """Called periodically to render the top animation pane."""
        display = self.query_one("#animation-display", Static)
        
        # Phase 1: Logo Animation
        if self.logo_phase:
            elapsed = time.time() - self.logo_start_time
            if elapsed > self.LOGO_DURATION:
                self.logo_phase = False
            else:
                # Simple fade/expand simulation based on elapsed time
                # In a real implementation, this would use the particle logic
                if elapsed < 1.5:
                    display.update(Align.center(Text(ASCII_LOGO_ART, style="bold blue")))
                else:
                    display.update(Align.center(Panel(Text(ASCII_LOGO_ART), title="Loading...", border_style="blue")))
                return

        # Phase 2: Sync Animation
        # Extract values from shared state refs (lists)
        func_name = self.shared_state['function_name'][0]
        cost = self.shared_state['cost'][0]
        
        # Call the internal render function from sync_animation module
        # We adapt the arguments to match what the module expects
        try:
            renderable = _render_animation_frame(
                basename=self.basename,
                function_name=func_name,
                cost=cost,
                budget=self.budget,
                prompt_path=self.shared_state['paths']['prompt'][0],
                code_path=self.shared_state['paths']['code'][0],
                example_path=self.shared_state['paths']['example'][0],
                tests_path=self.shared_state['paths']['tests'][0],
                prompt_color=self.shared_state['colors']['prompt'][0],
                code_color=self.shared_state['colors']['code'][0],
                example_color=self.shared_state['colors']['example'][0],
                tests_color=self.shared_state['colors']['tests'][0]
            )
            display.update(renderable)
        except Exception as e:
            display.update(f"Animation Error: {e}")

    @work(thread=True)
    def run_worker_task(self) -> None:
        """Executes the worker function in a separate thread with IO redirection."""
        log_widget = self.query_one("#log", RichLog)
        
        # 1. Setup Redirection
        original_stdout = sys.stdout
        original_stderr = sys.stderr
        original_stdin = sys.stdin
        
        # Calculate log width for COLUMNS env var
        log_width = 80
        
        # 2. Setup Environment
        old_env = os.environ.copy()
        os.environ["FORCE_COLOR"] = "1"
        os.environ["TERM"] = "xterm-256color"
        os.environ["COLUMNS"] = str(log_width)

        # 3. Install Redirectors
        sys.stdout = ThreadSafeRedirector(self, log_widget, is_stderr=False)
        sys.stderr = ThreadSafeRedirector(self, log_widget, is_stderr=True)
        
        # Stdin redirector needs to capture prompts from stdout
        stdin_redirector = TUIStdinRedirector(self)
        # We monkeypatch sys.stdout.write to also feed the stdin redirector's prompt capture
        original_redirector_write = sys.stdout.write
        def hooked_write(s):
            stdin_redirector.write(s)
            original_redirector_write(s)
        sys.stdout.write = hooked_write
        
        sys.stdin = stdin_redirector

        try:
            # 4. Run Worker
            result = self.worker_func()
            self.worker_result = result if result else {}
        except EOFError:
            self.worker_result = {"success": False, "error": "Input cancelled"}
        except BaseException as e:
            import traceback
            traceback.print_exc()
            self.worker_result = {"success": False, "error": str(e)}
        finally:
            # 5. Cleanup
            sys.stdout = original_stdout
            sys.stderr = original_stderr
            sys.stdin = original_stdin
            os.environ.clear()
            os.environ.update(old_env)
            
            # Stop animation
            self.stop_event.set()
            
            # Exit App
            self.call_from_thread(self.exit, self.worker_result)

    # --- Interaction Methods (Called from Worker Thread) ---

    def request_confirmation(self, prompt: str, timeout: float = 300.0) -> bool:
        """Thread-safe method to request Yes/No confirmation."""
        result_queue = queue.Queue()
        
        def show_modal():
            def callback(result: bool):
                result_queue.put(result)
            self.push_screen(ConfirmScreen(prompt), callback)

        self.call_from_thread(show_modal)
        
        try:
            return result_queue.get(timeout=timeout)
        except queue.Empty:
            return False # Default to No on timeout

    def request_input(self, prompt: str, password: bool = False, timeout: float = 300.0) -> Optional[str]:
        """Thread-safe method to request text input."""
        result_queue = queue.Queue()
        
        def show_modal():
            def callback(result: Optional[str]):
                result_queue.put(result)
            self.push_screen(InputScreen(prompt, password), callback)

        self.call_from_thread(show_modal)
        
        try:
            return result_queue.get(timeout=timeout)
        except queue.Empty:
            return None

    def request_choice(self, prompt: str, options: List[str], default_index: int = 0, timeout_s: float = 3.0) -> int:
        """Thread-safe method to request a choice from a list."""
        result_queue = queue.Queue()
        
        def show_modal():
            def callback(result: int):
                result_queue.put(result)
            self.push_screen(OptionPickerScreen(prompt, options, default_index, timeout_s), callback)

        self.call_from_thread(show_modal)
        
        try:
            idx = result_queue.get(timeout=timeout_s + 5.0) # Add buffer for UI latency
            
            # Log the choice
            log_msg = f"Steering: Selected '{options[idx]}'"
            if idx == default_index:
                log_msg += " (Default/Timeout)"
            
            self.call_from_thread(lambda: self.query_one("#log", RichLog).write(Text(log_msg, style="italic cyan")))
            
            return idx
        except queue.Empty:
            return default_index

# -----------------------------------------------------------------------------
# Standalone Exit Animation
# -----------------------------------------------------------------------------

def show_exit_animation():
    """Displays the logo centered on screen, waits, then clears."""
    console = Console()
    
    panel = Panel(
        Align.center(Text(ASCII_LOGO_ART, style="bold blue")),
        border_style="blue",
        padding=(1, 2),
        title="Sync Complete"
    )
    
    console.print(Align.center(panel, vertical="middle"), height=console.height)
    time.sleep(1.0)
    console.clear()
