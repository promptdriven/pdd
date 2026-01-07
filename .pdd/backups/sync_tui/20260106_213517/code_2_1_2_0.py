import os
import sys
import time
import threading
import queue
from typing import Any, Dict, List, Optional, Callable, Union

from textual import work
from textual.app import App, ComposeResult
from textual.binding import Binding

from textual.containers import Container, Vertical, Center, Middle
from textual.screen import ModalScreen
from textual.widgets import Header, Footer, RichLog, ProgressBar, Static, Input, Label, Button
from textual.message import Message

from rich.console import Console, Group
from rich.panel import Panel
from rich.text import Text
from rich.style import Style
from rich.align import Align

# Internal module imports (assumed to be in the same package or PYTHONPATH)
from pdd.sync_animation import AnimationState, _render_animation_frame
from pdd.logo_animation import (
    get_logo_particles, 
    update_particles, 
    LOGO_FORMATION_DURATION, 
    LOGO_HOLD_DURATION, 
    LOGO_TO_BOX_TRANSITION_DURATION,
    ASCII_LOGO_ART
)

# --- Redirectors ---

class ThreadSafeRedirector:
    """Redirects stdout/stderr to a Textual RichLog widget safely from a thread."""
    def __init__(self, app: App, log_widget: RichLog):
        self.app = app
        self.log_widget = log_widget
        self.buffer = ""

    def write(self, data: str) -> int:
        if not data:
            return 0
        
        # Handle carriage returns for progress bar updates
        if "\r" in data:
            parts = data.split("\r")
            # We only care about the content after the last \r for the current line
            data = parts[-1]

        self.buffer += data
        if "\n" in self.buffer:
            lines = self.buffer.split("\n")
            # Keep the last partial line in the buffer
            self.buffer = lines.pop()
            for line in lines:
                self.app.call_from_thread(self._write_line, line)
        return len(data)

    def _write_line(self, line: str) -> None:
        # Convert ANSI to Rich Text
        rich_text = Text.from_ansi(line)
        
        # Dim lines matching timestamp pattern YYYY-MM-DD HH:MM:SS
        # Simple check for "202x-xx-xx xx:xx:xx"
        if len(line) > 19 and line[4] == "-" and line[7] == "-" and line[10] == " " and line[13] == ":":
            rich_text.stylize("dim", 0, 19)
            
        self.log_widget.write(rich_text)

    def flush(self) -> None:
        if self.buffer:
            self.app.call_from_thread(self._write_line, self.buffer)
            self.buffer = ""

class TUIStdinRedirector:
    """Redirects stdin.readline() to a Textual Input modal."""
    def __init__(self, app: 'SyncApp'):
        self.app = app
        self.last_stdout = ""

    def write_stdout_capture(self, data: str):
        """Used by the app to feed the last prompt fragment to the redirector."""
        if not data.endswith("\n"):
            self.last_stdout = data
        else:
            self.last_stdout = ""

    def readline(self) -> str:
        prompt = self.last_stdout.strip() or "Input required:"
        is_password = any(kw in prompt.lower() for kw in ["password", "api", "key", "secret"])
        
        try:
            result = self.app.request_input(prompt, password=is_password)
            if result is None:
                raise EOFError("Input cancelled by user")
            return result + "\n"
        except Exception as e:
            raise EOFError(f"TUI Input failed: {e}")

# --- Modal Screens ---

class ConfirmScreen(ModalScreen[bool]):
    """A simple Yes/No confirmation dialog."""
    BINDINGS = [
        Binding("y", "submit(True)", "Yes"),
        Binding("n", "submit(False)", "No"),
        Binding("enter", "submit(True)", "Yes"),
        Binding("escape", "submit(False)", "No"),
    ]

    def __init__(self, message: str):
        super().__init__()
        self.message = message

    def compose(self) -> ComposeResult:
        yield Vertical(
            Static(self.message, id="question"),
            Center(
                Button("Yes (y)", variant="primary", id="yes"),
                Button("No (n)", variant="error", id="no"),
            ),
            id="dialog"
        )

    def on_button_pressed(self, event: Button.Pressed) -> None:
        self.dismiss(event.button.id == "yes")

    def action_submit(self, value: bool) -> None:
        self.dismiss(value)

class InputScreen(ModalScreen[str]):
    """A text input dialog."""
    def __init__(self, prompt: str, password: bool = False):
        super().__init__()
        self.prompt = prompt
        self.password = password

    def compose(self) -> ComposeResult:
        yield Vertical(
            Label(self.prompt),
            Input(password=self.password, id="input_field"),
            Center(
                Button("Submit", variant="primary", id="submit"),
                Button("Cancel", variant="error", id="cancel"),
            ),
            id="dialog"
        )

    def on_mount(self) -> None:
        self.query_one(Input).focus()

    def on_input_submitted(self, event: Input.Submitted) -> None:
        self.dismiss(event.value)

    def on_button_pressed(self, event: Button.Pressed) -> None:
        if event.button.id == "submit":
            self.dismiss(self.query_one(Input).value)
        else:
            self.dismiss(None)

class ChoiceScreen(ModalScreen[int]):
    """A ranked list selection dialog with auto-timeout."""
    def __init__(self, prompt: str, options: List[str], default_index: int = 0, timeout_s: float = 3.0):
        super().__init__()
        self.prompt = prompt
        self.options = options
        self.default_index = default_index
        self.timeout_s = timeout_s
        self.remaining = timeout_s
        self.timer = None

    def compose(self) -> ComposeResult:
        with Vertical(id="dialog"):
            yield Label(self.prompt, id="prompt_label")
            for i, opt in enumerate(self.options):
                label = f"[{i+1}] {opt}"
                if i == self.default_index:
                    label += " (Recommended)"
                yield Button(label, id=f"opt_{i}", variant="default")
            yield Label("", id="status_line")

    def on_mount(self) -> None:
        self.timer = self.set_interval(0.1, self.update_timer)

    def update_timer(self) -> None:
        self.remaining -= 0.1
        if self.remaining <= 0:
            self.timer.stop()
            self.dismiss(self.default_index)
        else:
            self.query_one("#status_line", Label).update(f"Auto-selecting default in {self.remaining:.1f}s...")

    def on_button_pressed(self, event: Button.Pressed) -> None:
        idx = int(event.button.id.split("_")[1])
        self.dismiss(idx)

    def on_key(self, event) -> None:
        if event.key.isdigit():
            idx = int(event.key) - 1
            if 0 <= idx < len(self.options):
                self.dismiss(idx)

# --- Main App ---

class SyncApp(App[Dict[str, Any]]):
    CSS = """
    #dialog {
        padding: 1 2;
        background: $panel;
        border: thick $primary;
        width: 60;
        height: auto;
        align: center middle;
    }
    #question { text-align: center; margin-bottom: 1; }
    #status_line { color: $text-muted; margin-top: 1; }
    RichLog { background: $surface; border: solid $primary; height: 1fr; }
    ProgressBar { width: 100%; margin: 1; }
    .hidden { display: none; }
    """

    def __init__(
        self, 
        basename: str, 
        budget: float, 
        worker_func: Callable,
        function_name_ref: List[str],
        cost_ref: List[float],
        paths: Dict[str, List[str]],
        colors: Dict[str, List[str]],
        stop_event: threading.Event,
        progress_callback_ref: Optional[List[Optional[Callable]]] = None
    ):
        super().__init__()
        self.basename = basename
        self.budget = budget
        self.worker_func = worker_func
        self.fn_ref = function_name_ref
        self.cost_ref = cost_ref
        self.paths = paths
        self.colors = colors
        self.stop_event = stop_event
        
        self.animation_phase = "logo" # logo -> main
        self.start_time = time.time()
        self.worker_result = {"success": False, "total_cost": 0.0}
        
        if progress_callback_ref is not None:
            progress_callback_ref[0] = self.update_progress

    def compose(self) -> ComposeResult:
        yield Header()
        yield Static("", id="animation_display")
        yield ProgressBar(show_eta=False, id="sync_progress", classes="hidden")
        yield RichLog(highlight=True, markup=True, id="worker_log")
        yield Footer()

    def on_mount(self) -> None:
        self.set_interval(0.05, self.update_animation)
        self.run_worker()

    def update_animation(self) -> None:
        display = self.query_one("#animation_display", Static)
        elapsed = time.time() - self.start_time

        if self.animation_phase == "logo":
            particles = get_logo_particles(self.size.width, self.size.height)
            update_particles(particles, elapsed, self.size.width, self.size.height)
            # Simplified rendering of particles for TUI
            # In a real implementation, we'd use a Canvas or custom widget
            display.update(Panel(Align.center(ASCII_LOGO_ART), title="PDD Sync Initializing"))
            
            total_logo_time = LOGO_FORMATION_DURATION + LOGO_HOLD_DURATION + LOGO_TO_BOX_TRANSITION_DURATION
            if elapsed > total_logo_time:
                self.animation_phase = "main"
        
        else:
            # Main Sync Animation
            frame = _render_animation_frame(
                self.fn_ref[0],
                self.basename,
                self.cost_ref[0],
                self.budget,
                self.colors['prompt'][0],
                self.colors['code'][0],
                self.colors['example'][0],
                self.colors['tests'][0],
                self.paths['prompt'][0],
                self.paths['code'][0],
                self.paths['example'][0],
                self.paths['tests'][0],
                self.size.width
            )
            display.update(frame)

    def update_progress(self, current: float, total: float) -> None:
        pb = self.query_one("#sync_progress", ProgressBar)
        if total > 0:
            pb.remove_class("hidden")
            pb.update(total=total, progress=current)
        else:
            pb.add_class("hidden")

    @work(thread=True)
    def run_worker(self) -> None:
        log_widget = self.query_one("#worker_log", RichLog)
        redirector = ThreadSafeRedirector(self, log_widget)
        stdin_redirector = TUIStdinRedirector(self)
        
        old_stdout, old_stderr, old_stdin = sys.stdout, sys.stderr, sys.stdin
        old_env = os.environ.copy()
        
        # Set environment for worker
        os.environ["FORCE_COLOR"] = "1"
        os.environ["TERM"] = "xterm-256color"
        os.environ["COLUMNS"] = str(log_widget.content_size.width or 80)

        sys.stdout = redirector
        sys.stderr = redirector
        sys.stdin = stdin_redirector

        try:
            self.worker_result = self.worker_func()
        except EOFError:
            self.worker_result = {"success": False, "error": "User cancelled input"}
        except Exception as e:
            self.worker_result = {"success": False, "error": str(e)}
        finally:
            sys.stdout, sys.stderr, sys.stdin = old_stdout, old_stderr, old_stdin
            os.environ.clear()
            os.environ.update(old_env)
            self.app.exit(self.worker_result)

    # --- Thread-safe Interaction Methods ---

    def request_confirmation(self, prompt: str) -> bool:
        res_queue = queue.Queue()
        def cb(res: bool): res_queue.put(res)
        self.call_from_thread(self.push_screen, ConfirmScreen(prompt), cb)
        return res_queue.get(timeout=300)

    def request_input(self, prompt: str, password: bool = False) -> Optional[str]:
        res_queue = queue.Queue()
        def cb(res: str): res_queue.put(res)
        self.call_from_thread(self.push_screen, InputScreen(prompt, password), cb)
        return res_queue.get(timeout=300)

    def request_choice(self, prompt: str, options: List[str], default_index: int = 0, timeout_s: float = 3.0) -> int:
        # Headless/Quiet check (simplified)
        if os.environ.get("PDD_QUIET") == "1":
            return default_index

        res_queue = queue.Queue()
        def cb(res: int): res_queue.put(res)
        self.call_from_thread(self.push_screen, ChoiceScreen(prompt, options, default_index, timeout_s), cb)
        
        choice = res_queue.get(timeout=300)
        
        # Log outcome
        source = "user-selected" if choice != default_index else "default/timeout"
        self.call_from_thread(self.query_one("#worker_log").write, f"[dim]Choice made: {options[choice]} ({source})[/]")
        
        return choice

def show_exit_animation():
    """Standalone exit sequence."""
    console = Console()
    exit_panel = Panel(
        Align.center(Text(ASCII_LOGO_ART, style="bold cyan")),
        title="PDD Sync Complete",
        border_style="green"
    )
    console.print(exit_panel)
    time.sleep(1.0)
    console.clear()",
  "focus": "A Textual-based TUI application for a synchronization tool.",
  "explanation": "The code implements a Textual application (`SyncApp`) designed to wrap a long-running worker process. It includes thread-safe redirection of stdout/stderr to a `RichLog` widget, a custom stdin redirector that triggers modal input screens, and several modal dialogs for user interaction (confirmation, text input, and timed choices). It also integrates an animation system for visual feedback during the sync process."
}