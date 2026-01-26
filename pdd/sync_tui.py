import threading
import sys
import os
from typing import List, Optional, Callable, Any
import io
import asyncio

from textual.app import App, ComposeResult
from textual.screen import ModalScreen
from textual.widgets import Static, RichLog, Button, Label, Input, ProgressBar
from textual.containers import Vertical, Container, Horizontal
from textual.binding import Binding
from textual.worker import Worker
from textual import work

from rich.console import Console
from rich.panel import Panel
from rich.align import Align
from rich.text import Text
import time
import re

# Reuse existing animation logic
from .sync_animation import AnimationState, _render_animation_frame, DEEP_NAVY, ELECTRIC_CYAN
from . import logo_animation
from rich.style import Style

# --- Sync steering (used by sync_orchestration.py) ---

_ACTIVE_SYNC_APP = None  # set by SyncApp when running interactively

# Default steering timeout (seconds).
DEFAULT_STEER_TIMEOUT_S = 8.0


def _is_headless_environment() -> bool:
    """Best-effort check for whether we're in a headless / CI / non-interactive run."""

    # Test override (used by unit tests and local debugging)
    try:
        override = os.environ.get("PDD_TEST_HEADLESS", "").strip().lower()
        if override in {"1", "true", "yes"}:
            return True
        if override in {"0", "false", "no"}:
            return False
    except Exception:
        pass

    try:
        if os.environ.get("CI", "").strip().lower() in {"1", "true", "yes"}:
            return True
    except Exception:
        pass

    # IMPORTANT: do not consult `sys.stdout` here because SyncApp redirects it.
    # Use the original stdio streams instead.
    try:
        return not bool(getattr(sys.__stdout__, "isatty", lambda: False)())
    except Exception:
        return True



class ChoiceScreen(ModalScreen[str]):
    """Modal choice picker with a default selection after a short timeout."""

    CSS = """
    ChoiceScreen {
        align: center middle;
    }

    #choice-dialog {
        width: 90;
        height: auto;
        border: thick $primary;
        background: #0A0A23;
        padding: 1 2;
    }

    #choice-title {
        width: 100%;
        text-align: center;
        text-style: bold;
        color: #00D8FF;
        margin-bottom: 1;
    }

    #choice-prompt {
        width: 100%;
        color: #FFFFFF;
        margin-bottom: 1;
    }

    #choice-buttons {
        width: 100%;
        height: auto;
    }

    #choice-buttons Button {
        width: 100%;
        margin: 0 0 1 0;
    }
    """

    BINDINGS = [
        Binding("escape", "cancel", "Cancel"),
    ]

    def __init__(
        self,
        title: str,
        prompt: str,
        choices: list[str],
        default: str,
        timeout_s: float,
    ) -> None:
        super().__init__()
        self.title_text = title
        self.prompt_text = prompt
        self.choices = choices
        self.default = default
        self.timeout_s = max(0.0, float(timeout_s))
        self._dismissed = False

    def compose(self) -> ComposeResult:
        with Container(id="choice-dialog"):
            yield Label(self.title_text, id="choice-title")
            yield Label(self.prompt_text, id="choice-prompt")
            with Vertical(id="choice-buttons"):
                for idx, choice in enumerate(self.choices, start=1):
                    # Show numeric shortcuts for the first 9 options
                    label = f"{idx}. {choice}" if idx <= 9 else choice
                    variant = "primary" if choice == self.default else "default"
                    # Use a stable, Textual-safe id and map back via index
                    yield Button(label, id=f"choice-{idx}", variant=variant)

    async def on_mount(self) -> None:
        # Auto-default after timeout
        if self.timeout_s > 0:
            asyncio.create_task(self._auto_default())

    async def _auto_default(self) -> None:
        try:
            await asyncio.sleep(self.timeout_s)
        except Exception:
            return
        if not self._dismissed:
            self._dismissed = True
            self.dismiss(self.default)

    def on_button_pressed(self, event: Button.Pressed) -> None:
        if event.button.id and event.button.id.startswith("choice-"):
            # Button ids are `choice-<1-based index>`
            try:
                idx_str = event.button.id[len("choice-"):]
                idx = int(idx_str)
                if 1 <= idx <= len(self.choices):
                    choice = self.choices[idx - 1]
                else:
                    choice = self.default
            except Exception:
                choice = self.default
            self._dismissed = True
            self.dismiss(choice)

    def on_key(self, event) -> None:
        # Numeric shortcuts 1-9
        try:
            if event.character and event.character.isdigit():
                idx = int(event.character)
                if 1 <= idx <= 9 and idx <= len(self.choices):
                    self._dismissed = True
                    self.dismiss(self.choices[idx - 1])
        except Exception:
            pass

    def action_cancel(self) -> None:
        # Treat cancel as choosing the default
        self._dismissed = True
        self.dismiss(self.default)

class ConfirmScreen(ModalScreen[bool]):
    """A modal confirmation dialog for user prompts within the TUI."""

    CSS = """
    ConfirmScreen {
        align: center middle;
    }

    #confirm-dialog {
        width: 70;
        height: auto;
        border: thick $primary;
        background: #0A0A23;
        padding: 1 2;
    }

    #confirm-title {
        width: 100%;
        text-align: center;
        text-style: bold;
        color: #00D8FF;
        margin-bottom: 1;
    }

    #confirm-message {
        width: 100%;
        text-align: center;
        color: #FFFFFF;
        margin-bottom: 1;
    }

    #confirm-buttons {
        width: 100%;
        align: center middle;
        margin-top: 1;
    }

    #confirm-buttons Button {
        margin: 0 2;
        min-width: 12;
    }
    """

    BINDINGS = [
        Binding("y", "confirm_yes", "Yes"),
        Binding("n", "confirm_no", "No"),
        Binding("enter", "confirm_yes", "Confirm"),
        Binding("escape", "confirm_no", "Cancel"),
    ]

    def __init__(self, message: str, title: str = "Confirmation Required"):
        super().__init__()
        self.message = message
        self.title_text = title

    def compose(self) -> ComposeResult:
        with Container(id="confirm-dialog"):
            yield Label(self.title_text, id="confirm-title")
            yield Label(self.message, id="confirm-message")
            with Horizontal(id="confirm-buttons"):
                yield Button("Yes (Y)", id="yes", variant="success")
                yield Button("No (N)", id="no", variant="error")

    def on_button_pressed(self, event: Button.Pressed) -> None:
        self.dismiss(event.button.id == "yes")

    def action_confirm_yes(self) -> None:
        self.dismiss(True)

    def action_confirm_no(self) -> None:
        self.dismiss(False)


class InputScreen(ModalScreen[str]):
    """A modal input dialog for text entry within the TUI."""

    CSS = """
    InputScreen {
        align: center middle;
    }

    #input-dialog {
        width: 70;
        height: auto;
        border: thick $primary;
        background: #0A0A23;
        padding: 1 2;
    }

    #input-title {
        width: 100%;
        text-align: center;
        text-style: bold;
        color: #00D8FF;
        margin-bottom: 1;
    }

    #input-message {
        width: 100%;
        text-align: center;
        color: #FFFFFF;
        margin-bottom: 1;
    }

    #input-field {
        width: 100%;
        margin-bottom: 1;
    }

    #input-buttons {
        width: 100%;
        align: center middle;
        margin-top: 1;
    }

    #input-buttons Button {
        margin: 0 2;
        min-width: 12;
    }
    """

    BINDINGS = [
        Binding("escape", "cancel", "Cancel"),
    ]

    def __init__(self, message: str, title: str = "Input Required", default: str = "", password: bool = False):
        super().__init__()
        self.message = message
        self.title_text = title
        self.default = default
        self.password = password

    def compose(self) -> ComposeResult:
        with Container(id="input-dialog"):
            yield Label(self.title_text, id="input-title")
            yield Label(self.message, id="input-message")
            yield Input(value=self.default, password=self.password, id="input-field")
            with Horizontal(id="input-buttons"):
                yield Button("OK (Enter)", id="ok", variant="success")
                yield Button("Cancel (Esc)", id="cancel", variant="error")

    def on_mount(self) -> None:
        self.query_one("#input-field", Input).focus()

    def on_button_pressed(self, event: Button.Pressed) -> None:
        if event.button.id == "ok":
            input_widget = self.query_one("#input-field", Input)
            self.dismiss(input_widget.value)
        else:
            self.dismiss(None)

    def on_input_submitted(self, event: Input.Submitted) -> None:
        self.dismiss(event.value)

    def action_cancel(self) -> None:
        self.dismiss(None)


class TUIStdinRedirector(io.TextIOBase):
    """
    Redirects stdin reads to the TUI's input mechanism.

    When code calls input() or sys.stdin.readline(), this redirector
    will request input via the TUI's modal dialog system.
    """

    def __init__(self, app_ref: List[Optional['SyncApp']]):
        super().__init__()
        self.app_ref = app_ref
        self._last_prompt = ""

    def readable(self) -> bool:
        return True

    def writable(self) -> bool:
        return False

    def readline(self, limit: int = -1) -> str:
        """Called by input() to read a line."""
        app = self.app_ref[0] if self.app_ref else None

        if app is None:
            raise EOFError("TUI not available for input")

        # Try to get input via TUI
        try:
            # Determine if this looks like an API key prompt
            is_password = "api" in self._last_prompt.lower() or "key" in self._last_prompt.lower()

            result = app.request_input(
                self._last_prompt if self._last_prompt else "Input required:",
                "Input Required",
                default="",
                password=is_password
            )

            # Reset the prompt for next time
            self._last_prompt = ""

            if result is None:
                raise EOFError("Input cancelled by user")
            return result + '\n'
        except Exception as e:
            self._last_prompt = ""
            if isinstance(e, EOFError):
                raise
            raise EOFError(f"TUI input failed: {e}")

    def read(self, size: int = -1) -> str:
        if size == 0:
            return ""
        return self.readline()

    def set_prompt(self, prompt: str) -> None:
        """Store the prompt for the next readline call."""
        self._last_prompt = prompt.strip()


class TUIStdoutWrapper(io.TextIOBase):
    """
    Wrapper for stdout that captures prompts written before input() calls.

    This allows us to detect when input() is about to be called and
    capture the prompt text to display in the TUI input modal.
    """

    def __init__(self, real_redirector: 'ThreadSafeRedirector', stdin_redirector: 'TUIStdinRedirector'):
        super().__init__()
        self.real_redirector = real_redirector
        self.stdin_redirector = stdin_redirector

    def write(self, s: str) -> int:
        # Capture potential prompts (text not ending in newline)
        if s and not s.endswith('\n'):
            self.stdin_redirector.set_prompt(s)
        return self.real_redirector.write(s)

    def flush(self) -> None:
        self.real_redirector.flush()

    @property
    def captured_logs(self) -> List[str]:
        return self.real_redirector.captured_logs


class ThreadSafeRedirector(io.TextIOBase):
    """
    Redirects writes to a Textual RichLog, handling ANSI codes and line buffering.
    """
    def __init__(self, app: App, log: RichLog):
        self.app = app
        self.log_widget = log
        self.buffer = ""
        # Heuristic pattern for standard logging timestamp (e.g., 2025-12-02 01:20:28,193)
        self.log_pattern = re.compile(r'^\d{4}-\d{2}-\d{2} \d{2}:\d{2}:\d{2}')
        self.captured_logs = [] # Store logs for debug

    def write(self, s: str) -> int:
        if not s:
            return 0

        self.buffer += s

        # Handle carriage return for in-place updates (progress bars)
        # When buffer has \r but no \n, it's an intermediate progress update
        # Keep only content after the last \r (ready for next update or final \n)
        if '\r' in self.buffer and '\n' not in self.buffer:
            self.buffer = self.buffer.rsplit('\r', 1)[-1]
            return len(s)

        # Process complete lines
        while '\n' in self.buffer:
            line, self.buffer = self.buffer.split('\n', 1)
            # Handle \r within line: keep only content after last \r
            if '\r' in line:
                line = line.rsplit('\r', 1)[-1]
            self.captured_logs.append(line)  # Capture processed line

            # Convert ANSI codes to Rich Text
            text = Text.from_ansi(line)

            # Check if the line looks like a log message and dim it
            # We strip ANSI codes for pattern matching to ensure the regex works
            plain_text = text.plain
            if self.log_pattern.match(plain_text):
                # Apply dim style to the whole text object
                # This layers 'dim' over existing styles (like colors)
                text.style = Style(dim=True)

            self.app.call_from_thread(self.log_widget.write, text)

        return len(s)

    def flush(self):
        # Write any remaining content in buffer
        if self.buffer:
            text = Text.from_ansi(self.buffer)
            if self.log_pattern.match(text.plain):
                text.style = Style(dim=True)
            self.app.call_from_thread(self.log_widget.write, text)
            self.buffer = ""


class SyncApp(App):
    def _reflow_log_widget(self, *, max_lines: int = 2000) -> None:
        """Reflow historical log lines so wrapping matches the current width.

        Textual/RichLog will repaint on resize, but it may not re-wrap already-added
        renderables. We keep a plain-text log buffer via redirector wrappers; on
        resize, clear and replay those lines.
        """
        if not hasattr(self, "log_widget") or self.log_widget is None:
            return

        # Prefer the redirector's captured logs when available; fall back to app property.
        try:
            lines = list(self.captured_logs)
        except Exception:
            lines = []

        if not lines:
            return

        # Bound replay to avoid excessive work on huge logs.
        if max_lines and len(lines) > max_lines:
            lines = lines[-max_lines:]

        # Clear and replay.
        try:
            self.log_widget.clear()
        except Exception:
            # If clear isn't available, do nothing.
            return

        log_pattern = re.compile(r'^\d{4}-\d{2}-\d{2} \d{2}:\d{2}:\d{2}')
        for line in lines:
            try:
                text = Text.from_ansi(line)
                if log_pattern.match(text.plain):
                    text.style = Style(dim=True)
                self.log_widget.write(text)
            except Exception:
                # Last resort: write raw.
                try:
                    self.log_widget.write(str(line))
                except Exception:
                    pass
    """Textual App for PDD Sync."""

    CSS = """
    Screen {
        background: #0A0A23; /* DEEP_NAVY */
    }

    #animation-container {
        height: auto;
        dock: top;
    }

    #progress-container {
        height: auto;
        padding: 0 1;
        display: none;
    }

    #progress-container.visible {
        display: block;
    }

    #progress-bar {
        width: 100%;
    }

    #log-container {
        height: 1fr;
        border: solid $primary;
        background: #0A0A23;
    }

    RichLog {
        background: #0A0A23;
        color: #00D8FF; /* ELECTRIC_CYAN */
        padding: 0 1;
    }
    """

    BINDINGS = [
        Binding("ctrl+c", "quit", "Quit"),
    ]

    def __init__(
        self,
        basename: str,
        budget: Optional[float],
        worker_func: Callable[[], Any],
        function_name_ref: List[str],
        cost_ref: List[float],
        prompt_path_ref: List[str],
        code_path_ref: List[str],
        example_path_ref: List[str],
        tests_path_ref: List[str],
        prompt_color_ref: List[str],
        code_color_ref: List[str],
        example_color_ref: List[str],
        tests_color_ref: List[str],
        stop_event: threading.Event,
        progress_callback_ref: Optional[List[Optional[Callable[[int, int], None]]]] = None,
        no_steer: bool = False,
    ):
        super().__init__()
        self.basename = basename
        self.budget = budget
        self.worker_func = worker_func

        # Shared state refs
        self.function_name_ref = function_name_ref
        self.cost_ref = cost_ref
        self.prompt_path_ref = prompt_path_ref
        self.code_path_ref = code_path_ref
        self.example_path_ref = example_path_ref
        self.tests_path_ref = tests_path_ref
        self.prompt_color_ref = prompt_color_ref
        self.code_color_ref = code_color_ref
        self.example_color_ref = example_color_ref
        self.tests_color_ref = tests_color_ref
        self.progress_callback_ref = progress_callback_ref

        self.stop_event = stop_event
        self.no_steer = no_steer

        # Internal animation state
        self.animation_state = AnimationState(basename, budget)

        # Result storage
        self.worker_result = None
        self.worker_exception = None

        # Confirmation mechanism for worker thread to request user input
        self._confirm_event = threading.Event()
        self._confirm_result = False
        self._confirm_message = ""
        self._confirm_title = ""

        # Input mechanism for worker thread to request text input
        self._input_event = threading.Event()
        self._input_result: Optional[str] = None
        self._input_message = ""
        self._input_title = ""
        self._input_default = ""
        self._input_password = False

        # Logo Animation State
        self.logo_phase = True
        self.logo_start_time = 0.0
        self.logo_expanded_init = False
        self.particles = []

        self.redirector = None # Will hold the redirector instance
        self._stdin_redirector = None  # Will hold stdin redirector

        # Track log widget width for proper text wrapping
        # Accounts for: log-container border (2), RichLog padding (2), scrollbar (2)
        self._log_width = 74  # Default fallback (80 - 6)
        # Minimum UI width used when clamping the layout to avoid overly narrow renders.
        self._min_ui_width = 80
        # _fixed_ui_width stores the frozen UI width that the app should render against.
        # It is set once based on the initial terminal size (respecting _min_ui_width)
        # and then reused for subsequent layout calculations. Keeping this width fixed
        # prevents resize-related rendering issues and reflow glitches in Textual/Rich
        # when the underlying terminal is resized while the app is running.
        self._fixed_ui_width: Optional[int] = None

        # Reference to self for stdin redirector (using list for mutability)
        self._app_ref: List[Optional['SyncApp']] = [None]

        # Choice mechanism for worker thread to request a selection
        self._choice_event = threading.Event()
        self._choice_result: Optional[str] = None
        self._choice_title = ""
        self._choice_prompt = ""
        self._choice_choices: list[str] = []
        self._choice_default = ""
        self._choice_timeout_s = 0.0

    @property
    def captured_logs(self) -> List[str]:
        if self.redirector:
            if hasattr(self.redirector, 'captured_logs'):
                return self.redirector.captured_logs
            elif hasattr(self.redirector, 'real_redirector'):
                return self.redirector.real_redirector.captured_logs
        return []

    def _update_progress(self, current: int, total: int) -> None:
        """Update the progress bar from the worker thread.

        Called by summarize_directory during auto-deps to show file processing progress.
        Uses call_from_thread to safely update the UI from the worker thread.
        """
        def _do_update():
            # Show progress container if hidden
            if "visible" not in self.progress_container.classes:
                self.progress_container.add_class("visible")

            # Update progress bar
            self.progress_bar.update(total=total, progress=current)

            # Hide when complete
            if current >= total:
                self.progress_container.remove_class("visible")

        self.call_from_thread(_do_update)

    def compose(self) -> ComposeResult:
        yield Container(Static(id="animation-view"), id="animation-container")
        yield Container(ProgressBar(id="progress-bar", show_eta=False), id="progress-container")
        yield Container(RichLog(highlight=True, markup=True, wrap=True, id="log"), id="log-container")

    def on_mount(self) -> None:
        global _ACTIVE_SYNC_APP
        _ACTIVE_SYNC_APP = self

        self.log_widget = self.query_one("#log", RichLog)
        self.progress_bar = self.query_one("#progress-bar", ProgressBar)
        self.progress_container = self.query_one("#progress-container", Container)

        # Set up progress callback if ref is available
        if self.progress_callback_ref is not None:
            self.progress_callback_ref[0] = self._update_progress
        self.animation_view = self.query_one("#animation-view", Static)

        # Initialize Logo Particles
        local_ascii_logo_art = logo_animation.ASCII_LOGO_ART
        if isinstance(local_ascii_logo_art, str):
            local_ascii_logo_art = local_ascii_logo_art.strip().splitlines()

        self.particles = logo_animation._parse_logo_art(local_ascii_logo_art)

        # Set initial styles and formation targets
        width = self.size.width if self.size.width > 0 else self._min_ui_width
        width = max(self._min_ui_width, int(width))
        self._fixed_ui_width = width
        height = 18  # Fixed animation height

        for p in self.particles:
            p.style = Style(color=logo_animation.ELECTRIC_CYAN)

        logo_target_positions = logo_animation._get_centered_logo_positions(
            self.particles, local_ascii_logo_art, width, height
        )

        for i, p in enumerate(self.particles):
            p.start_x = 0.0
            p.start_y = float(height - 1)
            p.current_x, p.current_y = p.start_x, p.start_y
            p.target_x, p.target_y = float(logo_target_positions[i][0]), float(logo_target_positions[i][1])

        self.logo_start_time = time.monotonic()

        # Start animation timer (20 FPS for smoother logo)
        self.set_interval(0.05, self.update_animation)

        # Calculate initial log width based on frozen UI width
        self._log_width = max(20, self._fixed_ui_width - 6)
        os.environ["COLUMNS"] = str(self._log_width)

        # Start worker
        self.run_worker_task()

    def on_resize(self, event) -> None:
        """Handle terminal resizes.

        Fixed-width mode: do not recompute animation/log widths. However, Textual can
        leave RichLog in a visually stale state after *horizontal* resizes until a
        later layout pass (often triggered by a vertical resize). Force an immediate
        layout + repaint so the bottom panel doesn't glitch.
        """
        try:
            # Recompute layout and repaint the screen.
            try:
                self.refresh(layout=True)
            except Exception:
                self.refresh()

            # Force the log widget to repaint at its new viewport size.
            if hasattr(self, "log_widget") and self.log_widget is not None:
                self.log_widget.refresh()
        except Exception:
            return

    @work(thread=True)
    def run_worker_task(self) -> None:
        """Runs the sync logic in a separate thread, capturing stdout/stderr/stdin."""

        # Set app reference for stdin redirector
        self._app_ref[0] = self

        # Save original environment values to restore later
        # This prevents subprocess from inheriting TUI-specific env vars
        original_force_color = os.environ.get("FORCE_COLOR")
        original_term = os.environ.get("TERM")
        original_columns = os.environ.get("COLUMNS")

        # Force Rich and other tools to output ANSI colors
        os.environ["FORCE_COLOR"] = "1"
        # Some tools check TERM
        os.environ["TERM"] = "xterm-256color"
        # Set COLUMNS so Rich Console/Panels render at log widget width, not terminal width
        # This must be set before any code imports/creates Rich Console objects
        os.environ["COLUMNS"] = str(self._log_width)

        # Capture stdout/stderr/stdin
        original_stdout = sys.stdout
        original_stderr = sys.stderr
        original_stdin = sys.stdin

        if isinstance(self, App):
            app_running = self.is_running
        else:
            app_running = False

        if app_running:
            # Create redirectors
            base_redirector = ThreadSafeRedirector(self, self.log_widget)
            self._stdin_redirector = TUIStdinRedirector(self._app_ref)

            # Wrap stdout to capture prompts for input() calls
            self.redirector = TUIStdoutWrapper(base_redirector, self._stdin_redirector)

            sys.stdout = self.redirector
            sys.stderr = base_redirector  # stderr doesn't need prompt capture
            sys.stdin = self._stdin_redirector
        else:
            # In tests / non-interactive contexts, the Textual loop isn't running.
            # Avoid redirectors that depend on call_from_thread / a running app.
            self.redirector = None
            self._stdin_redirector = None

        try:
            self.worker_result = self.worker_func()
        except EOFError as e:
            # Handle EOF from stdin redirector - input was needed but cancelled/failed
            self.worker_exception = e
            if app_running:
                self.call_from_thread(
                    self.log_widget.write,
                    f"[bold yellow]Input required but not provided: {e}[/bold yellow]\n"
                    "[dim]Hint: Ensure API keys are configured in environment or .env file[/dim]"
                )
            else:
                print(f"Input required but not provided: {e}", file=original_stderr)
            self.worker_result = {
                "success": False,
                "total_cost": 0.0,
                "model_name": "",
                "error": f"Input required: {e}",
                "operations_completed": [],
                "errors": [f"EOFError: {e}"]
            }
        except BaseException as e:
            self.worker_exception = e
            # Print to widget
            if app_running:
                self.call_from_thread(self.log_widget.write, f"[bold red]Error in sync worker: {e}[/bold red]")
            # Print to original stderr so it's visible after TUI closes
            print(f"\nError in sync worker thread: {type(e).__name__}: {e}", file=original_stderr)
            import traceback
            traceback.print_exc(file=original_stderr)

            # Create a failure result so the app returns something meaningful
            self.worker_result = {
                "success": False,
                "total_cost": 0.0,
                "model_name": "",
                "error": str(e),
                "operations_completed": [],
                "errors": [f"{type(e).__name__}: {e}"]
            }
        finally:
            if app_running:
                sys.stdout = original_stdout
                sys.stderr = original_stderr
                sys.stdin = original_stdin
            self._app_ref[0] = None

            # Restore original environment values
            # This is critical to prevent subprocess contamination
            if original_force_color is not None:
                os.environ["FORCE_COLOR"] = original_force_color
            elif "FORCE_COLOR" in os.environ:
                del os.environ["FORCE_COLOR"]

            if original_term is not None:
                os.environ["TERM"] = original_term
            elif "TERM" in os.environ:
                del os.environ["TERM"]

            if original_columns is not None:
                os.environ["COLUMNS"] = original_columns
            elif "COLUMNS" in os.environ:
                del os.environ["COLUMNS"]

            # Force flush any remaining buffer
            if app_running and self.redirector is not None:
                try:
                    if hasattr(self.redirector, 'flush'):
                        self.redirector.flush()
                except Exception:
                    pass
            try:
                self.call_from_thread(self.exit, result=self.worker_result)
            except RuntimeError:
                # In tests or other non-interactive contexts the Textual app may not be running.
                # Fall back to calling exit directly so worker cleanup doesn't crash.
                try:
                    self.exit(result=self.worker_result)
                except Exception:
                    pass

    def update_animation(self) -> None:
        """Updates the animation frame based on current shared state."""
        if self.stop_event.is_set():
            return

        # Render at a frozen UI width (determined at mount time), ignoring resizes.
        width = self._fixed_ui_width or self._min_ui_width

        # --- LOGO ANIMATION PHASE ---
        if self.logo_phase:
            current_time = time.monotonic()
            elapsed = current_time - self.logo_start_time

            formation_dur = logo_animation.LOGO_FORMATION_DURATION or 0.1
            hold_dur = logo_animation.LOGO_HOLD_DURATION or 0.1
            expand_dur = logo_animation.LOGO_TO_BOX_TRANSITION_DURATION or 0.1

            if elapsed < formation_dur:
                # Formation
                progress = elapsed / formation_dur
                for p in self.particles: p.update_progress(progress)
            elif elapsed < formation_dur + hold_dur:
                # Hold
                for p in self.particles: p.update_progress(1.0)
            elif elapsed < formation_dur + hold_dur + expand_dur:
                # Expansion
                if not self.logo_expanded_init:
                    box_targets = logo_animation._get_box_perimeter_positions(self.particles, width, 18)
                    for i, p in enumerate(self.particles):
                         p.set_new_transition(float(box_targets[i][0]), float(box_targets[i][1]))
                    self.logo_expanded_init = True

                expand_elapsed = elapsed - (formation_dur + hold_dur)
                progress = expand_elapsed / expand_dur
                for p in self.particles: p.update_progress(progress)
            else:
                # Logo animation done, switch to main UI
                self.logo_phase = False
                # Fall through to render main UI immediately

            if self.logo_phase:
                frame = logo_animation._render_particles_to_text(self.particles, width, 18)
                self.animation_view.update(frame)
                return

        # --- MAIN SYNC ANIMATION PHASE ---

        # Update state from refs
        current_func_name = self.function_name_ref[0] if self.function_name_ref else "checking"
        current_cost = self.cost_ref[0] if self.cost_ref else 0.0

        current_prompt_path = self.prompt_path_ref[0] if self.prompt_path_ref else ""
        current_code_path = self.code_path_ref[0] if self.code_path_ref else ""
        current_example_path = self.example_path_ref[0] if self.example_path_ref else ""
        current_tests_path = self.tests_path_ref[0] if self.tests_path_ref else ""

        self.animation_state.set_box_colors(
            self.prompt_color_ref[0] if self.prompt_color_ref else "",
            self.code_color_ref[0] if self.code_color_ref else "",
            self.example_color_ref[0] if self.example_color_ref else "",
            self.tests_color_ref[0] if self.tests_color_ref else ""
        )

        self.animation_state.update_dynamic_state(
            current_func_name, current_cost,
            current_prompt_path, current_code_path,
            current_example_path, current_tests_path
        )

        frame = _render_animation_frame(self.animation_state, width)
        self.animation_view.update(frame)

    def request_confirmation(self, message: str, title: str = "Confirmation Required") -> bool:
        """
        Request user confirmation from the worker thread.

        This method is thread-safe and can be called from the worker thread.
        It will block until the user responds to the modal dialog.

        Args:
            message: The confirmation message to display
            title: The title of the confirmation dialog

        Returns:
            True if user confirmed, False otherwise
        """
        self._confirm_event.clear()
        self._confirm_result = False
        self._confirm_message = message
        self._confirm_title = title

        def schedule_modal():
            """Called on main thread via call_from_thread."""
            # Create task to show modal - we're on the main thread with running event loop
            asyncio.create_task(self._show_confirm_modal_async())

        # Schedule on main thread using Textual's thread-safe mechanism
        self.call_from_thread(schedule_modal)

        # Block worker thread until user responds (with timeout to prevent infinite hang)
        if not self._confirm_event.wait(timeout=300):  # 5 minute timeout
            # Timeout - default to False (don't proceed)
            return False

        return self._confirm_result

    def request_choice(self, title: str, prompt: str, choices: list[str], default: str, *, timeout_s: float = DEFAULT_STEER_TIMEOUT_S) -> str:
        """Ask the user to choose from a list of options.

        Safe to call from non-UI threads.
        If the user provides no input for `timeout_s`, defaults to `default`.
        In headless mode, returns `default`.
        """
        if _is_headless_environment():
            return default

        self._choice_event.clear()
        self._choice_result = None
        self._choice_title = title
        self._choice_prompt = prompt
        self._choice_choices = list(choices)
        self._choice_default = default
        self._choice_timeout_s = float(timeout_s)

        def schedule_modal() -> None:
            asyncio.create_task(self._show_choice_modal_async())

        self.call_from_thread(schedule_modal)

        # Give the UI time to mount and the timeout to elapse; the screen itself
        # auto-dismisses at `timeout_s`, so we just need a safe cushion here.
        if not self._choice_event.wait(timeout=max(10.0, self._choice_timeout_s + 30.0)):
            return default

        return self._choice_result or default

    async def _show_choice_modal_async(self) -> None:
        """Async method to show the choice modal."""
        try:
            result = await self.push_screen_wait(
                ChoiceScreen(
                    self._choice_title,
                    self._choice_prompt,
                    self._choice_choices,
                    self._choice_default,
                    self._choice_timeout_s,
                )
            )
            self._choice_result = result
        except Exception as e:
            print(f"Choice modal error: {e}", file=sys.__stderr__)
            self._choice_result = self._choice_default
        finally:
            self._choice_event.set()


    def request_steering(self, recommended_op: str, reason: str, *, timeout_s: float = DEFAULT_STEER_TIMEOUT_S) -> tuple[str, bool]:
        """Return (chosen_operation, should_abort).

        In headless/CI mode, returns (recommended_op, False).
        """
        if _is_headless_environment():
            return recommended_op, False

        if self.no_steer:
            return recommended_op, False

        choices = [
            recommended_op,
            "generate",
            "example",
            "crash",
            "verify",
            "test",
            "test_extend",
            "fix",
            "update",
            "auto-deps",
            "abort",
        ]

        seen = set()
        deduped: list[str] = []
        for c in choices:
            if c not in seen:
                seen.add(c)
                deduped.append(c)

        title = "Sync steering"
        prompt = (
            f"Recommended: {recommended_op} ({reason})\nChoose next operation:"
            if reason else
            f"Recommended: {recommended_op}\nChoose next operation:"
        )

        chosen = self.request_choice(
            title=title,
            prompt=prompt,
            choices=deduped,
            default=recommended_op,
            timeout_s=timeout_s,
        )
        if chosen == "abort":
            return recommended_op, True
        return chosen, False

    async def _show_confirm_modal_async(self) -> None:
        """Async method to show the confirmation modal."""
        try:
            result = await self.push_screen_wait(
                ConfirmScreen(self._confirm_message, self._confirm_title)
            )
            self._confirm_result = result
        except Exception as e:
            # If modal fails, default to True to not block workflow
            print(f"Confirmation modal error: {e}", file=sys.__stderr__)
            self._confirm_result = True
        finally:
            self._confirm_event.set()

    def request_input(self, message: str, title: str = "Input Required",
                      default: str = "", password: bool = False) -> Optional[str]:
        """
        Request text input from the worker thread.

        This method is thread-safe and can be called from the worker thread.
        It will block until the user provides input or cancels.

        Args:
            message: The input prompt message
            title: The title of the input dialog
            default: Default value for the input field
            password: If True, mask the input (for passwords/API keys)

        Returns:
            The user's input string, or None if cancelled
        """
        self._input_event.clear()
        self._input_result = None
        self._input_message = message
        self._input_title = title
        self._input_default = default
        self._input_password = password

        def schedule_modal():
            """Called on main thread via call_from_thread."""
            asyncio.create_task(self._show_input_modal_async())

        # Schedule on main thread
        self.call_from_thread(schedule_modal)

        # Block worker thread until user responds (with timeout)
        if not self._input_event.wait(timeout=300):  # 5 minute timeout
            return None

        return self._input_result

    async def _show_input_modal_async(self) -> None:
        """Async method to show the input modal."""
        try:
            result = await self.push_screen_wait(
                InputScreen(
                    self._input_message,
                    self._input_title,
                    self._input_default,
                    self._input_password
                )
            )
            self._input_result = result
        except Exception as e:
            print(f"Input modal error: {e}", file=sys.__stderr__)
            self._input_result = None
        finally:
            self._input_event.set()


def show_exit_animation():
    """Shows the exit logo animation."""
    from .logo_animation import ASCII_LOGO_ART, ELECTRIC_CYAN, DEEP_NAVY

    logo_lines = ASCII_LOGO_ART
    if isinstance(logo_lines, str):
        logo_lines = logo_lines.strip().splitlines()

    # Calculate dimensions from raw lines to ensure panel fits
    max_width = max(len(line) for line in logo_lines) if logo_lines else 0

    console = Console()
    console.clear()

    # Join lines as-is to preserve ASCII shape
    logo_content = "\n".join(logo_lines)

    logo_panel = Panel(
        Text(logo_content, justify="left"), # Ensure left alignment within the block
        style=f"bold {ELECTRIC_CYAN} on {DEEP_NAVY}",
        border_style=ELECTRIC_CYAN,
        padding=(1, 4), # Add padding (top/bottom, right/left) inside the border
        expand=False # Shrink panel to fit content
    )

    console.print(Align.center(logo_panel))
    time.sleep(1.0)
    console.clear()

def maybe_steer_operation(
    operation: str,
    reason: str = "",
    app: Optional["SyncApp"] = None,
    quiet: bool = False,
    skip_tests: bool = False,
    skip_verify: bool = False,
    *,
    timeout_s: float = DEFAULT_STEER_TIMEOUT_S,
    **kwargs,
) -> tuple[str, bool]:
    """Adapter used by sync_orchestration.py to support user steering.

    Returns:
        (chosen_operation, should_abort)

    Notes:
    - In headless/CI/non-TTY runs we do not prompt.
    - `quiet`, `skip_tests`, and `skip_verify` are accepted for compatibility.
    - Extra kwargs are accepted so older/newer callers don't crash.
    """
    if quiet or _is_headless_environment():
        return operation, False

    disallowed = set()
    if skip_tests:
        disallowed.update({"test", "test_extend", "fix"})
    if skip_verify:
        disallowed.add("verify")

    active_app = app or _ACTIVE_SYNC_APP
    if active_app is None:
        return operation, False

    chosen, should_abort = active_app.request_steering(operation, reason, timeout_s=timeout_s)
    if chosen in disallowed:
        return operation, False

    return chosen, should_abort