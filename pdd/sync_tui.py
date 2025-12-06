import threading
import sys
import os
from typing import List, Optional, Callable, Any
import io

from textual.app import App, ComposeResult
from textual.screen import ModalScreen
from textual.widgets import Static, RichLog, Button, Label
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
        
        # Process complete lines
        while '\n' in self.buffer:
            line, self.buffer = self.buffer.split('\n', 1)
            self.captured_logs.append(line) # Capture raw line
            
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
    """Textual App for PDD Sync."""

    CSS = """
    Screen {
        background: #0A0A23; /* DEEP_NAVY */
    }
    
    #animation-container {
        height: auto;
        dock: top;
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
        
        self.stop_event = stop_event
        
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

        # Logo Animation State
        self.logo_phase = True
        self.logo_start_time = 0.0
        self.logo_expanded_init = False
        self.particles = []

        self.redirector = None # Will hold the redirector instance

        # Track log widget width for proper text wrapping
        # Accounts for: log-container border (2), RichLog padding (2), scrollbar (2)
        self._log_width = 74  # Default fallback (80 - 6)

    @property
    def captured_logs(self) -> List[str]:
        if self.redirector:
            return self.redirector.captured_logs
        return []

    def compose(self) -> ComposeResult:
        yield Container(Static(id="animation-view"), id="animation-container")
        yield Container(RichLog(highlight=True, markup=True, wrap=True, id="log"), id="log-container")

    def on_mount(self) -> None:
        self.log_widget = self.query_one("#log", RichLog)
        self.animation_view = self.query_one("#animation-view", Static)
        
        # Initialize Logo Particles
        local_ascii_logo_art = logo_animation.ASCII_LOGO_ART
        if isinstance(local_ascii_logo_art, str):
            local_ascii_logo_art = local_ascii_logo_art.strip().splitlines()
        
        self.particles = logo_animation._parse_logo_art(local_ascii_logo_art)
        
        # Set initial styles and formation targets
        width = self.size.width if self.size.width > 0 else 80
        height = 18 # Fixed animation height
        
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

        # Calculate initial log width based on current size
        if self.size.width > 0:
            self._log_width = max(20, self.size.width - 6)

        # Start worker
        self.run_worker_task()

    @work(thread=True)
    def run_worker_task(self) -> None:
        """Runs the sync logic in a separate thread, capturing stdout/stderr."""

        # Force Rich and other tools to output ANSI colors
        os.environ["FORCE_COLOR"] = "1"
        # Some tools check TERM
        os.environ["TERM"] = "xterm-256color"
        # Set COLUMNS so Rich Console/Panels render at log widget width, not terminal width
        # This must be set before any code imports/creates Rich Console objects
        os.environ["COLUMNS"] = str(self._log_width)

        # Capture stdout/stderr
        original_stdout = sys.stdout
        original_stderr = sys.stderr
        
        self.redirector = ThreadSafeRedirector(self, self.log_widget)
        
        sys.stdout = self.redirector
        sys.stderr = self.redirector
        
        try:
            self.worker_result = self.worker_func()
        except BaseException as e:
            self.worker_exception = e
            # Print to widget
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
            sys.stdout = original_stdout
            sys.stderr = original_stderr
            # Force flush any remaining buffer
            try:
                self.redirector.flush()
            except Exception:
                pass
            self.call_from_thread(self.exit, result=self.worker_result)

    def update_animation(self) -> None:
        """Updates the animation frame based on current shared state."""
        if self.stop_event.is_set():
            return

        # We need the width of the app/screen.
        width = self.size.width
        if width == 0: # Not ready yet
            width = 80

        # Update log width and COLUMNS env var for resize handling
        # This ensures Rich Panels created after resize use the new width
        # Offset of 6 accounts for: border (2), padding (2), scrollbar (2)
        new_log_width = max(20, width - 6)
        if new_log_width != self._log_width:
            self._log_width = new_log_width
            os.environ["COLUMNS"] = str(self._log_width)

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
        import asyncio

        self._confirm_event.clear()

        async def show_and_wait():
            """Async function to show the modal and wait for result."""
            try:
                result = await self.push_screen_wait(
                    ConfirmScreen(message, title)
                )
                self._confirm_result = result
            except Exception as e:
                # If modal fails, default to True to not block
                import sys
                print(f"Confirmation modal error: {e}", file=sys.__stderr__)
                self._confirm_result = True
            finally:
                self._confirm_event.set()

        # Schedule the coroutine directly on the app's event loop from this thread
        # using run_coroutine_threadsafe which is designed for cross-thread scheduling
        try:
            loop = self._loop  # Textual App exposes the event loop
            asyncio.run_coroutine_threadsafe(show_and_wait(), loop)
        except Exception as e:
            # Fallback if scheduling fails
            import sys
            print(f"Failed to schedule confirmation modal: {e}", file=sys.__stderr__)
            self._confirm_result = True
            self._confirm_event.set()

        # Block worker thread until user responds
        self._confirm_event.wait()
        return self._confirm_result


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

