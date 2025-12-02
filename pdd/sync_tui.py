import threading
import sys
from typing import List, Optional, Callable, Any
import io

from textual.app import App, ComposeResult
from textual.widgets import Static, RichLog
from textual.containers import Vertical, Container
from textual.binding import Binding
from textual.worker import Worker
from textual import work

from rich.console import Console
from rich.panel import Panel
from rich.align import Align
from rich.text import Text

# Reuse existing animation logic
from .sync_animation import AnimationState, _render_animation_frame, DEEP_NAVY, ELECTRIC_CYAN

class StdoutRedirector(io.TextIOBase):
    """Redirects writes to a Textual RichLog."""
    def __init__(self, log_widget: RichLog):
        self.log_widget = log_widget
        self.buffer = ""

    def write(self, s: str) -> int:
        self.log_widget.write(s)
        return len(s)
    
    def flush(self):
        pass

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

    def compose(self) -> ComposeResult:
        yield Container(Static(id="animation-view"), id="animation-container")
        yield Container(RichLog(highlight=True, markup=True, wrap=True, id="log"), id="log-container")

    def on_mount(self) -> None:
        self.log_widget = self.query_one("#log", RichLog)
        self.animation_view = self.query_one("#animation-view", Static)
        
        # Start animation timer (10 FPS)
        self.set_interval(0.1, self.update_animation)
        
        # Start worker
        self.run_worker_task()

    @work(thread=True)
    def run_worker_task(self) -> None:
        """Runs the sync logic in a separate thread, capturing stdout/stderr."""
        
        # Capture stdout/stderr
        original_stdout = sys.stdout
        original_stderr = sys.stderr
        
        # We need to use call_from_thread to safely write to widget from this thread
        # But Textual's RichLog.write is thread-safe-ish if scheduled? 
        # Better to use a custom redirector that schedules the write.
        
        class ThreadSafeRedirector(io.TextIOBase):
            def __init__(self, app: App, log: RichLog):
                self.app = app
                self.log = log
            def write(self, s: str):
                if s:
                    # Remove trailing newlines if any, as RichLog adds them or handles them?
                    # RichLog.write appends a line or content. 
                    # If we get partial writes, it might look weird.
                    # Let's just pass it through.
                    self.app.call_from_thread(self.log.write, s)
                return len(s)
            def flush(self): pass

        redirector = ThreadSafeRedirector(self, self.log_widget)
        
        sys.stdout = redirector
        sys.stderr = redirector
        
        try:
            self.worker_result = self.worker_func()
        except Exception as e:
            self.worker_exception = e
            self.app.call_from_thread(self.log_widget.write, f"[bold red]Error in sync worker: {e}[/bold red]")
        finally:
            sys.stdout = original_stdout
            sys.stderr = original_stderr
            self.app.call_from_thread(self.exit, result=self.worker_result)

    def update_animation(self) -> None:
        """Updates the animation frame based on current shared state."""
        if self.stop_event.is_set():
            return

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
        
        # Render frame
        # We need the width of the app/screen.
        width = self.size.width
        if width == 0: # Not ready yet
            width = 80
            
        # Render the frame using the existing function
        # Note: _render_animation_frame returns a Panel. 
        # We might need to adjust the height or style for Textual integration.
        # The function _render_animation_frame creates a panel with fixed height ANIMATION_BOX_HEIGHT (18).
        # That should be fine.
        
        frame = _render_animation_frame(self.animation_state, width)
        self.animation_view.update(frame)

