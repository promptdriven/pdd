import threading
import sys
import os
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
import time

# Reuse existing animation logic
from .sync_animation import AnimationState, _render_animation_frame, DEEP_NAVY, ELECTRIC_CYAN
from . import logo_animation
from rich.style import Style

class ThreadSafeRedirector(io.TextIOBase):
    """
    Redirects writes to a Textual RichLog, handling ANSI codes and line buffering.
    """
    def __init__(self, app: App, log: RichLog):
        self.app = app
        self.log = log
        self.buffer = ""

    def write(self, s: str) -> int:
        if not s:
            return 0
            
        self.buffer += s
        
        # Process complete lines
        while '\n' in self.buffer:
            line, self.buffer = self.buffer.split('\n', 1)
            # Convert ANSI codes to Rich Text
            text = Text.from_ansi(line)
            self.app.call_from_thread(self.log.write, text)
            
        return len(s)
    
    def flush(self):
        # Write any remaining content in buffer
        if self.buffer:
            text = Text.from_ansi(self.buffer)
            self.app.call_from_thread(self.log.write, text)
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
        
        # Logo Animation State
        self.logo_phase = True
        self.logo_start_time = 0.0
        self.logo_expanded_init = False
        self.particles = []

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
        
        # Start worker
        self.run_worker_task()

    @work(thread=True)
    def run_worker_task(self) -> None:
        """Runs the sync logic in a separate thread, capturing stdout/stderr."""
        
        # Force Rich and other tools to output ANSI colors
        os.environ["FORCE_COLOR"] = "1"
        # Some tools check TERM
        os.environ["TERM"] = "xterm-256color"
        
        # Capture stdout/stderr
        original_stdout = sys.stdout
        original_stderr = sys.stderr
        
        redirector = ThreadSafeRedirector(self, self.log_widget)
        
        sys.stdout = redirector
        sys.stderr = redirector
        
        try:
            self.worker_result = self.worker_func()
        except BaseException as e:
            self.worker_exception = e
            # Print to widget
            self.app.call_from_thread(self.log_widget.write, f"[bold red]Error in sync worker: {e}[/bold red]")
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
                redirector.flush()
            except Exception:
                pass
            self.app.call_from_thread(self.exit, result=self.worker_result)

    def update_animation(self) -> None:
        """Updates the animation frame based on current shared state."""
        if self.stop_event.is_set():
            return

        # We need the width of the app/screen.
        width = self.size.width
        if width == 0: # Not ready yet
            width = 80

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

