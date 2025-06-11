# pdd/logo_animation.py
import time
import threading
import math
from typing import List, Tuple, Optional
from dataclasses import dataclass, field

from rich.console import Console
from rich.live import Live
from rich.text import Text
from rich.style import Style

# Attempt to import constants from the package structure
# These will be mocked in the __main__ block for direct execution testing
try:
    from . import (
        ELECTRIC_CYAN, DEEP_NAVY,
        LOGO_FORMATION_DURATION, LOGO_TO_BOX_TRANSITION_DURATION,
        EXPANDED_BOX_HEIGHT, ANIMATION_FRAME_RATE, ASCII_LOGO_ART,
        DEFAULT_TIME as LOGO_HOLD_DURATION  # Use DEFAULT_TIME for hold duration
    )
except ImportError:
    # Fallback for direct execution or if constants are not yet in __init__.py
    # This section will be overridden by __main__ for testing
    ELECTRIC_CYAN = "#00D8FF"
    DEEP_NAVY = "#0A0A23"
    LOGO_FORMATION_DURATION = 1.5
    LOGO_HOLD_DURATION = 1.0
    LOGO_TO_BOX_TRANSITION_DURATION = 1.5
    EXPANDED_BOX_HEIGHT = 18
    ANIMATION_FRAME_RATE = 20
    ASCII_LOGO_ART = """
  +xxxxxxxxxxxxxxx+
xxxxxxxxxxxxxxxxxxxxx+
xxx                 +xx+
xxx      x+           xx+
xxx        x+         xxx
xxx         x+        xx+
xxx        x+         xx+
xxx      x+          xxx
xxx                +xx+ 
xxx     +xxxxxxxxxxx+
xxx   +xx+
xxx  +xx+
xxx+xx+
xxxx+
xx+
""".strip().splitlines()


@dataclass
class AnimatedParticle:
    """Represents a single character in the animated logo."""
    char: str
    orig_logo_x: int  # Original relative X in ASCII_LOGO_ART
    orig_logo_y: int  # Original relative Y in ASCII_LOGO_ART

    start_x: float = 0.0
    start_y: float = 0.0
    current_x: float = 0.0
    current_y: float = 0.0
    target_x: float = 0.0
    target_y: float = 0.0

    style: Style = field(default_factory=lambda: Style(color=ELECTRIC_CYAN))
    visible: bool = True

    def update_progress(self, progress: float):
        """Updates current_x, current_y based on linear interpolation."""
        self.current_x = self.start_x + (self.target_x - self.start_x) * progress
        self.current_y = self.start_y + (self.target_y - self.start_y) * progress

    def set_new_transition(self, new_target_x: float, new_target_y: float):
        """Sets the current position as the start for a new transition."""
        self.start_x = self.current_x
        self.start_y = self.current_y
        self.target_x = new_target_x
        self.target_y = new_target_y

_stop_animation_event = threading.Event()
_animation_thread: Optional[threading.Thread] = None

def _parse_logo_art(logo_art_lines: Optional[List[str]]) -> List[AnimatedParticle]:
    """Converts ASCII art strings into a list of AnimatedParticle objects."""
    if logo_art_lines is None: # Handle None input gracefully
        return []
    particles: List[AnimatedParticle] = []
    for y, line in enumerate(logo_art_lines):
        for x, char_val in enumerate(line):
            if char_val != ' ': # Only animate non-space characters
                particles.append(AnimatedParticle(char=char_val, orig_logo_x=x, orig_logo_y=y))
    return particles

def _get_centered_logo_positions(
    particles: List[AnimatedParticle],
    logo_art_lines: List[str], # Assumes logo_art_lines is not None here due to checks before calling
    console_width: int,
    console_height: int
) -> List[Tuple[int, int]]:
    """Calculates target positions for particles to form the centered logo."""
    if not logo_art_lines: return [(0,0)] * len(particles) # Should not happen if particles exist
    logo_width = max(len(line) for line in logo_art_lines) if logo_art_lines else 0
    logo_height = len(logo_art_lines)

    offset_x = (console_width - logo_width) // 2
    offset_y = (console_height - logo_height) // 2

    target_positions: List[Tuple[int,int]] = []
    for p in particles:
        target_positions.append((p.orig_logo_x + offset_x, p.orig_logo_y + offset_y))
    return target_positions

def _get_box_perimeter_positions(
    particles: List[AnimatedParticle],
    console_width: int,
    console_height: int
) -> List[Tuple[int, int]]:
    """Calculates target positions for particles on the perimeter of an expanded box."""
    actual_box_height = min(EXPANDED_BOX_HEIGHT, console_height)
    actual_box_width = max(1, console_width) # Ensure width is at least 1

    box_start_y = (console_height - actual_box_height) // 2
    box_start_x = 0

    perimeter_points: List[Tuple[int, int]] = []
    # Top edge
    for x in range(actual_box_width):
        perimeter_points.append((box_start_x + x, box_start_y))
    # Right edge (excluding corners if covered)
    if actual_box_height > 1:
        for y in range(1, actual_box_height - 1):
            perimeter_points.append((box_start_x + actual_box_width - 1, box_start_y + y))
    # Bottom edge (including corners if not covered)
    if actual_box_height > 1:
        for x in range(actual_box_width - 1, -1, -1):
            perimeter_points.append((box_start_x + x, box_start_y + actual_box_height - 1))
    # Left edge (excluding corners if covered)
    if actual_box_width > 1 and actual_box_height > 2:
        for y in range(actual_box_height - 2, 0, -1):
            perimeter_points.append((box_start_x, box_start_y + y))
    
    if not perimeter_points: # Fallback for very small console
        perimeter_points.append((box_start_x, box_start_y))

    num_particles = len(particles)
    target_positions: List[Tuple[int,int]] = []
    if not num_particles: return []

    for i in range(num_particles):
        # Distribute particles along the perimeter
        idx = math.floor(i * (len(perimeter_points) / num_particles))
        target_positions.append(perimeter_points[idx % len(perimeter_points)])
    return target_positions

def _render_particles_to_text(
    particles: List[AnimatedParticle],
    console_width: int,
    console_height: int = 18 # This argument is console_height for rendering logic
) -> Text:
    """Renders particles onto a Rich Text object for display with fixed 18-line height."""
    # Use fixed height to match sync_animation.py and prompt requirement
    fixed_render_height = 18 # Explicitly use 18 for rendering grid
    
    # Initialize Text with background color for fixed height
    text = Text(style=Style(bgcolor=DEEP_NAVY))
    
    # Create a 2D grid for characters and their styles
    char_grid = [[' ' for _ in range(console_width)] for _ in range(fixed_render_height)]
    # Base style for empty cells (background color, foreground matches background to be "invisible")
    base_style = Style(color=DEEP_NAVY, bgcolor=DEEP_NAVY)
    style_map = [[base_style for _ in range(console_width)] for _ in range(fixed_render_height)]

    # Style for particles (foreground color, global background)
    particle_render_style = Style(bgcolor=DEEP_NAVY)

    # Place particles onto the grid
    for p in particles:
        if p.visible:
            x, y = int(round(p.current_x)), int(round(p.current_y))
            if 0 <= y < fixed_render_height and 0 <= x < console_width:
                char_grid[y][x] = p.char
                style_map[y][x] = p.style + particle_render_style

    # Assemble the Text object row by row, optimizing for style runs
    for r_idx in range(fixed_render_height):
        current_run_chars: List[str] = []
        current_run_style: Optional[Style] = None
        
        for c_idx in range(console_width):
            char_val = char_grid[r_idx][c_idx]
            style_val = style_map[r_idx][c_idx]

            if current_run_style is None: # Start of a new run
                current_run_chars.append(char_val)
                current_run_style = style_val
            elif style_val == current_run_style: # Continue current run
                current_run_chars.append(char_val)
            else: # Style changed, finalize previous run and start new
                if current_run_style is not None: # Should always be true here
                    text.append("".join(current_run_chars), current_run_style)
                current_run_chars = [char_val]
                current_run_style = style_val
        
        # Append any remaining run from the row
        if current_run_chars and current_run_style is not None:
            text.append("".join(current_run_chars), current_run_style)
        
        if r_idx < fixed_render_height - 1:
            text.append("\n") # Add newline between rows
            
    return text

def _animation_loop(console: Console):
    """Main loop for the animation, running in a separate thread."""
    effective_frame_rate = max(1, ANIMATION_FRAME_RATE) # Ensure positive frame rate
    frame_duration = 1.0 / effective_frame_rate

    # Ensure ASCII_LOGO_ART is a list of strings, or handle if it's None (via _parse_logo_art)
    local_ascii_logo_art: Optional[List[str]] = ASCII_LOGO_ART
    if isinstance(local_ascii_logo_art, str):
        local_ascii_logo_art = local_ascii_logo_art.strip().splitlines()
    
    particles = _parse_logo_art(local_ascii_logo_art)
    if not particles: return # No particles to animate (handles None or empty art)

    # All subsequent uses of local_ascii_logo_art can assume it's List[str]
    # because if it were None, `particles` would be empty and we'd have returned.
    # However, to satisfy type checkers if they can't infer this, an explicit assertion or check
    # might be needed if local_ascii_logo_art is directly used later and needs to be List[str].
    # For _get_centered_logo_positions, it's passed, and that function expects List[str].
    # Let's ensure it's not None before passing if type hints are strict.
    # Given the logic, if particles is not empty, local_ascii_logo_art must have been a non-empty List[str].
    # If local_ascii_logo_art was None, particles is [], loop returns.
    # If local_ascii_logo_art was [], particles is [], loop returns.
    # So, if we reach here, local_ascii_logo_art must be a non-empty List[str].
    
    # The console height for animation logic is fixed at 18 lines as per prompt.
    animation_console_height = 18 
    console_width = console.width # Use actual console width
    
    # Set initial style for particles (foreground color)
    for p in particles:
        p.style = Style(color=ELECTRIC_CYAN)

    # Stage 1: Formation - Particles travel from bottom-left to form logo
    # We know local_ascii_logo_art is List[str] here if particles is not empty.
    logo_target_positions = _get_centered_logo_positions(particles, local_ascii_logo_art, console_width, animation_console_height)
    for i, p in enumerate(particles):
        p.start_x = 0.0  # Start at bottom-left
        p.start_y = float(animation_console_height - 1)
        p.current_x, p.current_y = p.start_x, p.start_y
        p.target_x, p.target_y = float(logo_target_positions[i][0]), float(logo_target_positions[i][1])

    with Live(console=console, refresh_per_second=effective_frame_rate, transient=True, screen=True) as live:
        # Animation Stage 1: Formation
        stage_duration = LOGO_FORMATION_DURATION or 0.1 # Ensure non-zero
        stage_start_time = time.monotonic()
        while not _stop_animation_event.is_set():
            elapsed = time.monotonic() - stage_start_time
            progress = min(elapsed / stage_duration, 1.0) if stage_duration > 0 else 1.0

            for p_obj in particles: p_obj.update_progress(progress)
            live.update(_render_particles_to_text(particles, console_width, animation_console_height))

            if progress >= 1.0: break
            if _stop_animation_event.wait(frame_duration): break
        
        if _stop_animation_event.is_set(): return

        # Hold Stage: Display formed logo
        hold_duration = LOGO_HOLD_DURATION or 0.1 # Ensure non-zero
        hold_start_time = time.monotonic()
        while not _stop_animation_event.is_set():
            if time.monotonic() - hold_start_time >= hold_duration: break
            live.update(_render_particles_to_text(particles, console_width, animation_console_height)) # Keep rendering
            if _stop_animation_event.wait(frame_duration): break
        
        if _stop_animation_event.is_set(): return

        # Animation Stage 2: Expansion to Box
        # _get_box_perimeter_positions uses console.height (from the console object) for its logic,
        # but the prompt specifies the box should be 18 lines tall.
        # The EXPANDED_BOX_HEIGHT constant is 18.
        # _get_box_perimeter_positions uses min(EXPANDED_BOX_HEIGHT, console_height_arg)
        # We should pass animation_console_height (18) to ensure the box logic aims for 18 lines.
        box_target_positions = _get_box_perimeter_positions(particles, console_width, animation_console_height)
        for i, p_obj in enumerate(particles):
            p_obj.set_new_transition(float(box_target_positions[i][0]), float(box_target_positions[i][1]))

        stage_duration = LOGO_TO_BOX_TRANSITION_DURATION or 0.1 # Ensure non-zero
        stage_start_time = time.monotonic()
        while not _stop_animation_event.is_set():
            elapsed = time.monotonic() - stage_start_time
            progress = min(elapsed / stage_duration, 1.0) if stage_duration > 0 else 1.0

            for p_obj in particles: p_obj.update_progress(progress)
            live.update(_render_particles_to_text(particles, console_width, animation_console_height))

            if progress >= 1.0: break
            if _stop_animation_event.wait(frame_duration): break
        
        # By removing the final 'while' loop that was here, the 'with Live(...)'
        # context will now properly exit, allowing other terminal output to be displayed.


def start_logo_animation():
    """Starts the logo animation in a separate daemon thread."""
    global _animation_thread
    if _animation_thread and _animation_thread.is_alive():
        return # Animation already running

    _stop_animation_event.clear()
    # The Console instance created here will have its own width/height.
    # _animation_loop uses console.width but hardcodes its internal animation_console_height to 18.
    console = Console(color_system="truecolor") 
    
    _animation_thread = threading.Thread(target=_animation_loop, args=(console,), daemon=True)
    _animation_thread.start()

def stop_logo_animation():
    """Signals the animation thread to stop and waits for it to terminate."""
    global _animation_thread
    _stop_animation_event.set()
    if _animation_thread and _animation_thread.is_alive():
        # Calculate a reasonable join timeout based on animation durations
        # Use max(0.1, ...) for durations to avoid issues if they are 0 or None
        timeout = (max(0.1, LOGO_FORMATION_DURATION or 0.1) +
                   max(0.1, LOGO_HOLD_DURATION or 0.1) +
                   max(0.1, LOGO_TO_BOX_TRANSITION_DURATION or 0.1) +
                   2.0) # Add a buffer
        _animation_thread.join(timeout=max(0.1, timeout)) # Ensure timeout is positive
    _animation_thread = None

# run_logo_animation_inline is not part of the primary API being tested by unit tests,
# but for completeness, ensure its logic for console_height is consistent if it were used.
# It currently uses `console_height = 18` which is consistent.
def run_logo_animation_inline(console: Console, stop_event: threading.Event):
    """Runs the logo animation inline without screen=True to avoid conflicts."""
    effective_frame_rate = max(1, ANIMATION_FRAME_RATE)
    frame_duration = 1.0 / effective_frame_rate

    local_ascii_logo_art: Optional[List[str]] = ASCII_LOGO_ART
    if isinstance(local_ascii_logo_art, str):
        local_ascii_logo_art = local_ascii_logo_art.strip().splitlines()
    
    particles = _parse_logo_art(local_ascii_logo_art)
    if not particles: 
        return

    animation_console_height = 18 # Fixed height for animation logic
    console_width = console.width
    
    for p in particles:
        p.style = Style(color=ELECTRIC_CYAN)

    logo_target_positions = _get_centered_logo_positions(particles, local_ascii_logo_art, console_width, animation_console_height)
    for i, p in enumerate(particles):
        p.start_x = 0.0
        p.start_y = float(animation_console_height - 1)
        p.current_x, p.current_y = p.start_x, p.start_y
        p.target_x, p.target_y = float(logo_target_positions[i][0]), float(logo_target_positions[i][1])

    with Live(console=console, refresh_per_second=effective_frame_rate, transient=True, screen=True) as live:
        stage_duration = LOGO_FORMATION_DURATION or 0.1
        stage_start_time = time.monotonic()
        while not stop_event.is_set():
            elapsed = time.monotonic() - stage_start_time
            progress = min(elapsed / stage_duration, 1.0) if stage_duration > 0 else 1.0
            for p_obj in particles: p_obj.update_progress(progress)
            live.update(_render_particles_to_text(particles, console_width, animation_console_height))
            if progress >= 1.0: break
            if stop_event.wait(frame_duration): break
        
        if stop_event.is_set(): return

        hold_duration = LOGO_HOLD_DURATION or 0.1
        hold_start_time = time.monotonic()
        while not stop_event.is_set():
            if time.monotonic() - hold_start_time >= hold_duration: break
            live.update(_render_particles_to_text(particles, console_width, animation_console_height))
            if stop_event.wait(frame_duration): break
        
        if stop_event.is_set(): return

        box_target_positions = _get_box_perimeter_positions(particles, console_width, animation_console_height)
        for i, p_obj in enumerate(particles):
            p_obj.set_new_transition(float(box_target_positions[i][0]), float(box_target_positions[i][1]))

        stage_duration = LOGO_TO_BOX_TRANSITION_DURATION or 0.1
        stage_start_time = time.monotonic()
        while not stop_event.is_set():
            elapsed = time.monotonic() - stage_start_time
            progress = min(elapsed / stage_duration, 1.0) if stage_duration > 0 else 1.0
            for p_obj in particles: p_obj.update_progress(progress)
            live.update(_render_particles_to_text(particles, console_width, animation_console_height))
            if progress >= 1.0: break
            if stop_event.wait(frame_duration): break
        
        # By removing the final 'while' loop that was here, the 'with Live(...)'
        # context will now properly exit.

# Main block for testing the animation directly
if __name__ == "__main__":
    # Mock constants for direct testing if they weren't imported (e.g. running file directly)
    mock_constants = {
        "ELECTRIC_CYAN": "#00D8FF", "DEEP_NAVY": "#0A0A23",
        "LOGO_FORMATION_DURATION": 1.5, "LOGO_HOLD_DURATION": 1.0,
        "LOGO_TO_BOX_TRANSITION_DURATION": 1.5, "EXPANDED_BOX_HEIGHT": 18,
        "ANIMATION_FRAME_RATE": 20,
        "ASCII_LOGO_ART": """
  +xxxxxxxxxxxxxxx+
xxxxxxxxxxxxxxxxxxxxx+
xxx                 +xx+
xxx      x+           xx+
xxx        x+         xxx
xxx         x+        xx+
xxx        x+         xx+
xxx      x+          xxx
xxx                +xx+ 
xxx     +xxxxxxxxxxx+
xxx   +xx+
xxx  +xx+
xxx+xx+
xxxx+
xx+
""".strip().splitlines()
    }
    # Apply mocks if constants are not defined or are None (e.g., due to failed import)
    for const_name, const_val in mock_constants.items():
        if const_name not in globals() or globals()[const_name] is None:
            globals()[const_name] = const_val
    
    # Special handling for LOGO_HOLD_DURATION if DEFAULT_TIME logic was intended
    if 'LOGO_HOLD_DURATION' not in globals() or globals()['LOGO_HOLD_DURATION'] is None:
        # If 'DEFAULT_TIME' was meant to be imported as LOGO_HOLD_DURATION and failed
        globals()['LOGO_HOLD_DURATION'] = mock_constants['LOGO_HOLD_DURATION']


    print("Starting logo animation test (Press Ctrl+C to stop)...")
    print(f"  Formation: {globals()['LOGO_FORMATION_DURATION']}s, Hold: {globals()['LOGO_HOLD_DURATION']}s, Expansion: {globals()['LOGO_TO_BOX_TRANSITION_DURATION']}s")
    
    start_logo_animation()
    try:
        # Calculate total expected animation time for the sleep duration
        total_anim_duration = (globals().get('LOGO_FORMATION_DURATION', 0) or 0) + \
                              (globals().get('LOGO_HOLD_DURATION', 0) or 0) + \
                              (globals().get('LOGO_TO_BOX_TRANSITION_DURATION', 0) or 0)
        # Sleep a bit longer than the animation to see its full course
        time.sleep(max(0.1, total_anim_duration + 2.0)) 
    except KeyboardInterrupt:
        print("\nInterrupted by user.")
    finally:
        print("Stopping logo animation...")
        stop_logo_animation()
        print("Animation stopped.")
