import time
import os
from datetime import datetime, timedelta
import threading
from typing import List, Dict, Optional, Tuple, Any

from rich.console import Console
from rich.live import Live
from rich.layout import Layout
from rich.panel import Panel
from rich.text import Text
from rich.align import Align
from rich.table import Table
from rich.progress_bar import ProgressBar # For cost/budget display if needed

from . import logo_animation
# Brand palette is owned by the central CLI color system (cli_theme.py, the
# Phase 1 design-refresh deliverable). Import it so every surface shares one
# palette rather than hand-defining hex values. Fall back to the same brand hex
# values when that module is absent (e.g. an integration branch that predates
# Phase 1), so the animation never hard-depends on it. The names are re-exported
# here, since sync_tui imports DEEP_NAVY / ELECTRIC_CYAN from this module.
try:
    from .cli_theme import (
        DEEP_NAVY,
        ELECTRIC_CYAN,
        LUMEN_PURPLE,
        PROMPT_MAGENTA,
        BUILD_GREEN,
        DIFF_YELLOW,
        BREAK_RED,
    )
except ImportError:  # pragma: no cover - palette fallback for pre-Phase-1 trees
    DEEP_NAVY = "#0A0A23"
    ELECTRIC_CYAN = "#00D8FF"
    LUMEN_PURPLE = "#8C47FF"
    PROMPT_MAGENTA = "#FF2AA6"
    BUILD_GREEN = "#18C07A"
    DIFF_YELLOW = "#FBBB35"
    BREAK_RED = "#F34842"

# Default colors for the four artifact boxes if not provided or invalid.
DEFAULT_PROMPT_COLOR = LUMEN_PURPLE
DEFAULT_CODE_COLOR = ELECTRIC_CYAN
DEFAULT_EXAMPLE_COLOR = BUILD_GREEN
DEFAULT_TESTS_COLOR = PROMPT_MAGENTA

# PDD Logo ASCII Art from branding document (section 7)
PDD_LOGO_ASCII = [
    "  +xxxxxxxxxxxxxxx+        ",
    "xxxxxxxxxxxxxxxxxxxxx+     ",
    "xxx                 +xx+   ",
    "xxx      x+           xx+  ",
    "xxx        x+         xxx  ",
    "xxx         x+        xx+  ",
    "xxx        x+         xx+  ",
    "xxx      x+          xxx   ",
    "xxx                +xx+    ",
    "xxx     +xxxxxxxxxxx+      ",
    "xxx   +xx+                 ",
    "xxx  +xx+                  ",
    "xxx+xx+                    ",
    "xxxx+                      ",
    "xx+                        ",
]
LOGO_HEIGHT = len(PDD_LOGO_ASCII)
LOGO_MAX_WIDTH = max(len(line) for line in PDD_LOGO_ASCII)

# Emojis for commands
EMOJIS = {
    "generate": "🔨",
    "example": "🌱",
    "crash_code": "💀",
    "crash_example": "💀",
    "verify_code": "🔍",
    "verify_example": "🔍",
    "test": "🧪",
    "test_extend": "🧪",
    "fix_code": "🔧",
    "fix_tests": "🔧",
    "update": "⬆️",
    "auto-deps": "📦",
    "checking": "🔍",
}

CONSOLE_WIDTH = 80  # Target console width for layout
ANIMATION_BOX_HEIGHT = 18 # Target height for the main animation box

# ---------------------------------------------------------------------------
# Execution pipeline model.
#
# The sync system flow (see the Mermaid diagram in issue #1560) is a pipeline:
# the CLI parses options, inspects on-disk state, the planner picks the next
# operation, the command-execution loop runs it, and outputs are written.
# Subgraphs 1, 2, 3, 4 and 6 are *runtime* stages; subgraph 5 ("validation
# seams") is test-only and never animated. The animation mirrors this: the front
# and back stages stay high-level boxes, while the command-execution stage —
# where the user actually spends time and money — is expanded in detail.
#
# The orchestrator drives the animation through a single mutable string
# (current_function_name) that takes the values below. We map each onto a stage
# so the visuals follow real execution rather than a decorative script.
# ---------------------------------------------------------------------------
STAGE_ENTRY = "entry"
STAGE_INSPECT = "inspect"
STAGE_PLAN = "plan"
STAGE_EXECUTE = "execute"
STAGE_OUTPUT = "output"

# Ordered stages with the short label and the sub-steps each one performs
# (sourced verbatim from the diagram's subgraph contents).
PIPELINE_STAGES: List[Tuple[str, str, str]] = [
    (STAGE_ENTRY,   "Entry",   "args · config · paths · budget"),
    (STAGE_INSPECT, "Inspect", "lock · fingerprint · files · hashes"),
    (STAGE_PLAN,    "Plan",    "determine next operation"),
    (STAGE_EXECUTE, "Execute", "run command"),
    (STAGE_OUTPUT,  "Output",  "artifacts · fingerprint · report"),
]
_STAGE_INDEX = {stage_id: i for i, (stage_id, _label, _sub) in enumerate(PIPELINE_STAGES)}

# The canonical order the planner walks the command-execution loop in. Shown as
# a step strip during Execute so the user can see intermediate steps and where
# the current operation sits in the overall workflow. 'crash' is the failure
# face of 'verify' and 'test_extend' the continuation of 'test', so they map
# onto the same strip slot (see _STEP_ALIASES).
COMMAND_SEQUENCE: List[str] = [
    "auto-deps", "generate", "example", "verify", "test", "fix", "update",
]
_STEP_ALIASES = {"crash": "verify", "test_extend": "test"}

# Probe operations run an artifact and inspect the result rather than producing
# a new artifact — the "check" behavior in the diagram. They get a distinct
# probe glyph and pulse so check steps read differently from build steps.
PROBE_OPERATIONS = {"verify", "crash", "test", "test_extend"}

# Operations that constitute the command-execution stage.
EXECUTE_OPERATIONS = {
    "auto-deps", "generate", "example", "verify", "crash",
    "test", "test_extend", "fix", "update",
}

# Terminal function names the orchestrator emits when the loop ends.
_OUTPUT_NAMES = {"synced", "nothing", "all_synced", "conflict", "done", "error",
                 "fail_and_request_manual_merge"}
_PLAN_NAMES = {"checking", "planning", "analyze", "analyze_conflict", "deciding"}
_ENTRY_NAMES = {"initializing", "init", "startup", ""}


def stage_for_function(function_name: Optional[str]) -> str:
    """Map an orchestrator function name onto a pipeline stage id.

    This is the single source of truth tying the animation to real execution:
    every value the orchestrator writes into ``current_function_name_ref`` is
    classified here, so the rail and body never show a stage the run is not
    actually in.
    """
    fn = (function_name or "").strip().lower()
    if fn in _ENTRY_NAMES:
        # Entry (arg parse) happens before/while the logo plays; by the time the
        # main frame renders we are reading on-disk state, so show Inspect.
        return STAGE_INSPECT
    if fn in _PLAN_NAMES:
        return STAGE_PLAN
    if fn in _OUTPUT_NAMES:
        return STAGE_OUTPUT
    if fn in EXECUTE_OPERATIONS:
        return STAGE_EXECUTE
    # Unknown / future operation names are still command execution.
    return STAGE_EXECUTE

def _get_valid_color(color_str: Optional[str], default_color: str) -> str:
    """Validates a color string or returns default."""
    if not color_str:
        return default_color
    return color_str if isinstance(color_str, str) else default_color

def _shorten_path(path_str: Optional[str], max_len: int) -> str:
    """Shortens a path string for display, trying relative path first."""
    if not path_str:
        return ""
    try:
        rel_path = os.path.relpath(path_str, start=os.getcwd())
    except ValueError:
        rel_path = path_str

    if len(rel_path) <= max_len:
        return rel_path
    
    basename = os.path.basename(rel_path)
    if len(basename) <= max_len:
        return basename
    
    return "..." + basename[-(max_len-3):]


class AnimationState:
    """Holds the current state of the animation."""
    def __init__(self, basename: str, budget: Optional[float]):
        self.current_function_name: str = "checking"
        self.basename: str = basename
        self.cost: float = 0.0
        self.budget: float = budget if budget is not None else float('inf')
        self.start_time: datetime = datetime.now()
        self.frame_count: int = 0
        
        self.paths: Dict[str, str] = {"prompt": "", "code": "", "example": "", "tests": ""}
        self.colors: Dict[str, str] = {
            "prompt": DEFAULT_PROMPT_COLOR, "code": DEFAULT_CODE_COLOR,
            "example": DEFAULT_EXAMPLE_COLOR, "tests": DEFAULT_TESTS_COLOR
        }
        self.scroll_offsets: Dict[str, int] = {"prompt": 0, "code": 0, "example": 0, "tests": 0}
        # Horizontal marquee offset for the command step strip, used only when
        # the fully-spelt-out strip is too wide for the terminal (see
        # _render_step_strip). Advances one cell per rendered frame.
        self.step_scroll_offset: int = 0
        self.path_box_content_width = 16 # Base chars for path inside its small box (will be dynamic)
        self.auto_deps_progress: int = 0  # Progress counter for auto-deps border thickening

        # Pipeline-stage tracking (see PIPELINE_STAGES). current_stage is derived
        # from current_function_name every update so it always matches reality.
        self.current_stage: str = stage_for_function(self.current_function_name)
        # Execute-loop steps that have already run this session, used to mark the
        # command step strip. Only populated as real operations are observed.
        self.executed_steps: List[str] = []
        self._last_op: Optional[str] = None

    def update_dynamic_state(self, function_name: str, cost: float,
                             prompt_path: str, code_path: str, example_path: str, tests_path: str):
        self.current_function_name = function_name.lower() if function_name else "checking"
        self.cost = cost if cost is not None else self.cost
        self.current_stage = stage_for_function(self.current_function_name)

        # Record completed execute-loop steps as the operation changes, so the
        # step strip can show what has already run. We normalize aliases (crash
        # -> verify, test_extend -> test) onto their canonical strip slot.
        op = self.current_function_name
        if op != self._last_op:
            prev = self._last_op
            if prev in EXECUTE_OPERATIONS:
                slot = _STEP_ALIASES.get(prev, prev)
                if slot not in self.executed_steps:
                    self.executed_steps.append(slot)
            self._last_op = op

        self.paths["prompt"] = prompt_path or ""
        self.paths["code"] = code_path or ""
        self.paths["example"] = example_path or ""
        self.paths["tests"] = tests_path or ""

        # Update auto-deps progress for border thickening animation
        if self.current_function_name == "auto-deps":
            self.auto_deps_progress = (self.auto_deps_progress + 1) % 120  # Cycle every 12 seconds at 10fps

    def set_box_colors(self, prompt_color: str, code_color: str, example_color: str, tests_color: str):
        self.colors["prompt"] = _get_valid_color(prompt_color, DEFAULT_PROMPT_COLOR)
        self.colors["code"] = _get_valid_color(code_color, DEFAULT_CODE_COLOR)
        self.colors["example"] = _get_valid_color(example_color, DEFAULT_EXAMPLE_COLOR)
        self.colors["tests"] = _get_valid_color(tests_color, DEFAULT_TESTS_COLOR)

    def get_elapsed_time_str(self) -> str:
        elapsed = datetime.now() - self.start_time
        return str(elapsed).split('.')[0] # Format as HH:MM:SS

    def _render_scrolling_path(self, path_key: str, content_width: int) -> str:
        """Renders a path, scrolling if it's too long for its display box."""
        full_display_path = _shorten_path(self.paths[path_key], 100) 
        
        if not full_display_path:
            return " " * content_width 

        if len(full_display_path) <= content_width:
            return full_display_path.center(content_width)

        offset = self.scroll_offsets[path_key]
        padded_text = f" {full_display_path} :: {full_display_path} "
        display_text = padded_text[offset : offset + content_width]
        
        self.scroll_offsets[path_key] = (offset + 1) % (len(full_display_path) + 4) 
        return display_text

    def get_emoji_for_box(self, box_name: str, blink_on: bool) -> str:
        """Gets the emoji for a given box based on the current function."""
        cmd = self.current_function_name
        emoji_char = ""

        if cmd == "checking":
            emoji_char = EMOJIS["checking"]
        elif cmd == "generate" and box_name == "code":
            emoji_char = EMOJIS["generate"]
        elif cmd == "example" and box_name == "example":
            emoji_char = EMOJIS["example"]
        elif cmd == "crash":
            if box_name == "code":
                emoji_char = EMOJIS["crash_code"]
            elif box_name == "example":
                emoji_char = EMOJIS["crash_example"]
        elif cmd == "verify":
            if box_name == "code":
                emoji_char = EMOJIS["verify_code"]
            elif box_name == "example":
                emoji_char = EMOJIS["verify_example"]
        elif cmd == "test" and box_name == "tests":
            emoji_char = EMOJIS["test"]
        elif cmd == "fix":
            if box_name == "code":
                emoji_char = EMOJIS["fix_code"]
            elif box_name == "tests":
                emoji_char = EMOJIS["fix_tests"]
        elif cmd == "update" and box_name == "prompt":
            emoji_char = EMOJIS["update"]
        elif cmd == "auto-deps" and box_name == "prompt":
            emoji_char = EMOJIS["auto-deps"]
        
        # Always return 2 chars to prevent shifting, with space after emoji
        if blink_on and emoji_char:
            return emoji_char + " "
        else:
            return "  "

def _get_path_waypoints(cmd: str, code_x: int, example_x: int, tests_x: int, prompt_x: int) -> List[Tuple[int, int, str]]:
    """Returns waypoints (x, y, direction) for the arrow path based on command."""
    waypoints = []
    
    if cmd == "generate":  # Prompt -> Code
        waypoints = [
            (prompt_x, 0, "v"),  # Start at prompt, go down
            (prompt_x, 1, "v"),  # Continue down
            (prompt_x, 2, ">"),  # Turn right at junction
            (code_x, 2, "v"),   # Turn down at code column
            (code_x, 3, "v"),   # Continue down
            (code_x, 4, "v"),   # Final down to code box
            (code_x, 5, "v")    # Connect to code box
        ]
    elif cmd == "example":  # Prompt -> Example (straight down)
        waypoints = [
            (prompt_x, 0, "v"),  # Start at prompt, go down
            (prompt_x, 1, "v"),  # Continue down
            (prompt_x, 2, "v"),  # Continue down through junction
            (prompt_x, 3, "v"),  # Continue down
            (prompt_x, 4, "v"),  # Final down to example box
            (prompt_x, 5, "v")   # Connect to example box
        ]
    elif cmd == "test":  # Prompt -> Tests
        waypoints = [
            (prompt_x, 0, "v"),  # Start at prompt, go down
            (prompt_x, 1, "v"),  # Continue down
            (prompt_x, 2, ">"),  # Turn right at junction
            (tests_x, 2, "v"),   # Turn down at tests column
            (tests_x, 3, "v"),   # Continue down
            (tests_x, 4, "v"),   # Final down to tests box
            (tests_x, 5, "v")    # Connect to tests box
        ]
    elif cmd == "auto-deps":  # No arrow animation - focus on border thickening
        waypoints = []  # Empty waypoints means no arrow animation
    elif cmd == "update":  # Code -> Prompt
        waypoints = [
            (code_x, 5, "^"),    # Start from code box, go up
            (code_x, 4, "^"),    # Continue up
            (code_x, 3, "^"),    # Continue up
            (code_x, 2, ">"),    # Turn right at junction
            (prompt_x, 2, "^"),  # Turn up at prompt column
            (prompt_x, 1, "^"),  # Continue up
            (prompt_x, 0, "^")   # Final up to prompt box
        ]
    elif cmd in ["crash", "verify"]:  # Code <-> Example (bidirectional)
        waypoints = [
            (code_x, 5, "^"),    # Start from code box, go up
            (code_x, 4, "^"),    # Continue up
            (code_x, 3, "^"),    # Continue up
            (code_x, 2, ">"),    # Turn right at junction
            (example_x, 2, "v"), # Turn down at example column
            (example_x, 3, "v"), # Continue down
            (example_x, 4, "v"), # Continue down
            (example_x, 5, "v")  # Final down to example box
        ]
    elif cmd == "fix":  # Code <-> Tests (bidirectional)
        waypoints = [
            (code_x, 5, "^"),    # Start from code box, go up
            (code_x, 4, "^"),    # Continue up
            (code_x, 3, "^"),    # Continue up
            (code_x, 2, ">"),    # Turn right at junction
            (tests_x, 2, "v"),   # Turn down at tests column
            (tests_x, 3, "v"),   # Continue down
            (tests_x, 4, "v"),   # Continue down
            (tests_x, 5, "v")    # Final down to tests box
        ]
    
    return waypoints

def _draw_connecting_lines_and_arrows(state: AnimationState, console_width: int) -> List[Text]:
    """Generates Text objects for lines and arrows based on current command."""
    lines = []
    cmd = state.current_function_name
    frame = state.frame_count

    # Dynamic positioning based on actual console width and auto-sized boxes
    # Calculate dynamic box width (same as in main render function)
    margin_space = 8  # Total margin space
    inter_box_space = 4  # Space between boxes (2 spaces each side)
    available_width = console_width - margin_space - inter_box_space
    box_width = max(state.path_box_content_width + 4, available_width // 3)
    
    # Calculate actual positions based on Rich's table layout
    # Rich centers the table automatically, so we need to account for that
    total_table_width = 3 * box_width + inter_box_space
    table_start = (console_width - total_table_width) // 2
    
    # Position connectors at the center of each box
    code_x = table_start + box_width // 2
    example_x = table_start + box_width + (inter_box_space // 2) + box_width // 2  
    tests_x = table_start + 2 * box_width + inter_box_space + box_width // 2
    
    # Prompt should align with the center box (Example)
    prompt_x = example_x
    
    # Animation parameters
    animation_cycle = 60  # Longer cycle for smoother animation
    waypoints = _get_path_waypoints(cmd, code_x, example_x, tests_x, prompt_x)
    
    # Handle bidirectional commands
    if cmd in ["crash", "verify", "fix"]:
        full_cycle = (frame // animation_cycle) % 2
        if full_cycle == 1:  # Reverse direction
            if cmd in ["crash", "verify"]:
                # Example -> Code
                waypoints = [
                    (example_x, 5, "^"), # Start from example box, go up
                    (example_x, 4, "^"), # Continue up
                    (example_x, 3, "^"), # Continue up
                    (example_x, 2, "<"), # Turn left at junction
                    (code_x, 2, "v"),    # Turn down at code column
                    (code_x, 3, "v"),    # Continue down
                    (code_x, 4, "v"),    # Continue down
                    (code_x, 5, "v")     # Final down to code box
                ]
            elif cmd == "fix":
                # Tests -> Code
                waypoints = [
                    (tests_x, 5, "^"),   # Start from tests box, go up
                    (tests_x, 4, "^"),   # Continue up
                    (tests_x, 3, "^"),   # Continue up
                    (tests_x, 2, "<"),   # Turn left at junction
                    (code_x, 2, "v"),    # Turn down at code column
                    (code_x, 3, "v"),    # Continue down
                    (code_x, 4, "v"),    # Continue down
                    (code_x, 5, "v")     # Final down to code box
                ]
    
    # Initialize all lines with basic structure
    line_parts = []
    for i in range(6):  # Extended to 6 lines to accommodate connections to boxes
        line_parts.append([" "] * console_width)
    
    # Draw the basic connecting line structure
    all_branch_xs = sorted([code_x, example_x, tests_x, prompt_x])
    min_x = min(all_branch_xs)
    max_x = max(all_branch_xs)

    # Draw horizontal line on line 2 (index 2)
    # Clamp drawing range to console width to prevent IndexError and wrapping
    draw_start = max(min_x, 0)
    draw_end = min(max_x, console_width - 1)
    
    if draw_start <= draw_end:
        for i in range(draw_start, draw_end + 1):
            line_parts[2][i] = "─"
    
    # Draw vertical connectors only where needed
    # Prompt always connects vertically (lines 0,1 above junction, lines 3,4,5 below)
    for line_idx in [0, 1, 3, 4, 5]:
        if prompt_x >= 0 and prompt_x < console_width:
            line_parts[line_idx][prompt_x] = "│"
    
    # Code and Tests only connect below the junction (lines 3,4,5)
    for line_idx in [3, 4, 5]:
        if code_x >= 0 and code_x < console_width:
            line_parts[line_idx][code_x] = "│"
        if tests_x >= 0 and tests_x < console_width:
            line_parts[line_idx][tests_x] = "│"
    
    # Set junction points on horizontal line
    if code_x >= 0 and code_x < console_width:
        line_parts[2][code_x] = "┌"  # Top-left corner
    if example_x >= 0 and example_x < console_width:
        line_parts[2][example_x] = "┼"  # 4-way junction (prompt connects here)
    if tests_x >= 0 and tests_x < console_width:
        line_parts[2][tests_x] = "┐"  # Top-right corner
    
    # Animate single arrow along path with distance-based timing
    if waypoints:
        # Calculate total path distance for normalization
        total_distance = 0
        segment_distances = []
        for i in range(len(waypoints) - 1):
            start_x, start_y, _ = waypoints[i]
            end_x, end_y, _ = waypoints[i + 1]
            distance = abs(end_x - start_x) + abs(end_y - start_y)  # Manhattan distance
            segment_distances.append(distance)
            total_distance += distance
        
        if total_distance > 0:
            current_pos_factor = (frame % animation_cycle) / animation_cycle
            target_distance = current_pos_factor * total_distance
            
            # Find which segment we're in based on distance traveled
            current_distance = 0
            current_segment = 0
            segment_factor = 0
            
            for i, seg_dist in enumerate(segment_distances):
                if current_distance + seg_dist >= target_distance:
                    current_segment = i
                    if seg_dist > 0:
                        segment_factor = (target_distance - current_distance) / seg_dist
                    break
                current_distance += seg_dist
            
            if current_segment < len(waypoints) - 1:
                start_waypoint = waypoints[current_segment]
                end_waypoint = waypoints[current_segment + 1]
                
                start_x, start_y, _ = start_waypoint
                end_x, end_y, _ = end_waypoint
                
                # Calculate current arrow position with consistent speed
                if start_x == end_x:  # Vertical movement
                    arrow_x = start_x
                    distance = abs(end_y - start_y)
                    if start_y < end_y:  # Moving down
                        arrow_y = start_y + round(distance * segment_factor)
                        arrow_char = "v"
                    else:  # Moving up
                        arrow_y = start_y - round(distance * segment_factor)
                        arrow_char = "^"
                else:  # Horizontal movement
                    arrow_y = start_y
                    distance = abs(end_x - start_x)
                    if start_x < end_x:  # Moving right
                        arrow_x = start_x + round(distance * segment_factor)
                        arrow_char = ">"
                    else:  # Moving left
                        arrow_x = start_x - round(distance * segment_factor)
                        arrow_char = "<"
                
                # Place the arrow
                if (0 <= arrow_x < console_width and 0 <= arrow_y < len(line_parts)):
                    line_parts[arrow_y][arrow_x] = arrow_char
    
    # Convert to Text objects
    for line_content in line_parts:
        lines.append(Text("".join(line_content), style=ELECTRIC_CYAN))
    
    return lines


# Full stage titles for the high-level cards (the diagram's subgraph names).
_STAGE_TITLES = {
    STAGE_ENTRY:   "CLI entry & options",
    STAGE_INSPECT: "State inspection",
    STAGE_PLAN:    "Operation planner",
    STAGE_EXECUTE: "Command execution",
    STAGE_OUTPUT:  "Outputs",
}

# Labels for the command step strip. The execute sub-commands are spelt out in
# full (issue #1560) — `auto-deps`, `generate`, … rather than `deps`, `gen`, …
# — so the strip reads as the real CLI commands the loop runs. When the full
# strip is too wide for the terminal it is first tightened (a compact separator)
# and, failing that, rotated as a marquee so every step still scrolls past; see
# _render_step_strip.
_STEP_LABELS = {
    "auto-deps": "auto-deps",
    "generate": "generate",
    "example": "example",
    "verify": "verify",
    "test": "test",
    "fix": "fix",
    "update": "update",
}
_PROBE_SLOTS = {"verify", "test"}  # canonical strip slots that are checks, not builds

# Separators tried in order when fitting the strip to the available width: the
# roomy one first, then a compact one. If neither fits the strip rotates.
_STRIP_SEPARATORS = ("  ·  ", " · ")


def _render_phase_rail(state: AnimationState, blink_on: bool) -> Text:
    """One-line rail showing pipeline progression Entry → … → Output.

    Completed stages are filled and green, the current stage pulses in accent,
    and pending stages stay dim. This is the always-on orientation strip that
    maps directly onto the diagram's top-level subgraphs.
    """
    cur_idx = _STAGE_INDEX.get(state.current_stage, _STAGE_INDEX[STAGE_INSPECT])
    rail = Text(justify="center")
    for i, (_stage_id, label, _sub) in enumerate(PIPELINE_STAGES):
        if i > 0:
            rail.append(" ─▶ ", style="dim " + ELECTRIC_CYAN)
        if i < cur_idx:
            rail.append("● ", style=BUILD_GREEN)
            rail.append(label, style=BUILD_GREEN)
        elif i == cur_idx:
            glyph = "◆ " if blink_on else "◇ "
            rail.append(glyph, style=f"bold {PROMPT_MAGENTA}")
            rail.append(label, style=f"bold {ELECTRIC_CYAN}")
        else:
            rail.append("○ ", style="dim " + ELECTRIC_CYAN)
            rail.append(label, style="dim " + ELECTRIC_CYAN)
    return rail


def _step_strip_cells(state: AnimationState, blink_on: bool,
                      separator: str) -> List[Tuple[str, str]]:
    """Build the command-execution strip as a flat list of (char, style) cells.

    Working in cells lets the renderer measure the strip's true width, choose a
    separator that fits, and — when nothing fits — take a styled marquee window
    without re-deriving any of the per-step coloring. Done steps get a check,
    the active step pulses (probe steps carry a probe glyph and turn red on a
    crash), and upcoming steps stay dim.
    """
    cur_op = state.current_function_name
    cur_slot = _STEP_ALIASES.get(cur_op, cur_op)
    is_crash = cur_op == "crash"
    cells: List[Tuple[str, str]] = []

    def add(segment: str, style: str) -> None:
        cells.extend((ch, style) for ch in segment)

    for i, step in enumerate(COMMAND_SEQUENCE):
        if i > 0:
            add(separator, "dim " + ELECTRIC_CYAN)
        label = _STEP_LABELS.get(step, step)
        if step == cur_slot:
            if step in _PROBE_SLOTS:
                marker = "◈" if blink_on else "◇"
                style = f"bold {BREAK_RED}" if is_crash else f"bold {DIFF_YELLOW}"
                add(f"{marker} ", style)
                add(label, style)
            else:
                glyph = "▸ " if blink_on else "▹ "
                style = f"bold {ELECTRIC_CYAN}"
                add(glyph, style)
                add(label, style)
        elif step in state.executed_steps:
            add("✓ ", BUILD_GREEN)
            add(label, BUILD_GREEN)
        else:
            add(label, "dim " + ELECTRIC_CYAN)
    return cells


def _cells_to_text(cells: List[Tuple[str, str]]) -> Text:
    """Reassemble (char, style) cells into a single-line, crop-safe Text."""
    text = Text(justify="center", no_wrap=True, overflow="crop")
    for ch, style in cells:
        text.append(ch, style=style or None)
    return text


def _render_step_strip(state: AnimationState, blink_on: bool,
                       content_width: Optional[int] = None) -> Text:
    """One-line strip of the command-execution loop with the active step lit.

    The execute sub-commands are spelt out in full, so the user sees the real
    commands the loop runs and where the current operation sits among them. The
    strip adapts to the terminal so the full names stay legible at any width:

    1. render it with the roomy separator if it fits;
    2. otherwise tighten the separator (resize) and render if *that* fits;
    3. otherwise rotate it as a marquee — a fixed-width window that scrolls one
       cell per frame, looping through a small gap — so every step still
       scrolls past on a narrow terminal instead of being silently cropped.

    ``content_width`` is the cell budget for the strip; when omitted (e.g. unit
    tests) the full strip is rendered untruncated.
    """
    if content_width is None or content_width <= 0:
        return _cells_to_text(_step_strip_cells(state, blink_on, _STRIP_SEPARATORS[0]))

    cells: List[Tuple[str, str]] = []
    for separator in _STRIP_SEPARATORS:
        cells = _step_strip_cells(state, blink_on, separator)
        if len(cells) <= content_width:
            return _cells_to_text(cells)

    # Still too wide even tightened: rotate the (compact) strip as a marquee.
    gap = [(" ", "")] * 4  # blank run so the loop seam reads as a gap, not a join
    loop = cells + gap
    offset = state.step_scroll_offset % len(loop)
    window = (loop + loop)[offset:offset + content_width]
    state.step_scroll_offset = (offset + 1) % len(loop)
    return _cells_to_text(window)


def _render_stage_card(state: AnimationState, console_width: int, blink_on: bool) -> Align:
    """High-level box for a non-execution stage (entry / inspect / plan / output).

    Keeps the early and late stages clean and box-based: a titled panel naming
    the stage, the sub-steps it performs, and a short live status line.
    """
    stage = state.current_stage
    title = _STAGE_TITLES.get(stage, stage.capitalize())
    sub = next((s for sid, _l, s in PIPELINE_STAGES if sid == stage), "")

    border = ELECTRIC_CYAN
    if stage == STAGE_OUTPUT:
        fn = state.current_function_name
        if fn in ("synced", "nothing", "all_synced", "done"):
            border = BUILD_GREEN
            status = "✓ workflow complete"
        elif fn in ("conflict", "fail_and_request_manual_merge"):
            border = DIFF_YELLOW
            status = "manual merge required"
        else:  # error
            border = BREAK_RED
            status = "✗ sync failed"
    else:
        ellipsis = "." * (1 + (state.frame_count // 4) % 3)
        verb = {STAGE_INSPECT: "reading last-known state",
                STAGE_PLAN: "choosing next operation",
                STAGE_ENTRY: "resolving configuration"}.get(stage, "working")
        status = f"{verb}{ellipsis}"

    card = Text(justify="center")
    card.append(sub + "\n", style=ELECTRIC_CYAN)
    card.append(status, style=f"bold {border}")

    inner_w = min(56, max(28, console_width - 8))
    panel = Panel(Align.center(card, vertical="middle"),
                  title=Text(title, style=f"bold {border}"),
                  border_style=border, width=inner_w, height=5)
    return Align.center(panel, vertical="middle")


def _build_artifact_graph(state: AnimationState, console_width: int, blink_on: bool) -> Layout:
    """Detailed command-execution view: the four artifact boxes plus the live
    arrow/probe flow between them. This is the expanded heart of the animation."""
    # Calculate dynamic box width based on console width
    # Leave space for margins and spacing between boxes
    margin_space = 8  # Total margin space
    inter_box_space = 4  # Space between boxes (2 spaces each side)
    available_width = console_width - margin_space - inter_box_space
    box_width = max(state.path_box_content_width + 4, available_width // 3)

    # Calculate the actual content width inside each panel (excluding borders)
    panel_content_width = box_width - 4  # Account for panel borders (2 chars each side)

    # Handle progressive border thickening for auto-deps command
    prompt_border_style = state.colors["prompt"]
    if state.current_function_name == "auto-deps":
        # Create thicker border effect by cycling through different border styles
        thickness_level = (state.auto_deps_progress // 30) % 4  # Change every 3 seconds
        if thickness_level == 0:
            prompt_border_style = state.colors["prompt"]
        elif thickness_level == 1:
            prompt_border_style = f"bold {state.colors['prompt']}"
        elif thickness_level == 2:
            # Use a different approach for bright colors that works with hex colors
            base_color = state.colors['prompt'].replace('#', '').lower()
            if base_color in ['8c47ff', 'purple']:
                prompt_border_style = "bold bright_magenta"
            elif base_color in ['00d8ff', 'cyan']:
                prompt_border_style = "bold bright_cyan"
            else:
                prompt_border_style = f"bold bright_white"
        else:
            # Final level: reverse colors for maximum thickness effect
            prompt_border_style = f"bold black on {state.colors['prompt']}"

    prompt_panel = Panel(Align.center(state._render_scrolling_path("prompt", panel_content_width)),
                         title=Text.assemble(state.get_emoji_for_box("prompt", blink_on), "Prompt"),
                         border_style=prompt_border_style, width=box_width, height=3)
    code_panel = Panel(Align.center(state._render_scrolling_path("code", panel_content_width)),
                       title=Text.assemble(state.get_emoji_for_box("code", blink_on), "Code"),
                       border_style=state.colors["code"], width=box_width, height=3)
    example_panel = Panel(Align.center(state._render_scrolling_path("example", panel_content_width)),
                          title=Text.assemble(state.get_emoji_for_box("example", blink_on), "Example"),
                          border_style=state.colors["example"], width=box_width, height=3)
    tests_panel = Panel(Align.center(state._render_scrolling_path("tests", panel_content_width)),
                        title=Text.assemble(state.get_emoji_for_box("tests", blink_on), "Tests"),
                        border_style=state.colors["tests"], width=box_width, height=3)

    org_chart_layout = Layout(name="org_chart_area")
    org_chart_layout.split_column(
        Layout(Align.center(prompt_panel), name="prompt_row", size=3),
        Layout(name="lines_row_1", size=1),
        Layout(name="lines_row_2", size=1),
        Layout(name="lines_row_3", size=1),
        Layout(name="lines_row_4", size=1),
        Layout(name="lines_row_5", size=1),
        Layout(name="lines_row_6", size=1),
        Layout(name="bottom_boxes_row", size=3)
    )

    # Use full console width since we're no longer centering the lines
    connecting_lines = _draw_connecting_lines_and_arrows(state, console_width)
    for idx in range(6):
        if idx < len(connecting_lines):
            org_chart_layout[f"lines_row_{idx + 1}"].update(connecting_lines[idx])

    bottom_boxes_table = Table.grid(expand=True)
    bottom_boxes_table.add_column()
    bottom_boxes_table.add_column()
    bottom_boxes_table.add_column()
    bottom_boxes_table.add_row(code_panel, example_panel, tests_panel)
    org_chart_layout["bottom_boxes_row"].update(Align.center(bottom_boxes_table))
    return org_chart_layout


def _render_animation_frame(state: AnimationState, console_width: int) -> Panel:
    """Renders a single frame of the main animation box.

    The frame is a fixed-height panel with three regions: a header, a body, and
    a footer. The body always carries the phase rail (pipeline progression). The
    rest of the body switches on the current stage: high-level command-execution
    detail (artifact graph + step strip) while a command runs, and a clean
    high-level stage card for the entry / inspect / plan / output stages.
    """
    layout = Layout(name="root")
    layout.split_column(
        Layout(name="header", size=1),
        Layout(name="body", ratio=1, minimum_size=10),
        Layout(name="footer", size=1)
    )

    blink_on = (state.frame_count // 5) % 2 == 0

    header_table = Table.grid(expand=True, padding=(0,1))
    header_table.add_column(justify="left", ratio=1)
    header_table.add_column(justify="right", ratio=1)
    # Make command blink in top right corner
    command_text = state.current_function_name.capitalize() if blink_on else ""
    header_table.add_row(
        Text("Prompt Driven Development", style=f"bold {ELECTRIC_CYAN}"),
        Text(command_text, style=f"bold {ELECTRIC_CYAN}")
    )
    layout["header"].update(header_table)

    footer_table = Table.grid(expand=True, padding=(0,1))
    footer_table.add_column(justify="left", ratio=1)
    footer_table.add_column(justify="center", ratio=1)
    footer_table.add_column(justify="right", ratio=1)

    cost_str = f"${state.cost:.2f}"
    budget_str = f"${state.budget:.2f}" if state.budget != float('inf') else "N/A"

    footer_table.add_row(
        Text(state.basename, style=ELECTRIC_CYAN),
        Text(f"Elapsed: {state.get_elapsed_time_str()}", style=ELECTRIC_CYAN),
        Text(f"{cost_str} / {budget_str}", style=ELECTRIC_CYAN)
    )
    layout["footer"].update(footer_table)

    # Body: always show the phase rail, then either the detailed execution view
    # or the high-level stage card depending on the current pipeline stage.
    body_layout = Layout(name="body_inner")
    rail = _render_phase_rail(state, blink_on)

    if state.current_stage == STAGE_EXECUTE:
        # The strip lives inside the framed panel: subtract its border (2 cells)
        # and horizontal padding (2 cells) to get the real cell budget.
        strip_width = max(10, console_width - 4)
        body_layout.split_column(
            Layout(rail, name="rail", size=1),
            Layout(_render_step_strip(state, blink_on, strip_width), name="step_strip", size=1),
            Layout(_build_artifact_graph(state, console_width, blink_on), name="graph", ratio=1),
        )
    else:
        body_layout.split_column(
            Layout(rail, name="rail", size=1),
            Layout(_render_stage_card(state, console_width, blink_on), name="card", ratio=1),
        )

    layout["body"].update(body_layout)
    state.frame_count += 1

    return Panel(layout, style=f"{ELECTRIC_CYAN} on {DEEP_NAVY}",
                 border_style=ELECTRIC_CYAN, height=ANIMATION_BOX_HEIGHT,
                 width=console_width)



def _final_logo_animation_sequence(console: Console):
    """Animates the PDD logo shrinking/disappearing."""
    # This is called after Live exits, so console is back to normal.
    console.clear()
    logo_panel_content = "\n".join(line.center(LOGO_MAX_WIDTH + 4) for line in PDD_LOGO_ASCII)
    logo_panel = Panel(logo_panel_content, style=f"bold {ELECTRIC_CYAN} on {DEEP_NAVY}", 
                       border_style=ELECTRIC_CYAN, width=LOGO_MAX_WIDTH + 6, height=LOGO_HEIGHT + 2)
    console.print(Align.center(logo_panel))
    time.sleep(1) # Show logo briefly
    console.clear() # Final clear


def sync_animation(
    function_name_ref: List[str],
    stop_event: threading.Event,
    basename: str,
    cost_ref: List[float],
    budget: Optional[float],
    prompt_color: List[str],
    code_color: List[str],
    example_color: List[str],
    tests_color: List[str],
    prompt_path_ref: List[str],
    code_path_ref: List[str],
    example_path_ref: List[str],
    tests_path_ref: List[str]
) -> None:
    """
    Displays an informative ASCII art animation in the terminal.
    Uses mutable list references to get updates from the main thread.
    The color arguments (prompt_color, code_color, example_color, tests_color) are expected to be List[str] references.
    """
    console = Console(legacy_windows=False) 
    animation_state = AnimationState(basename, budget)
    # Set initial box colors
    animation_state.set_box_colors(prompt_color[0], code_color[0], example_color[0], tests_color[0])

    logo_animation.run_logo_animation_inline(console, stop_event)
    
    if stop_event.is_set():
        _final_logo_animation_sequence(console)
        return

    try:
        with Live(_render_animation_frame(animation_state, console.width),
                  console=console, 
                  refresh_per_second=10, 
                  transient=False,
                  screen=True,
                  auto_refresh=True
                  ) as live:
            while not stop_event.is_set():
                current_func_name = function_name_ref[0] if function_name_ref else "checking"
                current_cost = cost_ref[0] if cost_ref else 0.0
                
                current_prompt_path = prompt_path_ref[0] if prompt_path_ref else ""
                current_code_path = code_path_ref[0] if code_path_ref else ""
                current_example_path = example_path_ref[0] if example_path_ref else ""
                current_tests_path = tests_path_ref[0] if tests_path_ref else ""

                # Update box colors from refs
                animation_state.set_box_colors(
                    prompt_color[0],
                    code_color[0],
                    example_color[0],
                    tests_color[0]
                )

                animation_state.update_dynamic_state(
                    current_func_name, current_cost,
                    current_prompt_path, current_code_path,
                    current_example_path, current_tests_path
                )
                
                live.update(_render_animation_frame(animation_state, console.width))
                time.sleep(0.1) 
    except Exception as e:
        if hasattr(console, 'is_alt_screen') and console.is_alt_screen:
             console.show_cursor(True)
             if hasattr(console, 'alt_screen'):
                 console.alt_screen = False
        console.clear() 
        console.print_exception(show_locals=True)
        print(f"Error in animation: {e}", flush=True)
    finally:
        _final_logo_animation_sequence(console)