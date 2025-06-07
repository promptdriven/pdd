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

# Assuming these might be in pdd/__init__.py or a constants module
# For this example, defining them locally based on the branding document
# Primary Colors
DEEP_NAVY = "#0A0A23"
ELECTRIC_CYAN = "#00D8FF"

# Accent Colors (can be used for boxes if specific inputs are not good)
LUMEN_PURPLE = "#8C47FF"
PROMPT_MAGENTA = "#FF2AA6"
BUILD_GREEN = "#18C07A" # Success, good for 'example' or 'tests'

# Default colors for boxes if not provided or invalid
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
    "fix_code": "🔧",
    "fix_tests": "🔧",
    "update": "⬆️",
    "checking": "🔍",
}

CONSOLE_WIDTH = 80  # Target console width for layout
ANIMATION_BOX_HEIGHT = 18 # Target height for the main animation box

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
        self.path_box_content_width = 16 # Base chars for path inside its small box (will be dynamic)

    def update_dynamic_state(self, function_name: str, cost: float,
                             prompt_path: str, code_path: str, example_path: str, tests_path: str):
        self.current_function_name = function_name.lower() if function_name else "checking"
        self.cost = cost if cost is not None else self.cost
        
        self.paths["prompt"] = prompt_path or ""
        self.paths["code"] = code_path or ""
        self.paths["example"] = example_path or ""
        self.paths["tests"] = tests_path or ""

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
        
        # Always return 2 chars to prevent shifting, with space after emoji
        if blink_on and emoji_char:
            return emoji_char + " "
        else:
            return "  "

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
    
    # Calculate animated arrow position - smoother character-by-character movement
    animation_cycle = 40  # Longer cycle for smoother animation
    current_pos_factor = (frame % animation_cycle) / (animation_cycle - 1)
    
    # Line 1: First vertical connector from Prompt
    line1_parts = [" "] * console_width
    if prompt_x >= 0 and prompt_x < console_width:
        if cmd == "example":
            # Animate arrow traveling down from Prompt to Example
            if current_pos_factor < 0.2:  # Arrow in first vertical segment
                line1_parts[prompt_x] = "v"
            else:
                line1_parts[prompt_x] = "│"
        elif cmd == "update":
            # Show upward flow from Code back to Prompt
            line1_parts[prompt_x] = "^" if current_pos_factor > 0.8 else "│"
        else:
            line1_parts[prompt_x] = "│"
    
    lines.append(Text("".join(line1_parts), style=ELECTRIC_CYAN))

    # Line 2: Second vertical connector
    line2_parts = [" "] * console_width
    if prompt_x >= 0 and prompt_x < console_width:
        if cmd == "example":
            if 0.2 <= current_pos_factor < 0.4:
                line2_parts[prompt_x] = "v"
            else:
                line2_parts[prompt_x] = "│"
        elif cmd == "update":
            line2_parts[prompt_x] = "^" if 0.6 < current_pos_factor <= 0.8 else "│"
        else:
            line2_parts[prompt_x] = "│"
    
    lines.append(Text("".join(line2_parts), style=ELECTRIC_CYAN))

    # Line 3: Horizontal connections and arrows (main horizontal line)
    line3_parts = [" "] * console_width
    
    # ALWAYS draw the basic org chart structure first
    if prompt_x >= 0 and prompt_x < console_width: 
        line3_parts[prompt_x] = "┼"  # 4-way connector 
    
    # Horizontal line connecting all branches
    all_branch_xs = sorted([code_x, example_x, tests_x, prompt_x])
    min_x = min(all_branch_xs)
    max_x = max(all_branch_xs)

    for i in range(min_x, max_x + 1):
        if line3_parts[i] == " ": 
            line3_parts[i] = "─"
    
    # Set junction points
    if code_x >= 0 and code_x < console_width:
        line3_parts[code_x] = "┌"  # Top-left corner (no stub above)
    if example_x >= 0 and example_x < console_width:
        line3_parts[example_x] = "┼" if example_x == prompt_x else "┴"  # 4-way or T-up
    if tests_x >= 0 and tests_x < console_width:
        line3_parts[tests_x] = "┐"  # Top-right corner (no stub above)

    # Add animated arrows for horizontal movements
    def place_horizontal_arrow(start_x, end_x, pos_factor, reverse=False):
        if start_x == end_x:  # No horizontal movement
            return
        
        if reverse:
            pos_factor = 1.0 - pos_factor
            
        distance = abs(end_x - start_x)
        if distance <= 1:
            return
            
        # Calculate arrow position character by character for smooth animation
        if start_x < end_x:
            # Move from left to right, one character at a time
            arrow_pos = start_x + 1 + int((distance - 1) * pos_factor)
            arrow_char = ">"
        else:
            # Move from right to left, one character at a time
            arrow_pos = start_x - 1 - int((distance - 1) * pos_factor)
            arrow_char = "<"
        
        # Only place arrow if it won't overwrite junction points
        if (0 <= arrow_pos < console_width and 
            arrow_pos not in [code_x, example_x, tests_x, prompt_x] and
            line3_parts[arrow_pos] == "─"):
            line3_parts[arrow_pos] = arrow_char

    # Apply command-specific animations
    if cmd == "generate": # Prompt -> Code
        place_horizontal_arrow(prompt_x, code_x, current_pos_factor)
    elif cmd == "example":
        # Vertical animation handled above, mark junction
        if prompt_x >= 0 and prompt_x < console_width:
            if 0.4 <= current_pos_factor < 0.6:
                line3_parts[prompt_x] = "v" if line3_parts[prompt_x] == "┼" else line3_parts[prompt_x]
    elif cmd == "update": # Code -> Prompt  
        place_horizontal_arrow(code_x, prompt_x, current_pos_factor)
    elif cmd == "crash": # Code <-> Example (bidirectional)
        reverse_cycle = (frame // animation_cycle) % 2 == 1
        place_horizontal_arrow(code_x, example_x, current_pos_factor, reverse_cycle)
    elif cmd == "verify": # Code <-> Example (bidirectional)
        reverse_cycle = (frame // animation_cycle) % 2 == 1
        place_horizontal_arrow(code_x, example_x, current_pos_factor, reverse_cycle)
    elif cmd == "test": # Prompt -> Tests
        place_horizontal_arrow(prompt_x, tests_x, current_pos_factor)
    elif cmd == "fix": # Code <-> Tests (bidirectional)
        reverse_cycle = (frame // animation_cycle) % 2 == 1
        place_horizontal_arrow(code_x, tests_x, current_pos_factor, reverse_cycle)

    lines.append(Text("".join(line3_parts), style=ELECTRIC_CYAN))
    
    # Line 4: Third vertical connector for all boxes
    line4_parts = [" "] * console_width
    # Add vertical line for Example box 
    if example_x >= 0 and example_x < console_width:
        if cmd == "example":
            if 0.6 <= current_pos_factor < 0.8:
                line4_parts[example_x] = "v"
            else:
                line4_parts[example_x] = "│"
        elif cmd == "update":
            # For update command, show upward arrow from Code area
            line4_parts[example_x] = "^" if 0.4 < current_pos_factor <= 0.6 else "│"
        else:
            line4_parts[example_x] = "│"
    
    # Add vertical connectors for Code and Tests boxes
    if code_x >= 0 and code_x < console_width:
        line4_parts[code_x] = "│"
    if tests_x >= 0 and tests_x < console_width:
        line4_parts[tests_x] = "│"
    
    lines.append(Text("".join(line4_parts), style=ELECTRIC_CYAN))
    
    # Line 5: Final vertical connector for all boxes
    line5_parts = [" "] * console_width
    # Add vertical line for Example box
    if example_x >= 0 and example_x < console_width:
        if cmd == "example":
            if current_pos_factor >= 0.8:
                line5_parts[example_x] = "v"
            else:
                line5_parts[example_x] = "│"
        elif cmd == "update":
            # For update command, show upward arrow from Code area
            line5_parts[example_x] = "^" if current_pos_factor <= 0.4 else "│"
        else:
            line5_parts[example_x] = "│"
    
    # Add vertical connectors for Code and Tests boxes
    if code_x >= 0 and code_x < console_width:
        line5_parts[code_x] = "│"
    if tests_x >= 0 and tests_x < console_width:
        line5_parts[tests_x] = "│"
    
    lines.append(Text("".join(line5_parts), style=ELECTRIC_CYAN))

    return lines


def _render_animation_frame(state: AnimationState, console_width: int) -> Panel:
    """Renders a single frame of the main animation box."""
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
    
    # Calculate dynamic box width based on console width
    # Leave space for margins and spacing between boxes
    margin_space = 8  # Total margin space
    inter_box_space = 4  # Space between boxes (2 spaces each side)
    available_width = console_width - margin_space - inter_box_space
    box_width = max(state.path_box_content_width + 4, available_width // 3)
    
    # Calculate the actual content width inside each panel (excluding borders)
    panel_content_width = box_width - 4  # Account for panel borders (2 chars each side)

    prompt_panel = Panel(Align.center(state._render_scrolling_path("prompt", panel_content_width)),
                         title=Text.assemble(state.get_emoji_for_box("prompt", blink_on), "Prompt"),
                         border_style=state.colors["prompt"], width=box_width, height=3)
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
        Layout(Text(" "), size=1),
        Layout(Align.center(prompt_panel), name="prompt_row", size=3),
        Layout(name="lines_row_1", size=1), 
        Layout(name="lines_row_2", size=1),
        Layout(name="lines_row_3", size=1),
        Layout(name="lines_row_4", size=1),
        Layout(name="lines_row_5", size=1),
        Layout(name="bottom_boxes_row", size=3) 
    )

    # Use full console width since we're no longer centering the lines
    connecting_lines = _draw_connecting_lines_and_arrows(state, console_width)
    if len(connecting_lines) > 0:
        org_chart_layout["lines_row_1"].update(connecting_lines[0])
    if len(connecting_lines) > 1:
        org_chart_layout["lines_row_2"].update(connecting_lines[1])
    if len(connecting_lines) > 2:
        org_chart_layout["lines_row_3"].update(connecting_lines[2])
    if len(connecting_lines) > 3:
        org_chart_layout["lines_row_4"].update(connecting_lines[3])
    if len(connecting_lines) > 4:
        org_chart_layout["lines_row_5"].update(connecting_lines[4])


    bottom_boxes_table = Table.grid(expand=True)
    bottom_boxes_table.add_column()
    bottom_boxes_table.add_column()
    bottom_boxes_table.add_column()
    bottom_boxes_table.add_row(code_panel, example_panel, tests_panel)
    org_chart_layout["bottom_boxes_row"].update(Align.center(bottom_boxes_table))
    
    layout["body"].update(org_chart_layout)
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
    prompt_color: str,
    code_color: str,
    example_color: str,
    tests_color: str,
    prompt_path_ref: List[str],
    code_path_ref: List[str],
    example_path_ref: List[str],
    tests_path_ref: List[str]
) -> None:
    """
    Displays an informative ASCII art animation in the terminal.
    Uses mutable list references to get updates from the main thread.
    """
    # Console for initial/final animations outside Live
    # Live will use its own console or this one if passed.
    # Using a single console instance.
    console = Console(legacy_windows=False) 
    animation_state = AnimationState(basename, budget)
    animation_state.set_box_colors(prompt_color, code_color, example_color, tests_color)

    # Run logo animation directly without separate screen context
    # This avoids screen buffer conflicts with sync_animation's Live context
    logo_animation.run_logo_animation_inline(console, stop_event)
    
    if stop_event.is_set():
        _final_logo_animation_sequence(console)
        return

    # The prompt: "After 1 sec, the logo will animate to expand to a 18 line tall box"
    # This transition is implicitly handled by Live starting up with the 18-line panel.

    try:
        # screen=True takes over the full terminal screen.
        # transient=False means the display persists until Live.stop() or context exit.
        with Live(_render_animation_frame(animation_state, console.width), # Initial frame
                  console=console, 
                  refresh_per_second=10, 
                  transient=False, # Animation stays until explicitly stopped/exited
                  screen=True,      # Use alternate screen
                  auto_refresh=True
                  ) as live:
            while not stop_event.is_set():
                current_func_name = function_name_ref[0] if function_name_ref else "checking"
                current_cost = cost_ref[0] if cost_ref else 0.0
                
                current_prompt_path = prompt_path_ref[0] if prompt_path_ref else ""
                current_code_path = code_path_ref[0] if code_path_ref else ""
                current_example_path = example_path_ref[0] if example_path_ref else ""
                current_tests_path = tests_path_ref[0] if tests_path_ref else ""

                animation_state.update_dynamic_state(
                    current_func_name, current_cost,
                    current_prompt_path, current_code_path,
                    current_example_path, current_tests_path
                )
                
                live.update(_render_animation_frame(animation_state, console.width))
                time.sleep(0.1) 
    except Exception as e:
        # If Live context fails or error in loop, ensure console is somewhat clean.
        # screen=True should restore on exit, but if error is severe:
        if hasattr(console, 'is_alt_screen') and console.is_alt_screen: # Check if alt screen is active
             console.show_cursor(True)
             if hasattr(console, 'alt_screen'):
                 console.alt_screen = False # Manually try to exit alt screen
        console.clear() 
        console.print_exception(show_locals=True)
        # Fallback print if Rich is broken
        print(f"Error in animation: {e}", flush=True)
    finally:
        # _final_logo_animation_sequence is called after Live context manager exits.
        # Live(screen=True) should restore the screen, then we can print final logo.
        _final_logo_animation_sequence(console)

