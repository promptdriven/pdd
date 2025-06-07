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
ANIMATION_BOX_HEIGHT = 20 # Target height for the main animation box

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
        self.path_box_content_width = 16 # Max chars for path inside its small box

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

    def _render_scrolling_path(self, path_key: str) -> str:
        """Renders a path, scrolling if it's too long for its display box."""
        full_display_path = _shorten_path(self.paths[path_key], 100) 
        
        if not full_display_path:
            return " " * self.path_box_content_width 

        if len(full_display_path) <= self.path_box_content_width:
            return full_display_path.center(self.path_box_content_width)

        offset = self.scroll_offsets[path_key]
        padded_text = f" {full_display_path} :: {full_display_path} "
        display_text = padded_text[offset : offset + self.path_box_content_width]
        
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
            if box_name == "code": emoji_char = EMOJIS["crash_code"]
            if box_name == "example": emoji_char = EMOJIS["crash_example"]
        elif cmd == "verify":
            if box_name == "code": emoji_char = EMOJIS["verify_code"]
            if box_name == "example": emoji_char = EMOJIS["verify_example"]
        elif cmd == "test" and box_name == "tests":
            emoji_char = EMOJIS["test"]
        elif cmd == "fix":
            if box_name == "code": emoji_char = EMOJIS["fix_code"]
            if box_name == "tests": emoji_char = EMOJIS["fix_tests"]
        elif cmd == "update" and box_name == "prompt":
            emoji_char = EMOJIS["update"]
        
        return (emoji_char + " ") if blink_on and emoji_char else "  "

def _draw_connecting_lines_and_arrows(state: AnimationState, console_width: int) -> List[Text]:
    """Generates Text objects for lines and arrows based on current command."""
    lines = []
    cmd = state.current_function_name
    frame = state.frame_count
    arrow_char = ">"
    blink_on = (frame // 5) % 2 == 0 # Blink rate for arrow character
    active_arrow = arrow_char if blink_on else " "
    inactive_arrow_placeholder = " " # if arrow is not active due to blinking

    prompt_x = console_width // 2
    code_x = console_width // 4
    example_x = console_width // 2
    tests_x = 3 * console_width // 4
    
    line1 = Text(" " * (prompt_x -1) + "│", style=ELECTRIC_CYAN) # Vertical stem from Prompt
    lines.append(Align.center(line1))

    line2_parts = [" "] * console_width # For horizontal connections and arrows
    
    def place_arrow(start_x, end_x, current_pos_factor):
        length = abs(end_x - start_x)
        # Ensure length is at least 1 to avoid division by zero or issues with pos calculation
        # if start_x and end_x are very close or same.
        if length == 0: 
            # Decide how to show arrow if start and end are same (e.g. direct vertical)
            # For now, this function assumes horizontal placement.
            return

        pos = int(length * current_pos_factor)
        char_idx = min(start_x, end_x) + pos
        
        # Ensure arrow is within bounds and doesn't overwrite crucial junctions
        if 0 <= char_idx < console_width:
            arrow_to_place = active_arrow if start_x <= end_x else ("<" if blink_on else inactive_arrow_placeholder)
            # Avoid overwriting existing line characters if arrow is just a space
            if not (arrow_to_place == inactive_arrow_placeholder and line2_parts[char_idx] != " "):
                 line2_parts[char_idx] = arrow_to_place


    current_pos_factor = (frame % 10) / 9.0 

    if cmd == "generate": # Prompt -> Code
        for i in range(min(prompt_x, code_x), max(prompt_x, code_x)): 
            if line2_parts[i] == " ": line2_parts[i] = "─"
        place_arrow(prompt_x, code_x, current_pos_factor)
    elif cmd == "example": # Prompt -> Example
        for i in range(min(prompt_x, example_x), max(prompt_x, example_x)): 
            if line2_parts[i] == " ": line2_parts[i] = "─"
        place_arrow(prompt_x, example_x, current_pos_factor)
    elif cmd == "update": # Code -> Prompt
        for i in range(min(code_x, prompt_x), max(code_x, prompt_x)): 
            if line2_parts[i] == " ": line2_parts[i] = "─"
        place_arrow(code_x, prompt_x, current_pos_factor) 
    elif cmd == "crash": # Code <-> Example
        for i in range(min(code_x, example_x), max(code_x, example_x)): 
            if line2_parts[i] == " ": line2_parts[i] = "─"
        place_arrow(code_x, example_x, current_pos_factor if (frame//10)%2 ==0 else 1-current_pos_factor)
    elif cmd == "verify": # Code <-> Example
        for i in range(min(code_x, example_x), max(code_x, example_x)):
            if line2_parts[i] == " ": line2_parts[i] = "─"
        place_arrow(code_x, example_x, current_pos_factor if (frame//10)%2 == 0 else 1-current_pos_factor)
    elif cmd == "test": # Prompt -> Tests (simplified from Prompt & Code -> Tests)
        for i in range(min(prompt_x, tests_x), max(prompt_x, tests_x)):
            if line2_parts[i] == " ": line2_parts[i] = "─"
        place_arrow(prompt_x, tests_x, current_pos_factor)
    elif cmd == "fix": # Code <-> Tests
        for i in range(min(code_x, tests_x), max(code_x, tests_x)):
            if line2_parts[i] == " ": line2_parts[i] = "─"
        place_arrow(code_x, tests_x, current_pos_factor if (frame//10)%2 == 0 else 1-current_pos_factor)
    else: # Default connections (static)
        if prompt_x-1 >=0 and prompt_x-1 < console_width: line2_parts[prompt_x-1] = "┬" 
        
        # Horizontal line connecting all three bottom branches at their x-positions on line2
        all_branch_xs = sorted(list(set([code_x-1, example_x-1, tests_x-1, prompt_x-1])))
        min_x_on_line2 = min(all_branch_xs)
        max_x_on_line2 = max(all_branch_xs)

        for i in range(min_x_on_line2, max_x_on_line2 + 1):
            if line2_parts[i] == " ": line2_parts[i] = "─"
        
        # Ensure junctions for vertical stems are correctly drawn
        for x_target_idx in [code_x-1, example_x-1, tests_x-1]:
            if x_target_idx >=0 and x_target_idx < console_width:
                if line2_parts[x_target_idx] == "─": # If it's part of the horizontal line
                    line2_parts[x_target_idx] = "┴" # Make it a T-junction downwards
                # If it's the same as prompt_x-1, it's already '┬' or should be part of it.
                # This part can be complex to make perfect with all x configurations.
                # The '┬' at prompt_x-1 and '┴' at targets is a common pattern.

    lines.append(Text("".join(line2_parts), style=ELECTRIC_CYAN))
    
    line3_parts = [" "] * console_width
    for x_target in [code_x, example_x, tests_x]:
        if x_target-1 >=0 and x_target-1 < console_width:
            line3_parts[x_target-1] = "│" # Vertical stems to bottom boxes
    lines.append(Text("".join(line3_parts), style=ELECTRIC_CYAN))

    return lines


def _render_animation_frame(state: AnimationState, console_width: int) -> Panel:
    """Renders a single frame of the main animation box."""
    layout = Layout(name="root")
    layout.split_column(
        Layout(name="header", size=1),
        Layout(name="body", ratio=1, minimum_size=10), 
        Layout(name="footer", size=1)
    )

    header_table = Table.grid(expand=True, padding=(0,1))
    header_table.add_column(justify="left", ratio=1)
    header_table.add_column(justify="right", ratio=1)
    header_table.add_row(
        Text("Prompt Driven Development", style=f"bold {ELECTRIC_CYAN}"),
        Text(state.basename, style=f"bold {ELECTRIC_CYAN}")
    )
    layout["header"].update(header_table)

    footer_table = Table.grid(expand=True, padding=(0,1))
    footer_table.add_column(justify="left", ratio=1)      
    footer_table.add_column(justify="center", ratio=1) 
    footer_table.add_column(justify="right", ratio=1)     
    
    cost_str = f"${state.cost:.2f}"
    budget_str = f"${state.budget:.2f}" if state.budget != float('inf') else "N/A"
    
    footer_table.add_row(
        Text(f"Running: {state.current_function_name.capitalize()}", style=ELECTRIC_CYAN),
        Text(f"Elapsed: {state.get_elapsed_time_str()}", style=ELECTRIC_CYAN),
        Text(f"Cost: {cost_str} / Budget: {budget_str}", style=ELECTRIC_CYAN)
    )
    layout["footer"].update(footer_table)

    blink_on = (state.frame_count // 5) % 2 == 0 
    
    box_width = state.path_box_content_width + 4 

    prompt_panel = Panel(Align.center(state._render_scrolling_path("prompt")),
                         title=Text.assemble(state.get_emoji_for_box("prompt", blink_on), "Prompt"),
                         border_style=state.colors["prompt"], width=box_width, height=3)
    code_panel = Panel(Align.center(state._render_scrolling_path("code")),
                       title=Text.assemble(state.get_emoji_for_box("code", blink_on), "Code"),
                       border_style=state.colors["code"], width=box_width, height=3)
    example_panel = Panel(Align.center(state._render_scrolling_path("example")),
                          title=Text.assemble(state.get_emoji_for_box("example", blink_on), "Example"),
                          border_style=state.colors["example"], width=box_width, height=3)
    tests_panel = Panel(Align.center(state._render_scrolling_path("tests")),
                        title=Text.assemble(state.get_emoji_for_box("tests", blink_on), "Tests"),
                        border_style=state.colors["tests"], width=box_width, height=3)

    org_chart_layout = Layout(name="org_chart_area")
    org_chart_layout.split_column(
        Layout(Align.center(prompt_panel), name="prompt_row", size=3),
        Layout(name="lines_row_1", size=1), 
        Layout(name="lines_row_2", size=1),
        Layout(name="lines_row_3", size=1),
        Layout(name="bottom_boxes_row", size=3),
        Layout(ratio=1) 
    )

    # console_width for _draw_connecting_lines_and_arrows should be the actual width available for lines
    # The main panel takes 2 chars for border.
    # If org_chart_layout is centered, it might have less. For simplicity, use console_width - 4.
    effective_line_width = console_width - 4 
    connecting_lines = _draw_connecting_lines_and_arrows(state, effective_line_width)
    if len(connecting_lines) > 0: org_chart_layout["lines_row_1"].update(Align.center(connecting_lines[0]))
    if len(connecting_lines) > 1: org_chart_layout["lines_row_2"].update(Align.center(connecting_lines[1]))
    if len(connecting_lines) > 2: org_chart_layout["lines_row_3"].update(Align.center(connecting_lines[2]))


    bottom_boxes_table = Table.grid(expand=True)
    h_padding = 2 
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


def _initial_logo_animation_sequence(console: Console, stop_event: threading.Event):
    """Animates the PDD logo appearing."""
    console.clear()
    # For the animation to appear at the top and expand, we need to manage lines carefully.
    # This simplified version prints and overwrites. Rich's Live screen=True is better for sustained animations.
    # This initial part is tricky without Live's full screen management yet.
    
    # Render logo centered, line by line from bottom up
    # Pad top with newlines to push it down, then remove newlines to make it rise
    max_padding_lines = console.height - LOGO_HEIGHT -1 # Max newlines to push logo to bottom
    max_padding_lines = max(0, max_padding_lines)

    for i in range(LOGO_HEIGHT): # i is number of lines revealed
        if stop_event.is_set(): return False
        
        console.clear() # Clear screen for each frame of this simple intro
        
        # Calculate padding to simulate rising from bottom
        # As more lines are revealed (i increases), padding decreases
        # This part is hard to get right for "rising from bottom" AND "expanding upwards"
        # Let's try "expanding upwards" at a fixed top position.
        
        # Print the currently revealed part of the logo
        # The logo lines are PDD_LOGO_ASCII[0] to PDD_LOGO_ASCII[LOGO_HEIGHT-1]
        # To expand upwards, we reveal PDD_LOGO_ASCII[LOGO_HEIGHT-1-i] up to PDD_LOGO_ASCII[LOGO_HEIGHT-1]
        
        # Calculate number of blank lines to print before the logo part
        # to keep the base of the revealed logo somewhat fixed while it "grows" upwards.
        # This is complex. A simpler "reveal in place" might be better.
        
        # Simpler: Reveal lines from top to bottom, centered.
        # For "expand up from bottom", it's more like printing the last line, then last two, etc.
        # while overprinting.
        
        # The original logic was:
        # current_logo_display = [" "] * LOGO_HEIGHT
        # current_logo_display[LOGO_HEIGHT - 1 - i] = PDD_LOGO_ASCII[LOGO_HEIGHT - 1 - i].center(CONSOLE_WIDTH)
        # ... then print relevant part of current_logo_display
        # This means it fills from bottom of PDD_LOGO_ASCII array, which is top of logo visually.
        # This is "expanding downwards".
        
        # To expand "up from the bottom of the screen":
        # We print the last `i+1` lines of the logo.
        # And position this block so its bottom is at a fixed screen row, or it rises.
        
        # Let's stick to a simpler reveal for robustness if the cursor logic is tricky.
        # Reveal line by line, centered.
        for line_idx in range(i + 1):
            console.print(Text(PDD_LOGO_ASCII[line_idx].center(CONSOLE_WIDTH), style=f"bold {ELECTRIC_CYAN} on {DEEP_NAVY}"))
        
        time.sleep(0.07) # Slightly slower for logo reveal
        if i < LOGO_HEIGHT -1: # If not the last frame of reveal
             # This clear is for the simple reveal. Original had cursor moves.
             # If using cursor moves, don't clear here.
             pass # With Live(screen=True) later, this initial animation might be replaced or simplified.

    if stop_event.is_set(): return False
    time.sleep(1) # Hold full logo
    
    # Transition to 20-line box (Live will handle this by starting its screen)
    if stop_event.is_set(): return False
    # console.clear() # Live(screen=True) will clear.
    return True

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
    console = Console(width=CONSOLE_WIDTH) 
    animation_state = AnimationState(basename, budget)
    animation_state.set_box_colors(prompt_color, code_color, example_color, tests_color)

    # Initial logo animation sequence
    # The prompt implies this happens before the main Live display.
    # Live(screen=True) will clear the screen when it starts.
    # So, _initial_logo_animation_sequence should run on the console, then Live takes over.
    
    # To make _initial_logo_animation_sequence effective before Live(screen=True) takes over:
    # It needs to print directly. The `console.clear()` inside it might be too aggressive.
    # A simple print of the logo, then sleep, might be enough.
    # The "expand up" is hard without full screen control like Live provides.
    # For now, let's assume _initial_logo_animation_sequence is simplified or works as intended.
    
    # Simplified initial display:
    console.clear()
    for line_ in PDD_LOGO_ASCII:
        console.print(Text(line_.center(CONSOLE_WIDTH), style=f"bold {ELECTRIC_CYAN} on {DEEP_NAVY}"))
    time.sleep(1) # Hold logo
    if stop_event.is_set(): # Check if already stopped
        _final_logo_animation_sequence(console)
        return

    # The prompt: "After 1 sec, the logo will animate to expand to a 20 line tall box"
    # This transition is implicitly handled by Live starting up with the 20-line panel.

    try:
        # screen=True takes over the full terminal screen.
        # transient=False means the display persists until Live.stop() or context exit.
        with Live(_render_animation_frame(animation_state, console.width), # Initial frame
                  console=console, 
                  refresh_per_second=10, 
                  transient=False, # Animation stays until explicitly stopped/exited
                  screen=True      # Use alternate screen
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


if __name__ == "__main__":
    _current_function_name = ["checking"]
    _stop_event = threading.Event()
    _current_cost = [0.0]
    _prompt_path = ["prompts/calculator_python.prompt"]
    _code_path = [""]
    _example_path = [""]
    _tests_path = [""]
    _budget_val = 10.0

    def _mock_pdd_sync_workflow():
        def update_state(func_name, cost_increase, p_path="", c_path="", e_path="", t_path=""):
            _current_function_name[0] = func_name
            _current_cost[0] += cost_increase
            if p_path: _prompt_path[0] = p_path
            if c_path: _code_path[0] = c_path
            if e_path: _example_path[0] = e_path
            if t_path: _tests_path[0] = t_path
            time.sleep(0.05) # Reduced from 0.1 to match example script

        try:
            # Initial state for animation to pick up
            update_state("checking", 0.0, p_path=_prompt_path[0])
            time.sleep(2) # Allow initial animation to show "checking"
            
            update_state("auto-deps", 0.01, p_path="prompts/calculator_python_deps.prompt")
            time.sleep(3)

            update_state("generate", 0.05, c_path="src/calculator.py")
            time.sleep(3)

            update_state("example", 0.02, e_path="examples/calculator_example.py")
            time.sleep(3)
            
            update_state("crash", 0.03, c_path="src/calculator_fixed_crash.py", e_path="examples/calculator_example_crash.py")
            time.sleep(3)

            update_state("verify", 0.04, c_path="src/calculator_verified.py", e_path="examples/calculator_example_verified.py")
            time.sleep(3)

            update_state("test", 0.03, t_path="tests/test_calculator.py")
            time.sleep(3)

            update_state("fix", 0.10, c_path="src/calculator_final.py", t_path="tests/test_calculator_fixed.py")
            time.sleep(3)
            
            update_state("update", 0.02, p_path="prompts/calculator_python_updated.prompt")
            time.sleep(3)

        except KeyboardInterrupt:
            print("Workflow interrupted by user.")
        finally:
            _stop_event.set()

    print("Starting PDD Sync Animation Demo...")
    print("Press Ctrl+C to stop the demo workflow.")
    # Create dummy paths for the demo if they don't exist
    os.makedirs("./prompts", exist_ok=True)
    os.makedirs("./src", exist_ok=True)
    os.makedirs("./examples", exist_ok=True)
    os.makedirs("./tests", exist_ok=True)
    # Create dummy files so _shorten_path can work with existing paths
    with open(_prompt_path[0], "a") as f: pass


    animation_thread = threading.Thread(
        target=sync_animation,
        args=(
            _current_function_name, _stop_event, "calculator_demo", _current_cost, _budget_val,
            "blue", "cyan", "green", "yellow", 
            _prompt_path, _code_path, _example_path, _tests_path
        )
    )
    animation_thread.daemon = True 
    animation_thread.start()

    _mock_pdd_sync_workflow() 
    
    print("Main workflow finished. Waiting for animation thread to clean up...")
    animation_thread.join(timeout=5) 
    if animation_thread.is_alive():
        print("Animation thread still alive after timeout.")
    print("PDD Sync Animation Demo Finished.")
