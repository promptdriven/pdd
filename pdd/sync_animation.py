import threading
import time
from rich.console import Console
from rich.layout import Layout
from rich.live import Live
from rich.panel import Panel
from rich.text import Text
from typing import Dict, Tuple, Optional, Callable, List, Any

# Assuming PDD_PROMPT_COLOR etc. are defined in pdd.__init__ or passed if not global
# For now, let's use the passed colors.

PDD_LOGO_COLOR = "#00D8FF"  # Electric-Cyan from branding
PDD_TEXT_COLOR = "white"    # Default text
PDD_BRAND_PRIMARY = "#00D8FF"
PDD_BRAND_NAVY = "#0A0A23"

PDD_ASCII_LOGO_LINES = [
    "  +xxxxxxxxxxxxxxx+",
    "xxxxxxxxxxxxxxxxxxxxx+",
    "xxx                 +xx+",
    "xxx      x+           xx+",
    "xxx        x+         xxx",
    "xxx         x+        xx+",
    "xxx        x+         xx+",
    "xxx      x+          xxx",
    "xxx                +xx+",
    "xxx     +xxxxxxxxxxx+",
    "xxx   +xx+",
    "xxx  +xx+",
    "xxx+xx+",
    "xxxx+",
    "xx+",
]

# Emojis
EMOJI_HAMMER = "🔨"
EMOJI_SEEDLING = "🌱"
EMOJI_SKULL = "💀"
EMOJI_MAGNIFYING_GLASS = "🔍"
EMOJI_TEST_TUBE = "🧪"
EMOJI_WRENCH = "🔧"
EMOJI_UP_ARROW = "⬆️"

CONSOLE_WIDTH = 80  # Fixed width for layout
CONSOLE_HEIGHT = 30 # Fixed height for layout


class AnimationState:
    def __init__(self):
        self.start_time = time.monotonic()
        self.phase = "logo_expand"  # logo_expand, main_display, logo_shrink, stopped
        self.logo_expand_progress = 0
        self.main_display_start_time = 0.0
        self.logo_shrink_progress = 0
        self.blink_on = True
        self.last_blink_toggle = time.monotonic()
        self.animation_step = 0

        self.current_function_name: str = "checking"
        self.current_basename: str = "basename"
        self.current_cost: float = 0.0
        self.current_budget: float = 10.0
        self.current_prompt_color: str = "blue"
        self.current_code_color: str = "green"
        self.current_example_color: str = "yellow"
        self.current_tests_color: str = "magenta"
        self.current_prompt_path: str = "./prompts/..."
        self.current_code_path: str = "./src/..."
        self.current_example_path: str = "./examples/..."
        self.current_tests_path: str = "./tests/..."
        self.lock = threading.Lock()

    def update_params(self, function_name: str, basename: str, cost: float, budget: float,
                      prompt_color: str, code_color: str, example_color: str, tests_color: str,
                      paths: Dict[str, str]):
        with self.lock:
            self.current_function_name = function_name
            self.current_basename = basename
            self.current_cost = cost
            self.current_budget = budget
            self.current_prompt_color = prompt_color
            self.current_code_color = code_color
            self.current_example_color = example_color
            self.current_tests_color = tests_color
            self.current_prompt_path = paths.get("prompt", self.current_prompt_path)
            self.current_code_path = paths.get("code", self.current_code_path)
            self.current_example_path = paths.get("example", self.current_example_path)
            self.current_tests_path = paths.get("tests", self.current_tests_path)


def _get_box_path_text(path: str, max_len: int = 18) -> str:
    if len(path) > max_len:
        return "..." + path[-(max_len - 3):]
    # Center the text manually
    padding = max_len - len(path)
    left_pad = padding // 2
    right_pad = padding - left_pad
    return " " * left_pad + path + " " * right_pad


def _draw_box_on_grid(grid: List[List[Any]], y_start: int, x_start: int, w: int, h: int,
                      title: str, path_text: str, emoji_char_to_draw: Optional[str],
                      color_style: str, blink_on: bool):
    """Draws a box with title, path, and optional emoji onto the grid."""
    grid_height, grid_width = len(grid), len(grid[0])

    # Title with emoji
    actual_emoji = ""
    if emoji_char_to_draw:
        actual_emoji = emoji_char_to_draw if blink_on else " "
    
    display_title = f"{actual_emoji} {title}".strip()
    
    for r_offset in range(h):
        r = y_start + r_offset
        if not (0 <= r < grid_height): continue

        for c_offset in range(w):
            c = x_start + c_offset
            if not (0 <= c < grid_width): continue

            char_to_set = ' '
            style_to_set = color_style # Border color by default

            if r_offset == 0:  # Top row (border and title)
                if c_offset == 0: char_to_set = '┌'
                elif c_offset == w - 1: char_to_set = '┐'
                else: char_to_set = '─'
                
                # Overlay title (centered)
                title_start_in_box = (w - 2 - len(display_title)) // 2 
                if 0 <= c_offset - 1 - title_start_in_box < len(display_title):
                    char_to_set = display_title[c_offset - 1 - title_start_in_box]
            elif r_offset == h - 1:  # Bottom border
                if c_offset == 0: char_to_set = '└'
                elif c_offset == w - 1: char_to_set = '┘'
                else: char_to_set = '─'
            elif c_offset == 0 or c_offset == w - 1:  # Side borders
                char_to_set = '│'
            elif r_offset == 1: # Path line (second line of box)
                path_display_str = _get_box_path_text(path_text, w - 2)
                path_char_idx = c_offset - 1 
                if 0 <= path_char_idx < len(path_display_str):
                    char_to_set = path_display_str[path_char_idx]
                style_to_set = "dim " + color_style # Dim color for path
            else: # Inner empty space
                style_to_set = "default"

            grid[r][c] = (char_to_set, style_to_set)


def _plot_line_with_arrow(grid: List[List[Any]], x0: int, y0: int, x1: int, y1: int,
                         step: int, total_steps: int, line_style: str = "dim white", arrow_style: str = "bold yellow"):
    """Plots a line using Bresenham's algorithm and places an arrow along it."""
    grid_height, grid_width = len(grid), len(grid[0])
    
    dx = abs(x1 - x0)
    dy = abs(y1 - y0)
    sx = 1 if x0 < x1 else -1
    sy = 1 if y0 < y1 else -1
    err = dx - dy
    
    path_points = []
    curr_x, curr_y = x0, y0
    
    while True:
        path_points.append((curr_x, curr_y))
        if curr_x == x1 and curr_y == y1: break
        e2 = 2 * err
        next_x, next_y = curr_x, curr_y
        if e2 > -dy:
            err -= dy
            next_x += sx
        if e2 < dx:
            err += dx
            next_y += sy
        # Check if stuck (can happen with imperfect Bresenham or endpoint conditions)
        if next_x == curr_x and next_y == curr_y and (curr_x != x1 or curr_y != y1) : break 
        curr_x, curr_y = next_x, next_y


    if not path_points or len(path_points) < 2: return

    # Draw line segments (excluding start/end points, handled by boxes)
    for i in range(1, len(path_points) - 1):
        px, py = path_points[i]
        prev_px, prev_py = path_points[i-1]
        next_px, next_py = path_points[i+1] if i + 1 < len(path_points) else (px,py) # Use current if at end

        char = '─' # Default horizontal
        if py != prev_py and px != prev_px : # Diagonal from prev
            char = '\\' if (px-prev_px)*(py-prev_py) > 0 else '/'
        elif py != prev_py : char = '│' # Vertical from prev
        
        if 0 <= py < grid_height and 0 <= px < grid_width:
            grid[py][px] = (char, line_style)

    # Place arrow
    if total_steps == 0: total_steps = 1 # Avoid division by zero
    arrow_idx = min(len(path_points) - 1, (step * (len(path_points) -1)) // total_steps)
    
    ax, ay = path_points[arrow_idx]

    # Determine arrow character based on direction from previous point on path
    arrow_char = '>' # Default
    if arrow_idx > 0:
        prev_ax, prev_ay = path_points[arrow_idx-1]
        if ax > prev_ax: arrow_char = '>'
        elif ax < prev_ax: arrow_char = '<'
        elif ay > prev_ay: arrow_char = 'v'
        elif ay < prev_ay: arrow_char = '^'
    elif len(path_points) > 1: # First point, determine from next
        next_ax, next_ay = path_points[1]
        if next_ax > ax: arrow_char = '>'
        elif next_ax < ax: arrow_char = '<'
        elif next_ay > ay: arrow_char = 'v'
        elif next_ay < ay: arrow_char = '^'


    if 0 <= ay < grid_height and 0 <= ax < grid_width:
        grid[ay][ax] = (arrow_char, arrow_style)


def _create_main_content_panel(state: AnimationState) -> Panel:
    grid_height = CONSOLE_HEIGHT - 2
    grid: List[List[Any]] = [[' ' for _ in range(CONSOLE_WIDTH)] for _ in range(grid_height)]

    box_width = 22
    box_height = 3  # Title (with emoji), Path

    code_y = 1
    example_y = code_y + box_height + 1
    tests_y = example_y + box_height + 1
    prompt_y = (grid_height - box_height) // 2

    # Determine emojis
    prompt_emoji, code_emoji, example_emoji, tests_emoji = None, None, None, None
    current_func = state.current_function_name
    if current_func == "generate": code_emoji = EMOJI_HAMMER
    elif current_func == "example": example_emoji = EMOJI_SEEDLING
    elif current_func == "crash": code_emoji, example_emoji = EMOJI_SKULL, EMOJI_SKULL
    elif current_func == "verify": code_emoji, example_emoji = EMOJI_MAGNIFYING_GLASS, EMOJI_MAGNIFYING_GLASS
    elif current_func == "test": tests_emoji = EMOJI_TEST_TUBE
    elif current_func == "fix": code_emoji, tests_emoji = EMOJI_WRENCH, EMOJI_WRENCH
    elif current_func == "update": prompt_emoji = EMOJI_UP_ARROW
    elif current_func == "checking": prompt_emoji, code_emoji, example_emoji, tests_emoji = EMOJI_MAGNIFYING_GLASS, EMOJI_MAGNIFYING_GLASS, EMOJI_MAGNIFYING_GLASS, EMOJI_MAGNIFYING_GLASS

    _draw_box_on_grid(grid, prompt_y, CONSOLE_WIDTH - box_width - 3, box_width, box_height, "Prompt", state.current_prompt_path, prompt_emoji, state.current_prompt_color, state.blink_on)
    _draw_box_on_grid(grid, code_y, 2, box_width, box_height, "Code", state.current_code_path, code_emoji, state.current_code_color, state.blink_on)
    _draw_box_on_grid(grid, example_y, 2, box_width, box_height, "Example", state.current_example_path, example_emoji, state.current_example_color, state.blink_on)
    _draw_box_on_grid(grid, tests_y, 2, box_width, box_height, "Tests", state.current_tests_path, tests_emoji, state.current_tests_color, state.blink_on)

    # Connection points (center of the side facing the other group of boxes)
    P_connect_x, P_connect_y = CONSOLE_WIDTH - box_width - 3 -1, prompt_y + box_height // 2
    C_connect_x, C_connect_y = 2 + box_width, code_y + box_height // 2
    E_connect_x, E_connect_y = 2 + box_width, example_y + box_height // 2
    T_connect_x, T_connect_y = 2 + box_width, tests_y + box_height // 2
    
    total_anim_steps = 20 # For arrow movement smoothness
    anim_step = state.animation_step % total_anim_steps

    if current_func == "generate": # P -> C
        _plot_line_with_arrow(grid, P_connect_x, P_connect_y, C_connect_x, C_connect_y, anim_step, total_anim_steps)
    elif current_func == "example": # P -> E
        _plot_line_with_arrow(grid, P_connect_x, P_connect_y, E_connect_x, E_connect_y, anim_step, total_anim_steps)
    elif current_func == "crash": # C <-> E
        if (state.animation_step // total_anim_steps) % 2 == 0: _plot_line_with_arrow(grid, C_connect_x, C_connect_y, E_connect_x, E_connect_y, anim_step, total_anim_steps)
        else: _plot_line_with_arrow(grid, E_connect_x, E_connect_y, C_connect_x, C_connect_y, anim_step, total_anim_steps)
    elif current_func == "verify": # E <-> C
        if (state.animation_step // total_anim_steps) % 2 == 0: _plot_line_with_arrow(grid, E_connect_x, E_connect_y, C_connect_x, C_connect_y, anim_step, total_anim_steps)
        else: _plot_line_with_arrow(grid, C_connect_x, C_connect_y, E_connect_x, E_connect_y, anim_step, total_anim_steps)
    elif current_func == "test": # C -> T and P -> T
        _plot_line_with_arrow(grid, C_connect_x, C_connect_y, T_connect_x, T_connect_y, anim_step, total_anim_steps)
        _plot_line_with_arrow(grid, P_connect_x, P_connect_y, T_connect_x, T_connect_y, anim_step, total_anim_steps)
    elif current_func == "fix": # C <-> T
        if (state.animation_step // total_anim_steps) % 2 == 0: _plot_line_with_arrow(grid, C_connect_x, C_connect_y, T_connect_x, T_connect_y, anim_step, total_anim_steps)
        else: _plot_line_with_arrow(grid, T_connect_x, T_connect_y, C_connect_x, C_connect_y, anim_step, total_anim_steps)
    elif current_func == "update": # C -> P
        _plot_line_with_arrow(grid, C_connect_x, C_connect_y, P_connect_x, P_connect_y, anim_step, total_anim_steps)

    final_text_output = Text()
    for r_idx, row_data in enumerate(grid):
        for char_data in row_data:
            if isinstance(char_data, tuple):
                char, style = char_data
                final_text_output.append(char, style=style)
            else:
                final_text_output.append(char_data) # Should be ' '
        if r_idx < grid_height - 1:
            final_text_output.append("\n")
    
    return Panel(final_text_output, style="default", border_style=PDD_LOGO_COLOR, height=CONSOLE_HEIGHT - 2, width=CONSOLE_WIDTH)


def _create_layout_wrapper(state: AnimationState) -> Layout:
    layout = Layout(name="root", size=CONSOLE_HEIGHT)
    layout.split_column(
        Layout(name="header", size=1),
        Layout(name="main_area_container", ratio=1),
        Layout(name="footer", size=1),
    )

    header_text = Text(justify="between")
    header_text.append("Prompt Driven Development", style=f"bold {PDD_LOGO_COLOR}")
    header_text.append(state.current_basename, style="bold white")
    layout["header"].update(header_text)

    elapsed_time_seconds = int(time.monotonic() - state.start_time)
    time_str = f"{elapsed_time_seconds // 60:02d}:{elapsed_time_seconds % 60:02d}"
    cost_str = f"${state.current_cost:.2f} / ${state.current_budget:.2f}"
    
    footer_text = Text(justify="between")
    footer_text.append(state.current_function_name.upper(), style="bold white")
    footer_text.append(time_str, style="white")
    footer_text.append(cost_str, style="white")
    layout["footer"].update(footer_text)
    
    main_content_panel = _create_main_content_panel(state)
    layout["main_area_container"].update(main_content_panel)
    
    return layout


def sync_animation(
    function_name_getter: Callable[[], str],
    stop_event: threading.Event,
    basename_getter: Callable[[], str],
    cost_getter: Callable[[], float],
    budget_getter: Callable[[], float],
    prompt_color_getter: Callable[[], str],
    code_color_getter: Callable[[], str],
    example_color_getter: Callable[[], str],
    tests_color_getter: Callable[[], str],
    paths_getter: Callable[[], Dict[str, str]]
):
    console = Console()
    state = AnimationState()

    # Initial parameters from getters
    state.update_params(
        function_name_getter(), basename_getter(), cost_getter(), budget_getter(),
        prompt_color_getter(), code_color_getter(), example_color_getter(), tests_color_getter(),
        paths_getter()
    )

    with Live(console=console, refresh_per_second=10, transient=True, screen=False) as live:
        while state.phase != "stopped":
            if stop_event.is_set() and state.phase == "main_display":
                state.phase = "logo_shrink"
                state.logo_shrink_progress = len(PDD_ASCII_LOGO_LINES) # Start full for shrinking

            current_time = time.monotonic()
            if state.phase != "logo_expand" and state.phase != "logo_shrink": # Avoid updates during transitions
                state.update_params(
                    function_name_getter(), basename_getter(), cost_getter(), budget_getter(),
                    prompt_color_getter(), code_color_getter(), example_color_getter(), tests_color_getter(),
                    paths_getter()
                )

            if current_time - state.last_blink_toggle > 0.5:
                state.blink_on = not state.blink_on
                state.last_blink_toggle = current_time
            
            state.animation_step += 1

            if state.phase == "logo_expand":
                state.logo_expand_progress += 1
                if state.logo_expand_progress >= len(PDD_ASCII_LOGO_LINES):
                    state.logo_expand_progress = len(PDD_ASCII_LOGO_LINES)
                    if state.main_display_start_time == 0: # Mark when logo is fully shown
                         state.main_display_start_time = current_time
                    if current_time - state.main_display_start_time > 1.0: # Wait 1 sec
                        state.phase = "main_display"
                
                visible_logo_lines = PDD_ASCII_LOGO_LINES[len(PDD_ASCII_LOGO_LINES) - state.logo_expand_progress:]
                logo_text = Text("\n".join(visible_logo_lines), style=PDD_LOGO_COLOR, justify="center")
                
                padding_height = CONSOLE_HEIGHT - len(visible_logo_lines)
                top_pad = padding_height // 2
                bottom_pad = padding_height - top_pad
                
                display_content = Text("\n" * top_pad, justify="center") + logo_text + Text("\n" * bottom_pad, justify="center")
                live.update(Panel(display_content, border_style=PDD_LOGO_COLOR, width=CONSOLE_WIDTH, height=CONSOLE_HEIGHT))

            elif state.phase == "main_display":
                layout_to_render = _create_layout_wrapper(state)
                live.update(layout_to_render)

            elif state.phase == "logo_shrink":
                state.logo_shrink_progress -= 1
                if state.logo_shrink_progress <= 0:
                    state.phase = "stopped"
                    live.update(Text("")) # Clear screen
                    continue # Exit loop immediately
                
                visible_logo_lines = PDD_ASCII_LOGO_LINES[len(PDD_ASCII_LOGO_LINES) - state.logo_shrink_progress:]
                logo_text = Text("\n".join(visible_logo_lines), style=PDD_LOGO_COLOR, justify="center")

                padding_height = CONSOLE_HEIGHT - len(visible_logo_lines)
                top_pad = padding_height // 2
                bottom_pad = padding_height - top_pad

                display_content = Text("\n" * top_pad, justify="center") + logo_text + Text("\n" * bottom_pad, justify="center")
                live.update(Panel(display_content, border_style=PDD_LOGO_COLOR, width=CONSOLE_WIDTH, height=CONSOLE_HEIGHT))
            
            if state.phase == "stopped":
                break
            time.sleep(0.05) 

    # Optional: print a final message if not quiet
    # console.print(f"PDD Sync Animation for '{state.current_basename}' finished.", style="dim white")
