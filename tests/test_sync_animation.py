import pytest
import threading
import time
import os
from unittest.mock import MagicMock, patch, call, ANY
from datetime import datetime, timedelta

# Assuming the module is in pdd.sync_animation based on typical structure
# Adjust if the actual path is different
from pdd.sync_animation import (
    sync_animation,
    AnimationState,
    _get_valid_color,
    _shorten_path,
    _render_animation_frame,
    _draw_connecting_lines_and_arrows,
    _get_path_waypoints,
    _final_logo_animation_sequence,
    DEEP_NAVY, ELECTRIC_CYAN,
    DEFAULT_PROMPT_COLOR, DEFAULT_CODE_COLOR, DEFAULT_EXAMPLE_COLOR, DEFAULT_TESTS_COLOR,
    PDD_LOGO_ASCII, LOGO_HEIGHT, LOGO_MAX_WIDTH, CONSOLE_WIDTH, ANIMATION_BOX_HEIGHT
)

# For testing emojis as per prompt, as CLoU has them empty.
# This dictionary will be used to patch the EMOJIS in the module.
TEST_EMOJIS_FROM_PROMPT = {
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
    "checking": "🔍"
}

@pytest.fixture(autouse=True)
def patch_emojis():
    with patch("pdd.sync_animation.EMOJIS", TEST_EMOJIS_FROM_PROMPT):
        yield

@pytest.fixture
def mock_console_obj():
    console = MagicMock()
    console.width = CONSOLE_WIDTH
    console.height = 24 # A typical terminal height
    return console

@pytest.fixture
def mock_live_obj():
    live_manager = MagicMock()
    live_instance = MagicMock()
    live_manager.__enter__.return_value = live_instance
    return live_manager, live_instance

# --- AnimationState Tests ---

def test_animation_state_initialization():
    state = AnimationState("test_base", 10.0)
    assert state.current_function_name == "checking"
    assert state.basename == "test_base"
    assert state.cost == 0.0
    assert state.budget == 10.0
    assert isinstance(state.start_time, datetime)
    assert state.paths == {"prompt": "", "code": "", "example": "", "tests": ""}
    assert state.colors["prompt"] == DEFAULT_PROMPT_COLOR
    assert state.scroll_offsets == {"prompt": 0, "code": 0, "example": 0, "tests": 0}
    assert state.path_box_content_width == 16

def test_animation_state_initialization_no_budget():
    state = AnimationState("test_base_no_budget", None)
    assert state.budget == float('inf')

def test_animation_state_update_dynamic_state():
    state = AnimationState("test", 5.0)
    state.update_dynamic_state("GENERATE", 1.23, "p.py", "c.py", "e.py", "t.py")
    assert state.current_function_name == "generate"
    assert state.cost == 1.23
    assert state.paths["prompt"] == "p.py"
    assert state.paths["code"] == "c.py"
    assert state.paths["example"] == "e.py"
    assert state.paths["tests"] == "t.py"

    state.update_dynamic_state(None, None, "", "", "", "") # Test None inputs
    assert state.current_function_name == "checking"
    assert state.cost == 1.23 # Cost should not change if None
    assert state.paths["prompt"] == ""

def test_animation_state_set_box_colors():
    state = AnimationState("test", 5.0)
    state.set_box_colors("red", "blue", "green", "yellow")
    assert state.colors["prompt"] == "red"
    assert state.colors["code"] == "blue"
    assert state.colors["example"] == "green"
    assert state.colors["tests"] == "yellow"

    state.set_box_colors(None, 123, [], "valid_color") # Test invalid inputs
    assert state.colors["prompt"] == DEFAULT_PROMPT_COLOR
    assert state.colors["code"] == DEFAULT_CODE_COLOR # 123 is invalid
    assert state.colors["example"] == DEFAULT_EXAMPLE_COLOR # [] is invalid
    assert state.colors["tests"] == "valid_color"


@patch("pdd.sync_animation.datetime")
def test_animation_state_get_elapsed_time_str(mock_datetime):
    start_time = datetime(2023, 1, 1, 12, 0, 0)
    current_time = datetime(2023, 1, 1, 12, 1, 30)
    mock_datetime.now.return_value = current_time
    
    state = AnimationState("test", 5.0)
    state.start_time = start_time # Override start time
    
    assert state.get_elapsed_time_str() == "0:01:30"

def test_animation_state_render_scrolling_path():
    state = AnimationState("test", 5.0)
    state.path_box_content_width = 10 # For easier testing

    # Empty path
    state.paths["prompt"] = ""
    assert state._render_scrolling_path("prompt", 10) == "          " # Centered empty

    # Short path
    state.paths["prompt"] = "short.py"
    assert state._render_scrolling_path("prompt", 10) == " short.py " # Centered

    # Long path - scrolling
    state.paths["prompt"] = "this_is_a_very_long_path_name.py"
    expected_len = len("this_is_a_very_long_path_name.py")
    
    first_scroll = state._render_scrolling_path("prompt", 10)
    assert len(first_scroll) == 10
    assert first_scroll == " this_is_a_"
    assert state.scroll_offsets["prompt"] == 1

    second_scroll = state._render_scrolling_path("prompt", 10)
    assert second_scroll == "this_is_a_v"
    assert state.scroll_offsets["prompt"] == 2
    
    # Scroll to wrap around
    for _ in range(expected_len + 4): # +4 for " :: "
        state._render_scrolling_path("prompt", 10)
    
    final_offset = state.scroll_offsets["prompt"]
    # Check if it wrapped around to a small number
    assert final_offset < (expected_len + 4)


def test_animation_state_get_emoji_for_box():
    state = AnimationState("test", 5.0)
    
    # Checking
    state.current_function_name = "checking"
    assert state.get_emoji_for_box("prompt", True) == TEST_EMOJIS_FROM_PROMPT["checking"] + " "
    assert state.get_emoji_for_box("code", False) == "  " # Blink off

    # Generate
    state.current_function_name = "generate"
    assert state.get_emoji_for_box("code", True) == TEST_EMOJIS_FROM_PROMPT["generate"] + " "
    assert state.get_emoji_for_box("prompt", True) == "  " # No emoji for prompt

    # Crash
    state.current_function_name = "crash"
    assert state.get_emoji_for_box("code", True) == TEST_EMOJIS_FROM_PROMPT["crash_code"] + " "
    assert state.get_emoji_for_box("example", True) == TEST_EMOJIS_FROM_PROMPT["crash_example"] + " "

    # Unknown command
    state.current_function_name = "unknown_command"
    assert state.get_emoji_for_box("prompt", True) == "  "


# --- Helper Function Tests ---

def test_get_valid_color():
    assert _get_valid_color("blue", "red") == "blue"
    assert _get_valid_color(None, "red") == "red"
    assert _get_valid_color(123, "red") == "red" # Non-string

@patch("pdd.sync_animation.os.path.relpath")
@patch("pdd.sync_animation.os.getcwd", return_value="/current/work/dir")
def test_shorten_path(mock_getcwd, mock_relpath):
    # Path shorter than max_len
    assert _shorten_path("/current/work/dir/file.py", 30) == "file.py"
    mock_relpath.assert_called_with("/current/work/dir/file.py", start="/current/work/dir")
    mock_relpath.return_value = "file.py"

    # Relative path is shorter
    mock_relpath.return_value = "short_rel/file.py" # 17 chars
    assert _shorten_path("/abs/path/to/very/long/file.py", 20) == "short_rel/file.py"

    # Basename is shorter
    mock_relpath.return_value = "a/very/long/relative/path/to/file.py" # > 15
    assert _shorten_path("/abs/path/to/very/long/file.py", 15) == "file.py" # basename

    # Truncation
    mock_relpath.return_value = "a/very/long/relative/path/to/super_long_filename.py"
    assert _shorten_path("/abs/path/to/very/long/file.py", 10) == "...ename.py" # "super_long_filename.py" -> "...ename.py"

    # Empty path
    assert _shorten_path("", 10) == ""
    assert _shorten_path(None, 10) == ""

    # Relpath fails (e.g. different drive)
    mock_relpath.side_effect = ValueError("Cannot make relative path")
    assert _shorten_path("D:\\another\\drive\\file.py", 10) == "...file.py"
    # Check os.path.basename was used
    with patch("pdd.sync_animation.os.path.basename", return_value="file.py") as mock_basename_call:
         _shorten_path("D:\\another\\drive\\file.py", 10)
         mock_basename_call.assert_called_with("D:\\another\\drive\\file.py")


# --- Animation Rendering Logic Tests ---
# Note: These test the *structure* and *content* passed to Rich, not visual output.

def test_draw_connecting_lines_and_arrows_structure():
    state = AnimationState("test", 5.0)
    lines = _draw_connecting_lines_and_arrows(state, CONSOLE_WIDTH)
    assert len(lines) == 5
    for line_text_obj in lines:
        assert isinstance(line_text_obj, MagicMock) # Rich Text objects are complex, Align returns a renderable
                                                    # Actually, the code returns Text directly, or Align(Text)
                                                    # The code returns List[Text] or List[Align]
                                                    # _draw_connecting_lines_and_arrows returns List[Text] or List[Align(Text)]
                                                    # The current code returns List[Align(Text)] for line1, and List[Text] for lines 2,3
                                                    # Let's check the type of the elements.
                                                    # The first element is Align, others are Text
        # For simplicity, we'll check if they are not None. Detailed content check below.
        assert line_text_obj is not None


@pytest.mark.parametrize("command, frame_count_for_arrow_visibility", [
    ("generate", 0), ("generate", 5), # Arrow visible, then not
    ("example", 0),
    ("update", 0),
    ("crash", 0), ("crash", 10), # Test direction change for crash
])
def test_draw_connecting_lines_and_arrows_commands_with_arrows(command, frame_count_for_arrow_visibility):
    state = AnimationState("test", 5.0)
    state.current_function_name = command
    state.frame_count = frame_count_for_arrow_visibility # To control blinking/movement

    # console_width for _draw_connecting_lines_and_arrows is main_panel_width - 4
    # If main panel is CONSOLE_WIDTH (80), then internal_width = 76
    internal_width = CONSOLE_WIDTH - 4
    lines = _draw_connecting_lines_and_arrows(state, internal_width)
    
    line2_text = lines[1].plain # This is a Text object

    # Check if an arrow character is present in line2
    # Arrow is ">" or "<"
    arrow_present = ">" in line2_text or "<" in line2_text
    
    # For blinking arrows, check visibility based on frame_count
    blink_on = (state.frame_count // 5) % 2 == 0
    if blink_on:
        assert arrow_present, f"Arrow should be visible for {command} at frame {state.frame_count}"
    else:
        assert not arrow_present, f"Arrow should NOT be visible for {command} at frame {state.frame_count}"

    # Verify line characters are empty (as per CLoU)
    # Example: prompt_x = internal_width // 2 = 38
    # code_x = internal_width // 4 = 19
    # Line 1: Text(" " * (prompt_x -1) + "")
    line1_content = lines[0].renderable.plain # Accessing plain text of the Text object inside Align
    assert line1_content.strip() == "", "Line 1 should be empty except for spaces"

    # Line 2 (where arrows are) should mostly be spaces if not an arrow
    # This is hard to assert precisely without knowing arrow position.
    # We've checked arrow presence. Other chars should be " " or "" (empty string from join)

    # Line 3: Text("".join(line3_parts), style=ELECTRIC_CYAN)
    # line3_parts has "" at x_target-1 positions.
    line3_text = lines[2].plain
    assert line3_text.strip() == "", "Line 3 should be empty except for spaces"


@pytest.mark.parametrize("command", ["verify", "test", "fix", "checking", "auto-deps", "some_other_command"])
def test_draw_connecting_lines_and_arrows_commands_default_no_arrows(command):
    state = AnimationState("test", 5.0)
    state.current_function_name = command
    state.frame_count = 0 # Arrow would be visible if logic existed

    internal_width = CONSOLE_WIDTH - 4
    lines = _draw_connecting_lines_and_arrows(state, internal_width)
    line2_text = lines[1].plain

    assert ">" not in line2_text
    assert "<" not in line2_text
    # And lines should be "empty" as per CLoU
    assert lines[0].renderable.plain.strip() == ""
    assert lines[2].plain.strip() == ""


@patch("pdd.sync_animation._draw_connecting_lines_and_arrows")
@patch.object(AnimationState, "_render_scrolling_path", side_effect=lambda key: f"scrolled_{key}")
@patch.object(AnimationState, "get_emoji_for_box", side_effect=lambda key, blink: f"emoji_{key}_{blink}")
@patch.object(AnimationState, "get_elapsed_time_str", return_value="0:01:00")
def test_render_animation_frame_structure_and_content(
    mock_get_elapsed_time, mock_get_emoji, mock_render_scrolling, mock_draw_lines
):
    mock_draw_lines.return_value = [MagicMock(), MagicMock(), MagicMock()] # Simulate 3 lines
    state = AnimationState("my_basename", 100.50)
    state.cost = 10.25
    state.current_function_name = "generate"
    state.frame_count = 0 # For predictable blink state (True)

    # Call the function
    panel = _render_animation_frame(state, CONSOLE_WIDTH)

    # Basic checks
    assert panel.style == f"{ELECTRIC_CYAN} on {DEEP_NAVY}"
    assert panel.height == ANIMATION_BOX_HEIGHT
    assert panel.width == CONSOLE_WIDTH
    
    layout = panel.renderable # This is the Layout object

    # Header checks
    header_content = layout["header"].renderable # This is a Table
    # To check table content, you'd typically need to render it or inspect its rows/columns.
    # For simplicity, we'll assume Rich's Table works and check if state values were used.
    # This requires a deeper dive into Rich's internals or a visual check.
    # Let's check if the mock calls were made for dynamic parts.
    
    # Footer checks
    mock_get_elapsed_time.assert_called_once()
    # Footer text would be like: "Running: Generate", "Elapsed: 0:01:00", "Cost: $10.25 / Budget: $100.50"

    # Body - Org Chart Panels
    # Example: Prompt Panel
    mock_render_scrolling.assert_any_call("prompt")
    mock_get_emoji.assert_any_call("prompt", True) # True because frame_count 0 -> blink_on True

    # Check if _draw_connecting_lines_and_arrows was called
    mock_draw_lines.assert_called_once_with(state, CONSOLE_WIDTH - 4)

    assert state.frame_count == 1 # Incremented

    # Test budget N/A
    state.budget = float('inf')
    state.frame_count = 0 # Reset for next call
    _render_animation_frame(state, CONSOLE_WIDTH) # Call again
    # A more robust test would capture the arguments to Panel/Text for footer.


# --- Animation Sequence Tests ---

# @patch("pdd.sync_animation.time.sleep")
# def test_initial_logo_animation_sequence_success(mock_sleep, mock_console_obj):
#     stop_event = threading.Event()
#     
#     # Simulate console height being just enough for the logo
#     mock_console_obj.height = LOGO_HEIGHT 
#     
#     result = _initial_logo_animation_sequence(mock_console_obj, stop_event)
#     assert result is True
#     mock_console_obj.clear.assert_any_call() # Called at start and end
#     
#     # Check print calls for logo lines
#     expected_print_calls = LOGO_HEIGHT # for each line reveal
#     # Each reveal prints multiple lines, plus cursor movements
#     # This is complex to assert precisely. Let's check key parts.
#     assert mock_console_obj.print.call_count > LOGO_HEIGHT 
#     
#     # Check that logo lines were printed (simplified check)
#     printed_text_combined = "".join(
#         str(arg[0]) for call_args in mock_console_obj.print.call_args_list for arg in call_args.args if isinstance(arg[0], MagicMock) # Rich Text
#     )
#     # This check is too fragile. Better to check for specific logo lines.
#     # Example: Check if the first line of the logo was part of any print call
#     # This requires inspecting the `Text` objects passed to print.
# 
#     # Check sleeps
#     assert mock_sleep.call_count == LOGO_HEIGHT + 1 # N in loop, 1 after
#     mock_sleep.assert_any_call(0.05)
#     mock_sleep.assert_any_call(1)


# @patch("pdd.sync_animation.time.sleep")
# def test_initial_logo_animation_sequence_stop_early(mock_sleep, mock_console_obj):
#     stop_event = threading.Event()
#     stop_event.set() # Stop immediately
#     
#     result = _initial_logo_animation_sequence(mock_console_obj, stop_event)
#     assert result is False
#     mock_console_obj.clear.assert_called_once() # Only at the start
#     # No long sleep, minimal prints
#     assert mock_sleep.call_count == 0


@patch("pdd.sync_animation.time.sleep")
def test_final_logo_animation_sequence(mock_sleep, mock_console_obj):
    _final_logo_animation_sequence(mock_console_obj)
    
    assert mock_console_obj.clear.call_count == 2 # Start and end
    mock_console_obj.print.assert_called_once() # For the Panel
    # Check that a Panel was printed
    assert isinstance(mock_console_obj.print.call_args[0][0].renderable, MagicMock) # Align(Panel)
    
    mock_sleep.assert_called_once_with(1)


# --- sync_animation Main Function Tests ---

@patch("pdd.sync_animation.Console", return_value=MagicMock(width=CONSOLE_WIDTH, height=24))
@patch("pdd.sync_animation.Live")
@patch("pdd.sync_animation._initial_logo_animation_sequence", return_value=True)
@patch("pdd.sync_animation._final_logo_animation_sequence")
@patch("pdd.sync_animation.time.sleep") # Mock sleep in the main loop
@patch("pdd.sync_animation._render_animation_frame")
def test_sync_animation_full_lifecycle(
    mock_render_frame, mock_loop_sleep, mock_final_seq, mock_initial_seq, mock_Live, mock_ConsoleCls
):
    mock_live_manager, mock_live_instance = mock_Live.return_value, mock_Live.return_value.__enter__.return_value
    
    fn_ref, cost_ref, p_path, c_path, e_path, t_path = ["gen"], [0.1], ["p"], ["c"], ["e"], ["t"]
    stop_event = threading.Event()

    def side_effect_live_update(*args):
        # Simulate a few iterations then stop
        if mock_live_instance.update.call_count >= 2:
            stop_event.set()

    mock_live_instance.update.side_effect = side_effect_live_update
    mock_render_frame.return_value = "frame_content"

    sync_animation(
        fn_ref, stop_event, "basename", cost_ref, 10.0,
        "red", "blue", "green", "yellow",
        p_path, c_path, e_path, t_path
    )

    mock_ConsoleCls.assert_called_once_with(width=CONSOLE_WIDTH)
    mock_initial_seq.assert_called_once()
    mock_Live.assert_called_once_with(console=ANY, refresh_per_second=10, transient=False, screen=True)
    
    assert mock_render_frame.call_count == 2 # Due to side_effect_live_update
    # Check if AnimationState was updated inside the loop (indirectly by _render_frame calls)
    # First call to _render_frame gets the initial state
    # Second call should reflect any changes if refs were modified (not done in this simple test)
    
    mock_loop_sleep.assert_called_with(0.1) # From the loop
    assert mock_loop_sleep.call_count == 2

    mock_final_seq.assert_called_once()


@patch("pdd.sync_animation.Console")
@patch("pdd.sync_animation.Live")
@patch("pdd.sync_animation._initial_logo_animation_sequence", return_value=False) # Stop early
@patch("pdd.sync_animation._final_logo_animation_sequence")
def test_sync_animation_stops_if_initial_fails(
    mock_final_seq, mock_initial_seq, mock_Live, mock_ConsoleCls
):
    fn_ref, cost_ref, p_path, c_path, e_path, t_path = [""], [0.0], [""], [""], [""], [""]
    stop_event = threading.Event()

    sync_animation(
        fn_ref, stop_event, "basename", cost_ref, 10.0,
        "red", "blue", "green", "yellow",
        p_path, c_path, e_path, t_path
    )
    
    mock_initial_seq.assert_called_once()
    mock_final_seq.assert_called_once() # Called due to early exit
    mock_Live.assert_not_called() # Live loop should not start


@patch("pdd.sync_animation.Console", return_value=MagicMock(width=CONSOLE_WIDTH, height=24))
@patch("pdd.sync_animation.Live")
@patch("pdd.sync_animation._initial_logo_animation_sequence", return_value=True)
@patch("pdd.sync_animation._final_logo_animation_sequence")
@patch("pdd.sync_animation.time.sleep")
@patch("pdd.sync_animation._render_animation_frame", side_effect=Exception("Test Render Error"))
def test_sync_animation_exception_in_loop(
    mock_render_frame, mock_loop_sleep, mock_final_seq, mock_initial_seq, mock_Live, mock_ConsoleCls
):
    mock_console_instance = mock_ConsoleCls.return_value
    mock_live_manager, mock_live_instance = mock_Live.return_value, mock_Live.return_value.__enter__.return_value
    
    fn_ref, cost_ref, p_path, c_path, e_path, t_path = ["gen"], [0.1], ["p"], ["c"], ["e"], ["t"]
    stop_event = threading.Event()

    # Let it run once, then raise exception
    def side_effect_live_update_then_error(*args):
        if mock_live_instance.update.call_count >= 1:
             # This exception will be caught by the try/except in sync_animation
            raise Exception("Test Render Error from live.update")

    mock_live_instance.update.side_effect = side_effect_live_update_then_error
    
    sync_animation(
        fn_ref, stop_event, "basename", cost_ref, 10.0,
        "red", "blue", "green", "yellow",
        p_path, c_path, e_path, t_path
    )

    mock_final_seq.assert_called_once() # Should be called in finally
    mock_console_instance.print_exception.assert_called_once()


# Example of how the main thread might update refs (for conceptual understanding)
# This is not a test itself, but informs how to test dynamic updates.
def _example_main_thread_update(refs_tuple, stop_event):
    fn_ref, cost_ref, p_path_ref, _, _, _ = refs_tuple
    time.sleep(0.2) # Let animation start
    fn_ref[0] = "new_function"
    cost_ref[0] = 1.0
    p_path_ref[0] = "new_prompt.py"
    time.sleep(0.2)
    stop_event.set()

# To test dynamic updates more thoroughly, one would run sync_animation in a thread,
# modify the refs from the main test thread, and then assert that AnimationState
# (perhaps by mocking _render_animation_frame and inspecting its 'state' argument)
# reflects these changes. This is more involved.
# The current test_sync_animation_full_lifecycle checks that the loop runs and calls
# _render_animation_frame, which implicitly uses the updated state.