import pytest
import threading
import time
from unittest.mock import MagicMock, patch, call

from rich.layout import Layout
from rich.panel import Panel
from rich.text import Text

# Assuming the code under test is in pdd.sync_animation
from pdd import sync_animation as pdd_sync_animation_module

# Import the class and constants from the module
AnimationState = pdd_sync_animation_module.AnimationState
PDD_ASCII_LOGO_LINES = pdd_sync_animation_module.PDD_ASCII_LOGO_LINES
CONSOLE_HEIGHT = pdd_sync_animation_module.CONSOLE_HEIGHT
CONSOLE_WIDTH = pdd_sync_animation_module.CONSOLE_WIDTH
EMOJI_HAMMER = pdd_sync_animation_module.EMOJI_HAMMER
EMOJI_SEEDLING = pdd_sync_animation_module.EMOJI_SEEDLING
EMOJI_SKULL = pdd_sync_animation_module.EMOJI_SKULL
EMOJI_MAGNIFYING_GLASS = pdd_sync_animation_module.EMOJI_MAGNIFYING_GLASS
EMOJI_TEST_TUBE = pdd_sync_animation_module.EMOJI_TEST_TUBE
EMOJI_WRENCH = pdd_sync_animation_module.EMOJI_WRENCH
EMOJI_UP_ARROW = pdd_sync_animation_module.EMOJI_UP_ARROW


# Helper to run animation in a thread
def run_animation_in_thread_helper(target_func, *args):
    thread = threading.Thread(target=target_func, args=args)
    thread.daemon = True
    thread.start()
    return thread

def get_plain_text_from_renderable(renderable) -> str:
    if hasattr(renderable, 'plain'):
        return renderable.plain
    if isinstance(renderable, Layout):
        # Crude way to get text from layout for basic checks
        # A more sophisticated parser would be needed for exact layout text
        texts = []
        for region_name in renderable.map:
            region = renderable.map[region_name]
            if region.renderable:
                 texts.append(get_plain_text_from_renderable(region.renderable))
        return "\n".join(texts)
    if isinstance(renderable, Panel):
        return get_plain_text_from_renderable(renderable.renderable)
    if isinstance(renderable, str):
        return renderable
    return ""

class TestAnimationState:

    def test_animation_state_initialization(self):
        state = AnimationState()
        assert state.phase == "logo_expand"
        assert state.logo_expand_progress == 0
        assert state.current_function_name == "checking"
        assert state.current_basename == "basename"
        assert state.current_cost == 0.0
        assert state.current_budget == 10.0
        assert state.current_prompt_path == "./prompts/..."
        # ... check other defaults

    def test_animation_state_update_params(self):
        state = AnimationState()
        new_paths = {
            "prompt": "./new/prompt.txt",
            "code": "/abs/new/code.py",
            "example": "example.js",
            "tests": "test_module.rs"
        }
        state.update_params(
            function_name="generate", basename="new_base", cost=5.5, budget=20.0,
            prompt_color="red", code_color="blue", example_color="green", tests_color="purple",
            paths=new_paths
        )
        assert state.current_function_name == "generate"
        assert state.current_basename == "new_base"
        assert state.current_cost == 5.5
        assert state.current_budget == 20.0
        assert state.current_prompt_color == "red"
        assert state.current_code_path == "/abs/new/code.py"
        assert state.current_example_path == "example.js"
        assert state.current_tests_path == "test_module.rs"

    def test_animation_state_update_params_missing_path_keys(self):
        state = AnimationState()
        initial_prompt_path = state.current_prompt_path
        new_paths = {"code": "./new/code.py"} # Missing prompt, example, tests
        state.update_params("test", "b", 0, 0, "c1", "c2", "c3", "c4", new_paths)
        assert state.current_prompt_path == initial_prompt_path # Should retain old
        assert state.current_code_path == "./new/code.py"

    def test_animation_state_update_params_edge_cases_none_values(self):
        state = AnimationState()
        paths = {}
        # Test None for function_name - expect SUT to fail later if not handled
        with pytest.raises(AttributeError, match="'NoneType' object has no attribute 'upper'"):
            # This specific error happens in _create_layout_wrapper, not update_params
            # To test update_params directly, we'd need to call the animation loop
            # For now, just check it stores None
            state.update_params(None, "basename", 0,0,"c1","c2","c3","c4",paths)
            assert state.current_function_name is None
            # The actual error would occur when sync_animation tries to use this state.
            # We'll test that in the sync_animation tests.

        # Test None for basename
        state.update_params("func", None, 0,0,"c1","c2","c3","c4",paths)
        assert state.current_basename is None

        # Test None for cost
        state.update_params("func", "base", None, 0,"c1","c2","c3","c4",paths)
        assert state.current_cost is None


@pytest.fixture
def mock_getters_event():
    getters = {
        "function_name": MagicMock(return_value="checking"),
        "basename": MagicMock(return_value="test_base"),
        "cost": MagicMock(return_value=1.23),
        "budget": MagicMock(return_value=10.0),
        "prompt_color": MagicMock(return_value="blue"),
        "code_color": MagicMock(return_value="green"),
        "example_color": MagicMock(return_value="yellow"),
        "tests_color": MagicMock(return_value="magenta"),
        "paths": MagicMock(return_value={
            "prompt": "./p.prompt", "code": "./c.py", "example": "./e.py", "tests": "./t.py"
        })
    }
    stop_event = threading.Event()
    return getters, stop_event

@pytest.fixture
def captured_output_live(monkeypatch):
    captured_updates = []
    class MockLive:
        def __init__(self, console, refresh_per_second, transient, screen):
            self.console = console
            captured_updates.append(("__init__", console, refresh_per_second, transient, screen))
        def __enter__(self):
            captured_updates.append(("__enter__",))
            return self
        def __exit__(self, exc_type, exc_val, exc_tb):
            captured_updates.append(("__exit__", exc_type, exc_val, exc_tb))
        def update(self, renderable):
            captured_updates.append(("update", renderable))
        def stop(self): # Ensure stop is also captured if called
            captured_updates.append(("stop",))


    monkeypatch.setattr(pdd_sync_animation_module, "Live", MockLive)
    return captured_updates

@pytest.fixture
def mock_time_monotonic(monkeypatch):
    mock_time = MagicMock()
    mock_time.current_time = 0.0  # Start time at 0

    def advance_time(seconds):
        mock_time.current_time += seconds

    mock_time.side_effect = lambda: mock_time.current_time
    mock_time.advance = advance_time # Attach helper to mock

    monkeypatch.setattr(pdd_sync_animation_module.time, "monotonic", mock_time)
    return mock_time


class TestSyncAnimation:

    def test_sync_animation_lifecycle_logo_expand_main_shrink_stop(self, mock_getters_event, captured_output_live, mock_time_monotonic):
        getters, stop_event = mock_getters_event

        animation_thread = run_animation_in_thread_helper(
            pdd_sync_animation_module.sync_animation,
            getters["function_name"], stop_event, getters["basename"], getters["cost"], getters["budget"],
            getters["prompt_color"], getters["code_color"], getters["example_color"], getters["tests_color"],
            getters["paths"]
        )

        # Logo Expansion Phase
        max_logo_lines = len(PDD_ASCII_LOGO_LINES)
        for i in range(max_logo_lines + 2): # A few steps for expansion
            mock_time_monotonic.advance(0.1)
            time.sleep(0.01) # Allow thread to run
        
        update_calls = [item for item in captured_output_live if item[0] == "update"]
        assert len(update_calls) > 0
        
        # Check for expanding logo panels
        logo_panel_found = False
        for _, renderable in update_calls:
            if isinstance(renderable, Panel):
                content_text = get_plain_text_from_renderable(renderable.renderable)
                if PDD_ASCII_LOGO_LINES[-1] in content_text: # Check for a line from the logo
                    logo_panel_found = True
                    break
        assert logo_panel_found, "Logo panel not found during expansion"
        
        initial_update_count = len(update_calls)

        # Transition to Main Display (after 1s of full logo)
        mock_time_monotonic.advance(1.1) # Ensure > 1s passes after logo is fully expanded
        time.sleep(0.01) # Allow thread to run a few more times

        update_calls_after_main_transition = [item for item in captured_output_live if item[0] == "update"]
        assert len(update_calls_after_main_transition) > initial_update_count
        
        last_renderable = update_calls_after_main_transition[-1][1]
        assert isinstance(last_renderable, Layout), "Main display should be a Layout"
        
        # Check header/footer of main display
        header_text = get_plain_text_from_renderable(last_renderable["header"].renderable)
        assert "Prompt Driven Development" in header_text
        assert "test_base" in header_text # from mock_getters_event

        footer_text = get_plain_text_from_renderable(last_renderable["footer"].renderable)
        assert "CHECKING" in footer_text # Initial function
        assert "0.00 / $10.00" in footer_text # Cost/budget

        # Stop Event and Logo Shrink
        stop_event.set()
        mock_time_monotonic.advance(0.1) # Allow shrink to start
        time.sleep(0.01)
        
        # Shrink phase will also produce Panel updates
        # For simplicity, we'll check the final clear screen
        for _ in range(max_logo_lines + 5): # More steps than lines to ensure it finishes
            mock_time_monotonic.advance(0.1)
            time.sleep(0.01)
            if not animation_thread.is_alive():
                break
        
        assert not animation_thread.is_alive(), "Animation thread did not terminate"
        
        # Check for final screen clear
        assert captured_output_live[-1][0] == "update", "Last captured call should be an update"
        final_renderable = captured_output_live[-1][1]
        assert isinstance(final_renderable, Text) and final_renderable.plain == "", "Screen not cleared at the end"


    def test_sync_animation_main_display_dynamic_content_updates(self, mock_getters_event, captured_output_live, mock_time_monotonic):
        getters, stop_event = mock_getters_event

        run_animation_in_thread_helper(
            pdd_sync_animation_module.sync_animation,
            getters["function_name"], stop_event, getters["basename"], getters["cost"], getters["budget"],
            getters["prompt_color"], getters["code_color"], getters["example_color"], getters["tests_color"],
            getters["paths"]
        )

        # Reach main display
        for _ in range(len(PDD_ASCII_LOGO_LINES) + 2): mock_time_monotonic.advance(0.1)
        mock_time_monotonic.advance(1.1)
        time.sleep(0.05) # Let it settle in main_display

        # Update getter return values
        getters["function_name"].return_value = "generate"
        getters["basename"].return_value = "updated_base"
        getters["cost"].return_value = 5.50
        getters["budget"].return_value = 15.00
        getters["paths"].return_value = {"prompt": "./new_p.prompt", "code": "./new_c.py"}

        mock_time_monotonic.advance(0.2) # Allow refresh
        time.sleep(0.01)

        update_calls = [item for item in captured_output_live if item[0] == "update"]
        last_layout = update_calls[-1][1]
        assert isinstance(last_layout, Layout)

        header_text = get_plain_text_from_renderable(last_layout["header"].renderable)
        assert "updated_base" in header_text

        footer_text = get_plain_text_from_renderable(last_layout["footer"].renderable)
        assert "GENERATE" in footer_text
        assert "$5.50 / $15.00" in footer_text
        
        main_content_panel_text = get_plain_text_from_renderable(last_layout["main_area_container"].renderable.renderable)
        assert "new_p.prompt" in main_content_panel_text # Check if path is visible
        assert "new_c.py" in main_content_panel_text

        stop_event.set()
        time.sleep(0.1) # Allow thread to stop

    @pytest.mark.parametrize("command_name, expected_emoji_or_arrow", [
        ("generate", EMOJI_HAMMER),
        ("example", EMOJI_SEEDLING),
        ("crash", EMOJI_SKULL),
        ("verify", EMOJI_MAGNIFYING_GLASS),
        ("test", EMOJI_TEST_TUBE),
        ("fix", EMOJI_WRENCH),
        ("update", EMOJI_UP_ARROW),
        ("checking", EMOJI_MAGNIFYING_GLASS),
        ("generate", ">"), # Arrow for generate
    ])
    def test_sync_animation_command_specific_visuals(self, command_name, expected_emoji_or_arrow, mock_getters_event, captured_output_live, mock_time_monotonic):
        getters, stop_event = mock_getters_event
        getters["function_name"].return_value = command_name

        run_animation_in_thread_helper(
            pdd_sync_animation_module.sync_animation,
            getters["function_name"], stop_event, getters["basename"], getters["cost"], getters["budget"],
            getters["prompt_color"], getters["code_color"], getters["example_color"], getters["tests_color"],
            getters["paths"]
        )

        for _ in range(len(PDD_ASCII_LOGO_LINES) + 2): mock_time_monotonic.advance(0.1)
        mock_time_monotonic.advance(1.1)
        time.sleep(0.05) 

        update_calls = [item for item in captured_output_live if item[0] == "update"]
        last_layout = update_calls[-1][1]
        assert isinstance(last_layout, Layout)

        footer_text = get_plain_text_from_renderable(last_layout["footer"].renderable)
        assert command_name.upper() in footer_text

        main_content_panel = last_layout["main_area_container"].renderable
        assert isinstance(main_content_panel, Panel)
        main_content_text = get_plain_text_from_renderable(main_content_panel.renderable)
        
        assert expected_emoji_or_arrow in main_content_text, f"Expected '{expected_emoji_or_arrow}' for command '{command_name}' not found in panel text."

        stop_event.set()
        time.sleep(0.1)

    def test_sync_animation_path_truncation_visual_effect(self, mock_getters_event, captured_output_live, mock_time_monotonic):
        getters, stop_event = mock_getters_event
        long_path = "a/b/c/d/e/f/g/h/i/j/k/l/m/n/o/p/q/r/s/t/u/v/w/x/y/z_very_long_file_name.py"
        getters["paths"].return_value = {"prompt": long_path, "code": "./short.py"}

        run_animation_in_thread_helper(
            pdd_sync_animation_module.sync_animation,
            getters["function_name"], stop_event, getters["basename"], getters["cost"], getters["budget"],
            getters["prompt_color"], getters["code_color"], getters["example_color"], getters["tests_color"],
            getters["paths"]
        )
        for _ in range(len(PDD_ASCII_LOGO_LINES) + 2): mock_time_monotonic.advance(0.1)
        mock_time_monotonic.advance(1.1)
        time.sleep(0.05)

        update_calls = [item for item in captured_output_live if item[0] == "update"]
        last_layout = update_calls[-1][1]
        main_content_text = get_plain_text_from_renderable(last_layout["main_area_container"].renderable.renderable)

        # _get_box_path_text truncates to max_len=18 (default in its signature, but called with w-2=20 from _draw_box_on_grid)
        # The box width is 22, path area is 20.
        # "..." + path[-(20-3):] = "..." + path[-17:]
        expected_truncated_path_segment = "..." + long_path[-(20-3):] 
        assert expected_truncated_path_segment in main_content_text
        assert long_path not in main_content_text # Full long path should not be there
        assert "./short.py" in main_content_text # Short path should be there fully

        stop_event.set()
        time.sleep(0.1)

    @pytest.mark.parametrize("getter_to_make_none, expected_exception", [
        ("function_name", AttributeError), # .upper() on None
        ("cost", TypeError),          # format None as float
        ("budget", TypeError),        # format None as float
        # Basename=None might be handled by Rich or might cause issues depending on Rich version.
        # For now, focusing on clear error sources.
    ])
    def test_sync_animation_handling_of_none_from_getters(self, getter_to_make_none, expected_exception, mock_getters_event, captured_output_live, mock_time_monotonic):
        getters, stop_event = mock_getters_event
        getters[getter_to_make_none].return_value = None

        animation_thread = run_animation_in_thread_helper(
            pdd_sync_animation_module.sync_animation,
            getters["function_name"], stop_event, getters["basename"], getters["cost"], getters["budget"],
            getters["prompt_color"], getters["code_color"], getters["example_color"], getters["tests_color"],
            getters["paths"]
        )

        # Let animation run enough to hit the problematic None value usage
        for _ in range(len(PDD_ASCII_LOGO_LINES) + 2): mock_time_monotonic.advance(0.1)
        mock_time_monotonic.advance(1.1) # Reach main display logic
        time.sleep(0.05) 

        # The exception will occur in the thread. Pytest won't catch it directly.
        # We check if the thread died unexpectedly.
        animation_thread.join(timeout=0.5) # Wait for thread
        assert not animation_thread.is_alive(), f"Animation thread should have terminated due to error with {getter_to_make_none}=None"
        
        # This test confirms the SUT currently errors out. A more robust SUT might catch these.
        # To assert the specific exception, one would need a more complex setup to capture thread exceptions.
        # For now, thread termination is a proxy for an unhandled error.

        # Cleanup stop event if it wasn't the cause of termination
        stop_event.set()
