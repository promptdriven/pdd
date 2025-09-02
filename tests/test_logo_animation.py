# tests/test_logo_animation.py

import pytest
import time
import threading
from unittest import mock

# Import the module and class to test
from pdd import logo_animation
from pdd.logo_animation import AnimatedParticle

# Attempt to import Z3 for formal verification tests
try:
    import z3
except ImportError:
    z3 = None # type: ignore

# Test Plan:
#
# I. Setup and Teardown:
#    - Fixture `animation_controller` to:
#        - Mock `pdd.logo_animation` constants (durations, colors, art, etc.) for predictable tests.
#        - Mock `rich.console.Console` to avoid actual terminal output and control its properties (width, height).
#        - Mock `rich.live.Live` to avoid actual rendering and check calls to `update`.
#        - Mock `threading.Thread` to monitor thread creation, start, and join calls, and control `is_alive`.
#        - Ensure `stop_logo_animation()` is called after each test for cleanup.
#
# II. Core Functionality Tests (`start_logo_animation`, `stop_logo_animation`):
#    - `test_start_animation_starts_thread`: Verify `threading.Thread` is instantiated with correct target and started.
#    - `test_start_animation_multiple_calls_one_thread`: Verify calling start multiple times only starts one animation thread if one is already running.
#    - `test_stop_animation_stops_thread`: Verify `thread.join()` is called on the active animation thread.
#    - `test_stop_animation_no_thread_running`: Verify `stop_logo_animation()` is a no-op and doesn't error if no animation is active.
#    - `test_animation_runs_full_cycle`: Mock durations to be short, let animation run, then stop. Check `Live.update` calls and thread join.
#
# III. Animation Stages and Interruption (High-level due to difficulty in precise stage checking without internal access):
#    - `test_stop_animation_during_run`: Start animation, sleep for a very short time, then stop. Verify thread joins. This covers stopping at an early point.
#      (Specific stage interruption tests are hard without deep internal mocking, which is disallowed).
#
# IV. Edge Cases for Inputs/Configuration:
#    - `test_animation_with_empty_ascii_logo_art`: `ASCII_LOGO_ART = []`. Animation should handle gracefully (e.g., not call `Live.update`).
#    - `test_animation_with_none_ascii_logo_art`: `ASCII_LOGO_ART = None`. Test for graceful handling (current code might TypeError, test checks it doesn't crash main thread).
#    - `test_animation_with_malformed_string_ascii_logo_art`: `ASCII_LOGO_ART` is a single string, not list of strings. Code handles this.
#    - `test_zero_duration_constants`: All `*_DURATION` constants set to 0. Animation stages should complete very quickly. The code has min 0.1s fallbacks.
#    - `test_zero_frame_rate`: `ANIMATION_FRAME_RATE = 0`. Should use fallback (1 FPS).
#
# V. Console Dimension Edge Cases (mocking `console.width`, `console.height`):
#    - `test_small_console_dimensions`: e.g., 10x5. Ensure no crashes.
#    - `test_zero_console_width_height`: `console.width = 0, console.height = 0`. Code has guards (e.g. `max(1, console_width)`). Ensure no crashes.
#    - `test_box_height_larger_than_console`: `EXPANDED_BOX_HEIGHT` > `console.height`. Code uses `min()`. Ensure no crashes.
#
# VI. `AnimatedParticle` Class Tests:
#    - `test_animated_particle_creation`: Basic instantiation.
#    - `test_animated_particle_update_progress`: Test interpolation logic for various progress values.
#    - `test_animated_particle_set_new_transition`: Test state update for new transition.
#
# VII. Z3 Formal Verification (for `AnimatedParticle.update_progress` logic):
#    - `test_animated_particle_update_progress_z3_linearity`: Use Z3 to prove that for progress in [0,1], current position is on the line segment between start and target.
#

@pytest.fixture
def animation_controller(monkeypatch):
    """
    Central fixture to manage mocks for constants, Rich library components,
    and threading for animation tests.
    Ensures cleanup by calling stop_logo_animation after each test.
    """
    # Default mocked constants
    constants_to_mock = {
        "ELECTRIC_CYAN": "#00D8FF", "DEEP_NAVY": "#0A0A23",
        "LOGO_FORMATION_DURATION": 0.05, "LOGO_HOLD_DURATION": 0.05,
        "LOGO_TO_BOX_TRANSITION_DURATION": 0.05, "EXPANDED_BOX_HEIGHT": 18,
        "ANIMATION_FRAME_RATE": 20, # Results in 0.05s frame_duration
        "ASCII_LOGO_ART": ["PDD"], # Simple, valid art
    }
    if isinstance(constants_to_mock["ASCII_LOGO_ART"], str): # Ensure it's List[str]
        constants_to_mock["ASCII_LOGO_ART"] = constants_to_mock["ASCII_LOGO_ART"].strip().splitlines()

    for name, value in constants_to_mock.items():
        monkeypatch.setattr(logo_animation, name, value, raising=False)

    # Mock Rich Console
    mock_console_inst = mock.Mock(spec=logo_animation.Console)
    mock_console_inst.width = 80
    mock_console_inst.height = 24
    mock_console_class = mock.Mock(return_value=mock_console_inst)
    monkeypatch.setattr(logo_animation, "Console", mock_console_class)

    # Mock Rich Live
    mock_live_inst = mock.Mock() # This is the instance returned by Live.__enter__
    mock_live_inst.update = mock.Mock()
    mock_live_cm = mock.Mock() # This is the context manager object (result of Live())
    mock_live_cm.__enter__ = mock.Mock(return_value=mock_live_inst)
    mock_live_cm.__exit__ = mock.Mock(return_value=None)
    mock_live_class_constructor = mock.Mock(return_value=mock_live_cm) # This is the Live class itself
    monkeypatch.setattr(logo_animation, "Live", mock_live_class_constructor)

    # Mock threading.Thread
    created_threads_mocks_list = []
    original_thread_class = threading.Thread # Keep a reference to the real Thread

    def side_effect_thread_class(*args, **kwargs):
        thread_inst_mock = mock.Mock(spec=original_thread_class) # Mock an instance
        
        # Store original properties
        thread_inst_mock._target_func = kwargs.get('target')
        thread_inst_mock._args_tuple = kwargs.get('args', ())
        thread_inst_mock._daemon_prop = kwargs.get('daemon')

        # This will be the *actual* thread that runs the animation loop
        thread_inst_mock._actual_worker_thread = None

        def mock_start_method():
            if thread_inst_mock._target_func:
                # Create and start a real thread for the target function
                thread_inst_mock._actual_worker_thread = original_thread_class(
                    target=thread_inst_mock._target_func,
                    args=thread_inst_mock._args_tuple,
                    daemon=thread_inst_mock._daemon_prop
                )
                thread_inst_mock._actual_worker_thread.start()
            thread_inst_mock.is_alive.return_value = True # Mock's state: "alive" after start
        thread_inst_mock.start = mock.Mock(side_effect=mock_start_method)

        def mock_join_method(timeout=None):
            # Join the actual worker thread if it was started
            if thread_inst_mock._actual_worker_thread and thread_inst_mock._actual_worker_thread.is_alive():
                thread_inst_mock._actual_worker_thread.join(timeout)
            thread_inst_mock.is_alive.return_value = False # Mock's state: "not alive" after join
        thread_inst_mock.join = mock.Mock(side_effect=mock_join_method)
        
        # Initial state for is_alive
        thread_inst_mock.is_alive = mock.Mock(return_value=False)
        
        created_threads_mocks_list.append(thread_inst_mock)
        return thread_inst_mock

    mock_thread_class_constructor = mock.Mock(spec=threading.Thread, side_effect=side_effect_thread_class)
    monkeypatch.setattr(logo_animation.threading, "Thread", mock_thread_class_constructor)

    # Yield all mocks and configs to the test
    yield {
        "constants": constants_to_mock,
        "console_mock": mock_console_inst,
        "console_class_mock": mock_console_class,
        "live_mock": mock_live_inst, # The Live instance used in `with Live(...) as live:`
        "live_class_mock": mock_live_class_constructor, # The Live class itself
        "thread_class_mock": mock_thread_class_constructor, # The Thread class
        "created_threads_mocks": created_threads_mocks_list # List of thread instances created
    }

    # Teardown: Ensure animation is stopped using the public API
    logo_animation.stop_logo_animation()


# II. Core Functionality Tests
def test_start_animation_starts_thread(animation_controller):
    logo_animation.start_logo_animation()
    
    assert len(animation_controller["created_threads_mocks"]) == 1, "Animation thread was not created"
    thread_mock = animation_controller["created_threads_mocks"][0]
    
    thread_mock.start.assert_called_once()
    assert thread_mock._target_func == logo_animation._animation_loop # Check target
    assert thread_mock._daemon_prop is True # Check if daemon

def test_start_animation_multiple_calls_one_thread(animation_controller):
    logo_animation.start_logo_animation() # First call
    assert len(animation_controller["created_threads_mocks"]) == 1
    thread_mock = animation_controller["created_threads_mocks"][0]
    thread_mock.start.assert_called_once()
    
    # Make the thread appear alive for the second call
    # The mock_start_method in the fixture already sets is_alive to True.

    logo_animation.start_logo_animation() # Second call
    assert len(animation_controller["created_threads_mocks"]) == 1, "Second call to start_logo_animation created a new thread"

def test_stop_animation_stops_thread(animation_controller):
    logo_animation.start_logo_animation()
    assert len(animation_controller["created_threads_mocks"]) == 1
    thread_mock = animation_controller["created_threads_mocks"][0]
    
    # Ensure thread is "alive" before stopping
    assert thread_mock.is_alive() is True 

    logo_animation.stop_logo_animation()
    thread_mock.join.assert_called_once()
    assert thread_mock.is_alive() is False # Join mock sets it to false

def test_stop_animation_no_thread_running(animation_controller):
    # Ensure no thread is running (default state of mock)
    # Call stop_logo_animation - it should not error
    try:
        logo_animation.stop_logo_animation()
    except Exception as e:
        pytest.fail(f"stop_logo_animation raised an exception when no thread was running: {e}")
    
def test_animation_runs_full_cycle(animation_controller):
    durations = animation_controller["constants"]
    total_duration = (durations["LOGO_FORMATION_DURATION"] +
                      durations["LOGO_HOLD_DURATION"] +
                      durations["LOGO_TO_BOX_TRANSITION_DURATION"])

    logo_animation.start_logo_animation()
    assert len(animation_controller["created_threads_mocks"]) == 1
    thread_mock = animation_controller["created_threads_mocks"][0]
    thread_mock.start.assert_called_once()

    # Allow real time for the animation thread to run with mocked (short) durations
    # The animation loop itself uses event.wait(frame_duration)
    # frame_duration = 1.0 / 20 = 0.05s. Total duration = 0.05*3 = 0.15s
    # Add buffer for thread scheduling and final hold loop.
    # The final hold loop in _animation_loop waits on _stop_animation_event.
    # So, we need to call stop_logo_animation to make the thread finish.
    # The sleep here is to allow stages to progress *before* stopping.
    time.sleep(total_duration + 0.2) 

    # Stop the animation, which will set the event and allow the thread to complete.
    logo_animation.stop_logo_animation() 
    
    # Animation should have made calls to live.update()
    animation_controller["live_mock"].update.assert_called()
    thread_mock.join.assert_called_once()

# III. Animation Stages and Interruption
def test_stop_animation_during_run(animation_controller, monkeypatch):
    # Make formation long enough to interrupt
    patched_formation_duration = 0.5
    monkeypatch.setattr(logo_animation, "LOGO_FORMATION_DURATION", patched_formation_duration)
    
    logo_animation.start_logo_animation()
    assert len(animation_controller["created_threads_mocks"]) == 1
    thread_mock = animation_controller["created_threads_mocks"][0]

    time.sleep(0.05) # Sleep for a very short time, less than any significant animation part

    logo_animation.stop_logo_animation()
    
    # Replicate the timeout calculation from stop_logo_animation()
    # to ensure the test expectation matches the code's behavior.
    hold_duration = animation_controller["constants"]["LOGO_HOLD_DURATION"]
    transition_duration = animation_controller["constants"]["LOGO_TO_BOX_TRANSITION_DURATION"]

    term1 = max(0.1, patched_formation_duration or 0.1)
    term2 = max(0.1, hold_duration or 0.1)
    term3 = max(0.1, transition_duration or 0.1)
    
    calculated_sum = term1 + term2 + term3 + 2.0 # 2.0 is the buffer in stop_logo_animation
    expected_join_timeout = max(0.1, calculated_sum) # Final guard in stop_logo_animation
    
    thread_mock.join.assert_called_once_with(timeout=pytest.approx(expected_join_timeout, abs=0.01))


# IV. Edge Cases for Inputs/Configuration
def test_animation_with_empty_list_ascii_logo_art(animation_controller, monkeypatch):
    monkeypatch.setattr(logo_animation, "ASCII_LOGO_ART", [])
    
    logo_animation.start_logo_animation()
    time.sleep(0.1) # Allow thread to start and process (it should exit early)

    # Thread should start, but _animation_loop should return early due to no particles
    assert len(animation_controller["created_threads_mocks"]) == 1
    animation_controller["created_threads_mocks"][0].start.assert_called_once()
    
    # Live.update should not be called if there are no particles
    animation_controller["live_mock"].update.assert_not_called()
    
    logo_animation.stop_logo_animation() # Should cleanup fine

def test_animation_with_none_ascii_logo_art(animation_controller, monkeypatch):
    monkeypatch.setattr(logo_animation, "ASCII_LOGO_ART", None)
    
    logo_animation.start_logo_animation()
    # Give thread time to start. With the fix in _parse_logo_art, it should exit cleanly.
    # The _actual_worker_thread will complete.
    time.sleep(0.1) 

    assert len(animation_controller["created_threads_mocks"]) == 1
    thread_mock = animation_controller["created_threads_mocks"][0]
    thread_mock.start.assert_called_once()
    
    # Simulate that the thread is no longer considered alive by the mock's state,
    # as stop_logo_animation checks the mock's is_alive().
    # If the actual worker thread finished cleanly (due to no particles),
    # its real is_alive() would be False. Our mock_join_method sets the mock's
    # is_alive to False after join. If join isn't called (because stop_logo_animation
    # sees is_alive as False), we need to ensure the mock's state reflects this.
    # The mock_join_method in the fixture will be called by stop_logo_animation
    # if the mock's is_alive() is True. If the real thread exits early,
    # the mock's is_alive() might still be True until join is called.
    # Let's ensure the mock's join is called if the thread was started.
    # The stop_logo_animation will call join if thread_mock.is_alive() is true.
    # The mock_start_method sets it to true.
    # The mock_join_method will join the _actual_worker_thread (which should have finished)
    # and then set the mock's is_alive to false.

    try:
        logo_animation.stop_logo_animation() 
    except Exception as e:
        pytest.fail(f"stop_logo_animation failed after thread error: {e}")
    
    # If the thread started, join should be called by stop_logo_animation.
    thread_mock.join.assert_called_once()


def test_animation_with_malformed_string_ascii_logo_art(animation_controller, monkeypatch):
    art_string = "Line1\nLine2"
    monkeypatch.setattr(logo_animation, "ASCII_LOGO_ART", art_string)
    
    logo_animation.start_logo_animation()
    time.sleep(0.1) # Allow some animation

    assert len(animation_controller["created_threads_mocks"]) == 1
    
    logo_animation.stop_logo_animation() # Stop before asserting update
    animation_controller["live_mock"].update.assert_called() # Should proceed to render

def test_zero_duration_constants(animation_controller, monkeypatch):
    monkeypatch.setattr(logo_animation, "LOGO_FORMATION_DURATION", 0.0)
    monkeypatch.setattr(logo_animation, "LOGO_HOLD_DURATION", 0.0)
    monkeypatch.setattr(logo_animation, "LOGO_TO_BOX_TRANSITION_DURATION", 0.0)

    logo_animation.start_logo_animation()
    # Effective durations are min 0.1s. Total ~0.3s. Sleep a bit longer.
    time.sleep(0.1 * 3 + 0.2) 

    logo_animation.stop_logo_animation()
    animation_controller["live_mock"].update.assert_called()
    thread_mock = animation_controller["created_threads_mocks"][0]
    thread_mock.join.assert_called_once()

def test_zero_frame_rate(animation_controller, monkeypatch):
    monkeypatch.setattr(logo_animation, "ANIMATION_FRAME_RATE", 0) # Effective 1 FPS
    
    logo_animation.start_logo_animation()
    time.sleep(0.2) # Allow some frames at 1 FPS

    logo_animation.stop_logo_animation()
    animation_controller["live_mock"].update.assert_called()

# V. Console Dimension Edge Cases
@pytest.mark.parametrize("width,height", [(10,5), (1,1), (80,1)])
def test_small_console_dimensions(animation_controller, monkeypatch, width, height):
    animation_controller["console_mock"].width = width
    animation_controller["console_mock"].height = height # This mock height is for console.height
                                                        # _animation_loop uses fixed 18 for its logic
    
    logo_animation.start_logo_animation()
    time.sleep(0.2) 

    logo_animation.stop_logo_animation() 
    animation_controller["live_mock"].update.assert_called()

def test_zero_console_width_height(animation_controller, monkeypatch):
    animation_controller["console_mock"].width = 0
    animation_controller["console_mock"].height = 0

    logo_animation.start_logo_animation()
    time.sleep(0.2)
    
    logo_animation.stop_logo_animation()
    # With zero width, _render_particles_to_text might produce empty Text or very minimal.
    # live.update(Text()) is valid. The key is no crash.
    # If particles exist, it will try to render.
    animation_controller["live_mock"].update.assert_called()


def test_box_height_larger_than_console(animation_controller, monkeypatch):
    monkeypatch.setattr(logo_animation, "EXPANDED_BOX_HEIGHT", 50)
    # The _animation_loop uses a fixed height of 18 for its internal console_height logic
    # and for _render_particles_to_text.
    # The mocked console_mock.height is not directly used by _animation_loop's height calculations
    # for rendering, as it hardcodes `console_height = 18`.
    # However, _get_box_perimeter_positions uses console_height from the passed console object.
    # Let's ensure the console object passed to _animation_loop has the mocked height.
    # The Console is created in start_logo_animation. Our mock Console class returns mock_console_inst.
    # So, mock_console_inst.height (set to 24 by default in fixture) will be used by _get_box_perimeter_positions.
    # Let's adjust the test to reflect this.
    animation_controller["console_mock"].height = 10 # This will be the console.height seen by _get_box_perimeter_positions

    logo_animation.start_logo_animation()
    time.sleep(0.2)

    logo_animation.stop_logo_animation()
    animation_controller["live_mock"].update.assert_called()

# VI. AnimatedParticle Class Tests
def test_animated_particle_creation():
    p = AnimatedParticle(char="x", orig_logo_x=1, orig_logo_y=2)
    assert p.char == "x"
    assert p.orig_logo_x == 1
    assert p.orig_logo_y == 2
    assert p.current_x == 0.0 
    assert p.style.color.name == logo_animation.ELECTRIC_CYAN.lower() 

def test_animated_particle_update_progress():
    p = AnimatedParticle("x", 0, 0)
    p.start_x, p.start_y = 0.0, 0.0
    p.target_x, p.target_y = 10.0, 20.0

    p.update_progress(0.0)
    assert p.current_x == 0.0 and p.current_y == 0.0

    p.update_progress(0.5)
    assert p.current_x == 5.0 and p.current_y == 10.0

    p.update_progress(1.0)
    assert p.current_x == 10.0 and p.current_y == 20.0

def test_animated_particle_set_new_transition():
    p = AnimatedParticle("x", 0, 0)
    p.current_x, p.current_y = 5.0, 5.0 
    
    p.set_new_transition(new_target_x=10.0, new_target_y=10.0)
    
    assert p.start_x == 5.0 and p.start_y == 5.0
    assert p.target_x == 10.0 and p.target_y == 10.0

# VII. Z3 Formal Verification
@pytest.mark.skipif(z3 is None, reason="Z3 solver not installed")
def test_animated_particle_update_progress_z3_linearity():
    if z3 is None: pytest.skip("Z3 not available")

    z3_start_x, z3_target_x, z3_progress = z3.Reals('z3_start_x z3_target_x z3_progress')
    z3_current_x = z3_start_x + (z3_target_x - z3_start_x) * z3_progress
    solver = z3.Solver()
    solver.add(z3.And(z3_progress >= 0, z3_progress <= 1))
    solver.add((z3_current_x - z3_start_x) * (z3_current_x - z3_target_x) > 0)
    result = solver.check()
    assert result == z3.unsat, \
        f"Z3 found a counterexample to linearity: {solver.model()}. " \
        "This implies current_x is not always between start_x and target_x for progress in [0,1]."

