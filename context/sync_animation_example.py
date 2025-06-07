# run_animation_example.py
import threading
import time
import sys
import os

# Ensure the 'pdd' directory is in the Python path for the import
# This is usually handled if 'pdd' is an installed package or if this script
# is run from the directory containing 'pdd'.
# For a direct script run, you might need to adjust sys.path:
# current_dir = os.path.dirname(os.path.abspath(__file__))
# pdd_package_dir = os.path.join(current_dir, "..") # If pdd is one level up
# sys.path.insert(0, pdd_package_dir)


# Assuming 'pdd' is an installed package or in PYTHONPATH
from pdd.sync_animation import sync_animation

# --- Shared state for the animation ---
# This dictionary will be updated by the main "PDD process" simulation
# and read by the getter functions passed to sync_animation.
shared_pdd_state: dict[str, any] = {
    "function_name": "checking",
    "basename": "example_feature",
    "cost": 0.0,
    "budget": 10.0,  # Budget in dollars
    "prompt_color": "cyan",
    "code_color": "green",
    "example_color": "yellow",
    "tests_color": "magenta",
    "paths": {
        "prompt": "./prompts/feature_x.prompt",
        "code": "./src/feature_x.py",
        "example": "./examples/ex_feature_x.py",
        "tests": "./tests/test_feature_x.py",
    },
    "stop_event": threading.Event(),
}

# --- Getter functions for sync_animation ---
# These functions provide the current state to the animation.
# They access the shared_pdd_state dictionary.

def get_current_function_name() -> str:
    """Returns the current function name from shared state."""
    return shared_pdd_state["function_name"]

def get_stop_event() -> threading.Event: # This is not a getter, but the event itself
    """Returns the stop event object from shared state."""
    return shared_pdd_state["stop_event"]

def get_basename() -> str:
    """Returns the basename from shared state."""
    return shared_pdd_state["basename"]

def get_cost() -> float:
    """Returns the current cost in dollars from shared state."""
    # Cost in dollars
    return shared_pdd_state["cost"]

def get_budget() -> float:
    """Returns the budget in dollars from shared state."""
    # Budget in dollars
    return shared_pdd_state["budget"]

def get_prompt_color() -> str:
    """Returns the prompt color from shared state."""
    return shared_pdd_state["prompt_color"]

def get_code_color() -> str:
    """Returns the code color from shared state."""
    return shared_pdd_state["code_color"]

def get_example_color() -> str:
    """Returns the example color from shared state."""
    return shared_pdd_state["example_color"]

def get_tests_color() -> str:
    """Returns the tests color from shared state."""
    return shared_pdd_state["tests_color"]

def get_paths() -> dict[str, str]:
    """Returns the paths dictionary from shared state."""
    return shared_pdd_state["paths"]


if __name__ == "__main__":
    print("Starting PDD process simulation with sync_animation.")
    print("The animation will run for a few cycles and then stop.")
    print("Look for the Rich TUI rendering below this message.")
    time.sleep(1) # Give a moment for the user to see the message

    # Create and start the animation thread
    animation_thread = threading.Thread(
        target=sync_animation,
        args=(
            get_current_function_name,
            get_stop_event(), # Pass the event object directly
            get_basename,
            get_cost,
            get_budget,
            get_prompt_color,
            get_code_color,
            get_example_color,
            get_tests_color,
            get_paths,
        ),
        daemon=True, # Allows main program to exit even if thread is still running
    )
    animation_thread.start()

    # Simulate a PDD process updating its state
    try:
        # Initial "checking" phase (already set in shared_pdd_state)
        time.sleep(2.5) # Let logo expand and show "checking"

        # Simulate "generate"
        shared_pdd_state["function_name"] = "generate"
        shared_pdd_state["cost"] += 0.50
        shared_pdd_state["paths"]["code"] = "./src/feature_x_v1.py"
        time.sleep(3)

        # Simulate "example"
        shared_pdd_state["function_name"] = "example"
        shared_pdd_state["cost"] += 0.20
        shared_pdd_state["paths"]["example"] = "./examples/ex_feature_x_v1.py"
        time.sleep(3)

        # Simulate "test"
        shared_pdd_state["function_name"] = "test"
        shared_pdd_state["cost"] += 0.75
        shared_pdd_state["paths"]["tests"] = "./tests/test_feature_x_v1.py"
        time.sleep(3)

        # Simulate "fix"
        shared_pdd_state["function_name"] = "fix"
        shared_pdd_state["cost"] += 1.25
        shared_pdd_state["code_color"] = "bright_red" # Show color change
        shared_pdd_state["paths"]["code"] = "./src/feature_x_v2_fixed.py"
        time.sleep(3)
        
        # Simulate "update"
        shared_pdd_state["function_name"] = "update"
        shared_pdd_state["cost"] += 0.30
        shared_pdd_state["prompt_color"] = "bright_blue"
        shared_pdd_state["paths"]["prompt"] = "./prompts/feature_x_updated.prompt"
        time.sleep(3)

        # Simulate "crash"
        shared_pdd_state["function_name"] = "crash"
        shared_pdd_state["cost"] += 0.60
        time.sleep(3)

        # Simulate "verify"
        shared_pdd_state["function_name"] = "verify"
        shared_pdd_state["cost"] += 0.40
        time.sleep(3)

    except KeyboardInterrupt:
        print("\nSimulation interrupted by user.")
    finally:
        # Signal the animation to stop
        print("\nSignaling animation to stop...")
        shared_pdd_state["stop_event"].set()

        # Wait for the animation thread to finish
        animation_thread.join(timeout=5) # Wait up to 5 seconds
        if animation_thread.is_alive():
            print("Animation thread did not stop in time.")
        else:
            print("Animation thread finished.")
        
        print(f"PDD process simulation finished. Total cost: ${shared_pdd_state['cost']:.2f}")