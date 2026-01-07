import threading
import time
import os
import sys
from typing import Dict, List

# Ensure the parent directory is in the path so we can import the module
sys.path.append(os.path.dirname(os.path.dirname(os.path.abspath(__file__))))

from pdd.sync_tui import SyncApp, show_exit_animation

def mock_worker_logic(app: SyncApp, stop_event: threading.Event) -> Dict[str, any]:
    """
    A mock worker function that simulates a PDD sync process.
    
    Args:
        app: The SyncApp instance (passed via closure or global access if needed).
        stop_event: A threading.Event to signal when the worker should stop.
        
    Returns:
        A dictionary containing the results of the operation.
    """
    try:
        print("Starting worker process...")
        time.sleep(2)  # Simulate initial setup

        # 1. Demonstrate Thread-Safe Input (Modal)
        # This blocks the worker thread until the user interacts with the TUI modal.
        user_name = app.request_input("Enter your name to begin sync:")
        print(f"Hello, {user_name}! Initializing files...")

        # 2. Demonstrate Progress Bar updates
        total_files = 10
        for i in range(total_files):
            if stop_event.is_set():
                break
            # Update the TUI progress bar via the callback
            app.update_progress(i + 1, total_files)
            print(f"Processing file {i+1}/{total_files}...")
            time.sleep(0.3)

        # 3. Demonstrate Interactive Steering (Choice Modal)
        # This will auto-select index 0 after 5 seconds if no input is given.
        options = ["Optimize for Speed", "Optimize for Cost", "Manual Review"]
        choice_idx = app.request_choice(
            prompt="Select optimization strategy:",
            options=options,
            default_index=0,
            timeout_s=5.0
        )
        print(f"Strategy selected: {options[choice_idx]}")

        # 4. Demonstrate Confirmation Modal
        if app.request_confirmation("Do you want to commit these changes?"):
            print("Changes committed successfully.")
            return {"success": True, "total_cost": 0.15, "strategy": options[choice_idx]}
        else:
            print("Commit aborted by user.")
            return {"success": False, "error": "User aborted"}

    except Exception as e:
        print(f"Worker encountered an error: {e}")
        return {"success": False, "error": str(e)}

def run_sync_tui_example():
    """
    Configures and runs the SyncApp TUI.
    """
    # Shared state references used by the animation system
    fn_ref = ["initializing"]
    cost_ref = [0.0]
    stop_event = threading.Event()
    
    # Path and Color configurations for the animation boxes
    paths = {
        'prompt': ["./prompts/main.prompt"],
        'code': ["./src/app.py"],
        'example': ["./docs/example.md"],
        'tests': ["./tests/test_app.py"]
    }
    colors = {
        'prompt': ["blue"],
        'code': ["green"],
        'example': ["yellow"],
        'tests': ["magenta"]
    }

    # Initialize the App
    # Note: We use a lambda to pass the app instance to the worker logic
    app = SyncApp(
        basename="example_project",
        budget=5.0,
        worker_func=lambda: mock_worker_logic(app, stop_event),
        function_name_ref=fn_ref,
        cost_ref=cost_ref,
        paths=paths,
        colors=colors,
        stop_event=stop_event
    )

    # Run the Textual App
    # The app.run() call returns the value passed to app.exit() in the worker thread
    result = app.run()

    # Show the final exit animation in the standard terminal
    show_exit_animation()

    print("--- Sync Results ---")
    print(result)

if __name__ == "__main__":
    run_sync_tui_example()