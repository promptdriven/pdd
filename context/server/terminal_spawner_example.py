import os
import sys
import time
from pathlib import Path

# --- Setup for importing the module ---
# This block ensures we can import the module regardless of where this script is run.
# It assumes the script is located in an 'examples' directory or similar, relative to the package.
current_dir = os.path.dirname(os.path.abspath(__file__))
parent_dir = os.path.dirname(current_dir)
sys.path.insert(0, parent_dir)

try:
    from pdd.server.terminal_spawner import TerminalSpawner
except ImportError:
    print("Error: Could not import 'TerminalSpawner'.")
    print(f"Ensure 'pdd/server/terminal_spawner.py' exists relative to {parent_dir}")
    sys.exit(1)


def main():
    """
    Demonstrates spawning terminal windows for various tasks.
    """
    print(f"Running on platform: {sys.platform}")
    print("Attempting to spawn terminal windows...\n")

    # 1. Simple Command Spawn
    # Spawns a terminal that echoes a message and lists the current directory.
    # The terminal will stay open because the implementation uses 'exec bash' or '-NoExit'.
    print("1. Spawning simple 'ls' command...")
    success = TerminalSpawner.spawn(
        command="echo 'Hello from PDD!' && ls -la",
        working_dir=os.getcwd()
    )
    
    if success:
        print("   -> Success: Terminal launched.")
    else:
        print("   -> Failed: Could not launch terminal.")
    
    time.sleep(1)  # Pause briefly between spawns

    # 2. Spawning with a specific Working Directory
    # This demonstrates the 'working_dir' argument.
    target_dir = os.path.expanduser("~")
    print(f"\n2. Spawning command in home directory ({target_dir})...")
    
    success = TerminalSpawner.spawn(
        command="echo 'I am running in your home directory' && pwd",
        working_dir=target_dir
    )

    if success:
        print("   -> Success: Terminal launched.")
    else:
        print("   -> Failed: Could not launch terminal.")

    # 3. Spawning with Job ID (Callback Simulation)
    # This demonstrates how the spawner constructs a callback command.
    # Note: Since we don't have a real server running on port 5000 to receive the curl/Invoke-RestMethod,
    # the callback part will fail silently in the spawned window, but the command itself will run.
    print("\n3. Spawning command with Job ID (simulating server callback)...")
    print("   (Note: The callback will fail silently as no server is running on port 5000)")
    
    success = TerminalSpawner.spawn(
        command="echo 'Running job 123...' && sleep 2 && echo 'Job done!'",
        job_id="job_123",
        server_port=5000
    )

    if success:
        print("   -> Success: Terminal launched with job tracking.")
    else:
        print("   -> Failed: Could not launch terminal.")

if __name__ == "__main__":
    main()