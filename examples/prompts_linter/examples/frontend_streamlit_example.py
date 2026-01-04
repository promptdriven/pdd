import sys
import os
import subprocess
from pathlib import Path

def run_streamlit_app():
    """
    Demonstrates how to launch the PDD Prompt Linter Streamlit application.
    
    Streamlit applications are typically run via the command line:
    $ streamlit run path/to/app.py
    
    This script locates the frontend module and executes it using subprocess
    to simulate that behavior from a Python script.
    """
    
    # 1. Locate the target Streamlit script
    # We need to find src/frontend/frontend_streamlit.py relative to this example file
    current_dir = Path(__file__).parent
    project_root = current_dir.parent # Assuming examples/ is one level deep
    
    # Construct path to the actual module file
    streamlit_script_path = project_root / "src" / "frontend" / "frontend_streamlit.py"
    
    if not streamlit_script_path.exists():
        print(f"Error: Could not find Streamlit app at {streamlit_script_path}")
        print("Please ensure the project structure is correct.")
        return

    print(f"--- Launching PDD Prompt Linter ---")
    print(f"Target Script: {streamlit_script_path}")
    print("Press Ctrl+C to stop the server.")
    print("-" * 40)

    # 2. Construct the command
    # Equivalent to: streamlit run src/frontend/frontend_streamlit.py
    cmd = [
        sys.executable, "-m", "streamlit", "run", 
        str(streamlit_script_path),
        "--server.headless=true" # Optional: prevents browser auto-open for CI/headless envs
    ]

    # 3. Execute
    try:
        subprocess.run(cmd, check=True)
    except KeyboardInterrupt:
        print("\nStopped by user.")
    except subprocess.CalledProcessError as e:
        print(f"\nStreamlit app crashed with exit code {e.returncode}")
    except FileNotFoundError:
        print("\nError: 'streamlit' is not installed in your environment.")
        print("Try running: pip install streamlit")

if __name__ == "__main__":
    # Check if we are running inside a Streamlit session already to avoid recursion
    # (Streamlit sets specific environment variables)
    if os.environ.get("STREAMLIT_RUN_ID"):
        print("This script is intended to launch the app, not be run by it.")
    else:
        run_streamlit_app()