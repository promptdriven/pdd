import sys
import os
from unittest.mock import MagicMock, patch

# --- Path Setup ---
# Add the parent directory to sys.path to allow importing the module
# relative to this example script.
current_dir = os.path.dirname(os.path.abspath(__file__))
# Assuming the structure:
#   /src/ui/streamlit_app.py
#   /examples/ui_streamlit_example.py
# We need to go up two levels to reach the root, then down to src/ui
project_root = os.path.dirname(current_dir)
sys.path.append(os.path.join(project_root, "src", "ui"))

try:
    import streamlit_app as app
except ImportError:
    print("Error: Could not import 'streamlit_app'. Ensure the file structure is correct.")
    sys.exit(1)

def example_helper_functions():
    """
    Demonstrates how to use the helper logic functions from the module
    independently of the Streamlit UI context.
    """
    print("--- Testing Helper Functions ---")

    # 1. Test Severity Color Logic
    print(f"Color for 'Error': {app.get_severity_color('Error')}")
    print(f"Color for 'Warning': {app.get_severity_color('Warning')}")
    print(f"Color for 'Unknown': {app.get_severity_color('Random')}")

    # 2. Test API Call Logic (Mocked)
    # Since we don't want to actually hit a backend server for this example,
    # we mock the requests.post method.
    print("\n--- Testing API Call Logic (Mocked) ---")
    
    mock_response_data = {
        "score": 85,
        "findings": [
            {"severity": "error", "message": "Test error"}
        ]
    }

    # We patch 'requests.post' to return our mock data
    with patch('requests.post') as mock_post:
        mock_response = MagicMock()
        mock_response.status_code = 200
        mock_response.json.return_value = mock_response_data
        mock_post.return_value = mock_response

        # Call the function from the module
        result = app.call_lint_api("Some prompt content", resolve_includes=True)
        
        print("API Call Result:", result)
        print("Mock called with URL:", app.API_URL)

def example_run_instructions():
    """
    Prints instructions on how to run the actual Streamlit application.
    """
    print("\n--- How to Run the Streamlit App ---")
    print("To launch the actual UI, run the following command in your terminal:")
    print(f"\n    streamlit run {os.path.join(project_root, 'src', 'ui', 'streamlit_app.py')}")
    print("\nTo override the API URL, set the environment variable:")
    print("\n    PDD_API_URL=http://my-api.com/lint streamlit run ...")

if __name__ == "__main__":
    # 1. Demonstrate internal logic
    example_helper_functions()

    # 2. Show how to launch the app
    example_run_instructions()