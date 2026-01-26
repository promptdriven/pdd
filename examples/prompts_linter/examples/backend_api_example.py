import sys
import os
import json
from fastapi.testclient import TestClient

# --- Path Setup ---
# We need to ensure we can import the 'backend_api' module.
# Assuming this example script is in 'examples/' and the module is in 'src/backend/'
current_dir = os.path.dirname(os.path.abspath(__file__))
project_root = os.path.abspath(os.path.join(current_dir, '..'))

if project_root not in sys.path:
    sys.path.insert(0, project_root)

try:
    # Import the FastAPI app instance from the module
    from src.backend.backend_api import app
except ImportError as e:
    print(f"Error importing backend_api: {e}")
    print("Please ensure you are running this script from the correct directory structure.")
    sys.exit(1)

def run_api_example():
    """
    Demonstrates how to interact with the PDD Linter API programmatically.
    """
    # Create a test client. This allows us to make HTTP requests to the app
    # directly in Python without running a uvicorn server.
    client = TestClient(app)

    print("--- 1. Health Check ---")
    response = client.get("/health")
    print(f"Status Code: {response.status_code}")
    print(f"Response: {response.json()}")
    
    print("\n--- 2. Linting a Prompt (Heuristic Only) ---")
    # Define the payload matching the LintRequest model
    payload_heuristic = {
        "content": "Write a python script to scrape google.",
        "config": {
            "use_llm": False,
            "generate_fix": False
        }
    }
    
    response = client.post("/lint", json=payload_heuristic)
    
    if response.status_code == 200:
        report = response.json()
        print(f"Linting Successful!")
        print(f"Score: {report.get('score')}")
        print(f"Issues Found: {len(report.get('issues', []))}")
        print(f"Summary: {report.get('summary')}")
    else:
        print(f"Error: {response.status_code}")
        print(response.text)

    print("\n--- 3. Linting with Invalid Configuration (Error Handling) ---")
    # Sending invalid config to demonstrate error handling
    payload_invalid = {
        "content": "Some prompt",
        "config": {
            "weights": "this should be a dictionary, not a string" 
        }
    }
    
    response = client.post("/lint", json=payload_invalid)
    print(f"Status Code: {response.status_code} (Expected 400 or 422)")
    print(f"Error Detail: {response.json()}")

if __name__ == "__main__":
    run_api_example()