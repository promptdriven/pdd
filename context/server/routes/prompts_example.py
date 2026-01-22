import sys
import os
from pathlib import Path
from unittest.mock import MagicMock, patch
from fastapi import FastAPI
from fastapi.testclient import TestClient

# -----------------------------------------------------------------------------
# 1. Mocking Dependencies
# -----------------------------------------------------------------------------
# Since the module relies on other parts of the 'pdd' package (security, token_counter, preprocess),
# we need to mock them before importing the module to make this example standalone.

# CRITICAL: Save originals BEFORE patching to avoid polluting sys.modules during pytest collection
# See context/pytest_isolation_example.py Pattern 7 for the correct approach
_saved = {}
_saved["pdd.security"] = sys.modules.get("pdd.security")
_saved["pdd.token_counter"] = sys.modules.get("pdd.token_counter")
_saved["pdd.preprocess"] = sys.modules.get("pdd.preprocess")

# Mock pdd.security
sys.modules["pdd.security"] = MagicMock()
from pdd.security import PathValidator, SecurityError

# Mock pdd.token_counter
sys.modules["pdd.token_counter"] = MagicMock()
# We need a real-ish return object for get_token_metrics
class MockCostEstimate:
    def to_dict(self):
        return {
            "input_cost": 0.002,
            "model": "claude-sonnet-4-20250514",
            "tokens": 150,
            "cost_per_million": 15.0,
            "currency": "USD"
        }

class MockTokenMetrics:
    def __init__(self, count):
        self.token_count = count
        self.context_limit = 200000
        self.context_usage_percent = (count / 200000) * 100
        self.cost_estimate = MockCostEstimate()

def mock_get_token_metrics(content, model, pricing_csv=None):
    # Simple mock: 1 token per word
    count = len(content.split())
    return MockTokenMetrics(count)

sys.modules["pdd.token_counter"].get_token_metrics = mock_get_token_metrics

# Mock pdd.preprocess
sys.modules["pdd.preprocess"] = MagicMock()
def mock_preprocess(content, recursive=True, double_curly_brackets=True):
    return content.replace("{{variable}}", "EXPANDED_VALUE")

sys.modules["pdd.preprocess"].preprocess = mock_preprocess

# RESTORE originals immediately after setting up mocks
# This prevents polluting sys.modules for other test files during pytest collection
for key, original in _saved.items():
    if original is None:
        sys.modules.pop(key, None)
    else:
        sys.modules[key] = original

# -----------------------------------------------------------------------------
# 2. Importing the Module
# -----------------------------------------------------------------------------
# Now we can import the router from the module we want to demonstrate.
# Assuming the file is named 'prompts.py' in the current directory or python path.
# For this example, we assume the code provided in the prompt is in 'prompts_module.py'
try:
    import prompts_module as prompts_route
except ImportError:
    # Fallback if running directly where the file might be named differently
    # In a real scenario, this would be: from pdd.server.routes import prompts
    print("Error: Could not import the module. Ensure 'prompts_module.py' exists.")
    sys.exit(1)

# -----------------------------------------------------------------------------
# 3. Setup Application
# -----------------------------------------------------------------------------

def create_example_app():
    app = FastAPI()
    
    # Include the router from the module
    app.include_router(prompts_route.router)
    
    # Setup the PathValidator dependency
    # In a real app, this points to the actual project root
    project_root = Path("./example_project_root")
    project_root.mkdir(exist_ok=True)
    
    # Create a dummy prompt file for testing
    prompt_file = project_root / "test_prompt.txt"
    prompt_file.write_text("Hello {{variable}}, this is a test prompt.", encoding="utf-8")
    
    # Configure the validator
    validator = MagicMock(spec=PathValidator)
    validator.project_root = project_root
    
    # Mock the validate method to return the absolute path if it exists
    def mock_validate(path_str):
        abs_path = project_root / path_str
        # Simulate security check
        if ".." in path_str:
            raise SecurityError("Path traversal detected")
        return abs_path
        
    validator.validate.side_effect = mock_validate
    
    # Inject the validator into the module
    prompts_route.set_path_validator(validator)
    
    return app, project_root

# -----------------------------------------------------------------------------
# 4. Example Usage
# -----------------------------------------------------------------------------

def run_examples():
    app, root_dir = create_example_app()
    client = TestClient(app)
    
    print(f"--- PDD Prompt Analysis API Example ---\n")

    # Example 1: Analyze a file (with preprocessing)
    print("1. Analyzing 'test_prompt.txt' (with preprocessing)...")
    response = client.post(
        "/api/v1/prompts/analyze",
        json={
            "path": "test_prompt.txt",
            "model": "claude-3-opus-20240229",
            "preprocess": True
        }
    )
    
    if response.status_code == 200:
        data = response.json()
        print(f"   Status: Success")
        print(f"   Raw Content: {data['raw_content']}")
        print(f"   Processed Content: {data['processed_content']}")
        print(f"   Raw Tokens: {data['raw_metrics']['token_count']}")
        print(f"   Processed Tokens: {data['processed_metrics']['token_count']}")
        print(f"   Est. Cost: ${data['processed_metrics']['cost_estimate']['input_cost']}")
    else:
        print(f"   Failed: {response.text}")
    print("-" * 40)

    # Example 2: Analyze direct content (no file)
    print("\n2. Analyzing raw string content directly...")
    response = client.post(
        "/api/v1/prompts/analyze",
        json={
            "path": "ignored_when_content_provided.txt", 
            "content": "This is a direct string analysis {{variable}}.",
            "preprocess": True
        }
    )
    
    if response.status_code == 200:
        data = response.json()
        print(f"   Status: Success")
        print(f"   Processed Content: {data['processed_content']}")
    print("-" * 40)

    # Example 3: Error Handling (File not found)
    print("\n3. Testing Error Handling (File Not Found)...")
    response = client.post(
        "/api/v1/prompts/analyze",
        json={
            "path": "non_existent_file.txt",
            "preprocess": False
        }
    )
    print(f"   Status Code: {response.status_code}")
    print(f"   Error Detail: {response.json()['detail']}")
    
    # Cleanup
    import shutil
    if root_dir.exists():
        shutil.rmtree(root_dir)

if __name__ == "__main__":
    run_examples()