import sys
import os
from unittest.mock import MagicMock
from typing import List, Dict, Any
from pydantic import BaseModel

# --- 1. Environment Setup ---
# Add the 'src' directory to sys.path to allow importing 'backend' packages.
# We assume the structure:
#   project_root/
#     src/backend/app/main.py
#     examples/api_main_example.py
current_dir = os.path.dirname(os.path.abspath(__file__))
project_root = os.path.abspath(os.path.join(current_dir, ".."))
src_path = os.path.join(project_root, "src")
sys.path.insert(0, src_path)

# --- 2. Mock Dependencies ---
# The 'main' module imports 'LintEngine' and 'LintReport' from internal packages.
# To make this example runnable without the full backend environment, we mock them.

# Mock the LintReport model (usually in backend.models.findings)
class MockLintReport(BaseModel):
    score: int
    summary: str
    findings: List[str]

mock_findings_module = MagicMock()
mock_findings_module.LintReport = MockLintReport
sys.modules["backend.models.findings"] = mock_findings_module

# Mock the LintEngine class (usually in backend.core.lint_engine)
class MockLintEngine:
    def lint(self, text: str) -> MockLintReport:
        # Simulate analysis logic
        return MockLintReport(
            score=85,
            summary="Analysis complete (Mocked)",
            findings=[f"Analyzed text length: {len(text)} chars", "No critical issues found"]
        )

mock_core_module = MagicMock()
mock_core_module.LintEngine = MockLintEngine
sys.modules["backend.core.lint_engine"] = mock_core_module

# --- 3. Import the Module ---
# Now we can safely import the app. The mocks above satisfy the internal imports in main.py.
from backend.app.main import app
from fastapi.testclient import TestClient

def run_api_interaction_example() -> None:
    """
    Demonstrates how to interact with the FastAPI application programmatically.
    """
    # Create a TestClient. This allows us to send HTTP requests to the app
    # without actually starting a uvicorn server on a port.
    client = TestClient(app)

    print("=== PDD Prompt Linter API Interaction ===\n")

    # Example 1: Health Check
    # -----------------------
    print("1. Checking System Health...")
    response = client.get("/health")
    
    if response.status_code == 200:
        print(f"   [SUCCESS] Status: {response.json()['status']}")
    else:
        print(f"   [FAILED] Status Code: {response.status_code}")
    print()

    # Example 2: Linting a Prompt
    # ---------------------------
    print("2. Submitting Prompt for Linting...")
    
    # Define the payload matching the LintRequest schema in main.py
    payload = {
        "prompt_text": "Write a python script to scrape google.",
        "options": {
            "strict_mode": True,
            "include_suggestions": True
        }
    }

    # Send POST request to /lint
    response = client.post("/lint", json=payload)

    if response.status_code == 200:
        report = response.json()
        print(f"   [SUCCESS] Report Received:")
        print(f"   - Score: {report['score']}")
        print(f"   - Summary: {report['summary']}")
        print(f"   - Findings: {report['findings']}")
    else:
        print(f"   [ERROR] Failed to lint prompt.")
        print(f"   Detail: {response.text}")

    # Example 3: Handling Errors
    # --------------------------
    print("\n3. Testing Error Handling (Invalid Payload)...")
    # Sending a payload missing the required 'prompt_text' field
    bad_payload = {"options": {}}
    
    response = client.post("/lint", json=bad_payload)
    
    print(f"   Status Code: {response.status_code} (Expected 422 Unprocessable Entity)")
    print(f"   Error Detail: {response.json()['detail'][0]['msg']}")

if __name__ == "__main__":
    run_api_interaction_example()