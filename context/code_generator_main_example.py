import asyncio
import click
import os
import shutil
import subprocess
import json # For mock_requests_post
from pathlib import Path
from typing import Tuple, Optional, Dict, Any
from unittest.mock import patch

# Assuming the module is in pdd.commands.generate as per the problem description
from pdd.commands.generate import code_generator_main

# --- Mock Dependencies ---
# These functions would normally involve LLM calls. We mock them for this example.

# Mock for pdd.code_generator.code_generator
def mock_code_generator_func(prompt: str, language: str, strength: float, temperature: float, verbose: bool) -> Tuple[str, float, str]:
    """Mocks the behavior of the actual code_generator."""
    if verbose:
        print(f"[Mock code_generator] Called with: lang={language}, strength={strength}, temp={temperature}")
        print(f"[Mock code_generator] Prompt starts with: {prompt[:50]}...")
    
    generated_code = f"# Mock generated code ({language})\n"
    generated_code += f"# Strength: {strength}, Temperature: {temperature}\n"
    generated_code += f"def locally_generated_function():\n    return 'Hello from mock local generator for {prompt[:20]}...'"
    cost_usd = 0.001  # Simulated cost in USD
    model_name = "mock_local_model_v1"
    return generated_code, cost_usd, model_name

# Mock for pdd.incremental_code_generator.incremental_code_generator
def mock_incremental_code_generator_func(
    original_prompt: str, new_prompt: str, existing_code: str, language: str,
    strength: float, temperature: float, time: float, force_incremental: bool,
    verbose: bool, preprocess_prompt: bool
) -> Tuple[str, bool, float, str]:
    """Mocks the behavior of the actual incremental_code_generator."""
    if verbose:
        print(f"[Mock incremental_generator] Called with: lang={language}, force_incremental={force_incremental}")
        print(f"[Mock incremental_generator] New prompt starts with: {new_prompt[:50]}...")

    was_incremental_operation = False
    generated_code_content = ""
    cost_usd = 0.0
    model_name_used = "mock_incremental_analyzer"

    # Simulate decision: if "major change" in prompt or not forced, suggest full.
    # Otherwise, perform incremental.
    if force_incremental or ("update" in new_prompt.lower() and "major change" not in new_prompt.lower()) :
        was_incremental_operation = True
        generated_code_content = existing_code + f"\n# Incremental update applied ({language})\n"
        generated_code_content += f"def new_feature_incrementally_added():\n    return 'incremental success for {new_prompt[:20]}...'"
        cost_usd = 0.0005
        model_name_used = "mock_incremental_model_v1"
        if verbose:
            print(f"[Mock incremental_generator] Performed incremental update.")
    else:
        was_incremental_operation = False
        generated_code_content = "" # Empty string signals to caller to do full generation
        cost_usd = 0.0001 # Cost for analysis
        model_name_used = "mock_incremental_analysis_suggests_full"
        if verbose:
            print(f"[Mock incremental_generator] Suggested full regeneration.")
            
    return generated_code_content, was_incremental_operation, cost_usd, model_name_used

# Mock for requests.post used in cloud generation
class MockRequestsResponse:
    def __init__(self, json_data: Dict[str, Any], status_code: int, text: Optional[str] = None):
        self.json_data = json_data
        self.status_code = status_code
        self._text = text if text is not None else json.dumps(json_data)

    def json(self) -> Dict[str, Any]:
        if self.status_code >= 400: # Simulate requests behavior where .json() might fail on error
            raise json.JSONDecodeError("Mock JSON decode error", "doc", 0)
        return self.json_data

    def raise_for_status(self) -> None:
        if self.status_code >= 400:
            # Simulate requests.exceptions.HTTPError
            http_error = type('MockHTTPError', (Exception,), {}) # Basic mock error
            http_error.response = self
            raise http_error(f"Mock HTTP Error {self.status_code}")
    
    @property
    def text(self):
        return self._text

def mock_requests_post_func(url: str, json: Dict[str, Any], headers: Dict[str, str], timeout: int):
    """Mocks requests.post for cloud generation calls."""
    print(f"[Mock requests.post] Called for URL: {url} with timeout: {timeout}")
    print(f"[Mock requests.post] Payload language: {json.get('language')}, strength: {json.get('strength')}")
    
    auth_header = headers.get("Authorization", "")
    if "Bearer mock_valid_jwt_token" in auth_header:
        # Simulate successful cloud call
        return MockRequestsResponse({
            "generatedCode": f"# Mocked cloud generated code ({json.get('language')})\ndef cloud_function():\n    return 'cloud success for {json.get('promptContent', '')[:20]}...'",
            "cost": 0.002,
            "modelName": "mock_cloud_model_v1"
        }, 200)
    elif "Bearer mock_timeout_jwt_token" in auth_header:
        # Simulate timeout
        # Actual requests.exceptions.Timeout
        timeout_error = type('MockTimeoutError', (Exception,), {})
        raise timeout_error("Mock request timed out")
    else:
        # Simulate auth failure or other HTTP error
        return MockRequestsResponse({"error": "Mock authentication failed", "message": "Invalid token"}, 401, text='{"error": "Mock authentication failed", "message": "Invalid token"}')

# Mock for pdd.get_jwt_token.get_jwt_token (async function)
# Define dummy AuthErrors for the mock to raise, assuming they'd be imported from .get_jwt_token
class MockAuthError(Exception): pass
class MockAuthTokenError(MockAuthError): pass

async def mock_get_jwt_token_func(firebase_api_key: str, github_client_id: str, app_name: str) -> str:
    """Mocks the asyncio get_jwt_token function."""
    print(f"[Mock get_jwt_token] Called for app: {app_name}")
    if firebase_api_key == "VALID_FIREBASE_KEY" and github_client_id == "VALID_GITHUB_ID":
        return "mock_valid_jwt_token"
    if firebase_api_key == "TIMEOUT_FIREBASE_KEY" and github_client_id == "TIMEOUT_GITHUB_ID":
        return "mock_timeout_jwt_token" # For testing timeout on requests.post
    print(f"[Mock get_jwt_token] Simulating token error due to invalid mock keys.")
    raise MockAuthTokenError("Mock token acquisition failed")

# --- Example Setup ---
EXAMPLE_BASE_DIR = Path("./output/pdd_code_generator_main_example_files")
PROMPTS_DIR = EXAMPLE_BASE_DIR / "prompts"
SRC_DIR = EXAMPLE_BASE_DIR / "src"
GIT_REPO_DIR = EXAMPLE_BASE_DIR / "git_repo_project"

def setup_directories():
    """Creates example directories, cleaning up if they exist."""
    if EXAMPLE_BASE_DIR.exists():
        shutil.rmtree(EXAMPLE_BASE_DIR)
    PROMPTS_DIR.mkdir(parents=True, exist_ok=True)
    SRC_DIR.mkdir(parents=True, exist_ok=True)
    GIT_REPO_DIR.mkdir(parents=True, exist_ok=True)

def create_file(path: Path, content: str):
    """Helper to create a file with given content."""
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(content, encoding="utf-8")
    print(f"Created file: {path}")

def print_results(generated_code: str, was_incremental: bool, cost: float, model: str, output_file: Optional[Path] = None):
    """Prints the results from code_generator_main and optionally the file content."""
    print(f"  Generated Code (first 100 chars): {generated_code[:100].replace(os.linesep, ' ')}...")
    print(f"  Was Incremental: {was_incremental}")
    print(f"  Total Cost (USD): {cost:.6f}")
    print(f"  Model Name: {model}")
    if output_file and output_file.exists():
        print(f"  Output File Content ({output_file}):")
        print("    " + output_file.read_text(encoding="utf-8").replace("\n", "\n    "))
    elif output_file:
        print(f"  Output File ({output_file}) was NOT created or found.")
    print("-" * 30)

def create_click_context(global_opts: Optional[Dict[str, Any]] = None) -> click.Context:
    """Creates a mock Click context."""
    # Create a dummy command to satisfy Click context requirements
    @click.command()
    def dummy_command():
        pass
    
    ctx = click.Context(dummy_command)
    ctx.obj = global_opts if global_opts is not None else {}
    return ctx

# --- Scenarios ---

def scenario_1_full_local_generation():
    """Demonstrates full code generation using local execution."""
    print("\n--- Scenario 1: Full Local Generation ---")
    prompt_content = "Write a Python function `hello_local()` that returns 'Hello from local!'"
    prompt_file = PROMPTS_DIR / "s1_hello_local_python.prompt"
    create_file(prompt_file, prompt_content)
    
    output_file = SRC_DIR / "s1_hello_local.py"

    ctx = create_click_context(global_opts={
        "verbose": True, 
        "local": True, # Force local execution
        "strength": 0.3,
        "temperature": 0.1
    })

    with patch('pdd.commands.generate.code_generator', side_effect=mock_code_generator_func):
        generated_code, was_incremental, cost, model = code_generator_main(
            ctx=ctx,
            prompt_file=str(prompt_file),
            output=str(output_file),
            original_prompt=None,
            incremental=False 
        )
    print_results(generated_code, was_incremental, cost, model, output_file)

def scenario_2_incremental_git_local_generation():
    """Demonstrates incremental code generation with Git integration (local execution)."""
    print("\n--- Scenario 2: Incremental Git-based Local Generation (Forced Incremental) ---")
    
    # Setup Git repo
    if GIT_REPO_DIR.exists(): # Clean up from previous partial runs if any
        shutil.rmtree(GIT_REPO_DIR)
    GIT_REPO_DIR.mkdir(parents=True, exist_ok=True)
    subprocess.run(["git", "init"], cwd=GIT_REPO_DIR, check=True, capture_output=True)

    original_prompt_content = "Write a Python function `math_op(a, b)` that returns `a + b`."
    prompt_file_rel = Path("prompts") / "s2_math_op_python.prompt" # Relative to git root
    prompt_file_abs = GIT_REPO_DIR / prompt_file_rel
    create_file(prompt_file_abs, original_prompt_content)

    original_code_content = "def math_op(a, b):\n    return a + b"
    code_file_rel = Path("src") / "s2_math_op.py" # Relative to git root
    code_file_abs = GIT_REPO_DIR / code_file_rel
    create_file(code_file_abs, original_code_content)
    
    subprocess.run(["git", "add", str(prompt_file_rel), str(code_file_rel)], cwd=GIT_REPO_DIR, check=True, capture_output=True)
    subprocess.run(["git", "commit", "-m", "Initial version"], cwd=GIT_REPO_DIR, check=True, capture_output=True)

    # Modify the prompt for incremental update
    updated_prompt_content = "Update the Python function `math_op(a, b)` to return `a * b` instead."
    create_file(prompt_file_abs, updated_prompt_content) # Overwrite with new prompt

    ctx = create_click_context(global_opts={
        "verbose": True,
        "local": True, # Incremental falls back to local if cloud fails, or if local is forced
        "strength": 0.6
    })

    # Patch both incremental and full generators, as incremental might suggest full
    with patch('pdd.commands.generate.incremental_code_generator', side_effect=mock_incremental_code_generator_func), \
         patch('pdd.commands.generate.code_generator', side_effect=mock_code_generator_func):
        
        # We pass prompt_file_abs and output=code_file_abs which are absolute paths
        # The git logic inside code_generator_main resolves paths relative to git root
        generated_code, was_incremental, cost, model = code_generator_main(
            ctx=ctx,
            prompt_file=str(prompt_file_abs), # Current (modified) prompt
            output=str(code_file_abs),        # Existing output file to be updated
            original_prompt=None,             # Let it use Git to find original
            incremental=True                  # Force attempt at incremental
        )
    print_results(generated_code, was_incremental, cost, model, code_file_abs)
    
    # Check git status (should show files staged if incremental was successful)
    git_status_result = subprocess.run(["git", "status", "--porcelain"], cwd=GIT_REPO_DIR, check=True, capture_output=True, text=True)
    print(f"  Git status in {GIT_REPO_DIR} after operation:\n{git_status_result.stdout.strip()}")


def scenario_3_cloud_generation_success():
    """Demonstrates successful cloud-based generation."""
    print("\n--- Scenario 3: Cloud Generation (Mock Success) ---")
    # Set mock environment variables for get_jwt_token to succeed
    os.environ["REACT_APP_FIREBASE_API_KEY"] = "VALID_FIREBASE_KEY"
    os.environ["GITHUB_CLIENT_ID"] = "VALID_GITHUB_ID"

    prompt_content = "Write a Python class `CloudGreeter` with a method `greet()`."
    prompt_file = PROMPTS_DIR / "s3_cloud_greeter_python.prompt"
    create_file(prompt_file, prompt_content)
    
    output_file = SRC_DIR / "s3_cloud_greeter.py"

    ctx = create_click_context(global_opts={
        "verbose": True,
        "local": False, # Attempt cloud
        "strength": 0.8
    })

    with patch('pdd.commands.generate.get_jwt_token', side_effect=mock_get_jwt_token_func), \
         patch('pdd.commands.generate.requests.post', side_effect=mock_requests_post_func), \
         patch('pdd.commands.generate.code_generator', side_effect=mock_code_generator_func): # For fallback if any
        generated_code, was_incremental, cost, model = code_generator_main(
            ctx=ctx,
            prompt_file=str(prompt_file),
            output=str(output_file),
            original_prompt=None,
            incremental=False
        )
    print_results(generated_code, was_incremental, cost, model, output_file)
    del os.environ["REACT_APP_FIREBASE_API_KEY"]
    del os.environ["GITHUB_CLIENT_ID"]

def scenario_4_cloud_generation_fail_fallback_local():
    """Demonstrates cloud generation failure and fallback to local."""
    print("\n--- Scenario 4: Cloud Generation (Mock Auth Fail -> Local Fallback) ---")
    # Set mock environment variables for get_jwt_token to fail
    os.environ["REACT_APP_FIREBASE_API_KEY"] = "INVALID_FIREBASE_KEY"
    os.environ["GITHUB_CLIENT_ID"] = "INVALID_GITHUB_ID"

    prompt_content = "Write a Python function `fallback_func()`."
    prompt_file = PROMPTS_DIR / "s4_fallback_python.prompt"
    create_file(prompt_file, prompt_content)
    
    output_file = SRC_DIR / "s4_fallback.py"

    ctx = create_click_context(global_opts={
        "verbose": True,
        "local": False, # Attempt cloud
        "strength": 0.4
    })

    # Patch get_jwt_token to simulate auth failure, requests.post (won't be hit if token fails),
    # and code_generator for the local fallback.
    with patch('pdd.commands.generate.get_jwt_token', side_effect=mock_get_jwt_token_func), \
         patch('pdd.commands.generate.requests.post', side_effect=mock_requests_post_func), \
         patch('pdd.commands.generate.code_generator', side_effect=mock_code_generator_func):
        generated_code, was_incremental, cost, model = code_generator_main(
            ctx=ctx,
            prompt_file=str(prompt_file),
            output=str(output_file),
            original_prompt=None,
            incremental=False
        )
    print_results(generated_code, was_incremental, cost, model, output_file)
    del os.environ["REACT_APP_FIREBASE_API_KEY"]
    del os.environ["GITHUB_CLIENT_ID"]


def main():
    """Runs all scenarios for demonstrating code_generator_main."""
    setup_directories()
    
    # Note: To run these examples, the PDD package structure must be correct and accessible
    # (e.g., via PYTHONPATH or installation) so that `from pdd.commands.generate import code_generator_main`
    # and its internal relative imports work.
    # The mocks ensure no actual LLM or cloud services are hit.

    scenario_1_full_local_generation()
    scenario_2_incremental_git_local_generation()
    scenario_3_cloud_generation_success()
    scenario_4_cloud_generation_fail_fallback_local()

    print(f"\nAll scenarios complete. Check the '{EXAMPLE_BASE_DIR}' directory for output files.")
    # To cleanup: shutil.rmtree(EXAMPLE_BASE_DIR)

if __name__ == "__main__":
    # This is needed for asyncio.run used within code_generator_main for get_jwt_token
    # In some environments (like older Python versions or specific OS),
    # a new event loop policy might be needed if running asyncio from a non-main thread
    # or if there are issues with default event loop. For typical CLI usage, this is fine.
    # asyncio.set_event_loop_policy(asyncio.WindowsSelectorEventLoopPolicy()) # Example for Windows if needed
    main()