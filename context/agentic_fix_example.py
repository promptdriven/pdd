import os
import tempfile
from pathlib import Path
import subprocess
import shutil

# In a real project, the module would be imported from your package structure, e.g.:
from pdd.agentic_fix import run_agentic_fix, AGENT_PROVIDER_PREFERENCE
from pdd.agentic_common import get_available_agents
# from agentic_fix import run_agentic_fix, AGENT_PROVIDER_PREFERENCE
# from agentic_common import get_available_agents

# --- 1. Define the buggy code, its failing test, and a fix prompt ---

BUGGY_CODE = """
def add(a, b):
    # This is intentionally incorrect to demonstrate the agentic fix.
    return a - b
"""

TEST_CODE = """
from buggy_calculator import add

def test_add_positive_numbers():
    assert add(2, 3) == 5

def test_add_negative_numbers():
    assert add(-1, -5) == -6
"""

PROMPT_TEXT = """
The `add` function in `buggy_calculator.py` is failing its tests.
It should correctly perform addition for both positive and negative numbers.
Please analyze the code, the test, and the error log to fix the implementation.
"""

def setup_scenario(temp_dir: Path) -> dict[str, str]:
    """
    Creates the necessary files for the agentic fix scenario in a temporary directory.

    Args:
        temp_dir: The root directory for the temporary project.

    Returns:
        A dictionary mapping file types to their absolute paths.
    """
    paths = {
        "code": temp_dir / "buggy_calculator.py",
        "test": temp_dir / "test_calculator.py",
        "prompt": temp_dir / "fix_prompt.txt",
        "error_log": temp_dir / "error.log",
    }

    # Write the code, test, and prompt files
    paths["code"].write_text(BUGGY_CODE)
    paths["test"].write_text(TEST_CODE)
    paths["prompt"].write_text(PROMPT_TEXT)

    # Generate the initial error log by running the failing test.
    # This simulates the pre-condition for calling run_agentic_fix.
    print("   - Generating initial error log by running pytest...")
    try:
        result = subprocess.run(
            ["pytest", str(paths["test"])],
            capture_output=True,
            text=True,
            cwd=temp_dir,
            check=False,  # Don't raise an exception on test failure
        )
        error_output = result.stdout + "\n" + result.stderr
        paths["error_log"].write_text(error_output)
        print("   - Initial error log generated successfully.")
    except FileNotFoundError:
        print("   - WARNING: `pytest` not found. Creating a placeholder error log.")
        paths["error_log"].write_text("Placeholder: pytest failed with an assertion error.")

    return {key: str(value) for key, value in paths.items()}


def check_prerequisites() -> bool:
    """Checks for available agents before running the example.

    Uses get_available_agents() which detects:
    - Claude CLI (subscription auth, no API key needed)
    - API keys (ANTHROPIC_API_KEY, GEMINI_API_KEY, OPENAI_API_KEY)
    - Vertex AI auth (GOOGLE_APPLICATION_CREDENTIALS + GOOGLE_GENAI_USE_VERTEXAI)
    """
    available = get_available_agents()

    if not available:
        print("🛑 ERROR: No agent available.")
        print("   Please ensure one of the following:")
        print("   - Claude CLI is installed (for Anthropic subscription users)")
        print("   - ANTHROPIC_API_KEY is set")
        print("   - GEMINI_API_KEY or GOOGLE_API_KEY is set (with gemini CLI)")
        print("   - OPENAI_API_KEY is set (with codex CLI)")
        return False

    print(f"   Available agents: {', '.join(available)}")
    return True


def main():
    """
    Main function to demonstrate a complete agentic fix workflow.
    """
    print("🚀 Starting agentic fix demonstration...")

    if not check_prerequisites():
        return

    # Use a temporary directory as a self-contained project root
    with tempfile.TemporaryDirectory() as temp_dir_str:
        temp_dir = Path(temp_dir_str)
        original_cwd = Path.cwd()
        # The module uses os.getcwd() as the project root, so we chdir into it
        os.chdir(temp_dir)

        try:
            # 2. Set up the project with the buggy code, test, and prompt
            print(f"\n🔧 Setting up scenario in: {temp_dir}")
            file_paths = setup_scenario(temp_dir)

            # 3. Invoke the agentic fix process
            print("\n🤖 Calling `run_agentic_fix`...")
            print("   This will invoke an LLM agent via its CLI.")
            print("   Please be patient, this may take a few minutes...\n")
            
            # Set log level to see agent activity (optional)
            os.environ["PDD_AGENTIC_LOGLEVEL"] = "normal"

            success, message, cost, model, changed_files = run_agentic_fix(
                prompt_file=file_paths["prompt"],
                code_file=file_paths["code"],
                unit_test_file=file_paths["test"],
                error_log_file=file_paths["error_log"],
            )

            # 4. Report the results
            print("\n--- AGENTIC FIX COMPLETE ---")
            if success:
                print(f"✅ Success: {message}")
                print(f"   - Model Used: {model}")
                print(f"   - Estimated Cost: ${cost:.4f}")
                if changed_files:
                    print(f"   - Changed Files: {', '.join(changed_files)}")
                
                # 5. Verify the fix by inspecting the corrected code
                fixed_code = Path(file_paths["code"]).read_text()
                print("\n📝 Corrected Code:")
                print("-------------------")
                print(fixed_code.strip())
                print("-------------------")
            else:
                print(f"❌ Failure: {message}")
                print(f"   - Model Used: {model}")
                print(f"   - Estimated Cost: ${cost:.4f}")

        finally:
            # Clean up by restoring the original working directory
            os.chdir(original_cwd)
            print("\n🧹 Cleaned up temporary directory.")


if __name__ == "__main__":
    main()