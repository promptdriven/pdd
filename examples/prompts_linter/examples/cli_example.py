import sys
import os
from typer.testing import CliRunner
from unittest.mock import patch, MagicMock

# --- Path Setup ---
# Add the project root to sys.path to allow importing from src
current_dir = os.path.dirname(os.path.abspath(__file__))
project_root = os.path.abspath(os.path.join(current_dir, '..'))
if project_root not in sys.path:
    sys.path.insert(0, project_root)

# Import the Typer app object from the CLI module
# Note: Adjust the import based on whether the file is named main.py or cli.py
from src.cli.cli import app

from src.utils.models import Report, Issue, Severity, RuleCategory

# Initialize the Typer test runner
runner = CliRunner()

def create_mock_report(filepath: str) -> Report:
    """Creates a dummy report to be returned by the mocked pipeline."""
    return Report(
        filepath=filepath,
        score=85,
        issues=[
            Issue(
                rule_id="MOD001",
                severity=Severity.WARNING,
                category=RuleCategory.MODULARITY,
                line_number=10,
                description="Prompt is getting too long.",
                fix_suggestion="Split into sub-prompts."
            )
        ],
        summary="Mock analysis complete."
    )

def main():
    """Main execution function for the programmatic CLI usage example."""
    print("=== PDD Linter CLI Programmatic Usage Example ===\n")

    # We create a dummy file to satisfy Typer's 'exists=True' check
    dummy_file = "test_prompt.txt"
    with open(dummy_file, "w") as f:
        f.write("This is a test prompt.")

    try:
        # We mock 'lint_file' so we don't actually run the heavy analysis logic
        # or make LLM calls during this example.
        with patch("src.cli.cli.lint_file") as mock_lint:
            # Configure the mock to return our dummy report
            mock_lint.return_value = create_mock_report(dummy_file)

            # --- Scenario 1: Basic Linting ---
            print("1. Running basic lint command...")
            result = runner.invoke(app, [dummy_file])
            
            print(f"Exit Code: {result.exit_code}")
            # The output will contain the Rich console output captured as a string
            print("Output snippet:")
            print(result.stdout[:200] + "...\n")

            # --- Scenario 2: JSON Output ---
            print("2. Running with JSON format...")
            result = runner.invoke(app, [dummy_file, "--format", "json"])
            
            print(f"Exit Code: {result.exit_code}")
            print("Output (JSON):")
            print(result.stdout)

            # --- Scenario 3: Fail-on Error (Simulating Failure) ---
            print("3. Running with --fail-on warning...")
            # Since our mock report has a WARNING, this should exit with code 1
            result = runner.invoke(app, [dummy_file, "--fail-on", "warning"])
            
            print(f"Exit Code: {result.exit_code} (Expected: 1)")
            if result.exit_code == 1:
                print("SUCCESS: CLI correctly failed on warning threshold.")
            else:
                print("FAILURE: CLI did not fail as expected.")

            # --- Scenario 4: Configuration Passing ---
            print("\n4. Verifying configuration passing...")
            runner.invoke(app, [
                dummy_file, 
                "--assume-cloud-grounding", 
                "--llm-provider", "openai",
                "--llm-budget-tokens", "1000"
            ])
            
            # Check what arguments were passed to the internal lint_file function
            call_args = mock_lint.call_args
            if call_args:
                _, kwargs = call_args
                config = kwargs.get('config')
                print("Config passed to pipeline:")
                
                # Helper to safely get attributes from object or dict
                def safe_get(obj, key, default=None):
                    if obj is None:
                        return default
                    if isinstance(obj, dict):
                        return obj.get(key, default)
                    return getattr(obj, key, default)

                print(f"  - Grounding: {safe_get(config, 'grounding')}")
                
                # Handle potential nested llm_config or flat attributes
                llm_config = safe_get(config, 'llm_config')
                if llm_config:
                     print(f"  - LLM Provider: {safe_get(llm_config, 'provider')}")
                     print(f"  - Token Budget: {safe_get(llm_config, 'budget_tokens')}")
                else:
                     # Fallback to checking flat attributes if llm_config isn't there
                     # We check both 'llm_provider' (CLI arg name) and 'provider' (LintConfig init arg name)
                     provider = safe_get(config, 'llm_provider') or safe_get(config, 'provider')
                     budget = safe_get(config, 'llm_budget_tokens') or safe_get(config, 'budget')
                     
                     print(f"  - LLM Provider: {provider}")
                     print(f"  - Token Budget: {budget}")
            else:
                print("Mock was not called.")

    finally:
        # Cleanup
        if os.path.exists(dummy_file):
            os.remove(dummy_file)

if __name__ == "__main__":
    main()