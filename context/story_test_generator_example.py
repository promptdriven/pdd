import os
import sys
from pathlib import Path
import shutil

# --- Setup for module import ---
# This script is located in 'context/', and the module is in 'pdd/'.
# We need to add the directory containing 'pdd' to sys.path.
# The PDD_PATH environment variable is set to the path of the 'pdd' directory.
# We need the parent of PDD_PATH to add to sys.path.
pdd_path = Path(os.environ.get("PDD_PATH", "")).resolve()
if not pdd_path.is_dir():
    print(f"Error: PDD_PATH environment variable is not set or points to an invalid directory: {pdd_path}")
    print("Please ensure PDD_PATH is set to the root 'pdd' directory.")
    sys.exit(0)

# Add the directory containing the 'pdd' package to sys.path
sys.path.insert(0, str(pdd_path.parent))

from pdd.story_test_generator import (  # noqa: E402
    parse_story_test_spec,
    render_story_test,
    generate_story_test,
    StoryTestSpec,
    StoryTestGenerationResult,
)

# --- Example Setup: Create dummy story and contract files ---
# Define paths relative to the current script's location
current_dir = Path(__file__).parent
# Keep every generated artifact inside this example's dedicated sandbox. Never
# write into or remove the repository's real user_stories/ tree.
project_root = current_dir / "output" / "story_test_generator_example"

user_stories_dir = project_root / "user_stories"
contracts_dir = user_stories_dir / "contracts"
output_dir = project_root / "output" / "tests" / "story_regression"

# Ensure directories exist
user_stories_dir.mkdir(parents=True, exist_ok=True)
contracts_dir.mkdir(parents=True, exist_ok=True)
output_dir.mkdir(parents=True, exist_ok=True)

# Define story and contract file paths
story_slug = "example_feature"
story_file_name = f"story__{story_slug}.md"
contract_file_name = f"{story_slug}.contract.md"

story_path = user_stories_dir / story_file_name
contract_path = contracts_dir / contract_file_name
generated_test_path = output_dir / f"test_story_{story_slug}.py"

# Content for the dummy story file
story_content = """
# Example Feature Story

As a user, I want to process some input data
so that I can get a transformed output.
"""

# Content for the dummy contract file
contract_content = """
## Entry Point
- module: example_module
- callable: process_data
- args: ["input_value"]
- kwargs: {"option": True}

## Seams
- example_module.dependency_func = "mock_value"
- another_module.config.setting = 123

## Covers
- R1: Basic processing
- RULE-2A: Edge case handling

## Oracle
- assert result == "processed_input_value_mock_value_123_True"
- assert "processed" in result

## Negative Cases
- assert "error" not in result
"""

# Write the dummy files
story_path.write_text(story_content, encoding="utf-8")
contract_path.write_text(contract_content, encoding="utf-8")

# --- Create a dummy 'example_module.py' for the generated test to import ---
# This module needs to be importable by the generated test.
# We'll place it in a temporary 'temp_modules' directory at project root.
temp_modules_dir = project_root / "temp_modules"
temp_modules_dir.mkdir(exist_ok=True)
example_module_path = temp_modules_dir / "example_module.py"

example_module_content = """
# This is a dummy module for the story test example.
import sys

def process_data(input_value, option=False):
    # Simulate some processing that might use mocked dependencies
    # and kwargs.
    # In a real scenario, 'dependency_func' and 'another_module.config.setting'
    # would be actual imports that get monkeypatched.
    try:
        from example_module import dependency_func
    except ImportError:
        dependency_func = lambda: "default_mock_value" # Fallback if not patched

    try:
        import another_module.config
        setting = another_module.config.setting
    except (ImportError, AttributeError):
        setting = 0 # Fallback if not patched

    return f"processed_{input_value}_{dependency_func()}_{setting}_{option}"

# Dummy dependency_func for potential patching
def dependency_func():
    return "original_dependency_value"

# Dummy another_module for potential patching
class Config:
    setting = 999

class AnotherModule:
    config = Config

sys.modules['another_module'] = AnotherModule()
"""
example_module_path.write_text(example_module_content, encoding="utf-8")

# Add temp_modules_dir to sys.path so 'example_module' can be imported
sys.path.insert(0, str(temp_modules_dir))

print(f"--- Created dummy story file: {story_path}")
print(f"--- Created dummy contract file: {contract_path}")
print(f"--- Created dummy example module: {example_module_path}")
print("-" * 80)

# --- 1. Demonstrate parse_story_test_spec ---
print("1. Parsing story test specification...")
try:
    spec: StoryTestSpec = parse_story_test_spec(story_path)
    print("\nSuccessfully parsed StoryTestSpec:")
    print(f"  Story ID: {spec.story_id}")
    print(f"  Story Hash: {spec.story_hash}")
    print(f"  Module: {spec.module}")
    print(f"  Callable: {spec.callable_name}")
    print(f"  Args: {spec.args}")
    print(f"  Kwargs: {spec.kwargs}")
    print(f"  Seams: {spec.seams}")
    print(f"  Rule IDs: {spec.rule_ids}")
    print(f"  Oracle Assertions: {spec.oracle_assertions}")
    print(f"  Negative Assertions: {spec.negative_assertions}")
except ValueError as e:
    print(f"Error parsing story test spec: {e}")
    sys.exit(0)
print("-" * 80)

# --- 2. Demonstrate render_story_test ---
print("2. Rendering pytest source from StoryTestSpec...")
generated_source: str = render_story_test(spec)
print("\n--- Generated Pytest Source Code ---")
print(generated_source)
print("--- End Generated Pytest Source Code ---")
print("-" * 80)

# --- 3. Demonstrate generate_story_test ---
print(f"3. Generating and writing pytest file to {generated_test_path}...")
try:
    result: StoryTestGenerationResult = generate_story_test(story_path, output=generated_test_path)
    print("\nSuccessfully generated story test file:")
    print(f"  Output Path: {result.output_path}")
    print(f"  Test Count: {result.test_count}")
    print(f"  Story ID: {result.story_id}")
    print(f"  Story Hash: {result.story_hash}")

    # Verify content
    if generated_test_path.exists():
        print(f"\nContent of generated file '{generated_test_path}':")
        print("---")
        print(generated_test_path.read_text(encoding="utf-8"))
        print("---")
    else:
        print(f"Error: Generated file not found at {generated_test_path}")

except ValueError as e:
    print(f"Error generating story test: {e}")
    sys.exit(0)
print("-" * 80)

# --- Cleanup ---
print("Cleaning up generated files and directories...")
try:
    if project_root.exists():
        shutil.rmtree(project_root)
        print(f"Removed example sandbox: {project_root}")

except OSError as e:
    print(f"Error during cleanup: {e}")

print("\nExample execution complete.")
