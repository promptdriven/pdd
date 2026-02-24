"""Example usage of validate_prompt_includes module."""

from pdd.validate_prompt_includes import validate_prompt_includes, validate_include_tag
from pathlib import Path
import tempfile
import os


def example_validate_single_include():
    """Example: Validate a single include tag."""
    # Create a temporary file to test with
    with tempfile.NamedTemporaryFile(mode='w', suffix='.py', delete=False) as f:
        f.write("# Example file\nprint('hello')\n")
        temp_file = f.name

    try:
        base_dir = os.path.dirname(temp_file)
        file_name = os.path.basename(temp_file)

        # This should return True (file exists)
        exists = validate_include_tag(file_name, base_dir)
        print(f"File exists: {exists}")  # True

        # This should return False (file doesn't exist)
        exists = validate_include_tag("nonexistent_file.py", base_dir)
        print(f"Nonexistent file exists: {exists}")  # False
    finally:
        os.unlink(temp_file)


def example_validate_prompt_with_invalid_includes():
    """Example: Validate a prompt with invalid <include> tags."""
    content = '''
% This is a test prompt

Dependencies
<database_models>
  <include>context/database_models_example.py</include>
</database_models>
<auth_utils>
  <include>context/auth_utils_example.py</include>
</auth_utils>

Instructions
- Implement the module
'''

    # Validate with replace mode (default)
    validated, invalid = validate_prompt_includes(content, base_dir=".", remove_invalid=False)

    print(f"Found {len(invalid)} invalid includes:")
    for path in invalid:
        print(f"  - {path}")

    print("\nValidated content (with comments):")
    print(validated)


def example_validate_prompt_remove_invalid():
    """Example: Validate a prompt and remove invalid <include> tags."""
    content = '''
Dependencies
<database_models>
  <include>context/database_models_example.py</include>
</database_models>
'''

    # Validate with remove mode
    validated, invalid = validate_prompt_includes(content, base_dir=".", remove_invalid=True)

    print(f"Removed {len(invalid)} invalid includes")
    print("\nValidated content (tags removed):")
    print(validated)


if __name__ == "__main__":
    print("=== Example 1: Validate single include ===")
    example_validate_single_include()

    print("\n=== Example 2: Validate prompt with invalid includes ===")
    example_validate_prompt_with_invalid_includes()

    print("\n=== Example 3: Remove invalid includes ===")
    example_validate_prompt_remove_invalid()
