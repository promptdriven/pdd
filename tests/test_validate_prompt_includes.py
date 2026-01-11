# tests/test_validate_prompt_includes.py
"""
Tests for the validate_prompt_includes module.

This module validates and cleans <include> tags in generated prompts,
removing or replacing references to non-existent files.

Related to Issue #225: Example import issue with template
"""

import pytest
import os
import tempfile
from pathlib import Path

from pdd.validate_prompt_includes import (
    validate_include_tag,
    validate_prompt_includes,
)


class TestValidateIncludeTag:
    """Tests for validate_include_tag function."""

    def test_existing_file_returns_true(self, tmp_path):
        """Test that existing files return True."""
        # Create a temporary file
        test_file = tmp_path / "existing_file.py"
        test_file.write_text("# test file")

        result = validate_include_tag("existing_file.py", str(tmp_path))
        assert result is True

    def test_nonexistent_file_returns_false(self, tmp_path):
        """Test that non-existent files return False."""
        result = validate_include_tag("nonexistent_file.py", str(tmp_path))
        assert result is False

    def test_absolute_path_existing(self, tmp_path):
        """Test absolute path to existing file."""
        test_file = tmp_path / "absolute_test.py"
        test_file.write_text("# test")

        result = validate_include_tag(str(test_file), str(tmp_path))
        assert result is True

    def test_absolute_path_nonexistent(self):
        """Test absolute path to non-existent file."""
        result = validate_include_tag("/nonexistent/path/file.py", ".")
        assert result is False

    def test_path_with_subdirectory(self, tmp_path):
        """Test path with subdirectory."""
        subdir = tmp_path / "context"
        subdir.mkdir()
        test_file = subdir / "example.py"
        test_file.write_text("# test")

        result = validate_include_tag("context/example.py", str(tmp_path))
        assert result is True

    def test_path_with_spaces(self, tmp_path):
        """Test path with spaces in filename."""
        test_file = tmp_path / "file with spaces.py"
        test_file.write_text("# test")

        result = validate_include_tag("file with spaces.py", str(tmp_path))
        assert result is True


class TestValidatePromptIncludes:
    """Tests for validate_prompt_includes function."""

    def test_valid_includes_unchanged(self, tmp_path):
        """Test that valid includes are not modified."""
        # Create test files
        context_dir = tmp_path / "context"
        context_dir.mkdir()
        (context_dir / "example.py").write_text("# test")

        content = """
<dependency>
  <include>context/example.py</include>
</dependency>
"""
        validated, invalid = validate_prompt_includes(content, str(tmp_path))

        assert len(invalid) == 0
        assert "<include>context/example.py</include>" in validated

    def test_invalid_includes_detected(self, tmp_path):
        """Test that invalid includes are detected."""
        content = """
<dependency>
  <include>context/nonexistent.py</include>
</dependency>
"""
        validated, invalid = validate_prompt_includes(content, str(tmp_path))

        assert len(invalid) == 1
        assert "context/nonexistent.py" in invalid

    def test_invalid_includes_replaced_with_comment(self, tmp_path):
        """Test that invalid includes are replaced with comments (default mode)."""
        content = """
<dependency>
  <include>context/nonexistent.py</include>
</dependency>
"""
        validated, invalid = validate_prompt_includes(
            content, str(tmp_path), remove_invalid=False
        )

        assert "<!-- Missing: context/nonexistent.py -->" in validated
        assert "<include>context/nonexistent.py</include>" not in validated

    def test_invalid_includes_removed(self, tmp_path):
        """Test that invalid includes are removed with remove_invalid=True."""
        content = """
<dependency>
  <include>context/nonexistent.py</include>
</dependency>
"""
        validated, invalid = validate_prompt_includes(
            content, str(tmp_path), remove_invalid=True
        )

        assert "<dependency>" not in validated
        assert "<include>" not in validated
        assert len(invalid) == 1

    def test_multiple_invalid_includes(self, tmp_path):
        """Test handling multiple invalid includes."""
        content = """
<dep1>
  <include>context/file1.py</include>
</dep1>
<dep2>
  <include>context/file2.py</include>
</dep2>
"""
        validated, invalid = validate_prompt_includes(content, str(tmp_path))

        assert len(invalid) == 2
        assert "context/file1.py" in invalid
        assert "context/file2.py" in invalid

    def test_mixed_valid_and_invalid(self, tmp_path):
        """Test mix of valid and invalid includes."""
        context_dir = tmp_path / "context"
        context_dir.mkdir()
        (context_dir / "valid.py").write_text("# valid")

        content = """
<valid_dep>
  <include>context/valid.py</include>
</valid_dep>
<invalid_dep>
  <include>context/invalid.py</include>
</invalid_dep>
"""
        validated, invalid = validate_prompt_includes(content, str(tmp_path))

        assert len(invalid) == 1
        assert "context/invalid.py" in invalid
        assert "<include>context/valid.py</include>" in validated

    def test_nested_tags(self, tmp_path):
        """Test handling of nested XML tags."""
        content = """
<dependencies>
  <database>
    <include>context/db.py</include>
  </database>
</dependencies>
"""
        validated, invalid = validate_prompt_includes(
            content, str(tmp_path), remove_invalid=True
        )

        assert "context/db.py" in invalid
        # The inner <database> block should be removed
        assert "<database>" not in validated

    def test_preserves_other_content(self, tmp_path):
        """Test that non-include content is preserved."""
        content = """
% This is a prompt header

Requirements
1. Do something
2. Do something else

<dependency>
  <include>context/missing.py</include>
</dependency>

Instructions
- Follow the requirements
"""
        validated, invalid = validate_prompt_includes(content, str(tmp_path))

        assert "% This is a prompt header" in validated
        assert "Requirements" in validated
        assert "Instructions" in validated
        assert len(invalid) == 1


class TestIssue225Integration:
    """Integration tests specifically for Issue #225 scenario."""

    def test_generated_prompt_with_fabricated_includes(self, tmp_path):
        """
        Test the exact scenario from Issue #225:
        LLM generates <include>context/xxx_example.py</include> for files that don't exist.
        """
        # Simulate the output from generic/generate_prompt template
        generated_prompt = """
% You are an expert Python engineer. Create user_service module.

Requirements
1. Implement user authentication
2. Handle user CRUD operations

Dependencies
<database_models>
  <include>context/database_models_example.py</include>
</database_models>
<auth_utils>
  <include>context/auth_utils_example.py</include>
</auth_utils>

Instructions
- Implement the service following best practices
"""
        validated, invalid = validate_prompt_includes(
            generated_prompt, str(tmp_path), remove_invalid=False
        )

        # Both includes should be detected as invalid
        assert len(invalid) == 2
        assert "context/database_models_example.py" in invalid
        assert "context/auth_utils_example.py" in invalid

        # Includes should be replaced with comments
        assert "<!-- Missing: context/database_models_example.py -->" in validated
        assert "<!-- Missing: context/auth_utils_example.py -->" in validated

        # Original content should be preserved
        assert "% You are an expert Python engineer" in validated
        assert "Requirements" in validated
        assert "Instructions" in validated

    def test_remove_mode_for_generated_prompt(self, tmp_path):
        """Test removing invalid includes from generated prompt."""
        generated_prompt = """
Dependencies
<pydantic>
  <include>context/pydantic_example.py</include>
</pydantic>

Prompt Dependencies:
- pydantic_Python.prompt (for data validation)
"""
        validated, invalid = validate_prompt_includes(
            generated_prompt, str(tmp_path), remove_invalid=True
        )

        assert len(invalid) == 1
        assert "<pydantic>" not in validated
        # Prompt Dependencies section should be preserved
        assert "Prompt Dependencies:" in validated


if __name__ == "__main__":
    pytest.main([__file__, "-v"])
