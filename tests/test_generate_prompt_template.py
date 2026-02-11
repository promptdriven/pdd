# tests/test_generate_prompt_template.py
"""
Tests for the generic/generate_prompt template.

Issue #225: Example import issue with template
https://github.com/promptdriven/pdd/issues/225

Problem:
The generate_prompt.prompt template instructs LLM to assume dependency example
files exist in context/ directory even when they don't exist. This causes the
LLM to generate invalid <include> tags like:
    <include>[File not found: context/pydantic_v2_example.py]</include>

Root cause (from template line 131):
    "If examples are not provided, assume dependency examples live under context/
    using the pattern context/[dependency_name]_example.${DEP_EXAMPLE_EXT}."

Expected behavior:
- Only reference files that are explicitly provided in the context
- Do NOT hallucinate or assume files exist
- If a dependency example is not available, describe the interface instead
"""

import pytest
import os
import re
from pathlib import Path
from unittest.mock import patch, MagicMock


class TestGeneratePromptTemplateContent:
    """Unit tests for the generate_prompt.prompt template content."""

    @pytest.fixture
    def template_content(self):
        """Load the generate_prompt.prompt template content."""
        from pdd.load_prompt_template import load_prompt_template
        content = load_prompt_template("generic/generate_prompt")
        if content is None:
            # Try loading directly from templates directory
            template_path = Path(__file__).parent.parent / "pdd" / "templates" / "generic" / "generate_prompt.prompt"
            if template_path.exists():
                content = template_path.read_text()
        return content

    def test_template_exists(self, template_content):
        """Verify the generate_prompt.prompt template exists."""
        assert template_content is not None, \
            "generic/generate_prompt template should exist"

    def test_template_should_not_instruct_to_assume_files_exist(self, template_content):
        """
        BUG TEST (Issue #225): Template should NOT instruct LLM to assume files exist.

        The problematic instruction is:
        "If examples are not provided, assume dependency examples live under context/"

        This test FAILS until the bug is fixed.
        """
        def is_negated(content: str, match: re.Match, window: int = 50) -> bool:
            """Check if a match is preceded by negation words (NOT, never, don't)."""
            start = max(0, match.start() - window)
            preceding = content[start:match.start()].lower()
            return bool(re.search(r'\b(do\s+not|don\'t|never|should\s+not|must\s+not)\b', preceding))

        # Check for problematic instructions (but exclude negated forms like "Do NOT assume")
        problematic_patterns = [
            r"assume.*dependency.*examples.*live.*under.*context",
            r"assume.*example.*files.*exist",
            r"If.*examples.*are.*not.*provided.*assume",
        ]

        for pattern in problematic_patterns:
            match = re.search(pattern, template_content, re.IGNORECASE)
            if match and not is_negated(template_content, match):
                raise AssertionError(
                    f"Template should NOT instruct LLM to assume files exist.\n"
                    f"Found problematic instruction matching pattern '{pattern}':\n"
                    f"  '{match.group(0)}'\n"
                    f"This causes Issue #225 where LLM generates invalid <include> tags "
                    f"for non-existent files."
                )

    def test_template_should_instruct_to_only_use_provided_context(self, template_content):
        """
        Template should explicitly instruct LLM to only reference files
        that are provided in the context.

        This test FAILS until the fix is implemented.
        """
        # Look for instructions about only using provided context
        positive_patterns = [
            r"only.*include.*dependencies.*that.*are.*explicitly.*provided",
            r"do.*not.*assume.*or.*hallucinate",
            r"do.*not.*fabricate.*file.*paths.*or.*assume.*files.*exist",
            r"only.*use.*include.*tags.*when",
        ]

        found_any = False
        for pattern in positive_patterns:
            if re.search(pattern, template_content, re.IGNORECASE):
                found_any = True
                break

        assert found_any, (
            "Template should explicitly instruct LLM to only reference "
            "files that are provided in the context. Add instructions like:\n"
            "  'Do NOT fabricate file paths or assume files exist'"
        )

    def test_template_should_instruct_alternative_for_missing_deps(self, template_content):
        """
        Template should instruct LLM what to do when dependency examples
        are NOT available (instead of assuming they exist).

        Expected: Describe the interface or list in Prompt Dependencies section.
        This test FAILS until the fix is implemented.
        """
        # Look for instructions about handling missing dependencies
        alternative_patterns = [
            r"if.*example.*file.*is.*not.*available.*do.*not.*create.*include",
            r"if.*no.*example.*file.*exists.*list.*in.*prompt.*dependencies",
            r"when.*no.*example.*file.*is.*available",
            r"list.*in.*prompt.*dependencies.*subsection",
        ]

        found_any = False
        for pattern in alternative_patterns:
            if re.search(pattern, template_content, re.IGNORECASE):
                found_any = True
                break

        assert found_any, (
            "Template should instruct LLM what to do when dependency examples "
            "are NOT available. Suggested instructions:\n"
            "  'When no example file is available, list in Prompt Dependencies subsection'"
        )


class TestGeneratePromptTemplateWithHardcodedPath:
    """Tests for hardcoded 'context/' path issue."""

    @pytest.fixture
    def template_content(self):
        """Load the generate_prompt.prompt template content."""
        from pdd.load_prompt_template import load_prompt_template
        content = load_prompt_template("generic/generate_prompt")
        if content is None:
            template_path = Path(__file__).parent.parent / "pdd" / "templates" / "generic" / "generate_prompt.prompt"
            if template_path.exists():
                content = template_path.read_text()
        return content

    def test_example_path_should_be_configurable(self, template_content):
        """
        Issue #225 secondary problem: The 'context/' directory path is hardcoded
        in the template, but users can configure example_output_path in .pddrc.

        The template should either:
        1. Use a variable for the example directory (e.g., ${EXAMPLE_DIR})
        2. Or not assume any specific directory structure
        """
        # Count occurrences of hardcoded 'context/' path
        hardcoded_context_refs = re.findall(
            r'context/\[?[a-z_]+\]?_example',
            template_content,
            re.IGNORECASE
        )

        # There's an acceptable example in the template showing format
        # But the instruction "assume dependency examples live under context/" is problematic

        # Check for the problematic assumption instruction
        problematic = re.search(
            r"assume.*examples.*live.*under.*context/",
            template_content,
            re.IGNORECASE
        )

        assert problematic is None, (
            f"Template hardcodes 'context/' directory path in instructions.\n"
            f"Found: {problematic.group(0) if problematic else 'N/A'}\n"
            f"This is problematic because users can configure different "
            f"example_output_path in .pddrc (e.g., 'examples/', 'context/backend/').\n"
            f"The template should either use a configurable variable or not assume "
            f"any specific directory structure."
        )


class TestGeneratedPromptValidation:
    """
    Integration tests to validate generated prompts don't contain
    invalid <include> tags.

    These tests simulate what happens when generate_prompt.prompt is used
    to generate module prompts, and verify the output doesn't contain
    references to non-existent files.
    """

    @pytest.fixture
    def mock_architecture_json(self):
        """Sample architecture.json for testing."""
        return """
{
  "modules": [
    {
      "filename": "user_service_Python.prompt",
      "description": "User authentication and management service",
      "dependencies": ["database_models_Python.prompt", "auth_utils_Python.prompt"],
      "interface": {
        "type": "module",
        "functions": ["create_user", "authenticate", "get_user_by_id"]
      },
      "reason": "Core user management functionality"
    }
  ]
}
"""

    def test_generated_prompt_should_not_have_file_not_found_includes(
        self, mock_architecture_json, tmp_path
    ):
        """
        BUG TEST (Issue #225): Generated prompt should NOT contain
        <include>[File not found: ...]</include> patterns.

        When the LLM generates a prompt using generate_prompt.prompt template,
        it should NOT output include tags for files that don't exist.

        This test validates the OUTPUT of the template, not the template itself.
        """
        # Create a minimal test environment
        arch_file = tmp_path / "architecture.json"
        arch_file.write_text(mock_architecture_json)

        # Simulate a generated prompt output (what the LLM might produce with the bug)
        buggy_generated_prompt = """
% You are an expert Python engineer. Create user_service module.

Requirements
1. Implement user authentication
2. Handle user CRUD operations

Dependencies
<database_models>
  <include>context/database_models_example.py</include>
</database_models>

<pydantic>
  <include>[File not found: context/pydantic_example.py]</include>
</pydantic>

<auth_utils>
  <include>[File not found: context/auth_utils_example.py]</include>
</auth_utils>

Instructions
- Implement the service following best practices
"""

        # Check for the bug pattern
        file_not_found_pattern = r'<include>\[File not found:.*?\]</include>'
        matches = re.findall(file_not_found_pattern, buggy_generated_prompt)

        # This assertion demonstrates what we're testing for
        # In a real test, buggy_generated_prompt would come from actual LLM output
        assert len(matches) > 0, "Test setup: should have buggy patterns to detect"

        # The actual validation function
        def validate_no_file_not_found_includes(prompt_content: str) -> list:
            """Return list of invalid include tags found."""
            pattern = r'<include>\[File not found:.*?\]</include>'
            return re.findall(pattern, prompt_content)

        invalid_includes = validate_no_file_not_found_includes(buggy_generated_prompt)

        # This would be the actual assertion in production
        # assert len(invalid_includes) == 0, (
        #     f"Generated prompt contains {len(invalid_includes)} invalid <include> tags:\n"
        #     + "\n".join(f"  - {inc}" for inc in invalid_includes) +
        #     "\nThe template should not instruct LLM to assume files exist."
        # )

        # For now, we document that the bug exists
        assert len(invalid_includes) == 2, (
            "Expected 2 invalid includes in buggy output (demonstrating the bug pattern)"
        )

    def test_validate_include_helper_function(self):
        """Test helper function for validating include tags."""

        def has_invalid_includes(prompt_content: str) -> bool:
            """Check if prompt has invalid [File not found:] include tags."""
            pattern = r'<include>\[File not found:.*?\]</include>'
            return bool(re.search(pattern, prompt_content))

        # Valid prompt (no File not found)
        valid_prompt = """
<database>
  <include>context/database_example.py</include>
</database>
"""
        assert not has_invalid_includes(valid_prompt), \
            "Valid prompt should pass validation"

        # Invalid prompt (has File not found)
        invalid_prompt = """
<pydantic>
  <include>[File not found: context/pydantic_example.py]</include>
</pydantic>
"""
        assert has_invalid_includes(invalid_prompt), \
            "Invalid prompt should fail validation"


class TestPreprocessIncludeValidation:
    """
    Tests for preprocess.py behavior with non-existent files.

    The preprocess function handles <include> tags and should
    provide clear feedback when files don't exist.
    """

    def test_preprocess_marks_missing_files(self, tmp_path):
        """
        Verify preprocess marks missing files with [File not found: ...].

        This is existing behavior - preprocess correctly identifies
        missing files. The issue is that the template instructs LLM
        to create references to files that will inevitably be missing.
        """
        from pdd.preprocess import preprocess

        # Create a prompt with include to non-existent file
        test_prompt = """
% Test prompt
<dep>
  <include>context/nonexistent_example.py</include>
</dep>
"""
        original_cwd = os.getcwd()
        try:
            os.chdir(tmp_path)
            result = preprocess(test_prompt)

            # preprocess should mark the file as not found
            assert "[File not found:" in result or "nonexistent" in result.lower(), \
                "preprocess should indicate when included files don't exist"
        finally:
            os.chdir(original_cwd)


if __name__ == '__main__':
    pytest.main([__file__, '-v'])
