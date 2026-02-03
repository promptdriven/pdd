"""
Test Plan for agentic_bug_step10_pr_LLM.prompt

This test file verifies that the Step 10 prompt generates a valid `pdd fix` command
that users can actually run.

Issue #351: pdd bug Step 10 should use agentic fix format

The prompt should use the simpler agentic format:
    pdd fix <github_issue_url>

Instead of the deprecated loop mode format:
    pdd --force fix --loop --max-attempts 5 ...

Test Categories:
1. Unit tests: Verify prompt uses the agentic fix format
2. Unit tests: Verify prompt doesn't reference non-existent log files
"""

import re
from pathlib import Path

import pytest


# --- Constants ---

PROMPT_PATH = Path(__file__).parent.parent / "pdd" / "prompts" / "agentic_bug_step10_pr_LLM.prompt"


# --- Fixtures ---


@pytest.fixture
def step10_prompt_content() -> str:
    """Load the Step 10 prompt content."""
    assert PROMPT_PATH.exists(), f"Prompt file not found: {PROMPT_PATH}"
    return PROMPT_PATH.read_text()


# --- Tests ---


class TestStep10AgenticFixCommandSyntax:
    """
    Test that the Step 10 prompt generates a valid agentic pdd fix command.

    Agentic fix syntax:
        pdd fix <github_issue_url>

    This format automatically detects prompt files, code files, and test files
    from the issue context.
    """

    def test_prompt_uses_agentic_fix_format(
        self, step10_prompt_content: str
    ) -> None:
        """
        Verify the prompt's pdd fix command uses the agentic format.

        The command template should be: pdd fix {issue_url}
        """
        # Look for the agentic pdd fix command template in the prompt
        pdd_fix_pattern = r'pdd\s+fix\s+\{issue_url\}'
        matches = re.findall(pdd_fix_pattern, step10_prompt_content, re.MULTILINE)

        assert matches, (
            "Step 10 prompt should contain 'pdd fix {issue_url}' command template"
        )

    def test_prompt_does_not_use_deprecated_loop_format(
        self, step10_prompt_content: str
    ) -> None:
        """
        Verify the prompt does NOT use the deprecated --loop format.

        The old format 'pdd fix --loop ...' is deprecated and should not appear.
        """
        pdd_fix_loop_pattern = r'pdd\s+.*?fix\s+--loop'
        matches = re.findall(pdd_fix_loop_pattern, step10_prompt_content, re.MULTILINE)

        assert not matches, (
            f"Step 10 prompt should NOT contain deprecated '--loop' format. "
            f"Found: {matches}"
        )

    def test_prompt_does_not_instruct_using_error_log_path(
        self, step10_prompt_content: str
    ) -> None:
        """
        Verify the prompt does NOT instruct using an error log file path.

        The prompt should not say things like:
        - "Use error log path: fix-issue-{issue_number}.log"
        - "error log path: `fix-issue-{issue_number}.log` for the fix command output"
        """
        content_lower = step10_prompt_content.lower()

        # Check for problematic instructions
        # Be specific: look for an error log path that uses a fix-issue-*.log filename,
        # rather than any occurrence of "error log", ".log", and "fix command".
        error_log_fix_issue_pattern = re.compile(
            r"error log(?: path)?:?\s+`?fix-issue-[^`\s]+\.log`?",
            re.IGNORECASE,
        )
        has_error_log_instruction = any([
            "error log path" in content_lower and "fix-issue-" in content_lower,
            bool(error_log_fix_issue_pattern.search(step10_prompt_content)),
        ])

        assert not has_error_log_instruction, (
            "Step 10 prompt instructs using an error log file path, but loop mode "
            "doesn't use ERROR_FILE parameter. The log file doesn't exist and will "
            "cause the command to fail."
        )


class TestStep10NoLogFileReferences:
    """
    Test that the generated command does not reference non-existent log files.
    """

    def test_command_does_not_reference_log_file(
        self, step10_prompt_content: str
    ) -> None:
        """
        Verify the pdd fix command template does not reference log files.

        The agentic format 'pdd fix {issue_url}' should not include any
        .log file references in the command.
        """
        # Find lines with pdd fix commands
        lines = step10_prompt_content.split('\n')
        pdd_fix_lines = [
            line for line in lines
            if 'pdd' in line and 'fix' in line
        ]

        for line in pdd_fix_lines:
            assert 'fix-issue-' not in line or '.log' not in line, (
                f"Step 10 command should not reference log files. Found: {line}"
            )


class TestStep10ExampleCommandValidity:
    """
    Test that the example command in the prompt is actually runnable.

    The command should use the agentic format and be valid.
    """

    def test_prompt_example_follows_agentic_syntax(
        self, step10_prompt_content: str
    ) -> None:
        """
        Verify any example pdd fix command follows agentic syntax.

        Agentic syntax:
            pdd fix {issue_url}

        Should be simple and not require manual file path arguments.
        """
        # Extract lines that look like pdd fix commands in bash blocks
        lines = step10_prompt_content.split('\n')
        pdd_fix_lines = [
            line for line in lines
            if 'pdd' in line and 'fix' in line and not line.strip().startswith('#')
        ]

        # There should be at least one pdd fix command
        assert pdd_fix_lines, (
            "Step 10 prompt should contain at least one 'pdd fix' command example"
        )

        # Check that commands use the agentic format (simple issue_url argument)
        has_agentic_format = any(
            '{issue_url}' in line for line in pdd_fix_lines
        )
        assert has_agentic_format, (
            f"Step 10 prompt should use agentic format 'pdd fix {{issue_url}}'. "
            f"Found commands: {pdd_fix_lines}"
        )
