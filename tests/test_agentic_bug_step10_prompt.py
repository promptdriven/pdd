"""
Test Plan for agentic_bug_step10_pr_LLM.prompt

This test file verifies that the Step 10 prompt generates a valid `pdd fix` command
that users can actually run without encountering file-not-found errors.

Issue #350: pdd bug Step 10 generates pdd fix command referencing non-existent log file

The bug: When Step 10 generates the `pdd fix` command, it includes `fix-issue-{issue_number}.log`
as the ERROR_FILE argument. However:
1. This file doesn't exist and was never created during the workflow
2. Loop mode (`--loop` flag) doesn't use ERROR_FILE parameter - it treats all args after
   code_file as test files
3. The command fails when users try to run it

These tests FAIL on the current buggy prompt and PASS once the fix is applied.

Test Categories:
1. Unit tests: Verify prompt doesn't reference non-existent log file
2. Unit tests: Verify loop mode command syntax is correct
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


class TestStep10LoopModeCommandSyntax:
    """
    Test that the Step 10 prompt generates a valid loop mode pdd fix command.

    Loop mode syntax:
        pdd fix --loop [OPTIONS] PROMPT_FILE CODE_FILE TEST_FILE [TEST_FILE...]

    Loop mode does NOT accept ERROR_FILE as the last argument.
    Loop mode discovers errors by running tests iteratively.
    """

    def test_prompt_does_not_include_log_file_in_command_template(
        self, step10_prompt_content: str
    ) -> None:
        """
        Verify the prompt's pdd fix command template does NOT reference a log file.

        The command template should not include `fix-issue-{issue_number}.log` or
        `fix-issue-{{issue_number}}.log` as an argument.
        """
        # Look for the pdd fix command template in the prompt
        # It should be in a bash code block
        pdd_fix_pattern = r'pdd\s+.*?fix.*?--loop.*'
        matches = re.findall(pdd_fix_pattern, step10_prompt_content, re.MULTILINE)

        assert matches, (
            "Step 10 prompt should contain a 'pdd fix --loop' command template"
        )

        # Check that none of the matches include a log file reference
        for match in matches:
            assert "fix-issue-" not in match or ".log" not in match, (
                f"Step 10 prompt's pdd fix command includes non-existent log file. "
                f"Loop mode doesn't use ERROR_FILE parameter. "
                f"Found: {match}"
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


class TestStep10CommandArgumentOrder:
    """
    Test that the generated command follows proper argument order for loop mode.

    Correct order for loop mode:
        pdd [GLOBAL_OPTIONS] fix --loop [FIX_OPTIONS] PROMPT_FILE CODE_FILE TEST_FILE [TEST_FILE...]

    The ERROR_FILE argument only applies to non-loop mode:
        pdd fix PROMPT_FILE CODE_FILE TEST_FILE [TEST_FILE...] ERROR_FILE
    """

    def test_command_ends_with_test_file_not_log_file(
        self, step10_prompt_content: str
    ) -> None:
        """
        Verify the pdd fix command template ends with TEST_FILE, not a .log file.

        In loop mode, the last positional argument should be the test file path
        (e.g., {{test_file_path}}), NOT a log file.
        """
        # Find the pdd fix command template
        # Look for the command that contains --loop and ends with arguments
        pdd_fix_pattern = r'pdd\s+.*?fix\s+--loop.*?(\{\{[^}]+\}\}|\S+)(?=\s*$|\s*\n)'
        matches = re.findall(pdd_fix_pattern, step10_prompt_content, re.MULTILINE)

        assert matches, (
            "Step 10 prompt should contain a complete 'pdd fix --loop' command template"
        )

        # Check the last argument in the command
        for match in matches:
            last_arg = match.strip()
            assert not last_arg.endswith('.log'), (
                f"Step 10 command template ends with a .log file, but loop mode "
                f"expects test files as the last arguments. Found last arg: {last_arg}"
            )
            assert ".log" not in last_arg, (
                f"Step 10 command template includes .log file reference in arguments. "
                f"Loop mode doesn't use ERROR_FILE parameter. Found: {last_arg}"
            )


class TestStep10ExampleCommandValidity:
    """
    Test that the example command in the prompt is actually runnable.

    The command should be valid and not reference files that don't exist.
    """

    def test_prompt_example_follows_loop_mode_syntax(
        self, step10_prompt_content: str
    ) -> None:
        """
        Verify any example pdd fix command follows loop mode syntax.

        Loop mode syntax:
            pdd fix --loop [OPTIONS] PROMPT_FILE CODE_FILE TEST_FILE

        Should NOT have ERROR_FILE at the end when --loop is present.
        """
        # Extract lines that look like pdd fix commands
        lines = step10_prompt_content.split('\n')
        pdd_fix_lines = [
            line for line in lines
            if 'pdd' in line and 'fix' in line and '--loop' in line
        ]

        for line in pdd_fix_lines:
            # If it's a loop mode command, it should not end with a .log file
            if '--loop' in line:
                # Extract the last word/token that looks like a file
                tokens = line.strip().split()
                if tokens:
                    # Find positional args (not starting with --)
                    positional_args = [
                        t for t in tokens
                        if not t.startswith('--') and not t.startswith('-')
                        and t != 'pdd' and t != 'fix'
                    ]
                    if positional_args:
                        last_positional = positional_args[-1]
                        assert not last_positional.endswith('.log'), (
                            f"Loop mode command should not end with .log file. "
                            f"Found in line: {line}"
                        )
