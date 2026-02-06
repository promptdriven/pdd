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


class TestStep10PromptFileStagingInstructions:
    """
    Test that the Step 10 prompt correctly instructs staging all files from files_to_stage.

    Issue #429: The Step 10 prompt previously instructed to "Stage ONLY the test file(s)
    created in Steps 7 and 9", which caused prompt files from Step 5.5 to be excluded
    from PRs even though the orchestrator correctly included them in files_to_stage.

    This test verifies that the prompt now instructs staging ALL files from files_to_stage,
    including prompt files from Step 5.5.
    """

    def test_prompt_instructs_staging_files_from_files_to_stage_variable(
        self, step10_prompt_content: str
    ) -> None:
        """
        Verify the prompt instructs staging files from the files_to_stage variable.

        The prompt should say "Stage ONLY the files listed in `files_to_stage`"
        rather than "Stage ONLY the test file(s) created in Steps 7 and 9".

        This is the core fix for issue #429.
        """
        # The prompt should reference the files_to_stage variable in the staging instruction
        files_to_stage_pattern = r'Stage ONLY the files listed in\s+`files_to_stage`'
        matches = re.findall(files_to_stage_pattern, step10_prompt_content, re.IGNORECASE)

        assert matches, (
            "Step 10 prompt should instruct 'Stage ONLY the files listed in `files_to_stage`' "
            "to include prompt files from Step 5.5, not just test files from Steps 7 and 9. "
            "This is the root cause of issue #429."
        )

    def test_prompt_does_not_restrict_staging_to_only_test_files(
        self, step10_prompt_content: str
    ) -> None:
        """
        Verify the prompt does NOT say "Stage ONLY the test file(s)".

        The old buggy instruction was:
            "CRITICAL: Stage ONLY the test file(s) created in Steps 7 and 9"

        This excluded prompt files from Step 5.5, causing issue #429.
        The prompt should no longer have this restrictive language.
        """
        # Look for the old buggy instruction that restricted staging to only test files
        buggy_instruction_pattern = r'Stage ONLY the test file\(s\) created in Steps 7 and 9'
        matches = re.findall(buggy_instruction_pattern, step10_prompt_content, re.IGNORECASE)

        assert not matches, (
            f"Step 10 prompt should NOT restrict staging to 'ONLY the test file(s) created "
            f"in Steps 7 and 9'. This instruction caused prompt files from Step 5.5 to be "
            f"excluded from PRs (issue #429). Found: {matches}"
        )

    def test_prompt_mentions_prompt_files_from_step5_5(
        self, step10_prompt_content: str
    ) -> None:
        """
        Verify the prompt mentions prompt files from Step 5.5 in staging instructions.

        The prompt should explicitly mention that files to stage may include
        prompt files from Step 5.5, not just test files from Steps 7 and 9.
        """
        # Look for mention of Step 5.5 or prompt files in the staging section
        content_lower = step10_prompt_content.lower()

        # The prompt should mention Step 5.5 in context of files to stage
        has_step5_5_mention = 'step 5.5' in content_lower or 'step5.5' in content_lower
        has_prompt_files_mention = 'prompt files' in content_lower or 'prompt file' in content_lower

        assert has_step5_5_mention or has_prompt_files_mention, (
            "Step 10 prompt should mention that files to stage may include prompt files "
            "from Step 5.5, not just test files. This ensures LLM understands to include "
            "prompt files in the PR."
        )


class TestStep10PRTemplateIncludesPromptFiles:
    """
    Test that the PR template acknowledges prompt files from Step 5.5.

    Issue #429: The PR template should include sections for prompt files
    so they are properly documented in the generated PR.
    """

    def test_pr_template_has_prompt_files_section(
        self, step10_prompt_content: str
    ) -> None:
        """
        Verify the PR body template includes a section for prompt files.

        The template should have a "## Prompt Files" section to document
        prompt files from Step 5.5 that are included in the PR.
        """
        # Look for a prompt files section in the PR template
        prompt_files_section_pattern = r'##\s+Prompt Files'
        matches = re.findall(prompt_files_section_pattern, step10_prompt_content, re.IGNORECASE)

        assert matches, (
            "Step 10 PR template should include a '## Prompt Files' section "
            "to document prompt files from Step 5.5 that are included in the PR."
        )

    def test_pr_template_mentions_prompt_fixes_in_contents(
        self, step10_prompt_content: str
    ) -> None:
        """
        Verify the PR template mentions prompt file fixes in the "What This PR Contains" section.

        The template should acknowledge that the PR may contain prompt file fixes
        from Step 5.5, not just test files.
        """
        # Look for the "What This PR Contains" section
        content_lines = step10_prompt_content.split('\n')
        in_pr_contains_section = False
        found_prompt_file_mention = False

        for line in content_lines:
            if '## What This PR Contains' in line:
                in_pr_contains_section = True
            elif in_pr_contains_section and line.startswith('##'):
                # We've moved to a new section
                break
            elif in_pr_contains_section and 'prompt' in line.lower():
                found_prompt_file_mention = True
                break

        assert found_prompt_file_mention, (
            "Step 10 PR template's 'What This PR Contains' section should mention "
            "prompt file fixes from Step 5.5, not just test files."
        )


class TestStep10CommentTemplateIncludesPromptFiles:
    """
    Test that the GitHub issue comment template acknowledges prompt files.

    Issue #429: The comment template should mention prompt files in the
    "What's Included" section so they are properly documented.
    """

    def test_comment_template_mentions_prompt_files_in_whats_included(
        self, step10_prompt_content: str
    ) -> None:
        """
        Verify the comment template includes prompt files in "What's Included" section.

        The template should list prompt files alongside test files in the
        summary comment posted to the GitHub issue.
        """
        # Look for the "What's Included" section in the comment template
        content_lines = step10_prompt_content.split('\n')
        in_whats_included_section = False
        found_prompt_file_mention = False

        for line in content_lines:
            if "What's Included" in line or "### What's Included" in line:
                in_whats_included_section = True
            elif in_whats_included_section and line.startswith('###'):
                # We've moved to a new section
                break
            elif in_whats_included_section and 'prompt' in line.lower():
                found_prompt_file_mention = True
                break

        assert found_prompt_file_mention, (
            "Step 10 comment template's 'What's Included' section should mention "
            "prompt files from Step 5.5 alongside test files."
        )
