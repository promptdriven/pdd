import os
import subprocess
import pytest
from unittest.mock import patch, MagicMock
from pathlib import Path
from pdd.ci_drift_heal import commit_and_push, DriftInfo

# --- Step 5 Reproduction Tests (Behavioral) ---

def test_issue_1248_meta_files_untracked():
    """
    Step 5 Reproduction Test: Asserts that .pdd/meta/ files are NOT tracked by git.
    This verifies that 'git rm --cached' was successful.
    """
    result = subprocess.run(
        ["git", "ls-files", ".pdd/meta/"],
        capture_output=True,
        text=True,
        check=True
    )
    tracked_files = [f for f in result.stdout.strip().split('\n') if f]
    assert not tracked_files, f"The following files in .pdd/meta/ are still tracked by git:\n" + "\n".join(tracked_files)

def test_gitignore_no_meta_exceptions():
    """
    Step 5 Reproduction Test: Asserts that .gitignore behaves as if .pdd/meta/ is ignored.
    This verifies that the negation rules were removed from .gitignore.
    We check a file that was previously explicitly negated (e.g. agentic_bug_python.json).
    """
    # Behavioral check: ask git if a previously negated file is ignored.
    # We use a path that was known to be in the negation block.
    negated_path = ".pdd/meta/agentic_bug_python.json"
    
    # We don't need the file to exist for check-ignore to work with --no-index or just normally
    # But to be safe, we'll use a path that we know was in the list.
    
    result = subprocess.run(
        ["git", "check-ignore", negated_path],
        capture_output=True,
        text=True
    )
    # returncode 0 means it IS ignored. 
    # In the buggy state (with !.pdd/meta/agentic_bug_python.json), it returns 1 (not ignored).
    assert result.returncode == 0, f"{negated_path} is not being ignored by git. This suggests negation rules are still present in .gitignore."

# --- Fix and Expansion Item Tests (Behavioral) ---

@patch("pdd.ci_drift_heal.subprocess.run")
@patch("pdd.ci_drift_heal.console")
def test_ci_drift_heal_tolerates_missing_metadata(mock_console, mock_run):
    """
    Scope addition: covers expansion item "Update ci_drift_heal.py to stop mandatory metadata staging verification"
    identified by Step 6.
    
    Verifies that commit_and_push logs a warning but proceeds with the commit
    even if metadata fingerprint files are missing from the staged set.
    """
    # Mock DriftInfo for a module that supposedly finalized metadata
    healed = [DriftInfo(basename="core/cloud", language="python", operation="heal", reason="drift")]
    finalized = [("core/cloud", "python")]
    
    # Mock subprocess.run responses
    def side_effect(args, **kwargs):
        if args[:3] == ["git", "diff", "--cached"]:
            if "--name-only" in args:
                # Return staged files, but MISSING the expected metadata file (.pdd/meta/core_cloud_python.json)
                return MagicMock(returncode=0, stdout="pdd/cloud.py\npdd/prompts/cloud.prompt\n")
            else:
                # git diff --cached --quiet returns 1 if there ARE changes staged
                return MagicMock(returncode=1)
        if args[:2] == ["git", "commit"]:
            return MagicMock(returncode=0, stdout="[main abcd123] chore: ...")
        if args[:2] == ["git", "push"]:
            return MagicMock(returncode=0)
        return MagicMock(returncode=0)

    mock_run.side_effect = side_effect
    
    # Call the function
    # We call commit_and_push and verify it returns True (success) despite missing metadata
    result = commit_and_push(healed, finalized_modules=finalized)
    
    # Assertions
    assert result is True, "commit_and_push should return True even if metadata is missing"
    
    # Verify warning was logged (Requirement 14 in prompt)
    mock_console.print.assert_any_call(
        "[yellow]metadata staging verification failed: missing .pdd/meta/core_cloud_python.json[/yellow]"
    )
    
    # Verify git commit was still called (it did not abort)
    commit_called = any(call.args[0][:2] == ["git", "commit"] for call in mock_run.call_args_list)
    assert commit_called, "git commit should have been called despite missing metadata"

def test_agentic_arch_prompt_loading():
    """
    Scope addition: covers expansion item "Update agentic_arch_step7_generate_LLM.prompt to stop re-introduction of un-ignore rules"
    identified by Step 6.
    
    Verifies that the prompt template can be loaded via the official utility,
    confirming it exists and is accessible. Behavioral check of the template loading logic.
    """
    from pdd.load_prompt_template import load_prompt_template
    
    # Behavioral: call the function that loads the template
    content = load_prompt_template("agentic_arch_step7_generate_LLM")
    
    assert isinstance(content, str)
    assert len(content) > 0, "Prompt content should not be empty"

def test_ci_drift_heal_prompt_loading():
    """
    Verifies that the CI drift heal prompt template can be loaded via the official utility.
    Confirming the prompt file is correctly named and present in the system.
    """
    from pdd.load_prompt_template import load_prompt_template
    
    content = load_prompt_template("ci_drift_heal_python")
    
    assert isinstance(content, str)
    assert len(content) > 0, "Prompt content should not be empty"
