"""
Issue #549 — Per-orchestrator behavioral tests for format string double-escaping.

Root cause: orchestrators call prompt_template.format(**context) to substitute
context values into the prompt template. When a context value contains curly
braces (e.g. JSON output from a prior step), Python's str.format() either
raises KeyError (unescaped) or, when the value was pre-escaped with
.replace("{", "{{"), produces doubled braces {{...}} in the instruction that
the LLM receives.

Fix: replace .format(**context) with iterative str.replace() as used in
template_expander.py:155-156.

This file adds per-orchestrator behavioral tests for:
  - agentic_checkup_orchestrator
  - agentic_test_orchestrator
  - agentic_change_orchestrator
  - agentic_e2e_fix_orchestrator
  - agentic_architecture_orchestrator

The tests FAIL on current code and PASS after the fix.
"""

from __future__ import annotations

from pathlib import Path
from unittest.mock import patch

import pytest


# ===========================================================================
# Section 1: agentic_checkup_orchestrator
# ===========================================================================


@pytest.fixture
def checkup_deps(tmp_path):
    """Patch external dependencies for run_agentic_checkup_orchestrator."""
    worktree = tmp_path / ".pdd" / "worktrees" / "fix-issue-1"
    worktree.mkdir(parents=True, exist_ok=True)

    with patch("pdd.agentic_checkup_orchestrator.run_agentic_task") as mock_run, \
         patch("pdd.agentic_checkup_orchestrator.load_prompt_template") as mock_load, \
         patch("pdd.agentic_checkup_orchestrator.load_workflow_state") as mock_state, \
         patch("pdd.agentic_checkup_orchestrator.save_workflow_state") as mock_save, \
         patch("pdd.agentic_checkup_orchestrator.clear_workflow_state"), \
         patch("pdd.agentic_checkup_orchestrator._setup_worktree") as mock_wt, \
         patch("pdd.agentic_checkup_orchestrator.console"):

        mock_state.return_value = (None, None)
        mock_save.return_value = None
        mock_wt.return_value = (worktree, None)
        # Default: all steps succeed, "All Issues Fixed" exits the fix-verify loop
        mock_run.return_value = (True, "Step output. All Issues Fixed", 0.1, "gpt-4")
        mock_load.return_value = "Prompt for {issue_number}"

        yield mock_run, mock_load


@pytest.fixture
def checkup_args(tmp_path):
    """Default kwargs for run_agentic_checkup_orchestrator."""
    return {
        "issue_url": "https://github.com/owner/repo/issues/1",
        "issue_content": "Bug description",
        "repo_owner": "owner",
        "repo_name": "repo",
        "issue_number": 1,
        "issue_title": "Bug Title",
        "architecture_json": '[]',
        "pddrc_content": "project: test",
        "cwd": tmp_path,
        "verbose": False,
        "quiet": True,
        "use_github_state": False,
    }


def test_checkup_json_step_output_not_double_escaped_in_next_prompt(
    checkup_deps, checkup_args
):
    """
    Issue #549 — checkup: JSON in step 1 output must reach step 2 as single braces.

    The checkup orchestrator escapes context values before .format(**context)
    (line ~572: escaped_output = output.replace("{", "{{").replace("}", "}}")),
    so step 2's instruction will contain {{...}} instead of {...}.

    After fix: iterative str.replace() leaves JSON intact.
    """
    from pdd.agentic_checkup_orchestrator import run_agentic_checkup_orchestrator

    mock_run, mock_load = checkup_deps

    JSON_OUTPUT = '{"error": "Insufficient role", "required": "admin"}'
    captured = {}

    def side_effect(**kwargs):
        label = kwargs.get("label", "")
        instruction = kwargs.get("instruction", "")
        captured[label] = instruction
        if label == "step1":
            return (True, JSON_OUTPUT, 0.1, "gpt-4")
        # All Issues Fixed exits the fix-verify loop cleanly
        return (True, "Step output. All Issues Fixed", 0.1, "gpt-4")

    mock_run.side_effect = side_effect

    def load_side_effect(name):
        if "step2" in name:
            return "Analysis: {step1_output}"
        return "Prompt for {issue_number}"

    mock_load.side_effect = load_side_effect

    run_agentic_checkup_orchestrator(**checkup_args)

    step2_instruction = captured.get("step2", "")
    assert step2_instruction, "run_agentic_task was not called for step2 in checkup"

    # BUG: checkup escapes values, so after .format() the doubled braces appear
    assert "{{" not in step2_instruction, (
        f"checkup step2 prompt has doubled curly braces — Issue #549.\n"
        f"Got: {repr(step2_instruction)}"
    )
    assert JSON_OUTPUT in step2_instruction, (
        f"checkup step2 prompt should contain the original JSON.\n"
        f"Got: {repr(step2_instruction)}"
    )


def test_checkup_does_not_escape_context_values_before_format():
    """
    Issue #549 STRUCTURAL — checkup: the value-escaping pattern
    output.replace("{", "{{").replace("}", "}}") must not exist in source.

    This pattern is the root cause: it pre-escapes JSON in context values,
    which then survive through .format(**context) as doubled braces.
    """
    import pdd.agentic_checkup_orchestrator as mod

    source = Path(mod.__file__).read_text()
    buggy_pattern = '.replace("{", "{{").replace("}", "}}")'

    assert buggy_pattern not in source, (
        f"Found buggy brace-escaping pattern in agentic_checkup_orchestrator.py — "
        "root cause of Issue #549. Remove the .replace calls and switch to "
        "iterative str.replace() for prompt substitution."
    )


def test_checkup_does_not_use_format_with_context_dict():
    """
    Issue #549 STRUCTURAL — checkup: prompt_template.format(**context)
    must not appear in source after the fix.
    """
    import pdd.agentic_checkup_orchestrator as mod

    source = Path(mod.__file__).read_text()

    assert ".format(**context)" not in source, (
        "agentic_checkup_orchestrator.py still uses .format(**context) — "
        "Issue #549. Replace with iterative str.replace()."
    )


# ===========================================================================
# Section 2: agentic_test_orchestrator
# ===========================================================================


@pytest.fixture
def test_orch_deps(tmp_path):
    """Patch external dependencies for run_agentic_test_orchestrator."""
    worktree = tmp_path / ".pdd" / "worktrees" / "fix-issue-1"
    worktree.mkdir(parents=True, exist_ok=True)

    with patch("pdd.agentic_test_orchestrator.run_agentic_task") as mock_run, \
         patch("pdd.agentic_test_orchestrator.load_prompt_template") as mock_load, \
         patch("pdd.agentic_test_orchestrator.load_workflow_state") as mock_state, \
         patch("pdd.agentic_test_orchestrator.save_workflow_state") as mock_save, \
         patch("pdd.agentic_test_orchestrator.clear_workflow_state"), \
         patch("pdd.agentic_test_orchestrator._setup_worktree") as mock_wt, \
         patch("pdd.agentic_test_orchestrator._get_git_root") as mock_git_root, \
         patch("pdd.agentic_test_orchestrator.console"):

        mock_state.return_value = (None, None)
        mock_save.return_value = None
        mock_wt.return_value = (worktree, None)
        mock_git_root.return_value = tmp_path
        mock_run.return_value = (True, "Step output", 0.1, "gpt-4")
        mock_load.return_value = "Prompt for {issue_number}"

        yield mock_run, mock_load


@pytest.fixture
def test_orch_args(tmp_path):
    """Default kwargs for run_agentic_test_orchestrator."""
    return {
        "issue_url": "https://github.com/owner/repo/issues/1",
        "issue_content": "Bug description",
        "repo_owner": "owner",
        "repo_name": "repo",
        "issue_number": 1,
        "issue_author": "user",
        "issue_title": "Bug Title",
        "cwd": tmp_path,
        "verbose": False,
        "quiet": True,
        "use_github_state": False,
    }


def test_test_orch_format_with_context_raises_keyerror_on_unknown_placeholder(
    test_orch_deps, test_orch_args
):
    """
    Issue #549 — test_orchestrator: .format(**context) raises KeyError when the
    prompt template contains a placeholder that is not in context.

    Real prompt templates often include optional or step-specific placeholders
    that may not be populated for every step. With .format(**context), any such
    missing key causes KeyError. With iterative str.replace(), unknown
    placeholders are left intact and no exception is raised.

    After fix: orchestrator completes without KeyError.
    """
    from pdd.agentic_test_orchestrator import run_agentic_test_orchestrator

    mock_run, mock_load = test_orch_deps

    captured = {}

    def side_effect(**kwargs):
        label = kwargs.get("label", "")
        instruction = kwargs.get("instruction", "")
        captured[label] = instruction
        if label == "step6":
            return (True, "FILES_CREATED: tests/test_foo.py", 0.1, "gpt-4")
        return (True, "Step output", 0.1, "gpt-4")

    mock_run.side_effect = side_effect

    def load_side_effect(name):
        if "step2" in name:
            # Template contains a placeholder NOT in context — triggers the bug.
            # str.replace() fixes this by leaving unknown placeholders intact.
            return "Analysis: {step1_output}. Related: {optional_context_key}"
        return "Prompt for {issue_number}"

    mock_load.side_effect = load_side_effect

    # BUG: .format(**context) raises KeyError for {optional_context_key}
    # FIX: iterative str.replace() leaves {optional_context_key} as-is
    try:
        run_agentic_test_orchestrator(**test_orch_args)
    except KeyError as exc:
        pytest.fail(
            f"Issue #549: KeyError raised in test_orchestrator for unknown placeholder.\n"
            f"KeyError key: {exc}\n"
            f"Fix: replace .format(**context) with iterative str.replace() — "
            f"unknown placeholders should remain as-is, not raise KeyError."
        )

    step2_instruction = captured.get("step2", "")
    assert step2_instruction, "run_agentic_task was not called for step2 in test_orch"

    # After fix: the known placeholder is substituted, unknown remains
    assert "{optional_context_key}" in step2_instruction, (
        f"test_orch step2 prompt should preserve unknown placeholder with str.replace().\n"
        f"Got: {repr(step2_instruction)}"
    )


def test_test_orchestrator_does_not_use_format_with_context_dict():
    """
    Issue #549 STRUCTURAL — test_orchestrator: prompt_template.format(**context)
    must not appear in source after the fix.
    """
    import pdd.agentic_test_orchestrator as mod

    source = Path(mod.__file__).read_text()

    assert ".format(**context)" not in source, (
        "agentic_test_orchestrator.py still uses .format(**context) — "
        "Issue #549. Replace with iterative str.replace()."
    )


# ===========================================================================
# Section 3: agentic_change_orchestrator
# ===========================================================================


@pytest.fixture
def change_deps(tmp_path):
    """Patch external dependencies for run_agentic_change_orchestrator."""
    worktree = tmp_path / ".pdd" / "worktrees" / "fix-issue-1"
    worktree.mkdir(parents=True, exist_ok=True)

    with patch("pdd.agentic_change_orchestrator.run_agentic_task") as mock_run, \
         patch("pdd.agentic_change_orchestrator.load_prompt_template") as mock_load, \
         patch("pdd.agentic_change_orchestrator.load_workflow_state") as mock_state, \
         patch("pdd.agentic_change_orchestrator.save_workflow_state") as mock_save, \
         patch("pdd.agentic_change_orchestrator.clear_workflow_state"), \
         patch("pdd.agentic_change_orchestrator._setup_worktree") as mock_wt, \
         patch("pdd.agentic_change_orchestrator.post_step_comment"), \
         patch("pdd.agentic_change_orchestrator.console"):

        mock_state.return_value = (None, None)
        mock_save.return_value = None
        mock_wt.return_value = (worktree, None)
        mock_run.return_value = (True, "Step output", 0.1, "gpt-4")
        mock_load.return_value = "Prompt for {issue_number}"

        yield mock_run, mock_load


@pytest.fixture
def change_args(tmp_path):
    """Default kwargs for run_agentic_change_orchestrator."""
    return {
        "issue_url": "https://github.com/owner/repo/issues/1",
        "issue_content": "Feature description",
        "repo_owner": "owner",
        "repo_name": "repo",
        "issue_number": 1,
        "issue_author": "user",
        "issue_title": "Feature Title",
        "cwd": tmp_path,
        "verbose": False,
        "quiet": True,
        "use_github_state": False,
    }


def test_change_format_with_context_raises_keyerror_on_unknown_placeholder(
    change_deps, change_args
):
    """
    Issue #549 — change_orchestrator: .format(**context) raises KeyError when
    the prompt template contains a placeholder not in context.

    Real prompt templates include placeholders that are populated only in some
    steps (e.g., {files_created}, {direct_edit_candidates}). With .format(**context)
    any missing key raises KeyError. With str.replace(), unknown placeholders
    remain intact.

    After fix: orchestrator completes without KeyError.
    """
    from pdd.agentic_change_orchestrator import run_agentic_change_orchestrator

    mock_run, mock_load = change_deps

    captured = {}

    def side_effect(**kwargs):
        label = kwargs.get("label", "")
        instruction = kwargs.get("instruction", "")
        captured[label] = instruction
        if label == "step9":
            return (True, "FILES_CREATED: src/foo.py", 0.1, "gpt-4")
        return (True, "Step output", 0.1, "gpt-4")

    mock_run.side_effect = side_effect

    def load_side_effect(name):
        if "step2" in name:
            # Template contains a placeholder NOT in context — triggers KeyError with format()
            return "Analysis: {step1_output}. Related: {optional_context_key}"
        return "Prompt for {issue_number}"

    mock_load.side_effect = load_side_effect

    # BUG: .format(**context) raises KeyError for {optional_context_key}
    # FIX: iterative str.replace() leaves {optional_context_key} as-is
    try:
        run_agentic_change_orchestrator(**change_args)
    except KeyError as exc:
        pytest.fail(
            f"Issue #549: KeyError raised in change_orchestrator for unknown placeholder.\n"
            f"KeyError key: {exc}\n"
            f"Fix: replace .format(**context) with iterative str.replace() — "
            f"unknown placeholders should remain as-is, not raise KeyError."
        )

    step2_instruction = captured.get("step2", "")
    assert step2_instruction, "run_agentic_task was not called for step2 in change_orch"

    assert "{optional_context_key}" in step2_instruction, (
        f"change_orch step2 prompt should preserve unknown placeholder with str.replace().\n"
        f"Got: {repr(step2_instruction)}"
    )


def test_change_orchestrator_does_not_use_format_with_context_dict():
    """
    Issue #549 STRUCTURAL — change_orchestrator: prompt_template.format(**context)
    must not appear in source after the fix.
    """
    import pdd.agentic_change_orchestrator as mod

    source = Path(mod.__file__).read_text()

    assert ".format(**context)" not in source, (
        "agentic_change_orchestrator.py still uses .format(**context) — "
        "Issue #549. Replace with iterative str.replace()."
    )


# ===========================================================================
# Section 4: agentic_e2e_fix_orchestrator
# ===========================================================================


@pytest.fixture
def e2e_fix_deps(tmp_path):
    """Patch external dependencies for run_agentic_e2e_fix_orchestrator."""
    with patch("pdd.agentic_e2e_fix_orchestrator.run_agentic_task") as mock_run, \
         patch("pdd.agentic_e2e_fix_orchestrator.load_prompt_template") as mock_load, \
         patch("pdd.agentic_e2e_fix_orchestrator.load_workflow_state") as mock_state, \
         patch("pdd.agentic_e2e_fix_orchestrator.save_workflow_state") as mock_save, \
         patch("pdd.agentic_e2e_fix_orchestrator.clear_workflow_state"), \
         patch("pdd.agentic_e2e_fix_orchestrator._get_state_dir") as mock_state_dir, \
         patch("pdd.agentic_e2e_fix_orchestrator._get_file_hashes") as mock_hashes, \
         patch("pdd.agentic_e2e_fix_orchestrator.console"):

        mock_state.return_value = (None, None)
        mock_save.return_value = None
        mock_state_dir.return_value = tmp_path / ".pdd" / "e2e-fix-state"
        mock_hashes.return_value = {}
        mock_run.return_value = (True, "Step output", 0.1, "gpt-4")
        mock_load.return_value = "Prompt for {issue_number}"

        yield mock_run, mock_load


@pytest.fixture
def e2e_fix_args(tmp_path):
    """Default kwargs for run_agentic_e2e_fix_orchestrator."""
    return {
        "issue_url": "https://github.com/owner/repo/issues/1",
        "issue_content": "Bug description",
        "repo_owner": "owner",
        "repo_name": "repo",
        "issue_number": 1,
        "issue_author": "user",
        "issue_title": "Bug Title",
        "cwd": tmp_path,
        "max_cycles": 1,
        "resume": False,
        "verbose": False,
        "quiet": True,
        "use_github_state": False,
    }


def test_e2e_fix_format_with_context_raises_keyerror_on_unknown_placeholder(
    e2e_fix_deps, e2e_fix_args
):
    """
    Issue #549 — e2e_fix_orchestrator: .format(**context) raises KeyError when
    the prompt template contains a placeholder not in context.

    The e2e_fix_orchestrator rebuilds context fresh each step from a base dict
    and then populates previous step outputs. Real templates include placeholders
    like {dev_units_identified} that are only available from step 5 onwards.
    For earlier steps, .format(**context) raises KeyError. With str.replace(),
    unknown placeholders remain intact.

    After fix: orchestrator completes without KeyError.
    """
    from pdd.agentic_e2e_fix_orchestrator import run_agentic_e2e_fix_orchestrator

    mock_run, mock_load = e2e_fix_deps

    captured = {}

    def side_effect(**kwargs):
        label = kwargs.get("label", "")
        instruction = kwargs.get("instruction", "")
        captured[label] = instruction
        if label == "cycle1_step9":
            return (True, "ALL_TESTS_PASSING", 0.1, "gpt-4")
        return (True, "Step output", 0.1, "gpt-4")

    mock_run.side_effect = side_effect

    def load_side_effect(name):
        if "step2" in name:
            # Template contains a placeholder NOT in step 2 context — triggers KeyError
            return "Analysis: {step1_output}. Related: {optional_context_key}"
        return "Prompt for {issue_number}"

    mock_load.side_effect = load_side_effect

    # BUG: .format(**context) raises KeyError for {optional_context_key}
    # FIX: iterative str.replace() leaves {optional_context_key} as-is
    try:
        run_agentic_e2e_fix_orchestrator(**e2e_fix_args)
    except KeyError as exc:
        pytest.fail(
            f"Issue #549: KeyError raised in e2e_fix_orchestrator for unknown placeholder.\n"
            f"KeyError key: {exc}\n"
            f"Fix: replace .format(**context) with iterative str.replace() — "
            f"unknown placeholders should remain as-is, not raise KeyError."
        )

    step2_instruction = captured.get("cycle1_step2", "")
    assert step2_instruction, (
        "run_agentic_task was not called for cycle1_step2 in e2e_fix_orch"
    )

    assert "{optional_context_key}" in step2_instruction, (
        f"e2e_fix_orch step2 prompt should preserve unknown placeholder with str.replace().\n"
        f"Got: {repr(step2_instruction)}"
    )


def test_e2e_fix_orchestrator_does_not_use_format_with_context_dict():
    """
    Issue #549 STRUCTURAL — e2e_fix_orchestrator: prompt_template.format(**context)
    must not appear in source after the fix.
    """
    import pdd.agentic_e2e_fix_orchestrator as mod

    source = Path(mod.__file__).read_text()

    assert ".format(**context)" not in source, (
        "agentic_e2e_fix_orchestrator.py still uses .format(**context) — "
        "Issue #549. Replace with iterative str.replace()."
    )


# ===========================================================================
# Section 5: agentic_architecture_orchestrator
# ===========================================================================


@pytest.fixture
def arch_deps(tmp_path):
    """Patch external dependencies for run_agentic_architecture_orchestrator."""
    with patch("pdd.agentic_architecture_orchestrator.run_agentic_task") as mock_run, \
         patch("pdd.agentic_architecture_orchestrator.load_prompt_template") as mock_load, \
         patch("pdd.agentic_architecture_orchestrator.load_workflow_state") as mock_state, \
         patch("pdd.agentic_architecture_orchestrator.save_workflow_state") as mock_save, \
         patch("pdd.agentic_architecture_orchestrator.clear_workflow_state"), \
         patch("pdd.agentic_architecture_orchestrator.HAS_MERMAID", False), \
         patch("pdd.agentic_architecture_orchestrator.console"):

        mock_state.return_value = (None, None)
        mock_save.return_value = None
        mock_run.return_value = (True, "Step output. VALIDATION_RESULT: VALID", 0.1, "gpt-4")
        mock_load.return_value = "Prompt for {issue_number}"

        yield mock_run, mock_load


@pytest.fixture
def arch_args(tmp_path):
    """Default kwargs for run_agentic_architecture_orchestrator."""
    return {
        "issue_url": "https://github.com/owner/repo/issues/1",
        "issue_content": "Feature description",
        "repo_owner": "owner",
        "repo_name": "repo",
        "issue_number": 1,
        "issue_author": "user",
        "issue_title": "Architecture Title",
        "cwd": tmp_path,
        "verbose": False,
        "quiet": True,
        "use_github_state": False,
        "skip_prompts": True,
    }


def test_arch_format_with_context_raises_keyerror_on_unknown_placeholder(
    arch_deps, arch_args
):
    """
    Issue #549 — architecture_orchestrator: .format(**context) raises KeyError
    when the prompt template contains a placeholder not in context.

    Architecture prompt templates include placeholders like {pddrc_content} and
    {architecture_json} that are populated at specific steps. For steps where
    these aren't set, .format(**context) raises KeyError. With str.replace(),
    unknown placeholders remain intact.

    After fix: orchestrator completes without KeyError.
    """
    from pdd.agentic_architecture_orchestrator import run_agentic_architecture_orchestrator

    mock_run, mock_load = arch_deps

    captured = {}

    def side_effect(**kwargs):
        label = kwargs.get("label", "")
        instruction = kwargs.get("instruction", "")
        captured[label] = instruction
        if label == "step7":
            arch_path = arch_args["cwd"] / "architecture.json"
            arch_path.write_text('{"modules": []}')
            return (True, "FILES_CREATED: architecture.json", 0.1, "gpt-4")
        return (True, "Step output. VALIDATION_RESULT: VALID", 0.1, "gpt-4")

    mock_run.side_effect = side_effect

    def load_side_effect(name):
        if "step2" in name:
            # Template contains a placeholder NOT in context — triggers KeyError
            return "Analysis: {step1_output}. Related: {optional_context_key}"
        return "Prompt for {issue_number}"

    mock_load.side_effect = load_side_effect

    # BUG: .format(**context) raises KeyError for {optional_context_key}
    # FIX: iterative str.replace() leaves {optional_context_key} as-is
    try:
        run_agentic_architecture_orchestrator(**arch_args)
    except KeyError as exc:
        pytest.fail(
            f"Issue #549: KeyError raised in architecture_orchestrator for unknown placeholder.\n"
            f"KeyError key: {exc}\n"
            f"Fix: replace .format(**context) with iterative str.replace() — "
            f"unknown placeholders should remain as-is, not raise KeyError."
        )

    step2_instruction = captured.get("step2", "")
    assert step2_instruction, (
        "run_agentic_task was not called for step2 in architecture_orch"
    )

    assert "{optional_context_key}" in step2_instruction, (
        f"arch_orch step2 prompt should preserve unknown placeholder with str.replace().\n"
        f"Got: {repr(step2_instruction)}"
    )


def test_architecture_orchestrator_does_not_use_format_with_context_dict():
    """
    Issue #549 STRUCTURAL — architecture_orchestrator: prompt_template.format(**context)
    must not appear in source after the fix.
    """
    import pdd.agentic_architecture_orchestrator as mod

    source = Path(mod.__file__).read_text()

    assert ".format(**context)" not in source, (
        "agentic_architecture_orchestrator.py still uses .format(**context) — "
        "Issue #549. Replace with iterative str.replace()."
    )
