"""
Regression tests for PR #1489: run_agentic_change_orchestrator should generate
user stories for changed non-LLM ``.prompt`` files.

After a successful agentic ``pdd change``, the orchestrator should:
- call ``generate_user_story`` for each changed non-LLM ``.prompt`` file
- link the story via ``pdd-story-prompts`` metadata
- skip ``*_LLM.prompt`` runtime templates
- skip non-prompt files (``.py``, ``.md``, ``.json``, etc.)
- skip missing/deleted prompt paths gracefully
- treat story-generation failure as a non-blocking warning (Step 13 still runs)
- pass only the changed prompts, not the entire prompt tree

NOTE: ``generate_user_story`` is patched with ``create=True`` throughout because
PR #1489 is not yet merged and the import does not yet exist in
``agentic_change_orchestrator.py``. Tests will fail at assertion time
(``assert_called_once_with`` / ``assert_not_called``) until the feature is
implemented — that is intentional; they serve as failing regression markers.
"""

import pytest
from pathlib import Path
from unittest.mock import MagicMock, patch, call

# Cap per-test runtime — these are pure mock-based tests.
pytestmark = pytest.mark.timeout(30)

from pdd.agentic_change_orchestrator import run_agentic_change_orchestrator


# ---------------------------------------------------------------------------
# Constants
# ---------------------------------------------------------------------------

_ISSUE_URL = "https://github.com/promptdriven/pdd/issues/42"
_ISSUE_NUMBER = 42

# generate_user_story return type:
#   Tuple[bool, str, float, str, str, List[str]]
#   (success, message, cost, model_name, story_path, linked_prompt_refs)
_STORY_SUCCESS = (
    True,
    "Story generated successfully.",
    0.05,
    "gpt-4o",
    "stories/story__issue-42.md",
    ["prompts/story_workflow_python.prompt"],
)

_STORY_FAILURE = (
    False,
    "Story generation failed: LLM returned empty output.",
    0.0,
    "",
    "",
    [],
)


# ---------------------------------------------------------------------------
# Shared fixtures
# ---------------------------------------------------------------------------


@pytest.fixture(autouse=True)
def _suppress_pre_checkup_gate():
    """Keep tests focused on story generation; gate behaviour is tested elsewhere."""
    with patch(
        "pdd.agentic_change_orchestrator.run_pre_checkup_gate",
        return_value=(True, "gate passed", 0.0),
    ):
        yield


@pytest.fixture()
def temp_cwd(tmp_path):
    return tmp_path


@pytest.fixture()
def existing_prompt(tmp_path):
    """Create a real non-LLM ``.prompt`` file; return its absolute path string."""
    p = tmp_path / "prompts" / "story_workflow_python.prompt"
    p.parent.mkdir(parents=True, exist_ok=True)
    p.write_text("% Story workflow prompt content\n")
    return str(p)


@pytest.fixture()
def existing_llm_prompt(tmp_path):
    """Create a ``*_LLM.prompt`` runtime template; return its absolute path string."""
    p = tmp_path / "prompts" / "agentic_change_step9_implement_LLM.prompt"
    p.parent.mkdir(parents=True, exist_ok=True)
    p.write_text("% LLM runtime template\n")
    return str(p)


@pytest.fixture()
def story_mocks(temp_cwd):
    """
    Full orchestrator mock stack — mirrors ``mock_dependencies`` from
    ``test_agentic_change_orchestrator.py`` — plus ``generate_user_story``
    (patched with ``create=True`` for PR #1489).
    """
    with (
        patch("pdd.agentic_change_orchestrator.run_agentic_task") as mock_run,
        patch("pdd.agentic_change_orchestrator.load_prompt_template") as mock_templates,
        patch("pdd.agentic_change_orchestrator.load_workflow_state") as mock_load_state,
        patch("pdd.agentic_change_orchestrator.save_workflow_state"),
        patch("pdd.agentic_change_orchestrator.clear_workflow_state"),
        patch("pdd.agentic_change_orchestrator.subprocess.run") as mock_subprocess,
        patch("pdd.agentic_change_orchestrator.post_step_comment"),
        patch("pdd.agentic_change_orchestrator.console"),
        patch(
            "pdd.agentic_change_orchestrator.preprocess",
            side_effect=lambda prompt, **kw: prompt,
        ),
        patch("pdd.agentic_change_orchestrator._check_existing_pr", return_value=None),
        patch(
            "pdd.agentic_change_orchestrator.generate_user_story",
            create=True,  # attribute does not exist until PR #1489 is merged
            return_value=_STORY_SUCCESS,
        ) as mock_story,
    ):
        mock_run.return_value = (True, "Default output", 0.1, "gpt-4")
        mock_templates.return_value = "Mocked Prompt"
        mock_load_state.return_value = (None, None)
        mock_subprocess.return_value.stdout = str(temp_cwd)
        mock_subprocess.return_value.returncode = 0

        yield {"run": mock_run, "generate_story": mock_story}


# ---------------------------------------------------------------------------
# Helpers
# ---------------------------------------------------------------------------


def _side_effect_for(step9_files: str, pr_url: str = "https://github.com/owner/repo/pull/999"):
    """
    Build a ``run_agentic_task`` side_effect that returns realistic per-step
    outputs.  ``step9_files`` is the comma-separated file list emitted after
    ``FILES_MODIFIED:``.
    """

    def _side_effect(**kwargs):
        label = kwargs.get("label", "")
        if label == "step9":
            return (True, f"Implementation done.\nFILES_MODIFIED: {step9_files}", 0.5, "gpt-4")
        if label == "step10":
            return (True, "ARCHITECTURE_FILES_MODIFIED: architecture.json", 0.1, "gpt-4")
        if label.startswith("step11"):
            return (True, "No Issues Found", 0.1, "gpt-4")
        if label == "step13":
            return (True, f"PR Created: {pr_url}", 0.2, "gpt-4")
        return (True, f"Output for {label}", 0.1, "gpt-4")

    return _side_effect


def _run(cwd):
    """Call the orchestrator with standard test inputs."""
    return run_agentic_change_orchestrator(
        issue_url=_ISSUE_URL,
        issue_content="Add story workflow for Python prompts.",
        repo_owner="promptdriven",
        repo_name="pdd",
        issue_number=_ISSUE_NUMBER,
        issue_author="test-user",
        issue_title="Add story workflow",
        cwd=cwd,
        verbose=False,
    )


# ---------------------------------------------------------------------------
# Test: changed non-LLM prompt → linked user story generated
# ---------------------------------------------------------------------------


def test_changed_non_llm_prompt_calls_generate_user_story(
    story_mocks, temp_cwd, existing_prompt
):
    """
    Scenario 1 — Happy path.

    When step 9 modifies an existing non-LLM ``.prompt`` file,
    ``generate_user_story`` must be called exactly once with that file and the
    issue URL so the story is linked via ``pdd-story-prompts`` metadata.
    """
    story_mocks["run"].side_effect = _side_effect_for(existing_prompt)

    success, msg, _, _, _ = _run(temp_cwd)

    assert success is True, f"Orchestrator returned failure: {msg}"
    story_mocks["generate_story"].assert_called_once_with(
        prompt_files=[existing_prompt],
        issue=_ISSUE_URL,
    )


def test_generate_user_story_receives_issue_url(story_mocks, temp_cwd, existing_prompt):
    """
    The issue URL must be passed as the ``issue`` keyword argument so the story
    body is derived from the issue (the behavioral source of truth), not from
    prompt content (independent TDD oracle requirement from PR #1489).
    """
    story_mocks["run"].side_effect = _side_effect_for(existing_prompt)

    _run(temp_cwd)

    assert story_mocks["generate_story"].called, (
        "generate_user_story was never called — the orchestrator must call it "
        "for changed non-LLM .prompt files (PR #1489 requirement)."
    )
    _, call_kwargs = story_mocks["generate_story"].call_args
    assert call_kwargs.get("issue") == _ISSUE_URL, (
        "generate_user_story must receive the issue URL so the story is "
        "authored from the issue, not from prompt content."
    )


# ---------------------------------------------------------------------------
# Test: LLM runtime template → skipped
# ---------------------------------------------------------------------------


def test_llm_runtime_template_is_skipped(story_mocks, temp_cwd, existing_llm_prompt):
    """
    Scenario 2 — ``*_LLM.prompt`` files are runtime-consumed templates that
    have no language-suffixed sync companion.  The orchestrator must skip them
    and never call ``generate_user_story``.
    """
    story_mocks["run"].side_effect = _side_effect_for(existing_llm_prompt)

    success, msg, _, _, _ = _run(temp_cwd)

    assert success is True, f"Orchestrator returned failure: {msg}"
    story_mocks["generate_story"].assert_not_called()


# ---------------------------------------------------------------------------
# Test: non-prompt files → skipped
# ---------------------------------------------------------------------------


@pytest.mark.parametrize(
    "non_prompt_file",
    [
        "pdd/agentic_change_orchestrator.py",
        "docs/ARCHITECTURE.md",
        "pdd/architecture.json",
        "tests/test_agentic_change_orchestrator.py",
    ],
)
def test_non_prompt_files_are_skipped(story_mocks, temp_cwd, non_prompt_file):
    """
    Scenario 3 — Files without a ``.prompt`` extension (Python, Markdown, JSON,
    etc.) must never trigger ``generate_user_story``.
    """
    story_mocks["run"].side_effect = _side_effect_for(non_prompt_file)

    success, msg, _, _, _ = _run(temp_cwd)

    assert success is True, f"Orchestrator returned failure: {msg}"
    story_mocks["generate_story"].assert_not_called()


# ---------------------------------------------------------------------------
# Test: missing/deleted path → skipped gracefully
# ---------------------------------------------------------------------------


def test_missing_prompt_path_skipped_gracefully(story_mocks, temp_cwd):
    """
    Scenario 4 — If a ``.prompt`` path listed in step 9's output no longer
    exists on disk (e.g. renamed or deleted during the agentic task),
    the orchestrator must skip it without raising and without calling
    ``generate_user_story``.
    """
    # Use an absolute path that is guaranteed not to exist.
    nonexistent = str(temp_cwd / "prompts" / "deleted_workflow.prompt")
    story_mocks["run"].side_effect = _side_effect_for(nonexistent)

    success, msg, _, _, _ = _run(temp_cwd)

    assert success is True, f"Orchestrator returned failure: {msg}"
    story_mocks["generate_story"].assert_not_called()


# ---------------------------------------------------------------------------
# Test: story generation failure is non-blocking
# ---------------------------------------------------------------------------


def test_story_generation_failure_does_not_block_pr_creation(
    story_mocks, temp_cwd, existing_prompt
):
    """
    Scenario 5a — When ``generate_user_story`` returns a failure tuple
    ``(False, ...)`` the orchestrator must still proceed to Step 13 and return
    ``success=True``.  The failure is a warning, not a hard stop.
    """
    story_mocks["generate_story"].return_value = _STORY_FAILURE
    story_mocks["run"].side_effect = _side_effect_for(existing_prompt)

    success, msg, _, _, _ = _run(temp_cwd)

    assert success is True, (
        "Orchestrator must succeed even when story generation returns False.  "
        f"Got: success={success!r}, msg={msg!r}"
    )
    # Step 13 must still run.
    step13_calls = [
        c for c in story_mocks["run"].call_args_list if c.kwargs.get("label") == "step13"
    ]
    assert step13_calls, "Step 13 (PR creation) must run even when story generation fails."


def test_story_generation_exception_does_not_block_pr_creation(
    story_mocks, temp_cwd, existing_prompt
):
    """
    Scenario 5b — When ``generate_user_story`` raises an unexpected exception
    the orchestrator must still proceed to Step 13 and return ``success=True``.
    The exception is treated as a non-fatal warning.
    """
    story_mocks["generate_story"].side_effect = RuntimeError(
        "LLM provider unavailable"
    )
    story_mocks["run"].side_effect = _side_effect_for(existing_prompt)

    success, msg, _, _, _ = _run(temp_cwd)

    assert success is True, (
        "Orchestrator must succeed even when story generation raises.  "
        f"Got: success={success!r}, msg={msg!r}"
    )
    step13_calls = [
        c for c in story_mocks["run"].call_args_list if c.kwargs.get("label") == "step13"
    ]
    assert step13_calls, "Step 13 (PR creation) must run even after a story-generation exception."


# ---------------------------------------------------------------------------
# Test: scoped validation — only changed prompts, not the full tree
# ---------------------------------------------------------------------------


def test_scoped_validation_passes_only_changed_prompt(
    story_mocks, temp_cwd, existing_prompt, tmp_path
):
    """
    Scenario 6 — ``generate_user_story`` must receive only the prompt files
    that were actually changed by the agentic task, not every prompt in the
    repository.  This ensures story validation is scoped to the changed
    artifact rather than the entire prompt tree.
    """
    # Create a second prompt that was NOT changed; it should not be passed.
    bystander = tmp_path / "prompts" / "unrelated_workflow.prompt"
    bystander.parent.mkdir(parents=True, exist_ok=True)
    bystander.write_text("% Unrelated prompt\n")

    # Step 9 only reports the one changed file.
    story_mocks["run"].side_effect = _side_effect_for(existing_prompt)

    _run(temp_cwd)

    # Exactly the one changed prompt — not the bystander — must be passed.
    story_mocks["generate_story"].assert_called_once_with(
        prompt_files=[existing_prompt],
        issue=_ISSUE_URL,
    )
    for c in story_mocks["generate_story"].call_args_list:
        _, ckw = c
        passed_files = ckw.get("prompt_files", [])
        assert str(bystander) not in passed_files, (
            "generate_user_story must not receive unchanged prompt files "
            "(scoped validation requirement from PR #1489)."
        )


# ---------------------------------------------------------------------------
# Test: multiple changed prompts → one story call per prompt
# ---------------------------------------------------------------------------


def test_multiple_changed_prompts_each_generate_a_story(story_mocks, temp_cwd, tmp_path):
    """
    When step 9 modifies two non-LLM ``.prompt`` files, ``generate_user_story``
    must be called once for each file so both prompts get linked stories.
    """
    prompt_a = tmp_path / "prompts" / "workflow_a.prompt"
    prompt_b = tmp_path / "prompts" / "workflow_b.prompt"
    for p in (prompt_a, prompt_b):
        p.parent.mkdir(parents=True, exist_ok=True)
        p.write_text("% Content\n")

    step9_files = f"{prompt_a}, {prompt_b}"
    story_mocks["run"].side_effect = _side_effect_for(step9_files)

    success, msg, _, _, _ = _run(temp_cwd)

    assert success is True, f"Orchestrator returned failure: {msg}"
    assert story_mocks["generate_story"].call_count == 2, (
        f"Expected 2 story-generation calls (one per changed prompt), "
        f"got {story_mocks['generate_story'].call_count}."
    )

    called_files = [
        c.kwargs.get("prompt_files", []) for c in story_mocks["generate_story"].call_args_list
    ]
    assert [str(prompt_a)] in called_files, f"Expected call for {prompt_a}"
    assert [str(prompt_b)] in called_files, f"Expected call for {prompt_b}"


# ---------------------------------------------------------------------------
# Test: mixed changed files — only .prompt files trigger story generation
# ---------------------------------------------------------------------------


def test_mixed_changed_files_only_prompt_triggers_story(
    story_mocks, temp_cwd, existing_prompt
):
    """
    When step 9 modifies both ``.prompt`` files and non-prompt source files,
    only the ``.prompt`` file(s) must trigger ``generate_user_story``.
    """
    # Include a Python module alongside the .prompt file.
    step9_files = f"pdd/agentic_change_orchestrator.py, {existing_prompt}"
    story_mocks["run"].side_effect = _side_effect_for(step9_files)

    success, msg, _, _, _ = _run(temp_cwd)

    assert success is True, f"Orchestrator returned failure: {msg}"
    assert story_mocks["generate_story"].call_count == 1, (
        "generate_user_story must be called exactly once for the single "
        f".prompt file; got {story_mocks['generate_story'].call_count} calls."
    )
    _, ckw = story_mocks["generate_story"].call_args
    assert ckw.get("prompt_files") == [existing_prompt], (
        "Only the .prompt file must be passed to generate_user_story, "
        "not the Python module."
    )
