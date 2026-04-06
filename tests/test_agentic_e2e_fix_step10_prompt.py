"""Tests for Step 10 CI validation prompt formatting and interface.

These tests verify that the new Step 10 CI validation prompt can be formatted
with the context variables provided by the orchestrator, and that the
orchestrator and CLI entry point accept the new CI-related parameters.
"""
import inspect
import json
import re
from pathlib import Path
from unittest.mock import patch

import pytest
from click.testing import CliRunner

from pdd.load_prompt_template import load_prompt_template


@pytest.fixture(autouse=True)
def set_pdd_path(monkeypatch):
    """Resolve prompt templates from this worktree, not the parent repo checkout."""
    monkeypatch.setenv("PDD_PATH", str(Path(__file__).resolve().parent.parent))


def _strip_pdd_metadata(template: str) -> str:
    """Strip <pdd-reason> and <pdd-interface> metadata blocks from a prompt template."""
    template = re.sub(r'<pdd-reason>.*?</pdd-reason>', '', template, flags=re.DOTALL)
    template = re.sub(r'<pdd-interface>.*?</pdd-interface>', '', template, flags=re.DOTALL)
    return template


def _find_repo_root() -> Path:
    """Find the repository root by walking up from the test file."""
    candidate = Path(__file__).resolve().parent.parent
    # In cloud CI, the source may be at /workspace or a subdirectory
    for root in [candidate, Path("/workspace"), candidate.parent]:
        if (root / "pyproject.toml").exists():
            return root
    return candidate


def _read_repo_text(relative_path: str) -> str:
    """Read a repository file relative to the worktree root."""
    repo_root = _find_repo_root()
    path = repo_root / relative_path
    if not path.exists():
        pytest.skip(f"Repository file not available in this environment: {relative_path}")
    return path.read_text(encoding="utf-8")


def _get_step10_architecture_entry() -> dict:
    """Load the architecture.json entry for the Step 10 CI prompt."""
    entries = json.loads(_read_repo_text("architecture.json"))
    return next(
        entry
        for entry in entries
        if entry["filename"] == "agentic_e2e_fix_step10_ci_validation_LLM.prompt"
    )


def _get_fix_command_architecture_entry() -> dict:
    """Load the architecture.json entry for the fix command prompt."""
    entries = json.loads(_read_repo_text("architecture.json"))
    return next(
        entry
        for entry in entries
        if entry["filename"] == "commands/fix_python.prompt"
    )


class TestStep10PromptFormatting:
    """Test that Step 10 prompt can be formatted with expected context."""

    @pytest.fixture
    def step10_context(self):
        """Context variables provided for Step 10."""
        return {
            "issue_url": "https://github.com/test/repo/issues/1",
            "repo_owner": "test",
            "repo_name": "repo",
            "issue_number": 1,
            "ci_attempt": 1,
            "ci_max_retries": 3,
            "ci_check_results": "Check 'lint' failed",
            "ci_failure_logs": "E: line 10: unused import 'os'",
            "ci_system": "github_actions"
        }

    def test_step10_prompt_formats_without_error(self, step10_context):
        """Step 10 template should format successfully with provided context."""
        template = load_prompt_template("agentic_e2e_fix_step10_ci_validation_LLM")
        assert template is not None, "Template should load"

        # This should NOT raise KeyError
        formatted = _strip_pdd_metadata(template).format(**step10_context)
        assert "step 10 of 11" in formatted
        assert "CI Failure Information" in formatted
        assert "github_actions" in formatted
        assert "{issue_url}" not in formatted  # Should be substituted


@pytest.mark.private_prompt
def test_generation_prompts_include_ci_examples():
    """The new generation prompts should include the examples they reference.

    Reads _python.prompt files not synced to the public repo.
    """
    orchestrator_prompt = _read_repo_text("pdd/prompts/agentic_e2e_fix_orchestrator_python.prompt")
    ci_validation_prompt = _read_repo_text("pdd/prompts/ci_validation_python.prompt")

    assert "<include>context/agentic_e2e_fix_orchestrator_example.py</include>" in orchestrator_prompt
    assert "<include>context/ci_validation_example.py</include>" in orchestrator_prompt
    assert "<include>context/agentic_common_example.py</include>" in ci_validation_prompt
    assert "<include>context/ci_validation_example.py</include>" in ci_validation_prompt


def test_agentic_common_example_demonstrates_post_pr_comment():
    """The shared example should demonstrate the PR comment helper used by CI validation."""
    example = _read_repo_text("context/agentic_common_example.py")

    assert "post_pr_comment" in example
    assert "def example_post_pr_comment():" in example
    assert "posted = post_pr_comment(" in example


def test_ci_failure_comments_use_shared_pr_helper(tmp_path):
    """CI failure summaries should be posted through the shared PR comment helper."""
    from pdd.ci_validation import post_ci_failure_comment

    with patch("pdd.ci_validation.post_pr_comment", return_value=True) as mock_post:
        posted = post_ci_failure_comment(
            repo_owner="test",
            repo_name="repo",
            pr_number=42,
            failures=["lint failed", "unit tests failed"],
            attempts=3,
            cwd=tmp_path,
        )

    assert posted is True
    kwargs = mock_post.call_args.kwargs
    assert kwargs["repo_owner"] == "test"
    assert kwargs["repo_name"] == "repo"
    assert kwargs["pr_number"] == 42
    assert "CI validation exhausted its retry budget." in kwargs["body"]
    assert "lint failed" in kwargs["body"]


def test_step10_architecture_metadata_matches_prompt_interface():
    """architecture.json should classify the Step 10 prompt as an LLM config template."""
    step10_entry = _get_step10_architecture_entry()

    assert step10_entry["tags"] == ["agentic", "config", "llm", "template", "fix"]
    assert step10_entry["interface"]["type"] == "config"
    assert step10_entry["interface"]["config"]["keys"] == [
        "issue_url",
        "repo_owner",
        "repo_name",
        "issue_number",
        "ci_attempt",
        "ci_max_retries",
        "ci_check_results",
        "ci_failure_logs",
        "ci_system",
    ]


def test_readme_ci_example_enables_validation():
    """The README CI example should actually exercise the validation loop."""
    readme = _read_repo_text("README.md")

    assert "pdd fix --ci-retries 5 https://github.com/myorg/myrepo/issues/42" in readme
    assert "pdd fix --ci-retries 5 --skip-ci https://github.com/myorg/myrepo/issues/42" not in readme


def test_orchestrator_has_ci_parameters():
    """run_agentic_e2e_fix_orchestrator should accept CI-related parameters."""
    from pdd.agentic_e2e_fix_orchestrator import run_agentic_e2e_fix_orchestrator

    sig = inspect.signature(run_agentic_e2e_fix_orchestrator)
    params = sig.parameters
    assert "ci_retries" in params
    assert "skip_ci" in params


def test_cli_entry_point_has_ci_parameters():
    """run_agentic_e2e_fix should accept CI-related parameters."""
    from pdd.agentic_e2e_fix import run_agentic_e2e_fix

    sig = inspect.signature(run_agentic_e2e_fix)
    params = sig.parameters
    assert "ci_retries" in params
    assert "skip_ci" in params


def test_fix_command_help_exposes_ci_flags():
    """The fix CLI help should expose the new CI validation flags."""
    from pdd.commands.fix import fix

    result = CliRunner().invoke(fix, ["--help"])
    assert result.exit_code == 0
    assert "--ci-retries" in result.output
    assert "--skip-ci" in result.output


def test_fix_prompt_dependency_points_to_real_prompt():
    """The fix command prompt metadata should reference the actual fix implementation prompt."""
    prompt = _read_repo_text("pdd/prompts/commands/fix_python.prompt")
    arch_entry = _get_fix_command_architecture_entry()

    assert "<pdd-dependency>fix_main_python.prompt</pdd-dependency>" in prompt
    assert "<pdd-dependency>fix_python.prompt</pdd-dependency>" not in prompt
    assert "fix_main_python.prompt" in arch_entry["dependencies"]
    assert "fix_python.prompt" not in arch_entry["dependencies"]


@pytest.mark.private_prompt
def test_ci_validation_prompt_uses_required_check_buckets():
    """The CI validation prompt should scope polling to merge-blocking checks.

    Reads ci_validation_python.prompt not synced to the public repo.
    """
    prompt = _read_repo_text("pdd/prompts/ci_validation_python.prompt")

    assert "gh pr checks --required --json name,state,bucket,link" in prompt
    assert "Use the `bucket` field" in prompt


def test_agentic_entry_point_passes_ci_parameters(tmp_path):
    """run_agentic_e2e_fix should forward CI options to the orchestrator."""
    from pdd.agentic_e2e_fix import run_agentic_e2e_fix

    issue_data = {
        "title": "Example issue",
        "body": "Bug details",
        "user": {"login": "octocat"},
        "comments_url": "",
    }

    with patch("pdd.agentic_e2e_fix._check_gh_cli", return_value=True), \
         patch("pdd.agentic_e2e_fix._fetch_issue_data", return_value=(issue_data, None)), \
         patch("pdd.agentic_e2e_fix._fetch_issue_comments", return_value=""), \
         patch("pdd.agentic_e2e_fix._find_working_directory", return_value=(tmp_path, None, False)), \
         patch("pdd.agentic_e2e_fix.run_agentic_e2e_fix_orchestrator", return_value=(True, "ok", 0.1, "gpt-4", [])) as mock_orchestrator:
        result = run_agentic_e2e_fix(
            "https://github.com/test/repo/issues/1",
            quiet=True,
            ci_retries=5,
            skip_ci=True,
        )

    assert result[0] is True
    kwargs = mock_orchestrator.call_args.kwargs
    assert kwargs["ci_retries"] == 5
    assert kwargs["skip_ci"] is True


@patch("pdd.agentic_e2e_fix_orchestrator._verify_tests_independently", return_value=(True, "1 passed"))
@patch("pdd.agentic_e2e_fix_orchestrator._extract_test_files", return_value=["tests/test_example.py"])
def test_orchestrator_runs_ci_validation_after_local_success(_mock_extract, _mock_verify, tmp_path):
    """The orchestrator should enter the CI validation stage after Step 9 passes."""
    from pdd.agentic_e2e_fix_orchestrator import run_agentic_e2e_fix_orchestrator

    def task_side_effect(*args, **kwargs):
        label = kwargs.get("label", "")
        if "step9" in label:
            return (True, "Verification complete. ALL_TESTS_PASS", 0.1, "gpt-4")
        return (True, f"Output for {label}", 0.1, "gpt-4")

    with patch("pdd.agentic_e2e_fix_orchestrator.run_agentic_task", side_effect=task_side_effect), \
         patch("pdd.agentic_e2e_fix_orchestrator.load_prompt_template", return_value="Prompt for {issue_number}"), \
         patch("pdd.agentic_e2e_fix_orchestrator.load_workflow_state", return_value=(None, None)), \
         patch("pdd.agentic_e2e_fix_orchestrator.save_workflow_state", return_value=None), \
         patch("pdd.agentic_e2e_fix_orchestrator.clear_workflow_state") as mock_clear, \
         patch("pdd.agentic_e2e_fix_orchestrator._check_e2e_environment", return_value=(True, "")), \
         patch("pdd.agentic_e2e_fix_orchestrator._get_file_hashes", return_value={}), \
         patch("pdd.agentic_e2e_fix_orchestrator._detect_changed_files", return_value=[]), \
         patch("pdd.agentic_e2e_fix_orchestrator._commit_and_push", return_value=(True, "Committed and pushed 1 file(s)")), \
         patch("pdd.agentic_e2e_fix_orchestrator.run_ci_validation_loop", return_value=(True, "Required CI checks passed", 0.3)) as mock_ci, \
         patch("pdd.agentic_e2e_fix_orchestrator.console"), \
         patch("pdd.agentic_e2e_fix_orchestrator.classify_step_output", return_value=None):
        success, message, cost, _model, _files = run_agentic_e2e_fix_orchestrator(
            issue_url="https://github.com/test/repo/issues/1",
            issue_content="Bug description",
            repo_owner="test",
            repo_name="repo",
            issue_number=1,
            issue_author="octocat",
            issue_title="Bug title",
            cwd=tmp_path,
            resume=False,
            quiet=True,
            use_github_state=False,
            ci_retries=4,
        )

    assert success is True
    assert message == "Required CI checks passed"
    assert cost == pytest.approx(1.2)
    assert mock_ci.call_count == 1
    assert mock_ci.call_args.kwargs["max_retries"] == 4
    assert mock_clear.call_count == 2


@patch("pdd.agentic_e2e_fix_orchestrator._verify_tests_independently", return_value=(True, "1 passed"))
@patch("pdd.agentic_e2e_fix_orchestrator._extract_test_files", return_value=["tests/test_example.py"])
def test_orchestrator_skip_ci_bypasses_ci_validation(_mock_extract, _mock_verify, tmp_path):
    """The orchestrator should bypass Step 10 when --skip-ci is enabled."""
    from pdd.agentic_e2e_fix_orchestrator import run_agentic_e2e_fix_orchestrator

    def task_side_effect(*args, **kwargs):
        label = kwargs.get("label", "")
        if "step9" in label:
            return (True, "Verification complete. ALL_TESTS_PASS", 0.1, "gpt-4")
        return (True, f"Output for {label}", 0.1, "gpt-4")

    with patch("pdd.agentic_e2e_fix_orchestrator.run_agentic_task", side_effect=task_side_effect), \
         patch("pdd.agentic_e2e_fix_orchestrator.load_prompt_template", return_value="Prompt for {issue_number}"), \
         patch("pdd.agentic_e2e_fix_orchestrator.load_workflow_state", return_value=(None, None)), \
         patch("pdd.agentic_e2e_fix_orchestrator.save_workflow_state", return_value=None), \
         patch("pdd.agentic_e2e_fix_orchestrator.clear_workflow_state") as mock_clear, \
         patch("pdd.agentic_e2e_fix_orchestrator._check_e2e_environment", return_value=(True, "")), \
         patch("pdd.agentic_e2e_fix_orchestrator._get_file_hashes", return_value={}), \
         patch("pdd.agentic_e2e_fix_orchestrator._detect_changed_files", return_value=[]), \
         patch("pdd.agentic_e2e_fix_orchestrator._commit_and_push", return_value=(True, "Committed and pushed 1 file(s)")), \
         patch("pdd.agentic_e2e_fix_orchestrator.run_ci_validation_loop") as mock_ci, \
         patch("pdd.agentic_e2e_fix_orchestrator.console"), \
         patch("pdd.agentic_e2e_fix_orchestrator.classify_step_output", return_value=None):
        success, message, cost, _model, _files = run_agentic_e2e_fix_orchestrator(
            issue_url="https://github.com/test/repo/issues/1",
            issue_content="Bug description",
            repo_owner="test",
            repo_name="repo",
            issue_number=1,
            issue_author="octocat",
            issue_title="Bug title",
            cwd=tmp_path,
            resume=False,
            quiet=True,
            use_github_state=False,
            skip_ci=True,
        )

    assert success is True
    assert message == "All tests passed after fixes (independently verified)."
    assert cost == pytest.approx(0.9)
    mock_ci.assert_not_called()
    assert mock_clear.call_count == 2
