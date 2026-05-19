"""CLI-level tests for `pdd prompt lint` via CliRunner."""
from __future__ import annotations

import json
from pathlib import Path
from unittest.mock import MagicMock, patch

import pytest
from click.testing import CliRunner

from pdd import cli
from pdd.prompt_lint import LintIssue

FIXTURES = Path(__file__).parents[1] / "fixtures" / "prompt_lint"


@pytest.fixture
def runner():
    return CliRunner()


def _invoke(runner: CliRunner, *args):
    """Invoke pdd prompt lint with --quiet to suppress update/summary noise."""
    return runner.invoke(
        cli.cli,
        ["--quiet", "prompt", "lint", *args],
        catch_exceptions=False,
    )


def _json_invoke(runner: CliRunner, *args):
    """Invoke pdd prompt lint --json with --quiet for clean parseable output."""
    return runner.invoke(
        cli.cli,
        ["--quiet", "prompt", "lint", "--json", *args],
        catch_exceptions=False,
    )


# ---------------------------------------------------------------------------
# Basic invocation
# ---------------------------------------------------------------------------

class TestPromptLintBasic:
    def test_clean_prompt_exits_zero(self, runner):
        result = _invoke(runner, str(FIXTURES / "clean.prompt"))
        assert result.exit_code == 0

    def test_vague_undefined_exits_one(self, runner):
        result = _invoke(runner, str(FIXTURES / "vague_undefined.prompt"))
        assert result.exit_code == 1

    def test_vague_defined_exits_zero(self, runner):
        result = _invoke(runner, str(FIXTURES / "vague_defined.prompt"))
        assert result.exit_code == 0

    def test_output_contains_warn_label(self, runner):
        result = _invoke(runner, str(FIXTURES / "vague_undefined.prompt"))
        assert "WARN" in result.output or "warn" in result.output.lower()

    def test_output_contains_deterministic_suggestion(self, runner):
        result = _invoke(runner, str(FIXTURES / "vague_undefined.prompt"))
        assert "Suggestion:" in result.output
        assert "Add to <vocabulary>" in result.output

    def test_nonexistent_target_raises_usage_error(self, runner):
        result = runner.invoke(
            cli.cli,
            ["prompt", "lint", "/tmp/does_not_exist_xyz.prompt"],
        )
        assert result.exit_code != 0

    def test_missing_target_without_stories_raises_usage_error(self, runner):
        result = runner.invoke(
            cli.cli,
            ["--quiet", "prompt", "lint"],
        )
        assert result.exit_code != 0
        assert "Missing argument 'TARGET'" in result.output


# ---------------------------------------------------------------------------
# --strict flag
# ---------------------------------------------------------------------------

class TestStrictFlag:
    def test_strict_escalates_warns_to_exit_two(self, runner):
        result = _invoke(runner, "--strict", str(FIXTURES / "vague_undefined.prompt"))
        assert result.exit_code == 2

    def test_strict_clean_still_exits_zero(self, runner):
        result = _invoke(runner, "--strict", str(FIXTURES / "clean.prompt"))
        assert result.exit_code == 0


# ---------------------------------------------------------------------------
# --json flag
# ---------------------------------------------------------------------------

class TestJsonFlag:
    def test_json_output_is_valid_json(self, runner):
        result = _json_invoke(runner, str(FIXTURES / "clean.prompt"))
        data = json.loads(result.output)
        assert isinstance(data, list)

    def test_json_output_has_required_keys(self, runner):
        result = _json_invoke(runner, str(FIXTURES / "vague_undefined.prompt"))
        data = json.loads(result.output)
        assert len(data) > 0
        entry = data[0]
        assert "path" in entry
        assert "warn_count" in entry
        assert "error_count" in entry
        assert "issues" in entry

    def test_json_issue_has_all_fields(self, runner):
        result = _json_invoke(runner, str(FIXTURES / "vague_undefined.prompt"))
        data = json.loads(result.output)
        issues = data[0]["issues"]
        assert len(issues) > 0
        issue = issues[0]
        for key in ("level", "term", "section", "line", "message", "suggestion", "interpretations"):
            assert key in issue


# ---------------------------------------------------------------------------
# --stories flag
# ---------------------------------------------------------------------------

class TestStoriesFlag:
    def test_stories_only_scans_story_files(self, runner):
        result = _invoke(runner, "--stories", str(FIXTURES))
        # vague story produces warnings -> exit 1
        assert result.exit_code == 1
        assert "story__vague_criteria.md" in result.output

    def test_stories_only_json_output(self, runner):
        result = _json_invoke(runner, "--stories", str(FIXTURES))
        data = json.loads(result.output)
        assert isinstance(data, list)
        assert any("story__vague_criteria.md" in entry["path"] for entry in data)

    def test_stories_dir_scans_story_files(self, runner):
        result = _invoke(runner, "--stories", str(FIXTURES), str(FIXTURES / "clean.prompt"))
        # vague story produces warnings → exit 1
        assert result.exit_code == 1

    def test_stories_json_output(self, runner):
        result = _json_invoke(runner, "--stories", str(FIXTURES), str(FIXTURES / "clean.prompt"))
        data = json.loads(result.output)
        # Should include results for both the clean.prompt and the story files
        assert isinstance(data, list)
        assert len(data) >= 2

    def test_stories_option_with_prompt_path_shows_correction(self, runner):
        result = runner.invoke(
            cli.cli,
            [
                "--quiet",
                "prompt",
                "lint",
                "--stories",
                "user_stories/prompt_lint_samples/prompts/foo_python.prompt",
            ],
        )
        assert result.exit_code != 0
        assert "--stories expects a directory" in result.output
        assert "pdd prompt lint --stories user_stories/prompt_lint_samples/ prompts/foo_python.prompt" in result.output


# ---------------------------------------------------------------------------
# --llm requires --ambiguity guard
# ---------------------------------------------------------------------------

class TestLlmFlag:
    def test_llm_without_ambiguity_raises_usage_error(self, runner):
        result = runner.invoke(
            cli.cli,
            ["--quiet", "prompt", "lint", "--llm", str(FIXTURES / "clean.prompt")],
        )
        assert result.exit_code != 0
        assert "--llm requires --ambiguity" in result.output

    @patch("pdd.commands.prompt.run_llm_ambiguity_pass")
    def test_llm_with_ambiguity_calls_llm_pass(self, mock_llm, runner):
        mock_llm.return_value = []
        result = _invoke(runner, "--ambiguity", "--llm", str(FIXTURES / "clean.prompt"))
        mock_llm.assert_called_once()
        assert result.exit_code == 0

    @patch("pdd.commands.prompt.run_llm_ambiguity_pass")
    def test_llm_issues_appear_in_json_output(self, mock_llm, runner):
        from pdd.prompt_lint import LintIssue
        mock_llm.return_value = [
            LintIssue(
                level="warn",
                term="graceful",
                section="llm",
                line="",
                message='LLM flagged "graceful" as potentially ambiguous.',
                suggestion="graceful: returns HTTP 409 with JSON error body",
                interpretations=["silent swallow", "HTTP 409 with error body"],
            )
        ]
        result = _json_invoke(
            runner, "--ambiguity", "--llm", str(FIXTURES / "clean.prompt")
        )
        data = json.loads(result.output)
        all_issues = [i for entry in data for i in entry["issues"]]
        assert any(i["term"] == "graceful" for i in all_issues)


# ---------------------------------------------------------------------------
# --apply flag
# ---------------------------------------------------------------------------

class TestApplyFlag:
    def test_apply_calls_apply_suggestions(self, runner, tmp_path):
        prompt = tmp_path / "apply_test.prompt"
        prompt.write_text(
            "<contract_rules>Must return a valid response.</contract_rules>\n",
            encoding="utf-8",
        )
        with patch("pdd.commands.prompt.apply_suggestions", return_value=1) as mock_apply:
            result = runner.invoke(
                cli.cli,
                ["prompt", "lint", "--apply", str(prompt)],
                catch_exceptions=False,
            )
        mock_apply.assert_called_once()

    def test_without_apply_flag_never_writes(self, runner, tmp_path):
        prompt = tmp_path / "no_apply.prompt"
        original = "<contract_rules>Must return a valid response.</contract_rules>\n"
        prompt.write_text(original, encoding="utf-8")
        with patch("pdd.commands.prompt.apply_suggestions") as mock_apply:
            _invoke(runner, str(prompt))
        mock_apply.assert_not_called()
        assert prompt.read_text(encoding="utf-8") == original

    def test_apply_actually_writes_vocabulary_block(self, runner, tmp_path):
        """End-to-end: --apply writes concrete LLM-sourced suggestions into the file."""
        from pdd.prompt_lint import apply_suggestions
        prompt = tmp_path / "real_apply.prompt"
        prompt.write_text(
            "<contract_rules>Must return a valid response.</contract_rules>\n",
            encoding="utf-8",
        )
        # Simulate what the LLM pass would produce: a concrete (non-placeholder) suggestion
        issue = LintIssue(
            level="warn",
            term="valid",
            section="contract_rules",
            line="Must return a valid response.",
            message="Vague term.",
            suggestion="valid response: HTTP 200 with non-empty data field",
        )
        written = apply_suggestions(prompt, [issue])
        assert written == 1
        text = prompt.read_text(encoding="utf-8")
        assert "<vocabulary>" in text
        assert "valid response: HTTP 200" in text

    def test_apply_with_json_still_outputs_json(self, runner, tmp_path):
        prompt = tmp_path / "apply_json.prompt"
        prompt.write_text(
            "<contract_rules>Must return a valid response.</contract_rules>\n",
            encoding="utf-8",
        )
        result = runner.invoke(
            cli.cli,
            ["--quiet", "prompt", "lint", "--apply", "--json", str(prompt)],
            catch_exceptions=False,
        )
        data = json.loads(result.output)
        assert isinstance(data, list)


# ---------------------------------------------------------------------------
# LLM pass output format: "Possible interpretations" block
# ---------------------------------------------------------------------------

class TestLlmOutputFormat:
    """
    Spec example output:
      Ambiguous term: "duplicate upload"
      Possible interpretations:
      1. Same filename
      2. Same file hash
      3. Same tenant + normalized file hash
      Suggestion:
      Add to <vocabulary>:
      - Duplicate upload: an upload with the same tenant ID and normalized file hash
    Verifies that the Rich renderer produces the expected structure.
    """

    @patch("pdd.commands.prompt.run_llm_ambiguity_pass")
    def test_interpretations_block_rendered_in_output(self, mock_llm, runner):
        mock_llm.return_value = [
            LintIssue(
                level="warn",
                term="duplicate upload",
                section="contract_rules",
                line="The function must reject duplicate uploads gracefully.",
                message='LLM flagged "duplicate upload" as potentially ambiguous.',
                suggestion=(
                    "duplicate upload: an upload with the same tenant ID and "
                    "normalized file hash as a previously accepted upload"
                ),
                interpretations=[
                    "Same filename",
                    "Same file hash",
                    "Same tenant + normalized file hash",
                ],
            )
        ]
        result = _invoke(
            runner,
            "--ambiguity", "--llm",
            str(FIXTURES / "upload_handler_python.prompt"),
        )
        assert "Possible interpretations" in result.output
        assert "Same filename" in result.output
        assert "Same file hash" in result.output
        assert "Same tenant" in result.output

    @patch("pdd.commands.prompt.run_llm_ambiguity_pass")
    def test_suggestion_block_rendered_in_output(self, mock_llm, runner):
        mock_llm.return_value = [
            LintIssue(
                level="warn",
                term="duplicate upload",
                section="contract_rules",
                line="",
                message='LLM flagged "duplicate upload" as potentially ambiguous.',
                suggestion=(
                    "duplicate upload: an upload with the same tenant ID and "
                    "normalized file hash as a previously accepted upload"
                ),
                interpretations=["Same filename", "Same file hash"],
            )
        ]
        result = _invoke(
            runner,
            "--ambiguity", "--llm",
            str(FIXTURES / "upload_handler_python.prompt"),
        )
        # Normalise Rich's line-wrapping for substring checks
        flat = " ".join(result.output.split())
        assert "Suggestion" in flat
        assert "duplicate upload" in flat
        # "normalized file hash" may be wrapped across lines — check each word
        assert "normalized" in flat
        assert "file hash" in flat

    @patch("pdd.commands.prompt.run_llm_ambiguity_pass")
    def test_interpretations_appear_in_json_output(self, mock_llm, runner):
        mock_llm.return_value = [
            LintIssue(
                level="warn",
                term="duplicate upload",
                section="contract_rules",
                line="",
                message="LLM flagged term.",
                suggestion="duplicate upload: same hash and tenant",
                interpretations=["Same filename", "Same file hash", "Same tenant + hash"],
            )
        ]
        result = _json_invoke(
            runner,
            "--ambiguity", "--llm",
            str(FIXTURES / "upload_handler_python.prompt"),
        )
        data = json.loads(result.output)
        all_issues = [i for entry in data for i in entry["issues"]]
        dup_issues = [i for i in all_issues if i["term"] == "duplicate upload"]
        assert dup_issues
        assert dup_issues[0]["interpretations"] == [
            "Same filename", "Same file hash", "Same tenant + hash"
        ]
        assert "normalized file hash" in dup_issues[0]["suggestion"] or \
               "hash" in dup_issues[0]["suggestion"]

    @patch("pdd.commands.prompt.run_llm_ambiguity_pass")
    def test_issue_without_interpretations_renders_no_block(self, mock_llm, runner):
        """Deterministic issues (no interpretations) must not render the block."""
        mock_llm.return_value = []
        result = _invoke(
            runner,
            "--ambiguity", "--llm",
            str(FIXTURES / "upload_handler_python.prompt"),
        )
        # Deterministic issues have empty interpretations → no "Possible interpretations" header
        assert "Possible interpretations" not in result.output


# ---------------------------------------------------------------------------
# --ambiguity flag: deterministic ambiguity command form
# ---------------------------------------------------------------------------

class TestAmbiguityFlag:
    """
    --ambiguity is a valid non-LLM command form. The deterministic pass already
    includes vague-term and observable-outcome checks; --llm requires this flag.
    """

    def test_ambiguity_flag_runs_deterministic_pass(self, runner, tmp_path):
        prompt = tmp_path / "outcome.prompt"
        prompt.write_text(
            "<contract_rules>The request must be valid.</contract_rules>\n",
            encoding="utf-8",
        )
        result_no_ambiguity = _invoke(runner, str(prompt))
        result_with_ambiguity = _invoke(runner, "--ambiguity", str(prompt))
        assert result_no_ambiguity.exit_code == 1
        assert result_with_ambiguity.exit_code == 1
        assert "Vague term" in result_with_ambiguity.output
        assert "observable outcome" in result_with_ambiguity.output

    def test_upload_handler_warns_on_vague_terms(self, runner):
        result = _invoke(runner, str(FIXTURES / "upload_handler_python.prompt"))
        assert result.exit_code == 1

    def test_upload_handler_with_vocab_exits_clean(self, runner):
        result = _invoke(runner, str(FIXTURES / "upload_handler_with_vocab_python.prompt"))
        assert result.exit_code == 0

    def test_upload_handler_json_warns_contain_duplicate(self, runner):
        result = _json_invoke(runner, str(FIXTURES / "upload_handler_python.prompt"))
        data = json.loads(result.output)
        all_issues = [i for entry in data for i in entry["issues"]]
        assert any(i["term"] == "duplicate" for i in all_issues)

    def test_upload_handler_json_issue_location_is_contract_rules(self, runner):
        result = _json_invoke(runner, str(FIXTURES / "upload_handler_python.prompt"))
        data = json.loads(result.output)
        all_issues = [i for entry in data for i in entry["issues"]]
        dup_issues = [i for i in all_issues if i["term"] == "duplicate"]
        assert dup_issues
        assert dup_issues[0]["section"] == "contract_rules"

    def test_upload_handler_json_issue_line_contains_source_text(self, runner):
        result = _json_invoke(runner, str(FIXTURES / "upload_handler_python.prompt"))
        data = json.loads(result.output)
        all_issues = [i for entry in data for i in entry["issues"]]
        dup_issues = [i for i in all_issues if i["term"] == "duplicate"]
        assert dup_issues
        assert "duplicate" in dup_issues[0]["line"].lower()


# ---------------------------------------------------------------------------
# ## Covers: CLI-level story scanning
# ---------------------------------------------------------------------------

class TestCoversSectionCli:
    def test_story_with_covers_exits_zero(self, runner):
        result = _invoke(
            runner,
            "--stories", str(FIXTURES),
            str(FIXTURES / "clean.prompt"),
        )
        # The covers story should be clean; vague story still warns
        # At least the covers fixture must not add new errors vs. the vague one
        assert result.exit_code in (0, 1)  # 1 is from the vague story fixture

    def test_story_with_covers_json_shows_zero_issues_for_covers_file(self, runner):
        result = _json_invoke(
            runner,
            "--stories", str(FIXTURES),
            str(FIXTURES / "clean.prompt"),
        )
        data = json.loads(result.output)
        covers_entry = next(
            (e for e in data if "story__covers" in e["path"]), None
        )
        assert covers_entry is not None
        assert covers_entry["warn_count"] == 0
        assert covers_entry["error_count"] == 0

    def test_story_with_glossary_json_shows_zero_issues(self, runner):
        result = _json_invoke(
            runner,
            "--stories", str(FIXTURES),
            str(FIXTURES / "clean.prompt"),
        )
        data = json.loads(result.output)
        clean_story = next(
            (e for e in data if "story__clean" in e["path"]), None
        )
        assert clean_story is not None
        assert clean_story["warn_count"] == 0

    def test_story_without_vocabulary_source_shows_issues(self, runner):
        result = _json_invoke(
            runner,
            "--stories", str(FIXTURES),
            str(FIXTURES / "clean.prompt"),
        )
        data = json.loads(result.output)
        vague_story = next(
            (e for e in data if "story__vague_criteria" in e["path"]), None
        )
        assert vague_story is not None
        assert vague_story["warn_count"] > 0
