"""CLI-level tests for `pdd contracts check` via CliRunner."""
from __future__ import annotations

import json
from pathlib import Path
from unittest.mock import patch

import pytest
from click.testing import CliRunner

from pdd import cli
from pdd.contract_check import ContractIssue

FIXTURES = Path(__file__).parents[1] / "fixtures" / "contract_check"


@pytest.fixture
def runner():
    return CliRunner()


def _invoke(runner: CliRunner, *args):
    """Invoke pdd contracts check with --quiet to suppress update/summary noise."""
    return runner.invoke(
        cli.cli,
        ["--quiet", "contracts", "check", *args],
        catch_exceptions=False,
    )


def _json_invoke(runner: CliRunner, *args):
    """Invoke pdd contracts check --json with --quiet for parseable output."""
    return runner.invoke(
        cli.cli,
        ["--quiet", "contracts", "check", "--json", *args],
        catch_exceptions=False,
    )


# ---------------------------------------------------------------------------
# TestContractsCheckBasic
# ---------------------------------------------------------------------------

class TestContractsCheckBasic:
    def test_valid_prompt_exits_zero(self, runner):
        result = _invoke(runner, str(FIXTURES / "valid_contract_python.prompt"))
        assert result.exit_code == 0

    def test_duplicate_ids_exits_nonzero(self, runner):
        result = _invoke(runner, str(FIXTURES / "duplicate_ids_python.prompt"))
        assert result.exit_code != 0

    def test_vague_no_vocab_exits_one(self, runner):
        result = _invoke(runner, str(FIXTURES / "vague_no_vocab_python.prompt"))
        assert result.exit_code == 1

    def test_legacy_prompt_exits_zero(self, runner):
        result = _invoke(runner, str(FIXTURES / "legacy_no_sections_python.prompt"))
        assert result.exit_code == 0

    def test_output_contains_error_label_for_duplicate(self, runner):
        result = _invoke(runner, str(FIXTURES / "duplicate_ids_python.prompt"))
        assert "ERROR" in result.output or "error" in result.output.lower()

    def test_output_contains_code_label(self, runner):
        result = _invoke(runner, str(FIXTURES / "duplicate_ids_python.prompt"))
        assert "DUPLICATE_ID" in result.output

    def test_output_contains_rule_id(self, runner):
        result = _invoke(runner, str(FIXTURES / "duplicate_ids_python.prompt"))
        assert "R1" in result.output

    def test_nonexistent_target_raises_error(self, runner):
        result = runner.invoke(
            cli.cli,
            ["contracts", "check", "/tmp/does_not_exist_xyz.prompt"],
        )
        assert result.exit_code != 0

    def test_clean_output_shows_checkmark(self, runner):
        result = _invoke(runner, str(FIXTURES / "valid_contract_python.prompt"))
        assert "clean" in result.output.lower() or result.exit_code == 0


# ---------------------------------------------------------------------------
# TestJsonOutput
# ---------------------------------------------------------------------------

class TestJsonOutput:
    def test_json_is_valid(self, runner):
        result = _json_invoke(runner, str(FIXTURES / "valid_contract_python.prompt"))
        data = json.loads(result.output)
        assert isinstance(data, list)

    def test_json_has_required_keys(self, runner):
        result = _json_invoke(runner, str(FIXTURES / "vague_no_vocab_python.prompt"))
        data = json.loads(result.output)
        assert len(data) > 0
        entry = data[0]
        for key in ("path", "warn_count", "error_count", "issues"):
            assert key in entry

    def test_json_issue_has_all_fields(self, runner):
        result = _json_invoke(runner, str(FIXTURES / "vague_no_vocab_python.prompt"))
        data = json.loads(result.output)
        issues = data[0]["issues"]
        assert len(issues) > 0
        issue = issues[0]
        for key in ("level", "code", "rule_id", "section", "line",
                    "message", "term", "suggestion", "interpretations"):
            assert key in issue

    def test_json_clean_prompt_has_zero_counts(self, runner):
        result = _json_invoke(runner, str(FIXTURES / "valid_contract_python.prompt"))
        data = json.loads(result.output)
        assert data[0]["warn_count"] == 0
        assert data[0]["error_count"] == 0
        assert data[0]["issues"] == []

    def test_json_duplicate_id_issue_code(self, runner):
        result = _json_invoke(runner, str(FIXTURES / "duplicate_ids_python.prompt"))
        data = json.loads(result.output)
        all_issues = [i for entry in data for i in entry["issues"]]
        assert any(i["code"] == "DUPLICATE_ID" for i in all_issues)

    def test_json_vague_term_code(self, runner):
        result = _json_invoke(runner, str(FIXTURES / "vague_no_vocab_python.prompt"))
        data = json.loads(result.output)
        all_issues = [i for entry in data for i in entry["issues"]]
        assert any(i["code"] == "VAGUE_TERM" for i in all_issues)

    def test_json_issue_has_source_line(self, runner):
        result = _json_invoke(runner, str(FIXTURES / "missing_modal_python.prompt"))
        data = json.loads(result.output)
        all_issues = [i for entry in data for i in entry["issues"]]
        modal_issues = [i for i in all_issues if i["code"] == "MISSING_MODAL"]
        assert modal_issues
        assert modal_issues[0]["line"] != ""


# ---------------------------------------------------------------------------
# TestStrictFlag
# ---------------------------------------------------------------------------

class TestStrictFlag:
    def test_strict_escalates_warns_to_exit_two(self, runner):
        result = _invoke(runner, "--strict",
                         str(FIXTURES / "vague_no_vocab_python.prompt"))
        assert result.exit_code == 2

    def test_strict_clean_prompt_exits_zero(self, runner):
        result = _invoke(runner, "--strict",
                         str(FIXTURES / "valid_contract_python.prompt"))
        assert result.exit_code == 0

    def test_strict_json_shows_errors_not_warns(self, runner):
        result = _json_invoke(runner, "--strict",
                              str(FIXTURES / "vague_no_vocab_python.prompt"))
        data = json.loads(result.output)
        all_issues = [i for entry in data for i in entry["issues"]]
        assert all(i["level"] == "error" for i in all_issues)


# ---------------------------------------------------------------------------
# TestDirectoryScan
# ---------------------------------------------------------------------------

class TestDirectoryScan:
    def test_directory_scan_produces_multiple_results(self, runner):
        result = _json_invoke(runner, str(FIXTURES))
        data = json.loads(result.output)
        assert len(data) >= 5  # at least several fixture files

    def test_directory_scan_includes_valid_prompt(self, runner):
        result = _json_invoke(runner, str(FIXTURES))
        data = json.loads(result.output)
        names = [Path(e["path"]).name for e in data]
        assert "valid_contract_python.prompt" in names

    def test_directory_scan_exit_code_nonzero_when_issues_present(self, runner):
        result = _invoke(runner, str(FIXTURES))
        assert result.exit_code != 0


# ---------------------------------------------------------------------------
# TestStoriesFlag
# ---------------------------------------------------------------------------

class TestStoriesFlag:
    def test_stories_flag_scans_story_files(self, runner):
        result = _json_invoke(
            runner,
            "--stories", str(FIXTURES),
            str(FIXTURES / "valid_contract_python.prompt"),
        )
        data = json.loads(result.output)
        paths = [Path(e["path"]).name for e in data]
        assert any("story__" in name for name in paths)

    def test_valid_story_has_zero_issues(self, runner):
        result = _json_invoke(
            runner,
            "--stories", str(FIXTURES),
            str(FIXTURES / "valid_contract_python.prompt"),
        )
        data = json.loads(result.output)
        valid_story = next(
            (e for e in data if "story__covers_rule_ids" in e["path"]), None
        )
        assert valid_story is not None
        assert valid_story["warn_count"] == 0

    def test_invalid_story_has_issues(self, runner):
        result = _json_invoke(
            runner,
            "--stories", str(FIXTURES),
            str(FIXTURES / "valid_contract_python.prompt"),
        )
        data = json.loads(result.output)
        invalid_story = next(
            (e for e in data if "story__unknown_rule_ids" in e["path"]), None
        )
        assert invalid_story is not None
        assert invalid_story["warn_count"] >= 1


# ---------------------------------------------------------------------------
# TestLlmAmbiguityFlag
# ---------------------------------------------------------------------------

class TestLlmAmbiguityFlag:
    @patch("pdd.commands.contracts.run_llm_ambiguity_pass")
    def test_llm_ambiguity_calls_llm_pass(self, mock_llm, runner):
        mock_llm.return_value = []
        result = _invoke(
            runner, "--llm-ambiguity",
            str(FIXTURES / "vague_no_vocab_python.prompt"),
        )
        mock_llm.assert_called_once()

    @patch("pdd.commands.contracts.run_llm_ambiguity_pass")
    def test_llm_issues_appear_in_output(self, mock_llm, runner):
        mock_llm.return_value = [
            ContractIssue(
                level="warn",
                code="LLM_AMBIGUITY",
                rule_id="",
                section="llm",
                line="",
                message='LLM flagged "duplicate" as potentially ambiguous.',
                suggestion="duplicate upload: same SHA-256 hash and tenant_id",
                interpretations=["Same filename", "Same hash", "Same tenant + hash"],
            )
        ]
        result = _invoke(
            runner, "--llm-ambiguity",
            str(FIXTURES / "vague_no_vocab_python.prompt"),
        )
        assert "LLM_AMBIGUITY" in result.output or "LLM" in result.output

    @patch("pdd.commands.contracts.run_llm_ambiguity_pass")
    def test_llm_interpretations_rendered(self, mock_llm, runner):
        mock_llm.return_value = [
            ContractIssue(
                level="warn",
                code="LLM_AMBIGUITY",
                rule_id="",
                section="llm",
                line="",
                message='LLM flagged "duplicate" as potentially ambiguous.',
                suggestion="duplicate upload: same hash and tenant",
                interpretations=["Same filename", "Same file hash", "Same tenant + hash"],
            )
        ]
        result = _invoke(
            runner, "--llm-ambiguity",
            str(FIXTURES / "vague_no_vocab_python.prompt"),
        )
        assert "Possible interpretations" in result.output
        assert "Same filename" in result.output

    @patch("pdd.commands.contracts.run_llm_ambiguity_pass")
    def test_llm_issues_appear_in_json(self, mock_llm, runner):
        mock_llm.return_value = [
            ContractIssue(
                level="warn",
                code="LLM_AMBIGUITY",
                rule_id="",
                section="llm",
                line="",
                message="LLM flagged term.",
                suggestion="duplicate: same hash",
                interpretations=["Same filename", "Same hash"],
            )
        ]
        result = _json_invoke(
            runner, "--llm-ambiguity",
            str(FIXTURES / "vague_no_vocab_python.prompt"),
        )
        data = json.loads(result.output)
        all_issues = [i for entry in data for i in entry["issues"]]
        assert any(i["code"] == "LLM_AMBIGUITY" for i in all_issues)
        llm_issue = next(i for i in all_issues if i["code"] == "LLM_AMBIGUITY")
        assert llm_issue["interpretations"] == ["Same filename", "Same hash"]

    @patch("pdd.commands.contracts.run_llm_ambiguity_pass")
    def test_llm_suggestion_rendered(self, mock_llm, runner):
        mock_llm.return_value = [
            ContractIssue(
                level="warn",
                code="LLM_AMBIGUITY",
                rule_id="",
                section="llm",
                line="",
                message="LLM flagged term.",
                suggestion="duplicate upload: an upload with the same tenant ID and normalized file hash",
                interpretations=["Same filename"],
            )
        ]
        result = _invoke(
            runner, "--llm-ambiguity",
            str(FIXTURES / "vague_no_vocab_python.prompt"),
        )
        flat = " ".join(result.output.split())
        assert "Suggestion" in flat
        assert "tenant" in flat


# ---------------------------------------------------------------------------
# TestLegacyPromptSafety
# ---------------------------------------------------------------------------

class TestLegacyPromptSafety:
    def test_legacy_prompt_exits_zero(self, runner):
        result = _invoke(runner, str(FIXTURES / "legacy_no_sections_python.prompt"))
        assert result.exit_code == 0

    def test_bundled_prompts_no_errors(self, runner):
        """Real bundled prompts must not emit errors (strict or not)."""
        pdd_prompts = Path(__file__).parents[2] / "pdd" / "prompts"
        for p in sorted(pdd_prompts.glob("*.prompt")):
            result = _json_invoke(runner, str(p))
            data = json.loads(result.output)
            errors = [i for entry in data for i in entry["issues"]
                      if i["level"] == "error"]
            assert errors == [], (
                f"{p.name} produced errors: {[e['message'] for e in errors]}"
            )
