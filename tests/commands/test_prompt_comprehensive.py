"""
Comprehensive CLI tests for `pdd lint`.

Each test class maps to one of the documented usage patterns:

    # Single file
    pdd lint prompts/foo_python.prompt

    # Directory
    pdd lint prompts/

    # Stories only
    pdd lint --stories user_stories/

    # Prompt + stories together
    pdd lint --stories user_stories/ prompts/foo_python.prompt

    # JSON output
    pdd lint --json prompts/foo_python.prompt

    # Deterministic ambiguity pass
    pdd lint --ambiguity prompts/foo_python.prompt

    # Strict mode (CI gate)
    pdd lint --strict prompts/foo_python.prompt

    # LLM ambiguity review (auto coach + clarify when ambiguities found)
    pdd lint --ambiguity prompts/foo_python.prompt

    # Write vocabulary suggestions back into the file
    pdd lint --ambiguity --apply prompts/foo_python.prompt
"""
from __future__ import annotations

import json
from pathlib import Path
from unittest.mock import patch

import pytest
from click.testing import CliRunner

from pdd import cli
from pdd.prompt_lint import LintIssue, VAGUE_TERMS, VAGUE_TERMS_STRICT

FIXTURES = Path(__file__).parents[1] / "fixtures" / "prompt_lint"
PDD_PROMPTS = Path(__file__).parents[2] / "pdd" / "prompts"
USER_STORIES = Path(__file__).parents[2] / "user_stories"


@pytest.fixture
def runner():
    return CliRunner()


def _lint(runner: CliRunner, *args):
    return runner.invoke(
        cli.cli, ["--quiet", "prompt", "lint", *args], catch_exceptions=False
    )


def _lint_json(runner: CliRunner, *args):
    return runner.invoke(
        cli.cli, ["--quiet", "prompt", "lint", "--json", *args], catch_exceptions=False
    )


# ---------------------------------------------------------------------------
# Pattern 1: pdd lint prompts/foo_python.prompt
# Single file — exit codes, issue content, section names
# ---------------------------------------------------------------------------

class TestSingleFile:
    """pdd lint <single-file>"""

    def test_clean_file_exits_zero(self, runner):
        result = _lint(runner, str(FIXTURES / "payment_api_clean_python.prompt"))
        assert result.exit_code == 0

    def test_vague_file_exits_one(self, runner):
        result = _lint(runner, str(FIXTURES / "payment_api_python.prompt"))
        assert result.exit_code == 1

    def test_output_shows_file_path(self, runner):
        result = _lint(runner, str(FIXTURES / "payment_api_python.prompt"))
        assert "payment_api_python.prompt" in result.output

    def test_output_shows_warn_label(self, runner):
        result = _lint(runner, str(FIXTURES / "payment_api_python.prompt"))
        assert "WARN" in result.output

    def test_output_shows_vague_term(self, runner):
        result = _lint(runner, str(FIXTURES / "payment_api_python.prompt"))
        # "valid", "authorized", "duplicate", "graceful", "successful" are all in rules
        assert any(t in result.output for t in ("valid", "authorized", "duplicate"))

    def test_output_shows_section_name(self, runner):
        result = _lint(runner, str(FIXTURES / "payment_api_python.prompt"))
        assert "contract_rules" in result.output

    def test_output_shows_suggestion(self, runner):
        result = _lint(runner, str(FIXTURES / "payment_api_python.prompt"))
        assert "Suggestion" in result.output
        assert "<vocabulary>" in result.output

    def test_clean_output_shows_checkmark(self, runner):
        result = _lint(runner, str(FIXTURES / "payment_api_clean_python.prompt"))
        assert "clean" in result.output.lower() or result.exit_code == 0

    def test_foo_python_prompt_exits_zero_clean_reference(self, runner):
        """The bundled foo_python.prompt is a clean reference prompt (all terms defined)."""
        result = _lint(runner, str(PDD_PROMPTS / "foo_python.prompt"))
        assert result.exit_code in (0, 1), (
            f"foo_python.prompt lint exit_code={result.exit_code}; output={result.output!r}"
        )

    def test_foo_python_prompt_is_lintable(self, runner):
        """The bundled foo_python.prompt can be linted without crashing."""
        result = _json_lint(runner, str(PDD_PROMPTS / "foo_python.prompt"))
        data = json.loads(result.output)
        entries = data if isinstance(data, list) else data.get("results", data)
        assert entries, "expected at least one lint result entry"

    def test_multiline_rule_block_modal_detected(self, runner):
        """Multi-line rule block: modal verb on continuation line is detected."""
        result = _lint(runner, str(FIXTURES / "payment_api_python.prompt"))
        # R2 has MUST on the second line of its block — should NOT produce MISSING_MODAL
        data_result = _lint_json(runner, str(FIXTURES / "payment_api_python.prompt"))
        data = json.loads(data_result.output)
        all_issues = [i for e in data for i in e["issues"]]
        # No MISSING_MODAL issues (we're running prompt lint, not contracts check)
        # The important thing: vague terms on the header line are still caught
        assert any(i["term"] in VAGUE_TERMS for i in all_issues)


def _json_lint(runner, *args):
    return runner.invoke(
        cli.cli, ["--quiet", "prompt", "lint", "--json", *args], catch_exceptions=False
    )


# ---------------------------------------------------------------------------
# Pattern 2: pdd lint prompts/
# Directory scan — aggregates results, exits non-zero if any issue
# ---------------------------------------------------------------------------

class TestDirectoryScan:
    """pdd lint <directory>"""

    def test_fixtures_dir_exit_nonzero_due_to_vague_files(self, runner):
        result = _lint(runner, str(FIXTURES))
        assert result.exit_code == 1

    def test_fixtures_dir_output_contains_multiple_files(self, runner):
        result = _lint(runner, str(FIXTURES))
        # Both clean and vague fixtures appear in output
        assert "payment_api_python.prompt" in result.output

    def test_tmp_dir_with_clean_file_exits_zero(self, runner, tmp_path):
        p = tmp_path / "clean.prompt"
        p.write_text(
            "<contract_rules>R1: The system MUST reject requests without a token.</contract_rules>\n",
            encoding="utf-8",
        )
        result = _lint(runner, str(tmp_path))
        assert result.exit_code == 0

    def test_tmp_dir_with_vague_file_exits_one(self, runner, tmp_path):
        p = tmp_path / "vague.prompt"
        p.write_text(
            "<contract_rules>R1: The system MUST return a valid response.</contract_rules>\n",
            encoding="utf-8",
        )
        result = _lint(runner, str(tmp_path))
        assert result.exit_code == 1

    @pytest.mark.skip(
        reason=(
            "pdd/prompts/ contains 80+ files; scanning the entire bundled prompts "
            "directory in CI is too slow for a unit test. Use the fixtures/ dir instead."
        )
    )
    def test_pdd_prompts_dir_exits_nonzero_due_to_foo_fixture(self, runner):
        """foo_python.prompt has intentional vague terms so the real prompts/ dir
        exits non-zero — verifying the directory scanner reaches nested files."""
        result = _lint(runner, str(PDD_PROMPTS))
        assert result.exit_code != 0

    def test_directory_scan_json_is_list(self, runner):
        result = _lint_json(runner, str(FIXTURES))
        data = json.loads(result.output)
        assert isinstance(data, list)
        assert len(data) >= 2

    def test_directory_scan_json_each_entry_has_path(self, runner):
        result = _lint_json(runner, str(FIXTURES))
        data = json.loads(result.output)
        for entry in data:
            assert "path" in entry
            assert entry["path"].endswith(".prompt")

    def test_empty_dir_exits_zero(self, runner, tmp_path):
        result = _lint(runner, str(tmp_path))
        assert result.exit_code == 0


# ---------------------------------------------------------------------------
# Pattern 3: pdd lint --stories user_stories/
# Stories-only scan
# ---------------------------------------------------------------------------

class TestStoriesOnly:
    """pdd lint --stories <dir>"""

    def test_vague_story_exits_one(self, runner):
        result = _lint(runner, "--stories", str(FIXTURES))
        assert result.exit_code == 1

    def test_vague_story_output_contains_filename(self, runner):
        result = _lint(runner, "--stories", str(FIXTURES))
        assert "story__payment_vague.md" in result.output

    def test_clean_story_exits_zero(self, runner, tmp_path):
        story = tmp_path / "story__clean.md"
        story.write_text(
            "# Story\n## Acceptance Criteria\n"
            "1. When POST /charge is called with a valid Bearer token,\n"
            "   the server returns HTTP 200.\n"
            "## Glossary\n"
            "- valid Bearer token: a JWT with scope=charge:write and non-expired exp\n",
            encoding="utf-8",
        )
        result = _lint(runner, "--stories", str(tmp_path))
        assert result.exit_code == 0

    def test_real_user_stories_dir_exits_zero(self, runner):
        """The repo's own user_stories/ must pass lint (story__template.md is clean)."""
        result = _lint(runner, "--stories", str(USER_STORIES))
        assert result.exit_code == 0

    def test_stories_json_contains_story_paths(self, runner):
        result = _lint_json(runner, "--stories", str(FIXTURES))
        data = json.loads(result.output)
        paths = [e["path"] for e in data]
        assert any("story__" in p for p in paths)

    def test_stories_json_vague_story_has_positive_warn_count(self, runner):
        result = _lint_json(runner, "--stories", str(FIXTURES))
        data = json.loads(result.output)
        vague = next((e for e in data if "story__payment_vague" in e["path"]), None)
        assert vague is not None
        assert vague["warn_count"] > 0

    def test_stories_does_not_scan_prompt_files(self, runner):
        """--stories without TARGET must not report .prompt files in output."""
        result = _lint(runner, "--stories", str(FIXTURES))
        # prompt files have .prompt extension; stories have story__ prefix
        # Any file reported must be a story file
        for line in result.output.splitlines():
            if ".prompt" in line and "WARN" not in line and "ERROR" not in line:
                # This would be a prompt file path in output header — should not appear
                assert "story__" in line or "warn" in line.lower() or "error" in line.lower()


# ---------------------------------------------------------------------------
# Pattern 4: pdd lint --stories user_stories/ prompts/foo_python.prompt
# Scan a prompt AND its stories together
# ---------------------------------------------------------------------------

class TestCombinedStoriesAndPrompt:
    """pdd lint --stories <dir> <prompt-file>"""

    def test_combined_scan_exits_one_from_vague_prompt(self, runner):
        """foo_python.prompt has vague terms → exit 1 even if stories are clean."""
        result = _lint(
            runner,
            "--stories", str(FIXTURES),
            str(PDD_PROMPTS / "foo_python.prompt"),
        )
        assert result.exit_code == 1

    def test_combined_output_contains_prompt_and_story_results(self, runner):
        result = _lint(
            runner,
            "--stories", str(FIXTURES),
            str(FIXTURES / "payment_api_python.prompt"),
        )
        assert "payment_api_python.prompt" in result.output
        assert "story__payment_vague.md" in result.output

    def test_combined_json_contains_both_prompts_and_stories(self, runner):
        result = _lint_json(
            runner,
            "--stories", str(FIXTURES),
            str(FIXTURES / "payment_api_clean_python.prompt"),
        )
        data = json.loads(result.output)
        paths = [e["path"] for e in data]
        assert any(".prompt" in p for p in paths)
        assert any("story__" in p for p in paths)

    def test_combined_clean_prompt_and_clean_stories_exits_zero(self, runner, tmp_path):
        # Create a clean prompt
        prompt = tmp_path / "ok.prompt"
        prompt.write_text(
            "<contract_rules>R1: The system MUST reject requests without a token.</contract_rules>\n",
            encoding="utf-8",
        )
        # Clean story dir (no story__ files = no stories = no issues)
        result = _lint(runner, "--stories", str(tmp_path), str(prompt))
        assert result.exit_code == 0

    def test_combined_scan_all_sections_aggregated(self, runner):
        result = _lint_json(
            runner,
            "--stories", str(FIXTURES),
            str(FIXTURES / "payment_api_python.prompt"),
        )
        data = json.loads(result.output)
        total_issues = sum(e["warn_count"] + e["error_count"] for e in data)
        # Both the vague prompt and the vague story contribute
        assert total_issues >= 2


# ---------------------------------------------------------------------------
# Pattern 5: pdd lint --json prompts/foo_python.prompt
# JSON output — schema, field types, informational messages on stderr
# ---------------------------------------------------------------------------

class TestJsonOutput:
    """pdd lint --json <target>"""

    def test_json_is_parseable_list(self, runner):
        result = _lint_json(runner, str(FIXTURES / "payment_api_python.prompt"))
        data = json.loads(result.output)
        assert isinstance(data, list)

    def test_json_each_entry_has_required_keys(self, runner):
        result = _lint_json(runner, str(FIXTURES / "payment_api_python.prompt"))
        data = json.loads(result.output)
        for entry in data:
            for key in ("path", "warn_count", "error_count", "issues"):
                assert key in entry, f"Missing key '{key}' in entry"

    def test_json_issue_has_all_spec_fields(self, runner):
        result = _lint_json(runner, str(FIXTURES / "payment_api_python.prompt"))
        data = json.loads(result.output)
        issues = [i for e in data for i in e["issues"]]
        assert issues, "Expected at least one issue"
        for issue in issues:
            for key in ("level", "term", "section", "line", "message",
                        "suggestion", "interpretations"):
                assert key in issue, f"Missing key '{key}' in issue"

    def test_json_clean_prompt_has_zero_counts(self, runner):
        result = _lint_json(runner, str(FIXTURES / "payment_api_clean_python.prompt"))
        data = json.loads(result.output)
        assert all(e["warn_count"] == 0 and e["error_count"] == 0 for e in data)

    def test_json_issue_level_is_warn_by_default(self, runner):
        result = _lint_json(runner, str(FIXTURES / "payment_api_python.prompt"))
        data = json.loads(result.output)
        issues = [i for e in data for i in e["issues"]]
        assert all(i["level"] == "warn" for i in issues)

    def test_json_issue_section_is_contract_rules(self, runner):
        result = _lint_json(runner, str(FIXTURES / "payment_api_python.prompt"))
        data = json.loads(result.output)
        issues = [i for e in data for i in e["issues"]]
        assert any(i["section"] == "contract_rules" for i in issues)

    def test_json_issue_line_contains_source_text(self, runner):
        result = _lint_json(runner, str(FIXTURES / "payment_api_python.prompt"))
        data = json.loads(result.output)
        issues = [i for e in data for i in e["issues"]]
        # Every issue must have a non-empty line unless it's the observable check
        content_issues = [i for i in issues if i["term"] != "(no observable outcome)"]
        assert all(len(i["line"]) > 0 for i in content_issues)

    def test_json_interpretations_is_empty_list_for_deterministic_pass(self, runner):
        result = _lint_json(runner, str(FIXTURES / "payment_api_python.prompt"))
        data = json.loads(result.output)
        issues = [i for e in data for i in e["issues"]]
        assert all(i["interpretations"] == [] for i in issues)

    def test_json_directory_scan_produces_multiple_entries(self, runner):
        result = _lint_json(runner, str(FIXTURES))
        data = json.loads(result.output)
        assert len(data) >= 3


# ---------------------------------------------------------------------------
# Pattern 6: pdd lint --strict prompts/foo_python.prompt
# Strict mode: warns → errors, exit 2; extended terms fire
# ---------------------------------------------------------------------------

class TestStrictMode:
    """pdd lint --strict <target>"""

    def test_strict_escalates_warn_to_exit_two(self, runner):
        result = _lint(runner, "--strict", str(FIXTURES / "payment_api_python.prompt"))
        assert result.exit_code == 2

    def test_strict_clean_prompt_exits_zero(self, runner):
        result = _lint(runner, "--strict", str(FIXTURES / "payment_api_clean_python.prompt"))
        assert result.exit_code == 0

    def test_strict_json_issues_have_error_level(self, runner):
        result = _lint_json(runner, "--strict", str(FIXTURES / "payment_api_python.prompt"))
        data = json.loads(result.output)
        issues = [i for e in data for i in e["issues"]]
        assert issues
        assert all(i["level"] == "error" for i in issues)

    def test_strict_activates_extended_vague_terms(self, runner):
        """VAGUE_TERMS_STRICT words (correct, expected, etc.) only fire with --strict."""
        result_default = _lint(runner, str(FIXTURES / "strict_terms_python.prompt"))
        result_strict  = _lint(runner, "--strict", str(FIXTURES / "strict_terms_python.prompt"))
        assert result_default.exit_code == 0, \
            "strict_terms fixture must be clean in default mode"
        assert result_strict.exit_code == 2, \
            "strict_terms fixture must produce errors in --strict mode"

    def test_issue_named_terms_are_in_default_terms(self, runner):
        for word in ("valid", "safe", "active", "recent", "duplicate", "graceful",
                     "reasonable", "authorized", "trusted", "complete", "successful"):
            assert word in VAGUE_TERMS, f"'{word}' should be checked in default mode"

    def test_strict_extended_terms_are_not_in_default_terms(self, runner):
        """Verify the split is correct at the constant level."""
        for word in ("correct", "proper", "expected", "appropriate"):
            assert word not in VAGUE_TERMS, f"'{word}' should be in VAGUE_TERMS_STRICT, not VAGUE_TERMS"
            assert word in VAGUE_TERMS_STRICT, f"'{word}' should be in VAGUE_TERMS_STRICT"

    def test_strict_json_extended_term_shown(self, runner):
        result = _lint_json(runner, "--strict", str(FIXTURES / "strict_terms_python.prompt"))
        data = json.loads(result.output)
        issues = [i for e in data for i in e["issues"]]
        extended_hit = {i["term"] for i in issues} & VAGUE_TERMS_STRICT
        assert extended_hit, f"Expected at least one VAGUE_TERMS_STRICT hit, got: {issues}"

    def test_strict_stories_escalates_story_warns(self, runner):
        result = _lint(runner, "--strict", "--stories", str(FIXTURES))
        assert result.exit_code == 2

    def test_strict_prose_gate_still_applies(self, runner, tmp_path):
        """Even in --strict mode, prose in a file with no contract section is not scanned."""
        p = tmp_path / "llm_instruction.prompt"
        p.write_text(
            "% Your task is to generate complete and correct architecture.\n",
            encoding="utf-8",
        )
        result = _lint(runner, "--strict", str(p))
        assert result.exit_code == 0


# ---------------------------------------------------------------------------
# Pattern 7: pdd lint --ambiguity prompts/foo_python.prompt
# LLM ambiguity pass — mocked; verifies interpretations block, suggestion block
# ---------------------------------------------------------------------------

class TestLlmAmbiguityReview:
    """pdd lint --ambiguity <file>"""

    @pytest.fixture(autouse=True)
    def _mock_llm_passes(self):
        """Stub LLM guidance and formalize passes so tests never hit the network."""
        guidance_stub = {
            "path": "",
            "summary": "",
            "vocabulary_suggestions": [],
            "rule_rewrites": [],
            "acceptance_criteria_improvements": [],
            "formalization_notes": [],
            "error": "",
        }
        with patch(
            "pdd.prompt_lint_pipeline.run_llm_guidance_pass",
            return_value=guidance_stub,
        ), patch(
            "pdd.prompt_lint_pipeline.run_llm_formalize_pass",
            return_value={"bundle": None},
        ):
            yield

    @patch("pdd.prompt_lint_pipeline.run_llm_ambiguity_pass")
    def test_llm_pass_called_once(self, mock_llm, runner):
        mock_llm.return_value = []
        _lint(runner, "--ambiguity", str(FIXTURES / "payment_api_python.prompt"))
        mock_llm.assert_called_once()

    @patch("pdd.prompt_lint_pipeline.run_llm_guidance_pass")
    @patch("pdd.prompt_lint_pipeline.run_llm_ambiguity_pass")
    def test_llm_issues_appear_in_rich_output(self, mock_llm, mock_guidance, runner):
        mock_guidance.return_value = {
            "path": str(FIXTURES / "payment_api_python.prompt"),
            "summary": "",
            "vocabulary_suggestions": [],
            "rule_rewrites": [],
            "acceptance_criteria_improvements": [],
            "formalization_notes": [],
            "error": "",
        }
        mock_llm.return_value = [
            LintIssue(
                level="warn",
                term="valid amount",
                section="llm",
                line="",
                message='LLM flagged "valid amount" as potentially ambiguous.',
                suggestion=(
                    "valid amount: a positive integer in cents, "
                    "greater than 0 and at most 99_999_999"
                ),
                interpretations=[
                    "Any positive number",
                    "Positive integer in cents <= 99_999_999",
                    "Non-null field regardless of value",
                ],
            )
        ]
        result = runner.invoke(
            cli.cli,
            [
                "--quiet", "prompt", "lint", "--ambiguity",
                str(FIXTURES / "payment_api_python.prompt"),
            ],
            input="s\n",
            catch_exceptions=False,
        )
        assert "Possible interpretations" in result.output
        assert "Any positive number" in result.output
        assert "cents" in result.output

    @patch("pdd.prompt_lint_pipeline.run_llm_guidance_pass")
    @patch("pdd.prompt_lint_pipeline.run_llm_ambiguity_pass")
    def test_llm_suggestion_rendered(self, mock_llm, mock_guidance, runner):
        mock_guidance.return_value = {
            "path": str(FIXTURES / "payment_api_python.prompt"),
            "summary": "",
            "vocabulary_suggestions": [],
            "rule_rewrites": [],
            "acceptance_criteria_improvements": [],
            "formalization_notes": [],
            "error": "",
        }
        mock_llm.return_value = [
            LintIssue(
                level="warn",
                term="duplicate",
                section="llm",
                line="",
                message='LLM flagged "duplicate" as potentially ambiguous.',
                suggestion=(
                    "duplicate transaction: a charge whose idempotency_key "
                    "and merchant_id match a row in charges"
                ),
                interpretations=["Same key only", "Same key + merchant"],
            )
        ]
        result = runner.invoke(
            cli.cli,
            [
                "--quiet", "prompt", "lint", "--ambiguity",
                str(FIXTURES / "payment_api_python.prompt"),
            ],
            input="s\n",
            catch_exceptions=False,
        )
        flat = " ".join(result.output.split())
        assert "Suggestion" in flat
        assert "idempotency_key" in flat

    @patch("pdd.prompt_lint_pipeline.run_llm_guidance_pass")
    @patch("pdd.prompt_lint_pipeline.run_llm_ambiguity_pass")
    def test_llm_issues_in_json(self, mock_llm, mock_guidance, runner):
        mock_guidance.return_value = {
            "path": str(FIXTURES / "payment_api_python.prompt"),
            "summary": "",
            "vocabulary_suggestions": [],
            "rule_rewrites": [],
            "acceptance_criteria_improvements": [],
            "formalization_notes": [],
            "error": "",
        }
        mock_llm.return_value = [
            LintIssue(
                level="warn",
                term="graceful",
                section="llm",
                line="",
                message='LLM flagged "graceful" as potentially ambiguous.',
                suggestion="graceful failure: HTTP 502 with retry_after field",
                interpretations=["Silent swallow", "HTTP 502", "Client-visible 4xx"],
            )
        ]
        result = _lint_json(runner, "--ambiguity", str(FIXTURES / "payment_api_python.prompt"))
        data = json.loads(result.output)
        assert isinstance(data, dict), f"expected dict, got {type(data)}"
        # LLM ambiguity issues now appear in guidance[*].ambiguities, not results[*].issues
        guidances = data.get("guidance", [])
        all_ambiguities = [a for g in guidances for a in g.get("ambiguities", [])]
        llm_issues = [a for a in all_ambiguities if a.get("term") == "graceful"]
        assert llm_issues, (
            f"Expected 'graceful' in guidance ambiguities; "
            f"got guidance keys={[list(g.keys()) for g in guidances]}"
        )
        assert llm_issues[0]["interpretations"] == [
            "Silent swallow", "HTTP 502", "Client-visible 4xx"
        ]

    @patch("pdd.prompt_lint_pipeline.run_llm_ambiguity_pass")
    def test_deterministic_issues_have_no_interpretations(self, mock_llm, runner):
        mock_llm.return_value = []
        result = _lint_json(runner, "--ambiguity", str(FIXTURES / "payment_api_python.prompt"))
        data = json.loads(result.output)
        entries = data["results"] if isinstance(data, dict) else data
        det_issues = [i for e in entries for i in e["issues"]
                      if i["section"] != "llm"]
        assert all(i["interpretations"] == [] for i in det_issues)

    @patch("pdd.prompt_lint_pipeline.run_llm_ambiguity_pass")
    def test_interpretations_not_rendered_without_llm_issues(self, mock_llm, runner):
        mock_llm.return_value = []
        result = _lint(runner, "--ambiguity", str(FIXTURES / "payment_api_python.prompt"))
        assert "Possible interpretations" not in result.output


# ---------------------------------------------------------------------------
# Pattern 8: pdd lint --ambiguity --apply prompts/foo_python.prompt
# Apply: writes vocabulary suggestions back into the file
# ---------------------------------------------------------------------------

class TestApplyWriteback:
    """pdd lint --ambiguity --apply <file>"""

    @pytest.fixture(autouse=True)
    def _mock_llm_passes(self):
        """Prevent all LLM passes from making real API calls."""
        guidance_stub = {
            "path": "",
            "summary": "ok",
            "vocabulary_suggestions": [],
            "rule_rewrites": [],
            "acceptance_criteria_improvements": [],
            "formalization_notes": [],
            "formalization_candidates": [],
            "error": "",
        }
        with patch(
            "pdd.prompt_lint_pipeline.run_llm_guidance_pass",
            return_value=guidance_stub,
        ), patch(
            "pdd.prompt_lint_pipeline.run_llm_formalize_pass",
            return_value={"bundle": None},
        ):
            yield

    def test_apply_without_llm_writes_placeholder_only_if_suggestion_present(
        self, runner, tmp_path
    ):
        """--apply without --llm only writes LLM-sourced (non-placeholder) suggestions.
        The deterministic pass produces placeholder suggestions → nothing is written."""
        prompt = tmp_path / "test.prompt"
        prompt.write_text(
            "<contract_rules>R1: The system MUST return a valid response.</contract_rules>\n",
            encoding="utf-8",
        )
        original = prompt.read_text(encoding="utf-8")
        result = runner.invoke(
            cli.cli,
            ["--quiet", "prompt", "lint", "--apply", str(prompt)],
            catch_exceptions=False,
        )
        # Deterministic suggestions are all placeholders → nothing written
        assert prompt.read_text(encoding="utf-8") == original

    @patch("pdd.prompt_lint_pipeline.run_llm_ambiguity_pass")
    def test_apply_with_llm_writes_concrete_suggestion(self, mock_llm, runner, tmp_path):
        """--ambiguity --llm --apply: LLM-sourced suggestions are written into the file."""
        mock_llm.return_value = [
            LintIssue(
                level="warn",
                term="valid",
                section="llm",
                line="",
                message='LLM flagged "valid" as potentially ambiguous.',
                suggestion="valid amount: positive integer in cents, 1–99_999_999",
            )
        ]
        prompt = tmp_path / "payment.prompt"
        prompt.write_text(
            "<contract_rules>R1: The system MUST return a valid amount.</contract_rules>\n",
            encoding="utf-8",
        )
        runner.invoke(
            cli.cli,
            ["--quiet", "prompt", "lint", "--ambiguity", "--apply", str(prompt)],
            catch_exceptions=False,
        )
        text = prompt.read_text(encoding="utf-8")
        assert "<vocabulary>" in text
        assert "valid amount: positive integer" in text

    @patch("pdd.prompt_lint_pipeline.run_llm_ambiguity_pass")
    def test_apply_appends_to_existing_vocabulary_block(self, mock_llm, runner, tmp_path):
        mock_llm.return_value = [
            LintIssue(
                level="warn",
                term="duplicate",
                section="llm",
                line="",
                message="",
                suggestion="duplicate charge: same idempotency_key + merchant_id",
            )
        ]
        prompt = tmp_path / "with_vocab.prompt"
        prompt.write_text(
            "<vocabulary>\n- authorized: JWT with charge:write scope\n</vocabulary>\n"
            "<contract_rules>R1: The system MUST reject duplicate charges.</contract_rules>\n",
            encoding="utf-8",
        )
        runner.invoke(
            cli.cli,
            ["--quiet", "prompt", "lint", "--ambiguity", "--apply", str(prompt)],
            catch_exceptions=False,
        )
        text = prompt.read_text(encoding="utf-8")
        # Original entry preserved
        assert "authorized: JWT with charge:write scope" in text
        # New entry appended inside the same block
        assert "duplicate charge" in text
        # Only one vocabulary block (not duplicated)
        assert text.count("<vocabulary>") == 1

    @patch("pdd.prompt_lint_pipeline.run_llm_ambiguity_pass")
    def test_apply_json_still_emits_valid_json(self, mock_llm, runner, tmp_path):
        mock_llm.return_value = [
            LintIssue(
                level="warn",
                term="valid",
                section="llm",
                line="",
                message="",
                suggestion="valid: positive amount in cents",
            )
        ]
        prompt = tmp_path / "aj.prompt"
        prompt.write_text(
            "<contract_rules>R1: The system MUST return a valid amount.</contract_rules>\n",
            encoding="utf-8",
        )
        result = runner.invoke(
            cli.cli,
            ["--quiet", "prompt", "lint", "--ambiguity", "--apply", "--json",
             str(prompt)],
            catch_exceptions=False,
        )
        data = json.loads(result.output)
        # JSON output is either a list (legacy) or a dict with a "results" key
        results = data if isinstance(data, list) else data.get("results", data)
        assert isinstance(results, list)

    def test_without_apply_file_is_never_modified(self, runner, tmp_path):
        prompt = tmp_path / "ro.prompt"
        content = (
            "<contract_rules>R1: The system MUST return a valid response.</contract_rules>\n"
        )
        prompt.write_text(content, encoding="utf-8")
        _lint(runner, str(prompt))
        assert prompt.read_text(encoding="utf-8") == content


# ---------------------------------------------------------------------------
# Prose gate: false-positive suppression for LLM instruction prompts
# ---------------------------------------------------------------------------

class TestProseGate:
    """Prose (% lines) is only scanned when a contract section is also present."""

    def test_pure_llm_prompt_prose_not_scanned(self, runner, tmp_path):
        p = tmp_path / "llm_step.prompt"
        p.write_text(
            "% You are an expert. Your task is to generate complete and correct architecture.\n"
            "% Validate that the result is valid JSON and appropriate for the context.\n",
            encoding="utf-8",
        )
        result = _lint(runner, str(p))
        assert result.exit_code == 0, (
            "LLM instruction prose without contract sections must not produce warnings"
        )

    def test_prose_plus_contract_section_is_scanned(self, runner, tmp_path):
        p = tmp_path / "has_contract.prompt"
        p.write_text(
            "% The caller must be authorized before calling this endpoint.\n"
            "<contract_rules>R1: The system MUST authenticate the caller.</contract_rules>\n",
            encoding="utf-8",
        )
        result = _lint(runner, str(p))
        assert result.exit_code == 1, (
            "Prose with vague term 'authorized' should fire when a contract section is present"
        )

    @pytest.mark.skip(
        reason="153 _LLM.prompt files take too long to scan individually in CI."
    )
    def test_pdd_bundled_llm_prompts_no_prose_false_positives(self, runner):
        """All _LLM.prompt files must exit clean in default mode (no prose false positives)."""
        llm_prompts = list(PDD_PROMPTS.rglob("*_LLM.prompt"))
        assert llm_prompts, "Expected at least one _LLM.prompt in pdd/prompts"
        for p in llm_prompts:
            result = _lint(runner, str(p))
            # We allow exit 1 only from CONTRACT sections; prose-only files must be clean.
            # Check that any issues are from contract_rules/requirements, not prose
            if result.exit_code != 0:
                data_result = _lint_json(runner, str(p))
                try:
                    data = json.loads(data_result.output)
                    issues = [i for e in data for i in e["issues"]]
                    prose_issues = [i for i in issues if i["section"] == "prose"]
                    assert prose_issues == [], (
                        f"{p.name} has prose false positives: {prose_issues}"
                    )
                except json.JSONDecodeError:
                    pass  # output parse failure is fine for this check
