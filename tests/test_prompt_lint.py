"""Tests for pdd.prompt_lint and pdd.prompt_lint_pipeline (deterministic + mocked LLM)."""
from __future__ import annotations

import json
from pathlib import Path
from unittest.mock import patch

import pytest

from pdd.prompt_lint import (
    LintIssue,
    LintResult,
    VAGUE_TERMS,
    VAGUE_TERMS_STRICT,
    _extract_sections,
    _extract_vocabulary_terms,
    apply_suggestions,
    append_vocabulary_definitions,
    run_llm_ambiguity_pass,
    run_llm_guidance_pass,
    scan_prompt,
    scan_stories,
)
from pdd.prompt_lint_pipeline import (
    PromptLintPipelineOptions,
    collect_clarify_definitions,
    concrete_suggestion,
    definition_from_interpretation,
    is_llm_ambiguity_issue,
    iter_prompt_paths,
    run_prompt_lint_pipeline,
)

FIXTURES = Path(__file__).parent / "fixtures" / "prompt_lint"


def _terms(result: LintResult) -> set[str]:
    return {i.term for i in result.issues if i.term and i.term != "(no observable outcome)"}


def _issues_for_term(result: LintResult, term: str) -> list[LintIssue]:
    return [i for i in result.issues if i.term == term]


# ---------------------------------------------------------------------------
# Section extraction (including parser regression)
# ---------------------------------------------------------------------------


class TestSectionExtraction:
    def test_xml_contract_rules_extracted(self):
        text = "<contract_rules>Only authorized users may call this.</contract_rules>"
        sections = _extract_sections(text)
        assert sections["contract_rules"] == "Only authorized users may call this."

    def test_xml_vocabulary_extracted(self):
        text = "<vocabulary>\n- valid: http 200\n</vocabulary>"
        sections = _extract_sections(text)
        assert "valid: http 200" in sections["vocabulary"]

    def test_percent_comment_vocabulary_literal_does_not_break_xml_sections(self):
        """Regression: <vocabulary> in a % line must not swallow real sections."""
        text = (
            "% Mention vocabulary block without opening a real section.\n"
            "<contract_rules>Reject duplicate uploads.</contract_rules>\n"
            "<vocabulary>\n- duplicate upload: same hash\n</vocabulary>\n"
        )
        sections = _extract_sections(text)
        assert "contract_rules" in sections
        assert "duplicate" in sections["contract_rules"]
        assert "vocabulary" in sections
        assert "duplicate upload" in sections["vocabulary"]

    def test_markdown_acceptance_criteria_extracted(self):
        text = "## Acceptance Criteria\n1. Given X, when Y, then Z.\n## Notes\nNote."
        sections = _extract_sections(text)
        assert "acceptance criteria" in sections
        assert "Given X" in sections["acceptance criteria"]

    def test_prose_percent_lines_extracted(self):
        text = "% Must return a valid response.\n"
        sections = _extract_sections(text)
        assert sections["prose"] == "Must return a valid response."


class TestVocabularyExtraction:
    def test_colon_definitions_and_word_splitting(self):
        vocab = "- valid response: HTTP 200\n- duplicate upload: same hash\n"
        terms = _extract_vocabulary_terms(vocab)
        assert "valid response" in terms
        assert "valid" in terms
        assert "duplicate upload" in terms
        assert "duplicate" in terms

    def test_cross_module_covers_format(self):
        vocab = "- prompts/payment_python.prompt#R3: no provider call before validation\n"
        terms = _extract_vocabulary_terms(vocab)
        assert "no provider call before validation" in terms
        assert "provider" in terms


# ---------------------------------------------------------------------------
# Deterministic scan — packaged fixtures
# ---------------------------------------------------------------------------


class TestDeterministicScanFixtures:
    def test_vague_undefined_warns(self):
        result = scan_prompt(FIXTURES / "vague_undefined.prompt")
        assert result.warn_count > 0
        assert result.error_count == 0
        assert "valid" in _terms(result)

    def test_vague_defined_is_clean(self):
        result = scan_prompt(FIXTURES / "vague_defined.prompt")
        assert result.warn_count == 0

    def test_clean_prompt_is_clean(self):
        result = scan_prompt(FIXTURES / "clean.prompt")
        assert len(result.issues) == 0

    def test_strict_terms_default_mode_is_clean(self):
        result = scan_prompt(FIXTURES / "strict_terms_python.prompt")
        assert result.warn_count == 0

    def test_strict_terms_strict_mode_errors(self):
        result = scan_prompt(FIXTURES / "strict_terms_python.prompt", strict=True)
        assert result.error_count > 0
        assert result.warn_count == 0
        assert any(i.term == "correct" for i in result.issues)


class TestUploadHandlerFixtures:
    """Canonical duplicate-upload example from docs/prompt_lint.md."""

    def test_ambiguous_upload_handler_flags_vague_terms(self):
        result = scan_prompt(FIXTURES / "upload_handler_python.prompt")
        terms = _terms(result)
        assert "duplicate" in terms
        assert "authorized" in terms
        assert "valid" in terms
        assert any(
            i.term == "duplicate" and i.section == "contract_rules"
            for i in result.issues
        )

    def test_upload_handler_with_vocab_is_clean(self):
        result = scan_prompt(FIXTURES / "upload_handler_with_vocab_python.prompt")
        assert result.warn_count == 0
        assert result.error_count == 0

    def test_suggestions_include_term_name(self):
        result = scan_prompt(FIXTURES / "upload_handler_python.prompt")
        dupes = _issues_for_term(result, "duplicate")
        assert dupes
        assert "duplicate" in dupes[0].suggestion.lower()


# ---------------------------------------------------------------------------
# Deterministic scan — inline prompts
# ---------------------------------------------------------------------------


class TestDeterministicScanInline:
    def test_undefined_vague_term_warns(self, tmp_path: Path):
        path = tmp_path / "t.prompt"
        path.write_text(
            "<contract_rules>Must return a valid response.</contract_rules>\n",
            encoding="utf-8",
        )
        result = scan_prompt(path)
        assert any(i.term == "valid" for i in result.issues)

    def test_defined_phrase_suppresses_word_warnings(self, tmp_path: Path):
        path = tmp_path / "t.prompt"
        path.write_text(
            "<vocabulary>\n- valid response: HTTP 200 with data\n</vocabulary>\n"
            "<contract_rules>Must return a valid response.</contract_rules>\n",
            encoding="utf-8",
        )
        result = scan_prompt(path)
        assert not any(i.term == "valid" for i in result.issues)

    def test_observable_outcome_gap_on_contract_rules(self, tmp_path: Path):
        path = tmp_path / "t.prompt"
        path.write_text(
            "<contract_rules>Only authorized users may call this.</contract_rules>\n",
            encoding="utf-8",
        )
        result = scan_prompt(path)
        assert any(i.term == "(no observable outcome)" for i in result.issues)

    def test_placeholder_angle_brackets_not_flagged(self, tmp_path: Path):
        path = tmp_path / "t.prompt"
        path.write_text(
            "<contract_rules>Returns <expected outcome> when input is well-formed.</contract_rules>\n",
            encoding="utf-8",
        )
        result = scan_prompt(path)
        assert result.warn_count == 0

    def test_legacy_plain_text_produces_no_issues(self, tmp_path: Path):
        path = tmp_path / "t.prompt"
        path.write_text("Plain instructions with valid and duplicate words.\n", encoding="utf-8")
        result = scan_prompt(path)
        assert len(result.issues) == 0

    def test_instruction_prompt_prose_not_scanned_without_contract_sections(self, tmp_path: Path):
        path = tmp_path / "t.prompt"
        path.write_text(
            "% Return a valid response for duplicate requests.\n",
            encoding="utf-8",
        )
        result = scan_prompt(path)
        assert len(result.issues) == 0


# ---------------------------------------------------------------------------
# User stories
# ---------------------------------------------------------------------------


class TestScanStories:
    def test_vague_story_warns(self):
        results = scan_stories(FIXTURES)
        vague = next(r for r in results if "vague_criteria" in r.path.name)
        assert vague.warn_count > 0

    def test_story_with_glossary_is_clean(self):
        results = scan_stories(FIXTURES)
        clean = next(r for r in results if r.path.name == "story__clean.md")
        assert len(clean.issues) == 0

    def test_missing_dir_returns_empty(self, tmp_path: Path):
        assert scan_stories(tmp_path / "missing") == []


# ---------------------------------------------------------------------------
# Apply / append vocabulary
# ---------------------------------------------------------------------------


class TestApplySuggestions:
    def test_creates_vocabulary_block(self, tmp_path: Path):
        path = tmp_path / "t.prompt"
        path.write_text(
            "<contract_rules>Must return a valid response.</contract_rules>\n",
            encoding="utf-8",
        )
        issue = LintIssue(
            level="warn",
            term="valid",
            section="contract_rules",
            line="x",
            message="m",
            suggestion="valid response: HTTP 200",
        )
        assert apply_suggestions(path, [issue]) == 1
        assert "valid response: HTTP 200" in path.read_text()

    def test_skips_placeholder_suggestions(self, tmp_path: Path):
        path = tmp_path / "t.prompt"
        path.write_text("<contract_rules>x</contract_rules>\n", encoding="utf-8")
        issue = LintIssue(
            level="warn",
            term="valid",
            section="contract_rules",
            line="x",
            message="m",
            suggestion="valid: <add a precise, observable definition here>",
        )
        assert apply_suggestions(path, [issue]) == 0
        assert "<vocabulary>" not in path.read_text()


class TestAppendVocabularyDefinitions:
    def test_appends_without_duplicates(self, tmp_path: Path):
        path = tmp_path / "t.prompt"
        path.write_text(
            "<vocabulary>\n- existing: already\n</vocabulary>\n",
            encoding="utf-8",
        )
        written = append_vocabulary_definitions(
            path,
            ["existing: already", "new term: definition"],
        )
        assert written == 1
        assert "new term: definition" in path.read_text()


# ---------------------------------------------------------------------------
# Pipeline orchestration (LLM mocked)
# ---------------------------------------------------------------------------


class TestPromptLintPipeline:
    def test_iter_prompt_paths_directory(self, tmp_path: Path):
        (tmp_path / "a.prompt").write_text("<contract_rules>x</contract_rules>\n")
        sub = tmp_path / "nested"
        sub.mkdir()
        (sub / "b.prompt").write_text("<contract_rules>y</contract_rules>\n")
        assert [p.name for p in iter_prompt_paths(tmp_path)] == ["a.prompt", "b.prompt"]

    @patch("pdd.prompt_lint_pipeline.run_llm_ambiguity_pass")
    def test_llm_mode_invokes_ambiguity_pass_per_prompt(self, mock_llm, tmp_path: Path):
        mock_llm.return_value = []
        (tmp_path / "one.prompt").write_text(
            "<contract_rules>Only authorized users may call this.</contract_rules>\n"
        )
        options = PromptLintPipelineOptions(target=tmp_path, llm=True)
        result = run_prompt_lint_pipeline(options)
        assert len(result.results) == 1
        assert mock_llm.call_count == 1

    @patch("pdd.prompt_lint_pipeline.run_llm_guidance_pass")
    @patch("pdd.prompt_lint_pipeline.run_llm_ambiguity_pass")
    def test_llm_ambiguities_trigger_guidance(self, mock_ambiguity, mock_guidance, tmp_path: Path):
        mock_ambiguity.return_value = [
            LintIssue(
                level="warn",
                term="duplicate",
                section="contract_rules",
                line="reject duplicate uploads",
                message='LLM flagged "duplicate" as potentially ambiguous.',
                suggestion="duplicate upload: same hash",
                interpretations=["same filename", "same hash"],
            )
        ]
        mock_guidance.return_value = {
            "path": "x",
            "summary": "ok",
            "vocabulary_suggestions": [],
            "rule_rewrites": [],
            "acceptance_criteria_improvements": [],
            "formalization_notes": [],
            "error": "",
        }
        path = tmp_path / "one.prompt"
        path.write_text(
            "<contract_rules>Reject duplicate uploads.</contract_rules>\n",
            encoding="utf-8",
        )
        options = PromptLintPipelineOptions(
            target=path,
            llm=True,
            non_interactive=True,
        )
        pipeline = run_prompt_lint_pipeline(options)
        mock_guidance.assert_called_once()
        assert pipeline.guidances

    def test_clarify_helpers(self):
        issue = LintIssue(
            level="warn",
            term="valid",
            section="contract_rules",
            line="x",
            message="m",
            suggestion="valid: HTTP 200",
            interpretations=["HTTP 200", "schema valid"],
        )
        assert is_llm_ambiguity_issue(issue)
        assert concrete_suggestion(issue) == "valid: HTTP 200"
        assert definition_from_interpretation(issue, "HTTP 200") == "valid: HTTP 200"

        accepted = collect_clarify_definitions(
            [issue],
            non_interactive=True,
            prompt_choice=lambda *a, **k: "a",
            prompt_text=lambda *a, **k: "",
            prompt_int=lambda *a, **k: 1,
        )
        assert accepted == ["valid: HTTP 200"]


# ---------------------------------------------------------------------------
# LLM passes — local only, mocked at llm_invoke boundary
# ---------------------------------------------------------------------------


class TestLlmPassesLocal:
    @patch("pdd.llm_invoke.llm_invoke")
    def test_ambiguity_pass_uses_local_llm(self, mock_llm, tmp_path: Path):
        mock_llm.return_value = {"result": "[]"}
        path = tmp_path / "t.prompt"
        path.write_text(
            "<contract_rules>Handle requests appropriately.</contract_rules>\n",
            encoding="utf-8",
        )
        run_llm_ambiguity_pass(path)
        assert mock_llm.call_args.kwargs.get("use_cloud") is False

    @patch("pdd.llm_invoke.llm_invoke")
    def test_ambiguity_pass_parses_json_issues(self, mock_llm, tmp_path: Path):
        payload = json.dumps([
            {
                "term": "valid",
                "section": "contract_rules",
                "interpretations": ["HTTP 200"],
                "suggestion": "valid: HTTP 200 with JSON body",
            }
        ])
        mock_llm.return_value = {"result": payload}
        path = tmp_path / "t.prompt"
        path.write_text("<contract_rules>Return valid output.</contract_rules>\n", encoding="utf-8")
        issues = run_llm_ambiguity_pass(path)
        assert len(issues) == 1
        assert issues[0].term == "valid"
        assert issues[0].interpretations == ["HTTP 200"]

    @patch("pdd.llm_invoke.llm_invoke")
    def test_guidance_pass_uses_local_llm(self, mock_llm, tmp_path: Path):
        mock_llm.return_value = {
            "result": json.dumps({
                "summary": "ok",
                "vocabulary_suggestions": [],
                "rule_rewrites": [],
                "acceptance_criteria_improvements": [],
                "formalization_notes": [],
            })
        }
        path = tmp_path / "t.prompt"
        path.write_text("<contract_rules>x</contract_rules>\n", encoding="utf-8")
        run_llm_guidance_pass(path)
        assert mock_llm.call_args.kwargs.get("use_cloud") is False

    @patch("pdd.llm_invoke.llm_invoke", side_effect=RuntimeError("network down"))
    def test_ambiguity_pass_failure_returns_empty(self, _mock_llm, tmp_path: Path):
        path = tmp_path / "t.prompt"
        path.write_text("<contract_rules>x</contract_rules>\n", encoding="utf-8")
        assert run_llm_ambiguity_pass(path) == []


# ---------------------------------------------------------------------------
# Constants
# ---------------------------------------------------------------------------


def test_vague_term_sets():
    for word in ("valid", "duplicate", "authorized", "successful"):
        assert word in VAGUE_TERMS
    for word in ("correct", "proper", "expected"):
        assert word in VAGUE_TERMS_STRICT
        assert word not in VAGUE_TERMS
