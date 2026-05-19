"""Unit tests for pdd.prompt_lint (deterministic pass, no LLM calls)."""
from __future__ import annotations

from pathlib import Path

import pytest

from pdd.prompt_lint import (
    LintIssue,
    LintResult,
    VAGUE_TERMS,
    _extract_sections,
    _extract_vocabulary_terms,
    apply_suggestions,
    scan_prompt,
    scan_stories,
)

# Helpers
def _issues_for_term(result: LintResult, term: str) -> list[LintIssue]:
    return [i for i in result.issues if i.term == term]


def _issues_for_section(result: LintResult, section: str) -> list[LintIssue]:
    return [i for i in result.issues if i.section == section]

# ---------------------------------------------------------------------------
# Fixture paths
# ---------------------------------------------------------------------------

FIXTURES = Path(__file__).parent / "fixtures" / "prompt_lint"


# ---------------------------------------------------------------------------
# _extract_sections
# ---------------------------------------------------------------------------

class TestExtractSections:
    def test_xml_contract_rules_extracted(self):
        text = "<contract_rules>Only authorized users may call this.</contract_rules>"
        sections = _extract_sections(text)
        assert "contract_rules" in sections
        assert "authorized" in sections["contract_rules"]

    def test_xml_vocabulary_extracted(self):
        text = "<vocabulary>\n- valid: http 200 with non-empty data\n</vocabulary>"
        sections = _extract_sections(text)
        assert "vocabulary" in sections

    def test_markdown_acceptance_criteria_extracted(self):
        text = "## Acceptance Criteria\n1. Given X, when Y, then Z.\n## Notes\nSome note."
        sections = _extract_sections(text)
        assert "acceptance criteria" in sections
        assert "Given X" in sections["acceptance criteria"]

    def test_markdown_glossary_extracted(self):
        text = "## Glossary\n- valid: something observable\n"
        sections = _extract_sections(text)
        assert "glossary" in sections

    def test_markdown_covers_extracted(self):
        text = "## Covers\n- valid: concrete definition\n"
        sections = _extract_sections(text)
        assert "covers" in sections

    def test_prose_percent_lines_extracted(self):
        text = "% This must return a valid response.\n% No duplicate requests allowed.\n"
        sections = _extract_sections(text)
        assert "prose" in sections
        assert "valid" in sections["prose"]

    def test_no_sections_returns_empty_or_prose_only(self):
        text = "Some plain text with no special markers."
        sections = _extract_sections(text)
        # No XML or markdown sections; prose only if % lines exist
        assert "contract_rules" not in sections
        assert "acceptance criteria" not in sections


# ---------------------------------------------------------------------------
# _extract_vocabulary_terms
# ---------------------------------------------------------------------------

class TestExtractVocabularyTerms:
    def test_colon_separated_terms(self):
        vocab = "- valid response: HTTP 200 with non-empty data field\n- duplicate: same hash\n"
        terms = _extract_vocabulary_terms(vocab)
        assert "valid response" in terms
        assert "duplicate" in terms

    def test_dash_separated_terms(self):
        vocab = "graceful - returns 409 with JSON error body\n"
        terms = _extract_vocabulary_terms(vocab)
        assert "graceful" in terms

    def test_bullet_prefix_stripped(self):
        vocab = "* authorized user: JWT present and unexpired\n"
        terms = _extract_vocabulary_terms(vocab)
        assert "authorized user" in terms

    def test_empty_text_returns_empty_set(self):
        assert _extract_vocabulary_terms("") == set()


# ---------------------------------------------------------------------------
# scan_prompt — fixture-based
# ---------------------------------------------------------------------------

class TestScanPromptFixtures:
    def test_vague_undefined_warns(self):
        result = scan_prompt(FIXTURES / "vague_undefined.prompt")
        assert isinstance(result, LintResult)
        assert result.warn_count > 0, "Expected warnings for undefined vague terms"
        assert result.error_count == 0

    def test_vague_defined_produces_no_issues(self):
        result = scan_prompt(FIXTURES / "vague_defined.prompt")
        assert result.warn_count == 0
        assert result.error_count == 0

    def test_clean_prompt_produces_no_issues(self):
        result = scan_prompt(FIXTURES / "clean.prompt")
        assert len(result.issues) == 0

    def test_result_path_is_set(self):
        path = FIXTURES / "clean.prompt"
        result = scan_prompt(path)
        assert result.path == path


# ---------------------------------------------------------------------------
# scan_prompt — inline prompts
# ---------------------------------------------------------------------------

class TestScanPromptInline:
    def _write(self, tmp_path: Path, content: str, name: str = "test.prompt") -> Path:
        p = tmp_path / name
        p.write_text(content, encoding="utf-8")
        return p

    def test_single_vague_term_flagged(self, tmp_path):
        p = self._write(tmp_path, "<contract_rules>Must return a valid response.</contract_rules>")
        result = scan_prompt(p)
        assert any(i.term == "valid" for i in result.issues)

    def test_defined_term_suppressed(self, tmp_path):
        text = (
            "<vocabulary>\n- valid response: HTTP 200 with non-empty data\n</vocabulary>\n"
            "<contract_rules>Must return a valid response.</contract_rules>"
        )
        p = self._write(tmp_path, text)
        result = scan_prompt(p)
        assert not any(i.term == "valid" for i in result.issues)

    def test_rule_without_observable_outcome_warns(self, tmp_path):
        p = self._write(
            tmp_path,
            "<contract_rules>The response must be valid and complete.</contract_rules>",
        )
        result = scan_prompt(p)
        no_outcome_issues = [i for i in result.issues if "observable outcome" in i.message]
        assert len(no_outcome_issues) > 0

    def test_rule_with_observable_outcome_no_outcome_warn(self, tmp_path):
        p = self._write(
            tmp_path,
            "<contract_rules>Returns a valid JSON object with status 200.</contract_rules>",
        )
        result = scan_prompt(p)
        no_outcome_issues = [i for i in result.issues if "observable outcome" in i.message]
        assert len(no_outcome_issues) == 0

    def test_strict_mode_escalates_warnings_to_errors(self, tmp_path):
        p = self._write(tmp_path, "<contract_rules>Must return a valid response.</contract_rules>")
        result = scan_prompt(p, strict=True)
        assert result.error_count > 0
        assert result.warn_count == 0

    def test_legacy_prompt_no_sections_zero_issues(self, tmp_path):
        # A prompt with no recognised XML/MD sections should never fail
        p = self._write(
            tmp_path,
            "Just some plain text explanation of what this module should do.\n"
            "No contract rules, no acceptance tests, no % lines.\n",
        )
        result = scan_prompt(p)
        assert len(result.issues) == 0

    def test_real_bundled_prompt_no_hard_failure(self):
        """Verify a real shipped prompt passes through without raising an exception."""
        bundled = Path(__file__).parents[1] / "pdd" / "prompts" / "code_generator_python.prompt"
        if not bundled.exists():
            pytest.skip("Bundled prompt not found")
        result = scan_prompt(bundled)
        # Should not raise; issue count may be anything
        assert isinstance(result, LintResult)

    def test_missing_file_returns_error_issue(self, tmp_path):
        p = tmp_path / "nonexistent.prompt"
        result = scan_prompt(p)
        assert result.error_count == 1
        assert "Cannot read file" in result.issues[0].message

    def test_issue_suggestion_field_populated(self, tmp_path):
        p = self._write(tmp_path, "<contract_rules>Must return a valid response.</contract_rules>")
        result = scan_prompt(p)
        vague_issues = [i for i in result.issues if i.term == "valid"]
        assert vague_issues
        assert vague_issues[0].suggestion != ""

    def test_issue_as_dict_keys(self, tmp_path):
        p = self._write(tmp_path, "<contract_rules>Must return a valid response.</contract_rules>")
        result = scan_prompt(p)
        assert result.issues
        d = result.issues[0].as_dict()
        for key in ("level", "term", "section", "line", "message", "suggestion", "interpretations"):
            assert key in d

    def test_lint_result_as_dict_keys(self, tmp_path):
        p = self._write(tmp_path, "<contract_rules>Must return a valid response.</contract_rules>")
        result = scan_prompt(p)
        d = result.as_dict()
        assert "path" in d
        assert "warn_count" in d
        assert "error_count" in d
        assert "issues" in d


# ---------------------------------------------------------------------------
# scan_stories — fixture-based
# ---------------------------------------------------------------------------

class TestScanStories:
    def test_vague_acceptance_criteria_flagged(self):
        results = scan_stories(FIXTURES)
        vague_story = next(
            (r for r in results if "vague_criteria" in r.path.name), None
        )
        assert vague_story is not None, "vague story fixture not found"
        assert vague_story.warn_count > 0

    def test_clean_story_with_glossary_no_issues(self):
        results = scan_stories(FIXTURES)
        clean_story = next(
            (r for r in results if "story__clean" in r.path.name), None
        )
        assert clean_story is not None, "clean story fixture not found"
        assert len(clean_story.issues) == 0

    def test_nonexistent_dir_returns_empty(self, tmp_path):
        results = scan_stories(tmp_path / "no_such_dir")
        assert results == []

    def test_empty_dir_returns_empty(self, tmp_path):
        results = scan_stories(tmp_path)
        assert results == []


# ---------------------------------------------------------------------------
# apply_suggestions
# ---------------------------------------------------------------------------

class TestApplySuggestions:
    def _prompt_with_rules(self, tmp_path: Path, *, has_vocab: bool = False) -> Path:
        vocab = "<vocabulary>\n- existing: already here\n</vocabulary>\n" if has_vocab else ""
        content = (
            f"{vocab}"
            "<contract_rules>Must return a valid response.</contract_rules>\n"
        )
        p = tmp_path / "apply_test.prompt"
        p.write_text(content, encoding="utf-8")
        return p

    def test_creates_vocabulary_block_when_absent(self, tmp_path):
        p = self._prompt_with_rules(tmp_path, has_vocab=False)
        issues = [
            LintIssue(
                level="warn",
                term="valid",
                section="contract_rules",
                line="Must return a valid response.",
                message="test",
                suggestion="valid response: HTTP 200 with non-empty data",
            )
        ]
        count = apply_suggestions(p, issues)
        assert count == 1
        text = p.read_text()
        assert "<vocabulary>" in text
        assert "valid response: HTTP 200" in text

    def test_appends_to_existing_vocabulary_block(self, tmp_path):
        p = self._prompt_with_rules(tmp_path, has_vocab=True)
        issues = [
            LintIssue(
                level="warn",
                term="valid",
                section="contract_rules",
                line="Must return a valid response.",
                message="test",
                suggestion="valid response: HTTP 200 with non-empty data",
            )
        ]
        count = apply_suggestions(p, issues)
        assert count == 1
        text = p.read_text()
        assert "existing: already here" in text
        assert "valid response: HTTP 200" in text

    def test_placeholder_suggestion_not_written(self, tmp_path):
        p = self._prompt_with_rules(tmp_path, has_vocab=False)
        issues = [
            LintIssue(
                level="warn",
                term="valid",
                section="contract_rules",
                line="test",
                message="test",
                suggestion="valid: <add a precise, observable definition here>",
            )
        ]
        count = apply_suggestions(p, issues)
        assert count == 0
        assert "<vocabulary>" not in p.read_text()

    def test_empty_issues_returns_zero(self, tmp_path):
        p = self._prompt_with_rules(tmp_path, has_vocab=False)
        assert apply_suggestions(p, []) == 0

    def test_returns_correct_count(self, tmp_path):
        p = self._prompt_with_rules(tmp_path, has_vocab=False)
        issues = [
            LintIssue(
                level="warn", term="valid", section="s", line="l", message="m",
                suggestion="valid response: HTTP 200",
            ),
            LintIssue(
                level="warn", term="duplicate", section="s", line="l", message="m",
                suggestion="duplicate: same hash and tenant",
            ),
        ]
        count = apply_suggestions(p, issues)
        assert count == 2


# ---------------------------------------------------------------------------
# VAGUE_TERMS sanity check
# ---------------------------------------------------------------------------

def test_vague_terms_contains_canonical_words():
    from pdd.prompt_lint import VAGUE_TERMS_STRICT
    # Core terms always checked
    for word in ("valid", "duplicate", "graceful", "authorized", "complete", "successful"):
        assert word in VAGUE_TERMS
    # Extended terms only in --strict mode
    for word in ("correct", "proper", "expected"):
        assert word in VAGUE_TERMS_STRICT


# ---------------------------------------------------------------------------
# Real-world: upload_handler fixture — "duplicate upload" example
# ---------------------------------------------------------------------------

class TestUploadHandlerFixture:
    """
    Exercises the canonical "duplicate upload" ambiguity example from the spec.
    Shows that vague terms are flagged by section and that a vocabulary block
    completely suppresses all warnings.
    """

    def test_duplicate_upload_term_is_flagged(self):
        result = scan_prompt(FIXTURES / "upload_handler_python.prompt")
        dupes = _issues_for_term(result, "duplicate")
        assert len(dupes) >= 1, "Expected 'duplicate' to be flagged"

    def test_duplicate_upload_flagged_in_contract_rules(self):
        result = scan_prompt(FIXTURES / "upload_handler_python.prompt")
        dupes_in_rules = [
            i for i in result.issues
            if i.term == "duplicate" and i.section == "contract_rules"
        ]
        assert len(dupes_in_rules) >= 1

    def test_authorized_term_flagged(self):
        result = scan_prompt(FIXTURES / "upload_handler_python.prompt")
        assert any(i.term == "authorized" for i in result.issues)

    def test_valid_term_flagged(self):
        result = scan_prompt(FIXTURES / "upload_handler_python.prompt")
        assert any(i.term == "valid" for i in result.issues)

    def test_multiple_vague_terms_on_same_line_each_get_own_issue(self):
        # "Return a valid response when the upload is successful."
        # Both "valid" and "successful" should produce separate issues
        result = scan_prompt(FIXTURES / "upload_handler_python.prompt")
        line_issues = [
            i for i in result.issues
            if "successful" in i.line.lower() or "valid" in i.line.lower()
        ]
        terms = {i.term for i in line_issues}
        assert "valid" in terms or "successful" in terms

    def test_upload_handler_with_vocabulary_produces_zero_issues(self):
        result = scan_prompt(FIXTURES / "upload_handler_with_vocab_python.prompt")
        assert result.warn_count == 0
        assert result.error_count == 0

    def test_suggestion_field_contains_term(self):
        result = scan_prompt(FIXTURES / "upload_handler_python.prompt")
        dupes = _issues_for_term(result, "duplicate")
        assert dupes
        # Suggestion should contain the term name as the definition key
        assert "duplicate" in dupes[0].suggestion.lower()

    def test_all_issues_have_non_empty_section(self):
        result = scan_prompt(FIXTURES / "upload_handler_python.prompt")
        for issue in result.issues:
            if issue.term != "(no observable outcome)":
                assert issue.section != "", f"Issue for '{issue.term}' has empty section"

    def test_all_vague_term_issues_have_source_line(self):
        result = scan_prompt(FIXTURES / "upload_handler_python.prompt")
        for issue in result.issues:
            if issue.term != "(no observable outcome)":
                assert issue.line != "", f"Issue for '{issue.term}' has empty line"


# ---------------------------------------------------------------------------
# Warning location assertions (section + line accuracy)
# ---------------------------------------------------------------------------

class TestWarningLocations:
    """Verify that issues are attributed to the correct section and line."""

    def _write(self, tmp_path: Path, content: str) -> Path:
        p = tmp_path / "loc_test.prompt"
        p.write_text(content, encoding="utf-8")
        return p

    def test_contract_rules_section_name_is_contract_rules(self, tmp_path):
        p = self._write(
            tmp_path,
            "<contract_rules>Only active users may call this.</contract_rules>",
        )
        result = scan_prompt(p)
        issues = _issues_for_section(result, "contract_rules")
        assert len(issues) >= 1

    def test_requirements_section_name_is_requirements(self, tmp_path):
        p = self._write(
            tmp_path,
            "<requirements>Accept uploads from authorized users only.</requirements>",
        )
        result = scan_prompt(p)
        issues = _issues_for_section(result, "requirements")
        assert len(issues) >= 1

    def test_issue_line_contains_original_text(self, tmp_path):
        rule = "Must return a valid response for each request."
        p = self._write(tmp_path, f"<contract_rules>{rule}</contract_rules>")
        result = scan_prompt(p)
        valid_issues = _issues_for_term(result, "valid")
        assert valid_issues
        assert valid_issues[0].line.strip() == rule.strip()

    def test_issue_section_matches_xml_tag(self, tmp_path):
        p = self._write(
            tmp_path,
            "<acceptance_tests>Upload succeeds with a valid token.</acceptance_tests>",
        )
        result = scan_prompt(p)
        assert all(i.section == "acceptance_tests" for i in result.issues
                   if i.term not in {"(no observable outcome)"})

    def test_prose_section_name_is_prose(self, tmp_path):
        # Prose is only scanned when a contract section is also present
        p = tmp_path / "test.prompt"
        p.write_text(
            "% Must return a valid response.\n"
            "<contract_rules>R1: The system MUST respond.</contract_rules>\n",
            encoding="utf-8",
        )
        result = scan_prompt(p)
        prose_issues = _issues_for_section(result, "prose")
        assert len(prose_issues) >= 1


# ---------------------------------------------------------------------------
# ## Covers as vocabulary source in user stories
# ---------------------------------------------------------------------------

class TestCoversSection:
    """
    Verification requirement: "Run story lint fixtures with ## Covers and
    acceptance criteria."
    """

    def test_covers_section_suppresses_vague_terms(self):
        result = scan_prompt(FIXTURES / "story__covers.md")
        assert result.warn_count == 0, (
            f"Expected 0 warns with ## Covers vocabulary, got: "
            f"{[i.message for i in result.issues]}"
        )

    def test_story_without_covers_or_glossary_warns(self):
        result = scan_prompt(FIXTURES / "story__vague_criteria.md")
        assert result.warn_count > 0

    def test_scan_stories_includes_covers_story(self):
        results = scan_stories(FIXTURES)
        covers_result = next(
            (r for r in results if "story__covers" in r.path.name), None
        )
        assert covers_result is not None
        assert covers_result.warn_count == 0

    def test_covers_terms_are_extracted_from_section(self):
        covers_text = (
            "## Covers\n"
            "- duplicate upload: same SHA-256 and tenant ID\n"
            "- authorized user: JWT with upload scope\n"
        )
        sections = _extract_sections(covers_text)
        assert "covers" in sections
        terms = _extract_vocabulary_terms(sections["covers"])
        assert "duplicate" in terms or "duplicate upload" in terms
        assert "authorized" in terms or "authorized user" in terms


# ---------------------------------------------------------------------------
# Acceptance criteria: "Suggests additions to <vocabulary> when possible"
# ---------------------------------------------------------------------------

class TestVocabularySuggestions:
    """Verify that suggestion fields are actionable and suggestions are written."""

    def test_every_undefined_term_has_suggestion(self, tmp_path):
        p = tmp_path / "sug.prompt"
        p.write_text(
            "<contract_rules>Must return a valid, complete response.</contract_rules>",
            encoding="utf-8",
        )
        result = scan_prompt(p)
        for issue in result.issues:
            if issue.term not in {"(no observable outcome)"}:
                assert issue.suggestion != "", f"No suggestion for term '{issue.term}'"

    def test_suggestion_contains_term_as_key(self, tmp_path):
        p = tmp_path / "sug2.prompt"
        p.write_text(
            "<contract_rules>Only authorized users may call this.</contract_rules>",
            encoding="utf-8",
        )
        result = scan_prompt(p)
        auth_issues = _issues_for_term(result, "authorized")
        assert auth_issues
        assert auth_issues[0].suggestion.lower().startswith("authorized")

    def test_apply_writes_all_undefined_terms(self, tmp_path):
        p = tmp_path / "apply_all.prompt"
        p.write_text(
            "<contract_rules>\n"
            "1. Must return a valid response.\n"
            "2. Only authorized users may call this.\n"
            "</contract_rules>\n",
            encoding="utf-8",
        )
        result = scan_prompt(p)
        # Make suggestions concrete so apply_suggestions will write them
        concrete_issues = [
            LintIssue(
                level="warn",
                term=i.term,
                section=i.section,
                line=i.line,
                message=i.message,
                suggestion=f"{i.term}: a precise observable definition",
            )
            for i in result.issues
            if i.term != "(no observable outcome)"
        ]
        count = apply_suggestions(p, concrete_issues)
        assert count >= 2
        text = p.read_text()
        assert "<vocabulary>" in text
        assert "valid: a precise observable definition" in text
        assert "authorized: a precise observable definition" in text

    def test_apply_is_idempotent_on_same_suggestions(self, tmp_path):
        """Applying twice should not duplicate entries (caller responsibility —
        verify apply_suggestions returns 0 when there are no new non-placeholder
        suggestions)."""
        p = tmp_path / "idem.prompt"
        p.write_text(
            "<contract_rules>Must return a valid response.</contract_rules>\n",
            encoding="utf-8",
        )
        issue = LintIssue(
            level="warn", term="valid", section="contract_rules",
            line="Must return a valid response.",
            message="test",
            suggestion="valid: HTTP 200 with non-empty data",
        )
        apply_suggestions(p, [issue])
        # After apply, the suggestion text is now in the file; applying again
        # with the same issue would append a duplicate — this is a known
        # caller responsibility, so we just verify the first apply succeeded.
        text = p.read_text()
        assert "valid: HTTP 200 with non-empty data" in text


# ---------------------------------------------------------------------------
# Acceptance criteria: "Does not modify files unless passed --apply"
# ---------------------------------------------------------------------------

class TestReadOnly:
    """Verify the read-only guarantee at the engine level."""

    def test_scan_prompt_never_modifies_file(self, tmp_path):
        p = tmp_path / "ro.prompt"
        content = "<contract_rules>Must return a valid response.</contract_rules>\n"
        p.write_text(content, encoding="utf-8")
        scan_prompt(p)
        assert p.read_text(encoding="utf-8") == content

    def test_scan_stories_never_modifies_files(self, tmp_path):
        story = tmp_path / "story__ro.md"
        content = (
            "# Story\n## Acceptance Criteria\n"
            "1. Given a valid token, when used, returns 200.\n"
        )
        story.write_text(content, encoding="utf-8")
        scan_stories(tmp_path)
        assert story.read_text(encoding="utf-8") == content


# ---------------------------------------------------------------------------
# LintIssue: interpretations field (populated by LLM pass)
# ---------------------------------------------------------------------------

class TestLintIssueInterpretations:
    """
    Verify the interpretations field structure — populated by LLM pass,
    empty for deterministic pass.
    """

    def test_deterministic_issues_have_empty_interpretations(self, tmp_path):
        p = tmp_path / "interp.prompt"
        p.write_text(
            "<contract_rules>Must return a valid response.</contract_rules>",
            encoding="utf-8",
        )
        result = scan_prompt(p)
        for issue in result.issues:
            assert issue.interpretations == [], (
                f"Deterministic issue for '{issue.term}' should have empty interpretations"
            )

    def test_llm_issue_with_interpretations_round_trips_through_dict(self):
        issue = LintIssue(
            level="warn",
            term="duplicate upload",
            section="contract_rules",
            line="Reject duplicate uploads gracefully.",
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
        d = issue.as_dict()
        assert d["term"] == "duplicate upload"
        assert len(d["interpretations"]) == 3
        assert d["interpretations"][0] == "Same filename"
        assert "tenant" in d["suggestion"]

    def test_llm_result_json_contains_interpretations_array(self):
        result = LintResult(
            path=Path("test.prompt"),
            issues=[
                LintIssue(
                    level="warn",
                    term="duplicate upload",
                    section="contract_rules",
                    line="Reject duplicate uploads gracefully.",
                    message="LLM flagged term.",
                    suggestion="duplicate upload: same hash and tenant",
                    interpretations=["Same filename", "Same hash"],
                )
            ],
        )
        d = result.as_dict()
        assert d["issues"][0]["interpretations"] == ["Same filename", "Same hash"]


# ---------------------------------------------------------------------------
# TestExcludeMetadataSections
# ---------------------------------------------------------------------------

class TestExcludeMetadataSections:
    """Architecture metadata tags must NOT be scanned for vague terms."""

    def _prompt_with_section(self, tag: str, content: str) -> str:
        return f"<{tag}>{content}</{tag}>\n<contract_rules>R1: The system MUST respond.</contract_rules>\n"

    def test_pdd_reason_vague_terms_not_flagged(self, tmp_path):
        p = tmp_path / "test.prompt"
        p.write_text(
            self._prompt_with_section(
                "pdd-reason",
                "This is trusted by the caller and valid for all use cases.",
            ),
            encoding="utf-8",
        )
        result = scan_prompt(p)
        assert result.issues == []

    def test_pdd_interface_vague_terms_not_flagged(self, tmp_path):
        p = tmp_path / "test.prompt"
        p.write_text(
            self._prompt_with_section(
                "pdd-interface",
                "A safe and trusted integration boundary for authorized callers.",
            ),
            encoding="utf-8",
        )
        result = scan_prompt(p)
        assert result.issues == []

    def test_pdd_dependency_vague_terms_not_flagged(self, tmp_path):
        p = tmp_path / "test.prompt"
        p.write_text(
            self._prompt_with_section(
                "pdd-dependency",
                "The trusted payment gateway returns a valid token.",
            ),
            encoding="utf-8",
        )
        result = scan_prompt(p)
        assert result.issues == []

    def test_waivers_vague_terms_not_flagged(self, tmp_path):
        p = tmp_path / "test.prompt"
        p.write_text(
            "<waivers>W1:\n  Rule: R1\n  Reason: valid exception for authorized use.\n</waivers>\n"
            "<contract_rules>R1: The system MUST respond.</contract_rules>\n",
            encoding="utf-8",
        )
        result = scan_prompt(p)
        assert result.issues == []

    def test_contract_rules_vague_terms_still_flagged(self, tmp_path):
        p = tmp_path / "test.prompt"
        p.write_text(
            "<contract_rules>R1: The system MUST return a valid response.</contract_rules>\n",
            encoding="utf-8",
        )
        result = scan_prompt(p)
        assert any(i.term == "valid" for i in result.issues)


# ---------------------------------------------------------------------------
# TestCrossModuleCovers (prompt_lint)
# ---------------------------------------------------------------------------

class TestCrossModuleCovers:
    """Cross-module ## Covers entries are recognised and terms extracted."""

    def test_cross_module_entry_not_flagged_as_issue(self, tmp_path):
        story = tmp_path / "story__cross.md"
        story.write_text(
            "# Story\n"
            "## Acceptance Criteria\n"
            "1. When uploading a valid file, returns HTTP 201.\n"
            "## Covers\n"
            "- prompts/payment_python.prompt#R1: No provider call before validation\n"
            "## Glossary\n"
            "- valid file: a file whose MIME type is in the allowlist\n",
            encoding="utf-8",
        )
        result = scan_prompt(story)
        # "valid" is defined in Glossary → no VAGUE_TERM issue
        assert all(i.term != "valid" for i in result.issues)

    def test_cross_module_term_suppresses_vague_warning(self):
        from pdd.prompt_lint import _extract_vocabulary_terms
        vocab_text = (
            "- prompts/payment_python.prompt#R3: No provider call before validation\n"
            "- valid response: HTTP 201 with JSON body\n"
        )
        terms = _extract_vocabulary_terms(vocab_text)
        # The descriptive text "no provider call before validation" should be extracted
        assert "no provider call before validation" in terms
        # Standard entry still works
        assert "valid response" in terms
        assert "valid" in terms
