"""Unit tests for pdd.contract_check (deterministic pass, no LLM calls)."""
from __future__ import annotations

from datetime import date
from pathlib import Path

import pytest

from pdd.contract_check import (
    ContractIssue,
    ContractResult,
    Rule,
    Waiver,
    _check_capabilities_modals,
    _check_coverage_entries,
    _check_duplicate_ids,
    _check_malformed_ids,
    _check_missing_modal,
    _check_must_not_coverage,
    _check_sequential_ids,
    _check_story_covers,
    _check_vague_terms,
    _check_waivers,
    _extract_rules,
    _extract_waivers,
    check_directory,
    check_prompt,
    check_stories,
)

FIXTURES = Path(__file__).parent / "fixtures" / "contract_check"


# ---------------------------------------------------------------------------
# Helpers
# ---------------------------------------------------------------------------

def _issues_for_code(result: ContractResult, code: str) -> list[ContractIssue]:
    return [i for i in result.issues if i.code == code]


def _issues_for_rule(result: ContractResult, rule_id: str) -> list[ContractIssue]:
    return [i for i in result.issues if i.rule_id == rule_id]


def _rule(raw_id: str, num: int | None, modal: str, line: str,
          is_must_not: bool = False) -> Rule:
    """Convenience constructor so tests don't need to pass block=."""
    return Rule(raw_id=raw_id, num=num, modal=modal, line=line,
                block=line, is_must_not=is_must_not)


# ---------------------------------------------------------------------------
# TestExtractRules
# ---------------------------------------------------------------------------

class TestExtractRules:
    def test_explicit_r_ids_no_dash(self):
        text = (
            "R1: The system MUST reject duplicates.\n"
            "R2: The system MAY log attempts.\n"
        )
        rules = _extract_rules(text)
        assert len(rules) == 2
        assert rules[0].raw_id == "R1"
        assert rules[1].raw_id == "R2"

    def test_explicit_r_ids_with_dash(self):
        text = (
            "R-001: The system MUST reject duplicates.\n"
            "R-002: The system MAY log attempts.\n"
        )
        rules = _extract_rules(text)
        assert len(rules) == 2
        assert rules[0].raw_id == "R-001"
        assert rules[1].raw_id == "R-002"

    def test_rule_ids_are_normalised_uppercase(self):
        rules = _extract_rules("rule-003: The service MUST respond.\n")
        assert rules[0].raw_id == "RULE-003"

    def test_sequential_ids(self):
        text = "1. The system MUST accept uploads.\n2. The system MUST log requests.\n"
        rules = _extract_rules(text)
        assert rules[0].raw_id == "S-001"
        assert rules[1].raw_id == "S-002"
        assert rules[0].num == 1
        assert rules[1].num == 2

    def test_unnumbered_bullet_rules(self):
        text = "- The system MUST reject unauthorized requests.\n"
        rules = _extract_rules(text)
        assert rules[0].raw_id == "(unnumbered)"

    def test_modal_extracted_must(self):
        rules = _extract_rules("R1: The system MUST reject duplicates.\n")
        assert rules[0].modal == "MUST"

    def test_modal_extracted_must_not(self):
        rules = _extract_rules("R1: The system MUST NOT expose secrets.\n")
        assert rules[0].modal == "MUST NOT"
        assert rules[0].is_must_not is True

    def test_modal_extracted_may(self):
        rules = _extract_rules("R1: The service MAY cache results.\n")
        assert rules[0].modal == "MAY"

    def test_modal_extracted_should(self):
        rules = _extract_rules("R1: The system SHOULD log requests.\n")
        assert rules[0].modal == "SHOULD"

    def test_no_modal_produces_empty_string(self):
        rules = _extract_rules("R1: The system rejects requests.\n")
        assert rules[0].modal == ""

    def test_empty_text_returns_no_rules(self):
        assert _extract_rules("") == []

    def test_blank_lines_skipped(self):
        text = "\n\nR1: The system MUST respond.\n\n"
        rules = _extract_rules(text)
        assert len(rules) == 1


# ---------------------------------------------------------------------------
# TestMultiLineRules
# ---------------------------------------------------------------------------

class TestMultiLineRules:
    def test_multiline_block_single_rule(self):
        text = (
            "R1 - Reject duplicate uploads\n"
            "\n"
            "For every POST /upload request,\n"
            "the system MUST reject the request\n"
            "when the SHA-256 hash matches an existing upload.\n"
            "\n"
            "This rule is violated if HTTP 200 is returned.\n"
        )
        rules = _extract_rules(text)
        assert len(rules) == 1
        assert rules[0].raw_id == "R1"
        assert rules[0].modal == "MUST"
        assert "SHA-256" in rules[0].block

    def test_multiline_modal_on_continuation_line(self):
        text = (
            "R1 - Validate before calling provider\n"
            "\n"
            "The service MUST NOT call the provider\n"
            "before file type validation passes.\n"
        )
        rules = _extract_rules(text)
        assert len(rules) == 1
        assert rules[0].is_must_not is True

    def test_two_multiline_blocks(self):
        text = (
            "R1 - First rule\n"
            "\n"
            "The system MUST do X.\n"
            "\n"
            "\n"
            "R2 - Second rule\n"
            "\n"
            "The system MUST NOT do Y.\n"
        )
        rules = _extract_rules(text)
        assert len(rules) == 2
        assert rules[0].raw_id == "R1"
        assert rules[1].raw_id == "R2"
        assert rules[1].is_must_not is True

    def test_header_line_captured(self):
        text = "R1 - Reject duplicate uploads\nThe system MUST reject duplicates.\n"
        rules = _extract_rules(text)
        assert rules[0].line == "R1 - Reject duplicate uploads"


# ---------------------------------------------------------------------------
# TestCheckDuplicateIds
# ---------------------------------------------------------------------------

class TestCheckDuplicateIds:
    def test_duplicate_id_produces_error(self):
        rules = [
            _rule("R1", 1, "MUST", "R1: The system MUST accept uploads."),
            _rule("R2", 2, "MUST", "R2: The system MUST log."),
            _rule("R1", 1, "MUST", "R1: The system MUST also reject."),
        ]
        issues = _check_duplicate_ids(rules)
        assert len(issues) == 1
        assert issues[0].code == "DUPLICATE_ID"
        assert issues[0].rule_id == "R1"
        assert issues[0].level == "error"

    def test_no_duplicates_returns_empty(self):
        rules = [
            _rule("R1", 1, "MUST", "R1: The system MUST accept."),
            _rule("R2", 2, "MUST", "R2: The system MUST log."),
        ]
        assert _check_duplicate_ids(rules) == []

    def test_unnumbered_rules_not_flagged(self):
        rules = [
            _rule("(unnumbered)", None, "MUST", "- The system MUST accept."),
            _rule("(unnumbered)", None, "MUST", "- The system MUST log."),
        ]
        assert _check_duplicate_ids(rules) == []

    def test_fixture_duplicate_ids(self):
        result = check_prompt(FIXTURES / "duplicate_ids_python.prompt")
        dups = _issues_for_code(result, "DUPLICATE_ID")
        assert len(dups) >= 1
        assert dups[0].rule_id == "R1"

    def test_fixture_valid_no_duplicates(self):
        result = check_prompt(FIXTURES / "valid_contract_python.prompt")
        assert _issues_for_code(result, "DUPLICATE_ID") == []


# ---------------------------------------------------------------------------
# TestCheckMalformedIds
# ---------------------------------------------------------------------------

class TestCheckMalformedIds:
    def test_rr_prefix_is_malformed(self):
        issues = _check_malformed_ids("RR-01: The system MUST reject requests.\n")
        assert any(i.code == "MALFORMED_ID" for i in issues)

    def test_underscore_separator_is_malformed(self):
        issues = _check_malformed_ids("R_002: The system MUST log.\n")
        assert any(i.code == "MALFORMED_ID" for i in issues)

    def test_valid_r_no_dash_not_flagged(self):
        issues = _check_malformed_ids("R1: The system MUST respond.\n")
        assert issues == []

    def test_valid_r_dash_not_flagged(self):
        issues = _check_malformed_ids("R-001: The system MUST respond.\n")
        assert issues == []

    def test_sequential_number_not_flagged(self):
        issues = _check_malformed_ids("1. The system MUST respond.\n")
        assert issues == []

    def test_bullet_not_flagged(self):
        issues = _check_malformed_ids("- The system MUST respond.\n")
        assert issues == []

    def test_fixture_malformed_ids(self):
        result = check_prompt(FIXTURES / "malformed_ids_python.prompt")
        malformed = _issues_for_code(result, "MALFORMED_ID")
        assert len(malformed) >= 2


# ---------------------------------------------------------------------------
# TestCheckSequentialIds
# ---------------------------------------------------------------------------

class TestCheckSequentialIds:
    def test_gap_produces_warn(self):
        rules = [
            _rule("R1", 1, "MUST", "R1: ..."),
            _rule("R3", 3, "MUST", "R3: ..."),
        ]
        issues = _check_sequential_ids(rules)
        assert len(issues) == 1
        assert issues[0].code == "NON_SEQUENTIAL_ID"
        assert issues[0].level == "warn"

    def test_sequential_produces_no_issues(self):
        rules = [
            _rule("R1", 1, "MUST", "R1: ..."),
            _rule("R2", 2, "MUST", "R2: ..."),
            _rule("R3", 3, "MUST", "R3: ..."),
        ]
        assert _check_sequential_ids(rules) == []

    def test_unnumbered_rules_ignored(self):
        rules = [_rule("(unnumbered)", None, "MUST", "- ...")]
        assert _check_sequential_ids(rules) == []

    def test_fixture_non_sequential(self):
        result = check_prompt(FIXTURES / "non_sequential_ids_python.prompt")
        gaps = _issues_for_code(result, "NON_SEQUENTIAL_ID")
        assert len(gaps) >= 1
        assert gaps[0].level == "warn"


# ---------------------------------------------------------------------------
# TestCheckMissingModal
# ---------------------------------------------------------------------------

class TestCheckMissingModal:
    def test_rule_without_modal_produces_issue(self):
        rules = [_rule("R1", 1, "", "R1: The system rejects duplicates.")]
        issues = _check_missing_modal(rules, strict=False)
        assert len(issues) == 1
        assert issues[0].code == "MISSING_MODAL"
        assert issues[0].level == "warn"

    def test_rule_with_modal_produces_no_issue(self):
        rules = [_rule("R1", 1, "MUST", "R1: The system MUST reject duplicates.")]
        assert _check_missing_modal(rules, strict=False) == []

    def test_strict_escalates_to_error(self):
        rules = [_rule("R1", 1, "", "R1: The system rejects duplicates.")]
        issues = _check_missing_modal(rules, strict=True)
        assert issues[0].level == "error"

    def test_fixture_missing_modal(self):
        result = check_prompt(FIXTURES / "missing_modal_python.prompt")
        missing = _issues_for_code(result, "MISSING_MODAL")
        assert len(missing) >= 2  # R1, R2, and R4 lack modals


# ---------------------------------------------------------------------------
# TestCheckVagueTerms
# ---------------------------------------------------------------------------

class TestCheckVagueTerms:
    def test_undefined_vague_term_warns(self):
        issues = _check_vague_terms(
            "R1: The system MUST return a valid response.",
            vocab_terms=set(),
            strict=False,
        )
        assert any(i.code == "VAGUE_TERM" and i.term == "valid" for i in issues)

    def test_defined_term_suppresses_warning(self):
        issues = _check_vague_terms(
            "R1: The system MUST return a valid response.",
            vocab_terms={"valid", "response", "valid response"},
            strict=False,
        )
        assert issues == []

    def test_fixture_vague_no_vocab_warns(self):
        result = check_prompt(FIXTURES / "vague_no_vocab_python.prompt")
        vague = _issues_for_code(result, "VAGUE_TERM")
        assert len(vague) >= 3

    def test_fixture_vague_with_vocab_clean(self):
        result = check_prompt(FIXTURES / "vague_with_vocab_python.prompt")
        vague = _issues_for_code(result, "VAGUE_TERM")
        assert vague == []


# ---------------------------------------------------------------------------
# TestCheckCoverageEntries  (replaces TestCheckCoverageRefs)
# ---------------------------------------------------------------------------

class TestCheckCoverageEntries:
    def test_unknown_ref_produces_error(self):
        issues = _check_coverage_entries(
            "- R99: some test\n",
            known_ids={"R1", "R2"},
            known_waiver_ids=set(),
        )
        assert len(issues) == 1
        assert issues[0].code == "UNKNOWN_COVERAGE_REF"
        assert issues[0].level == "error"
        assert issues[0].rule_id == "R99"

    def test_known_ref_produces_no_issue(self):
        issues = _check_coverage_entries(
            "- R1: test_upload\n",
            known_ids={"R1", "R2"},
            known_waiver_ids=set(),
        )
        assert issues == []

    def test_todo_entry_produces_unchecked_warn(self):
        issues = _check_coverage_entries(
            "- R2: TODO add idempotency story\n",
            known_ids={"R1", "R2"},
            known_waiver_ids=set(),
        )
        assert len(issues) == 1
        assert issues[0].code == "UNCHECKED_RULE"
        assert issues[0].level == "warn"
        assert issues[0].rule_id == "R2"

    def test_waived_known_waiver_produces_no_issue(self):
        issues = _check_coverage_entries(
            "- R2: WAIVED W1\n",
            known_ids={"R1", "R2"},
            known_waiver_ids={"W1"},
        )
        assert issues == []

    def test_waived_unknown_waiver_produces_error(self):
        issues = _check_coverage_entries(
            "- R2: WAIVED W99\n",
            known_ids={"R1", "R2"},
            known_waiver_ids={"W1"},
        )
        assert len(issues) == 1
        assert issues[0].code == "WAIVER_REF_MISSING"
        assert issues[0].level == "error"

    def test_fixture_unknown_coverage_ref(self):
        result = check_prompt(FIXTURES / "unknown_coverage_refs_python.prompt")
        refs = _issues_for_code(result, "UNKNOWN_COVERAGE_REF")
        assert len(refs) >= 1
        assert any(i.rule_id == "R99" for i in refs)

    def test_fixture_valid_coverage_refs(self):
        result = check_prompt(FIXTURES / "with_coverage_python.prompt")
        refs = _issues_for_code(result, "UNKNOWN_COVERAGE_REF")
        assert refs == []

    def test_fixture_unchecked_rule(self):
        result = check_prompt(FIXTURES / "coverage_unchecked_python.prompt")
        unchecked = _issues_for_code(result, "UNCHECKED_RULE")
        assert len(unchecked) >= 1
        assert any(i.rule_id == "R2" for i in unchecked)

    def test_fixture_waiver_ref_missing(self):
        result = check_prompt(FIXTURES / "waiver_ref_missing_python.prompt")
        refs = _issues_for_code(result, "WAIVER_REF_MISSING")
        assert len(refs) >= 1


# ---------------------------------------------------------------------------
# TestCheckMustNotCoverage
# ---------------------------------------------------------------------------

class TestCheckMustNotCoverage:
    def test_uncovered_must_not_warns(self):
        rules = [
            _rule("R1", 1, "MUST", "R1: The system MUST accept."),
            _rule("R2", 2, "MUST NOT", "R2: The system MUST NOT expose secrets.",
                  is_must_not=True),
        ]
        issues = _check_must_not_coverage(rules, "- R1: some_test\n")
        assert len(issues) == 1
        assert issues[0].code == "UNCOVERED_MUST_NOT"
        assert issues[0].rule_id == "R2"
        assert issues[0].level == "warn"

    def test_covered_must_not_no_issue(self):
        rules = [
            _rule("R1", 1, "MUST NOT", "R1: The system MUST NOT expose secrets.",
                  is_must_not=True),
        ]
        issues = _check_must_not_coverage(rules, "- R1: test_secrets_not_exposed\n")
        assert issues == []

    def test_unnumbered_must_not_skipped(self):
        rules = [
            _rule("(unnumbered)", None, "MUST NOT",
                  "- The system MUST NOT expose secrets.", is_must_not=True),
        ]
        assert _check_must_not_coverage(rules, "") == []

    def test_fixture_uncovered_must_not(self):
        result = check_prompt(FIXTURES / "uncovered_mustnot_python.prompt")
        uncovered = _issues_for_code(result, "UNCOVERED_MUST_NOT")
        assert len(uncovered) >= 1
        assert any(i.rule_id == "R2" for i in uncovered)

    def test_fixture_all_covered_no_issue(self):
        result = check_prompt(FIXTURES / "with_coverage_python.prompt")
        uncovered = _issues_for_code(result, "UNCOVERED_MUST_NOT")
        assert uncovered == []


# ---------------------------------------------------------------------------
# TestCheckWaivers
# ---------------------------------------------------------------------------

class TestCheckWaivers:
    def test_expired_waiver_warns(self):
        text = (
            "W1:\n"
            "  Rule: R2\n"
            "  Status: temporary\n"
            "  Reason: Test fixture not available.\n"
            "  Approved by: security-review\n"
            "  Expires: 2020-01-01\n"
            "  Follow-up: Add test.\n"
        )
        issues = _check_waivers(text)
        expired = [i for i in issues if i.code == "EXPIRED_WAIVER"]
        assert len(expired) == 1
        assert expired[0].rule_id == "W1"
        assert expired[0].level == "warn"

    def test_future_expiry_no_issue(self):
        text = (
            "W1:\n"
            "  Rule: R2\n"
            "  Status: temporary\n"
            "  Reason: Test fixture not available.\n"
            "  Approved by: security-review\n"
            "  Expires: 2099-01-01\n"
            "  Follow-up: Add test.\n"
        )
        issues = _check_waivers(text)
        expired = [i for i in issues if i.code == "EXPIRED_WAIVER"]
        assert expired == []

    def test_missing_required_fields_warns(self):
        text = (
            "W1:\n"
            "  Rule: R2\n"
            "  Status: temporary\n"
            "  Reason: Test fixture not available.\n"
        )
        issues = _check_waivers(text)
        missing = [i for i in issues if i.code == "MISSING_WAIVER_FIELDS"]
        assert len(missing) >= 1
        assert "approved by" in missing[0].message.lower() or "expires" in missing[0].message.lower()

    def test_fixture_expired_waiver(self):
        result = check_prompt(FIXTURES / "waiver_expired_python.prompt")
        expired = _issues_for_code(result, "EXPIRED_WAIVER")
        assert len(expired) >= 1

    def test_fixture_missing_waiver_fields(self):
        result = check_prompt(FIXTURES / "waiver_missing_fields_python.prompt")
        missing = _issues_for_code(result, "MISSING_WAIVER_FIELDS")
        assert len(missing) >= 1

    def test_fixture_valid_waiver_no_issues(self):
        result = check_prompt(FIXTURES / "waiver_valid_python.prompt")
        assert result.warn_count == 0
        assert result.error_count == 0


# ---------------------------------------------------------------------------
# TestCheckCapabilitiesModals
# ---------------------------------------------------------------------------

class TestCheckCapabilitiesModals:
    def test_line_without_modal_warns(self):
        text = "- Stores files in S3-compatible object storage.\n"
        issues = _check_capabilities_modals(text)
        assert len(issues) == 1
        assert issues[0].code == "MISSING_MODAL"
        assert issues[0].section == "capabilities"
        assert issues[0].level == "warn"

    def test_line_with_may_no_issue(self):
        text = "- MAY accept multipart/form-data POST requests.\n"
        issues = _check_capabilities_modals(text)
        assert issues == []

    def test_line_with_must_not_no_issue(self):
        text = "- MUST NOT expose internal stack traces.\n"
        issues = _check_capabilities_modals(text)
        assert issues == []

    def test_blank_lines_skipped(self):
        text = "\n- MAY read from S3.\n\n"
        issues = _check_capabilities_modals(text)
        assert issues == []

    def test_comment_lines_skipped(self):
        text = "# This is a comment\n- MAY read files.\n"
        issues = _check_capabilities_modals(text)
        assert issues == []

    def test_fixture_capabilities_no_modal(self):
        result = check_prompt(FIXTURES / "capabilities_no_modal_python.prompt")
        missing = _issues_for_code(result, "MISSING_MODAL")
        cap_missing = [i for i in missing if i.section == "capabilities"]
        assert len(cap_missing) >= 1

    def test_fixture_valid_capabilities_no_missing_modal(self):
        result = check_prompt(FIXTURES / "valid_contract_python.prompt")
        cap_missing = [i for i in result.issues
                       if i.code == "MISSING_MODAL" and i.section == "capabilities"]
        assert cap_missing == []


# ---------------------------------------------------------------------------
# TestCheckStoryCovers
# ---------------------------------------------------------------------------

class TestCheckStoryCovers:
    def _story(self, covers_lines: str) -> str:
        return (
            "# Story\n"
            "<!-- pdd-story-prompts: test_prompt.prompt -->\n"
            "## Acceptance Criteria\n"
            "1. Given X, when Y, then Z.\n"
            f"## Covers\n{covers_lines}\n"
        )

    def test_known_rule_id_no_issue(self):
        text = self._story("- R1: duplicate upload rejection\n")
        issues = _check_story_covers(
            text, Path("story.md"), {"test_prompt.prompt": {"R1", "R2"}}
        )
        assert issues == []

    def test_unknown_rule_id_warns(self):
        text = self._story("- R99: this does not exist\n")
        issues = _check_story_covers(
            text, Path("story.md"), {"test_prompt.prompt": {"R1", "R2"}}
        )
        assert len(issues) == 1
        assert issues[0].code == "UNKNOWN_STORY_REF"
        assert issues[0].rule_id == "R99"
        assert issues[0].level == "warn"

    def test_no_covers_section_returns_empty(self):
        text = "# Story\n## Acceptance Criteria\n1. Given X.\n"
        assert _check_story_covers(text, Path("story.md"), {}) == []

    def test_no_linked_prompts_skips_id_check(self):
        text = self._story("- R99 from unknown.prompt\n")
        issues = _check_story_covers(text, Path("story.md"), None)
        assert issues == []

    def test_fixture_valid_story(self):
        results = check_stories(FIXTURES, FIXTURES)
        valid = next((r for r in results if "story__covers_rule_ids" in r.path.name), None)
        assert valid is not None
        assert _issues_for_code(valid, "UNKNOWN_STORY_REF") == []

    def test_fixture_unknown_story_ids(self):
        results = check_stories(FIXTURES, FIXTURES)
        invalid = next(
            (r for r in results if "story__unknown_rule_ids" in r.path.name), None
        )
        assert invalid is not None
        assert len(_issues_for_code(invalid, "UNKNOWN_STORY_REF")) >= 1


# ---------------------------------------------------------------------------
# TestCrossModuleCovers
# ---------------------------------------------------------------------------

class TestCrossModuleCovers:
    def _story(self, covers_lines: str, prompt_file: str = "test_prompt.prompt") -> str:
        return (
            f"# Story\n"
            f"<!-- pdd-story-prompts: {prompt_file} -->\n"
            "## Acceptance Criteria\n"
            "1. Given X, when Y, then Z.\n"
            f"## Covers\n{covers_lines}\n"
        )

    def test_cross_module_known_id_no_issue(self):
        text = self._story("- test_prompt.prompt#R1: Reject duplicates\n")
        issues = _check_story_covers(
            text, Path("story.md"), {"test_prompt.prompt": {"R1", "R2"}}
        )
        assert issues == []

    def test_cross_module_unknown_id_warns(self):
        text = self._story("- test_prompt.prompt#R99: does not exist\n")
        issues = _check_story_covers(
            text, Path("story.md"), {"test_prompt.prompt": {"R1", "R2"}}
        )
        assert len(issues) == 1
        assert issues[0].code == "UNKNOWN_STORY_REF"
        assert issues[0].rule_id == "R99"

    def test_fixture_cross_module_story_no_issues(self):
        results = check_stories(FIXTURES, FIXTURES)
        cross = next(
            (r for r in results if "story__cross_module_covers" in r.path.name), None
        )
        assert cross is not None
        assert _issues_for_code(cross, "UNKNOWN_STORY_REF") == []


# ---------------------------------------------------------------------------
# TestExtractWaivers
# ---------------------------------------------------------------------------

class TestExtractWaivers:
    def test_parses_single_waiver(self):
        text = (
            "W1:\n"
            "  Rule: R6\n"
            "  Status: temporary\n"
            "  Reason: Provider error fixture not available.\n"
            "  Approved by: security-review\n"
            "  Expires: 2099-06-01\n"
            "  Follow-up: Add test.\n"
        )
        waivers = _extract_waivers(text)
        assert len(waivers) == 1
        w = waivers[0]
        assert w.raw_id == "W1"
        assert w.rule_id == "R6"
        assert w.approved_by == "security-review"
        assert w.expires == date(2099, 6, 1)

    def test_parses_multiple_waivers(self):
        text = (
            "W1:\n  Rule: R1\n  Reason: A\n  Approved by: x\n  Expires: 2099-01-01\n"
            "W2:\n  Rule: R2\n  Reason: B\n  Approved by: y\n  Expires: 2099-02-01\n"
        )
        waivers = _extract_waivers(text)
        assert len(waivers) == 2
        assert waivers[0].raw_id == "W1"
        assert waivers[1].raw_id == "W2"

    def test_invalid_expires_handled_gracefully(self):
        text = (
            "W1:\n  Rule: R1\n  Reason: A\n"
            "  Approved by: x\n  Expires: not-a-date\n"
        )
        waivers = _extract_waivers(text)
        assert len(waivers) == 1
        assert waivers[0].expires is None


# ---------------------------------------------------------------------------
# TestCheckPromptFixtures (integration)
# ---------------------------------------------------------------------------

class TestCheckPromptFixtures:
    def test_valid_contract_produces_no_issues(self):
        result = check_prompt(FIXTURES / "valid_contract_python.prompt")
        assert result.warn_count == 0
        assert result.error_count == 0

    def test_valid_contract_result_path_set(self):
        result = check_prompt(FIXTURES / "valid_contract_python.prompt")
        assert result.path == FIXTURES / "valid_contract_python.prompt"

    def test_duplicate_ids_error_count_positive(self):
        result = check_prompt(FIXTURES / "duplicate_ids_python.prompt")
        assert result.error_count >= 1

    def test_malformed_ids_error_count_positive(self):
        result = check_prompt(FIXTURES / "malformed_ids_python.prompt")
        assert result.error_count >= 2

    def test_non_sequential_warn_count_positive(self):
        result = check_prompt(FIXTURES / "non_sequential_ids_python.prompt")
        assert result.warn_count >= 1

    def test_missing_modal_issues_present(self):
        result = check_prompt(FIXTURES / "missing_modal_python.prompt")
        assert len(_issues_for_code(result, "MISSING_MODAL")) >= 2

    def test_legacy_prompt_zero_issues(self):
        result = check_prompt(FIXTURES / "legacy_no_sections_python.prompt")
        assert result.warn_count == 0
        assert result.error_count == 0

    def test_strict_escalates_warns_to_errors(self):
        result_normal = check_prompt(FIXTURES / "non_sequential_ids_python.prompt")
        result_strict = check_prompt(FIXTURES / "non_sequential_ids_python.prompt",
                                     strict=True)
        assert result_normal.warn_count > 0
        assert result_strict.error_count >= result_normal.warn_count
        assert result_strict.warn_count == 0

    def test_missing_file_returns_error_issue(self):
        result = check_prompt(FIXTURES / "does_not_exist.prompt")
        assert result.error_count >= 1
        assert any(i.code == "FILE_NOT_FOUND" for i in result.issues)


# ---------------------------------------------------------------------------
# TestCheckDirectory
# ---------------------------------------------------------------------------

class TestCheckDirectory:
    def test_scans_all_prompt_files(self):
        results = check_directory(FIXTURES)
        paths = {r.path.name for r in results}
        assert "valid_contract_python.prompt" in paths
        assert "duplicate_ids_python.prompt" in paths

    def test_empty_dir_returns_empty(self, tmp_path):
        assert check_directory(tmp_path) == []

    def test_legacy_prompt_included_but_clean(self):
        results = check_directory(FIXTURES)
        legacy = next(r for r in results if r.path.name == "legacy_no_sections_python.prompt")
        assert legacy.warn_count == 0
        assert legacy.error_count == 0


# ---------------------------------------------------------------------------
# TestReadOnly
# ---------------------------------------------------------------------------

class TestReadOnly:
    def test_check_prompt_never_modifies_file(self, tmp_path):
        p = tmp_path / "ro.prompt"
        content = (
            "<contract_rules>\n"
            "R1: The system MUST accept uploads.\n"
            "</contract_rules>\n"
        )
        p.write_text(content, encoding="utf-8")
        check_prompt(p)
        assert p.read_text(encoding="utf-8") == content

    def test_check_stories_never_modifies_files(self, tmp_path):
        s = tmp_path / "story__ro.md"
        content = (
            "# Story\n## Covers\n- R1: foo\n"
        )
        s.write_text(content, encoding="utf-8")
        check_stories(tmp_path)
        assert s.read_text(encoding="utf-8") == content


# ---------------------------------------------------------------------------
# TestContractIssueAndResult
# ---------------------------------------------------------------------------

class TestContractIssueAndResult:
    def test_issue_as_dict_has_all_keys(self):
        issue = ContractIssue(
            level="error",
            code="DUPLICATE_ID",
            rule_id="R1",
            section="contract_rules",
            line="R1: The system MUST ...",
            message="Duplicate.",
        )
        d = issue.as_dict()
        for key in ("level", "code", "rule_id", "section", "line", "message",
                    "suggestion", "interpretations"):
            assert key in d

    def test_result_as_dict_has_required_keys(self):
        result = ContractResult(path=Path("test.prompt"))
        d = result.as_dict()
        for key in ("path", "warn_count", "error_count", "issues"):
            assert key in d

    def test_result_counts_are_correct(self):
        result = ContractResult(path=Path("test.prompt"), issues=[
            ContractIssue("warn", "VAGUE_TERM", "", "contract_rules", "", ""),
            ContractIssue("error", "DUPLICATE_ID", "R1", "contract_rules", "", ""),
            ContractIssue("warn", "MISSING_MODAL", "R2", "contract_rules", "", ""),
        ])
        assert result.warn_count == 2
        assert result.error_count == 1

    def test_llm_issue_round_trips(self):
        issue = ContractIssue(
            level="warn",
            code="LLM_AMBIGUITY",
            rule_id="",
            section="llm",
            line="",
            message='LLM flagged "duplicate" as ambiguous.',
            suggestion="duplicate upload: same hash and tenant",
            interpretations=["Same filename", "Same hash", "Same tenant + hash"],
        )
        d = issue.as_dict()
        assert d["interpretations"] == ["Same filename", "Same hash", "Same tenant + hash"]
        assert "tenant" in d["suggestion"]


# ---------------------------------------------------------------------------
# TestRealPromptLegacySafety
# ---------------------------------------------------------------------------

class TestRealPromptLegacySafety:
    """Existing real prompts must never hard-fail (exit 0 or warns only, no errors)."""

    def test_bundled_prompts_no_errors(self):
        pdd_prompts = Path(__file__).parents[1] / "pdd" / "prompts"
        for p in pdd_prompts.glob("*.prompt"):
            result = check_prompt(p)
            assert result.error_count == 0, (
                f"{p.name} produced {result.error_count} error(s): "
                f"{[i.message for i in result.issues if i.level == 'error']}"
            )
