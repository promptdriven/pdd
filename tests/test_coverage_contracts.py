"""
Unit tests for pdd.coverage_contracts.

Covers:
  - Section extraction (_extract_sections, _extract_markdown_section)
  - Rule ID parsing (_parse_rule_ids)
  - Waiver map parsing (_parse_waiver_rule_map)
  - Coverage block parsing (_parse_coverage_block)
  - Story evidence scanning (scan_story_evidence)
  - Test file heuristic scanning (scan_test_evidence, _scan_test_file)
  - Status classification (_classify_rule)
  - Public API (build_coverage, build_coverage_directory)
  - Legacy safety (no <contract_rules> → empty result)
"""
from __future__ import annotations

import textwrap
from pathlib import Path

import pytest

from pdd.coverage_contracts import (
    STATUS_CHECKED,
    STATUS_STORY_ONLY,
    STATUS_TEST_ONLY,
    STATUS_UNCHECKED,
    STATUS_WAIVED,
    STATUS_FAILED,
    CoverageResult,
    RuleCoverage,
    _classify_rule,
    _extract_markdown_section,
    _extract_sections,
    _parse_coverage_block,
    _parse_rule_ids,
    _parse_waiver_rule_map,
    _rule_ids_from_covers,
    _scan_test_file,
    _story_links_prompt,
    build_coverage,
    build_coverage_directory,
    scan_story_validation_failures,
    scan_story_evidence,
    scan_test_evidence,
    scan_test_validation_failures,
)

# ---------------------------------------------------------------------------
# Helpers
# ---------------------------------------------------------------------------

FIXTURES = Path(__file__).parent / "fixtures" / "coverage_contracts"


def _make_prompt(tmp_path: Path, content: str, name: str = "test_python.prompt") -> Path:
    p = tmp_path / name
    p.write_text(textwrap.dedent(content), encoding="utf-8")
    return p


def _make_story(tmp_path: Path, content: str, name: str = "story__test.md") -> Path:
    p = tmp_path / name
    p.write_text(textwrap.dedent(content), encoding="utf-8")
    return p


def _make_test_file(tmp_path: Path, content: str, name: str = "test_foo.py") -> Path:
    p = tmp_path / name
    p.write_text(textwrap.dedent(content), encoding="utf-8")
    return p


# ===========================================================================
# Section extraction
# ===========================================================================

class TestExtractSections:
    def test_single_section(self):
        text = "<contract_rules>\nR1: The system MUST do X.\n</contract_rules>"
        sections = _extract_sections(text)
        assert "contract_rules" in sections
        assert "R1" in sections["contract_rules"]

    def test_multiple_sections(self):
        text = (
            "<contract_rules>\nR1: MUST X\n</contract_rules>\n"
            "<vocabulary>\nfoo: bar\n</vocabulary>"
        )
        sections = _extract_sections(text)
        assert "contract_rules" in sections
        assert "vocabulary" in sections

    def test_tag_normalised_to_lowercase(self):
        text = "<Contract_Rules>\nR1: MUST do\n</Contract_Rules>"
        sections = _extract_sections(text)
        assert "contract_rules" in sections

    def test_empty_section(self):
        text = "<coverage></coverage>"
        sections = _extract_sections(text)
        assert sections.get("coverage", "") == ""

    def test_no_sections_returns_empty_dict(self):
        assert _extract_sections("no xml here") == {}

    def test_unknown_section_tags_included(self):
        text = "<custom_section>\ndata\n</custom_section>"
        sections = _extract_sections(text)
        assert "custom_section" in sections


class TestExtractMarkdownSection:
    def test_h2_section(self):
        text = "## Covers\n- R1: rule\n## Notes\nfoo"
        result = _extract_markdown_section(text, "Covers")
        assert "R1" in result
        assert "Notes" not in result

    def test_h3_section(self):
        text = "### Covers\n- R2: rule\n### Notes\nfoo"
        result = _extract_markdown_section(text, "Covers")
        assert "R2" in result

    def test_missing_section_returns_empty(self):
        assert _extract_markdown_section("no covers here", "Covers") == ""

    def test_case_insensitive(self):
        text = "## COVERS\n- R1: rule\n"
        result = _extract_markdown_section(text, "covers")
        assert "R1" in result

    def test_section_at_end_of_file(self):
        text = "## Notes\nfoo\n## Covers\n- R3: rule"
        result = _extract_markdown_section(text, "Covers")
        assert "R3" in result


# ===========================================================================
# Rule ID parsing
# ===========================================================================

class TestParseRuleIds:
    def test_explicit_r_ids(self):
        text = "R1 - Rule one\nR2 - Rule two\nR3 - Rule three"
        ids = _parse_rule_ids(text)
        assert ids == ["R1", "R2", "R3"]

    def test_dashed_ids(self):
        text = "R-001 - First rule\nR-002 - Second rule"
        ids = _parse_rule_ids(text)
        assert ids == ["R-001", "R-002"]

    def test_sequential_ids(self):
        text = "1. MUST do A\n2. MUST do B"
        ids = _parse_rule_ids(text)
        assert ids == ["S-001", "S-002"]

    def test_mixed_content_skips_blank_and_prose(self):
        text = "R1 - Rule A\n\nSome prose here.\n\nR2 - Rule B"
        ids = _parse_rule_ids(text)
        assert ids == ["R1", "R2"]

    def test_duplicate_ids_deduplicated(self):
        text = "R1 - First\nR1 - Duplicate"
        ids = _parse_rule_ids(text)
        assert ids.count("R1") == 1

    def test_normalised_to_uppercase(self):
        text = "r1 - lower case id"
        ids = _parse_rule_ids(text)
        assert ids == ["R1"]

    def test_empty_text(self):
        assert _parse_rule_ids("") == []

    def test_no_ids_in_text(self):
        ids = _parse_rule_ids("Just some prose without any rule IDs.")
        assert ids == []


# ===========================================================================
# Waiver map parsing
# ===========================================================================

class TestParseWaiverRuleMap:
    def test_basic_waiver(self):
        text = "W1:\n  Rule: R6\n  Rationale: Not applicable."
        result = _parse_waiver_rule_map(text)
        assert result.get("R6") == "W1"

    def test_multiple_waivers(self):
        text = "W1:\n  Rule: R3\nW2:\n  Rule: R5"
        result = _parse_waiver_rule_map(text)
        assert result["R3"] == "W1"
        assert result["R5"] == "W2"

    def test_empty_waivers_text(self):
        assert _parse_waiver_rule_map("") == {}

    def test_normalises_rule_ids(self):
        text = "W1:\n  Rule: r4"
        result = _parse_waiver_rule_map(text)
        assert "R4" in result

    def test_dashed_waiver_id(self):
        text = "W-1:\n  Rule: R2"
        result = _parse_waiver_rule_map(text)
        assert result.get("R2") == "W-1"


# ===========================================================================
# Coverage block parsing
# ===========================================================================

class TestParseCoverageBlock:
    def test_story_reference(self):
        text = "R1: story__foo.md"
        result = _parse_coverage_block(text)
        assert result.get("R1") == "story__foo.md"

    def test_waived_entry(self):
        text = "R6: WAIVED W1"
        result = _parse_coverage_block(text)
        assert "WAIVED W1" in result.get("R6", "")

    def test_todo_entry(self):
        text = "R5: TODO add test"
        result = _parse_coverage_block(text)
        assert result.get("R5") == "TODO add test"

    def test_multiple_entries(self):
        text = "R1: story__bar.md\nR2: test_foo\nR3: TODO"
        result = _parse_coverage_block(text)
        assert "R1" in result
        assert "R2" in result
        assert "R3" in result

    def test_empty_block(self):
        assert _parse_coverage_block("") == {}

    def test_normalises_rule_id(self):
        text = "r2: story__baz.md"
        result = _parse_coverage_block(text)
        assert "R2" in result

    def test_bullet_prefix_stripped(self):
        text = "- R1: test_bar"
        result = _parse_coverage_block(text)
        assert "R1" in result


# ===========================================================================
# Story evidence scanning
# ===========================================================================

class TestStoryLinkPrompt:
    def test_linked_story(self):
        text = "<!-- pdd-story-prompts: foo_python.prompt -->\n## Covers\n- R1"
        assert _story_links_prompt(text, "foo_python.prompt")

    def test_unlinked_story(self):
        text = "<!-- pdd-story-prompts: other_python.prompt -->\n## Covers\n- R1"
        assert not _story_links_prompt(text, "foo_python.prompt")

    def test_no_metadata_not_linked(self):
        text = "## Covers\n- R1: rule"
        assert not _story_links_prompt(text, "foo_python.prompt")

    def test_path_variant_matches(self):
        text = "<!-- pdd-story-prompts: prompts/foo_python.prompt -->"
        assert _story_links_prompt(text, "foo_python.prompt")

    def test_case_insensitive_match(self):
        text = "<!-- pdd-story-prompts: FOO_PYTHON.PROMPT -->"
        assert _story_links_prompt(text, "foo_python.prompt")


class TestRuleIdsFromCovers:
    def test_single_module_refs(self):
        covers = "- R1: description\n- R2: another"
        ids = _rule_ids_from_covers(covers, "foo.prompt")
        assert "R1" in ids
        assert "R2" in ids

    def test_cross_module_refs_matching_prompt(self):
        covers = "- prompts/foo.prompt#R3: description"
        ids = _rule_ids_from_covers(covers, "foo.prompt")
        assert "R3" in ids

    def test_cross_module_refs_other_prompt_excluded(self):
        covers = "- prompts/bar.prompt#R3: description"
        ids = _rule_ids_from_covers(covers, "foo.prompt")
        assert "R3" not in ids

    def test_empty_covers(self):
        assert _rule_ids_from_covers("", "foo.prompt") == set()

    def test_normalises_to_uppercase(self):
        ids = _rule_ids_from_covers("- r5: rule", "foo.prompt")
        assert "R5" in ids


class TestScanStoryEvidence:
    def test_linked_story_provides_evidence(self, tmp_path):
        stories_dir = tmp_path / "stories"
        stories_dir.mkdir()
        prompt_path = tmp_path / "foo_python.prompt"
        prompt_path.write_text("", encoding="utf-8")

        story = stories_dir / "story__foo.md"
        story.write_text(
            "<!-- pdd-story-prompts: foo_python.prompt -->\n## Covers\n- R1: rule\n",
            encoding="utf-8",
        )
        evidence = scan_story_evidence(stories_dir, prompt_path)
        assert "R1" in evidence
        assert "story__foo.md" in evidence["R1"]

    def test_unlinked_story_excluded(self, tmp_path):
        stories_dir = tmp_path / "stories"
        stories_dir.mkdir()
        prompt_path = tmp_path / "foo_python.prompt"
        prompt_path.write_text("", encoding="utf-8")

        story = stories_dir / "story__other.md"
        story.write_text(
            "<!-- pdd-story-prompts: other_python.prompt -->\n## Covers\n- R1: rule\n",
            encoding="utf-8",
        )
        evidence = scan_story_evidence(stories_dir, prompt_path)
        assert not evidence

    def test_missing_stories_dir_returns_empty(self, tmp_path):
        prompt_path = tmp_path / "foo_python.prompt"
        evidence = scan_story_evidence(tmp_path / "nonexistent", prompt_path)
        assert evidence == {}

    def test_recursive_scanning(self, tmp_path):
        stories_dir = tmp_path / "stories"
        subdir = stories_dir / "sub"
        subdir.mkdir(parents=True)
        prompt_path = tmp_path / "foo_python.prompt"
        prompt_path.write_text("", encoding="utf-8")

        story = subdir / "story__sub.md"
        story.write_text(
            "<!-- pdd-story-prompts: foo_python.prompt -->\n## Covers\n- R2: rule\n",
            encoding="utf-8",
        )
        evidence = scan_story_evidence(stories_dir, prompt_path)
        assert "R2" in evidence

    def test_multiple_stories_same_rule(self, tmp_path):
        stories_dir = tmp_path / "stories"
        stories_dir.mkdir()
        prompt_path = tmp_path / "foo_python.prompt"
        prompt_path.write_text("", encoding="utf-8")

        for i in range(2):
            s = stories_dir / f"story__s{i}.md"
            s.write_text(
                f"<!-- pdd-story-prompts: foo_python.prompt -->\n## Covers\n- R1: rule\n",
                encoding="utf-8",
            )
        evidence = scan_story_evidence(stories_dir, prompt_path)
        assert len(evidence["R1"]) == 2


class TestStoryValidationFailures:
    def test_linked_story_missing_acceptance_criteria_fails_covered_rule(self, tmp_path):
        stories_dir = tmp_path / "stories"
        stories_dir.mkdir()
        prompt_path = tmp_path / "foo_python.prompt"
        prompt_path.write_text("", encoding="utf-8")

        story = stories_dir / "story__bad.md"
        story.write_text(
            "<!-- pdd-story-prompts: foo_python.prompt -->\n"
            "# Story\n\n"
            "## Covers\n"
            "- R1: covered without acceptance criteria\n",
            encoding="utf-8",
        )

        failures = scan_story_validation_failures(stories_dir, prompt_path)
        assert "R1" in failures
        assert "missing ## Acceptance Criteria" in failures["R1"][0]

    def test_story_with_acceptance_criteria_has_no_failure(self, tmp_path):
        stories_dir = tmp_path / "stories"
        stories_dir.mkdir()
        prompt_path = tmp_path / "foo_python.prompt"
        prompt_path.write_text("", encoding="utf-8")

        story = stories_dir / "story__good.md"
        story.write_text(
            "<!-- pdd-story-prompts: foo_python.prompt -->\n"
            "## Covers\n"
            "- R1: covered\n\n"
            "## Acceptance Criteria\n"
            "- Given X, when Y, then Z.\n",
            encoding="utf-8",
        )

        assert scan_story_validation_failures(stories_dir, prompt_path) == {}


# ===========================================================================
# Test evidence scanning
# ===========================================================================

class TestScanTestEvidence:
    def test_function_name_heuristic(self, tmp_path):
        tests_dir = tmp_path
        _make_test_file(tmp_path, "def test_R1_rejects_zero():\n    pass\n")
        evidence = scan_test_evidence(tests_dir)
        assert "R1" in evidence
        assert "test_R1_rejects_zero" in evidence["R1"]

    def test_comment_heuristic(self, tmp_path):
        _make_test_file(tmp_path, "def test_something():  # R3: covers rule 3\n    pass\n")
        evidence = scan_test_evidence(tmp_path)
        assert "R3" in evidence

    def test_docstring_heuristic(self, tmp_path):
        content = 'def test_foo():\n    """R5: covers idempotency."""\n    pass\n'
        _make_test_file(tmp_path, content)
        evidence = scan_test_evidence(tmp_path)
        assert "R5" in evidence

    def test_non_test_function_excluded(self, tmp_path):
        _make_test_file(tmp_path, "def helper_R1_foo():\n    pass\n")
        evidence = scan_test_evidence(tmp_path)
        assert not evidence

    def test_missing_tests_dir_returns_empty(self, tmp_path):
        assert scan_test_evidence(tmp_path / "nonexistent") == {}

    def test_recursive_scanning(self, tmp_path):
        subdir = tmp_path / "subdir"
        subdir.mkdir()
        _make_test_file(subdir, "def test_R2_foo():\n    pass\n")
        evidence = scan_test_evidence(tmp_path)
        assert "R2" in evidence

    def test_case_insensitive_function_name(self, tmp_path):
        _make_test_file(tmp_path, "def test_r4_lower():\n    pass\n")
        evidence = scan_test_evidence(tmp_path)
        assert "R4" in evidence

    def test_multiple_rules_from_one_function(self, tmp_path):
        content = "def test_R1_and_r2():  # R2: also covers\n    pass\n"
        _make_test_file(tmp_path, content)
        evidence = scan_test_evidence(tmp_path)
        assert "R1" in evidence
        assert "R2" in evidence

    def test_syntax_error_file_falls_back_to_regex(self, tmp_path):
        bad_source = "def test_R6_broken(:\n    pass\n"  # intentional syntax error
        _make_test_file(tmp_path, bad_source)
        # Should not raise; may or may not find R6 depending on regex
        scan_test_evidence(tmp_path)  # just assert no exception


class TestScanTestValidationFailures:
    def test_syntax_error_with_rule_reference_marks_failure(self, tmp_path):
        _make_test_file(tmp_path, "def test_R6_broken(:\n    pass\n")
        failures = scan_test_validation_failures(tmp_path)
        assert "R6" in failures
        assert "syntax error" in failures["R6"][0]

    def test_valid_test_file_has_no_failure(self, tmp_path):
        _make_test_file(tmp_path, "def test_R6_ok():\n    assert True\n")
        assert scan_test_validation_failures(tmp_path) == {}


class TestScanTestFileDirectly:
    def test_docstring_covers_tag(self):
        source = 'def test_foo():\n    """R7: validates boundary."""\n    pass\n'
        evidence: dict = {}
        _scan_test_file(source, evidence)
        assert "R7" in evidence

    def test_covers_comment_style(self):
        source = "def test_bar():  # covers R8\n    pass\n"
        evidence: dict = {}
        _scan_test_file(source, evidence)
        assert "R8" in evidence

    def test_rule_comment_style(self):
        source = "def test_baz():  # rule R9\n    pass\n"
        evidence: dict = {}
        _scan_test_file(source, evidence)
        assert "R9" in evidence


# ===========================================================================
# Status classification
# ===========================================================================

class TestClassifyRule:
    def _call(self, rule_id, coverage_entries=None, waiver_map=None,
              story_evidence=None, test_evidence=None, validation_failures=None):
        return _classify_rule(
            rule_id,
            coverage_entries or {},
            waiver_map or {},
            story_evidence or {},
            test_evidence or {},
            validation_failures or {},
        )

    def test_unchecked_no_evidence(self):
        rc = self._call("R5")
        assert rc.status == STATUS_UNCHECKED
        assert rc.stories == []
        assert rc.tests == []
        assert rc.waiver is None

    def test_checked_story_and_test(self):
        rc = self._call("R1",
            story_evidence={"R1": ["story__a.md"]},
            test_evidence={"R1": ["test_R1_foo"]},
        )
        assert rc.status == STATUS_CHECKED
        assert "story__a.md" in rc.stories
        assert "test_R1_foo" in rc.tests

    def test_story_only(self):
        rc = self._call("R2",
            story_evidence={"R2": ["story__b.md"]},
        )
        assert rc.status == STATUS_STORY_ONLY

    def test_test_only(self):
        rc = self._call("R3",
            test_evidence={"R3": ["test_R3_foo"]},
        )
        assert rc.status == STATUS_TEST_ONLY

    def test_waived_via_coverage_block(self):
        rc = self._call("R6",
            coverage_entries={"R6": "WAIVED W1"},
        )
        assert rc.status == STATUS_WAIVED
        assert rc.waiver == "W1"

    def test_waived_via_waivers_block(self):
        rc = self._call("R6",
            waiver_map={"R6": "W2"},
        )
        assert rc.status == STATUS_WAIVED
        assert rc.waiver == "W2"

    def test_waived_takes_priority_over_evidence(self):
        rc = self._call("R6",
            coverage_entries={"R6": "WAIVED W1"},
            story_evidence={"R6": ["story__s.md"]},
            test_evidence={"R6": ["test_R6_foo"]},
        )
        assert rc.status == STATUS_WAIVED

    def test_failed_takes_priority_over_non_waived_evidence(self):
        rc = self._call("R4",
            story_evidence={"R4": ["story__bad.md"]},
            test_evidence={"R4": ["test_R4_bad"]},
            validation_failures={"R4": ["story__bad.md: missing ## Acceptance Criteria"]},
        )
        assert rc.status == STATUS_FAILED
        assert rc.failures

    def test_todo_coverage_entry_means_unchecked(self):
        rc = self._call("R5",
            coverage_entries={"R5": "TODO add test"},
        )
        assert rc.status == STATUS_UNCHECKED

    def test_rule_id_normalised(self):
        rc = self._call("r1",
            story_evidence={"R1": ["story__a.md"]},
            test_evidence={"R1": ["test_R1_foo"]},
        )
        assert rc.rule_id == "R1"
        assert rc.status == STATUS_CHECKED


# ===========================================================================
# Public API — build_coverage
# ===========================================================================

class TestBuildCoverage:
    def test_legacy_prompt_returns_empty_rules(self, tmp_path):
        prompt = _make_prompt(tmp_path, "# No contracts here\n")
        result = build_coverage(prompt)
        assert result.has_contract_rules is False
        assert result.rules == []
        assert result.error is None

    def test_file_not_found(self, tmp_path):
        result = build_coverage(tmp_path / "missing.prompt")
        assert result.error is not None
        assert "not found" in result.error.lower() or "missing.prompt" in result.error

    def test_rules_extracted(self, tmp_path):
        prompt = _make_prompt(tmp_path, """\
            <contract_rules>
            R1 - First rule
            For every action, the system MUST do X.
            R2 - Second rule
            The system MUST NOT do Y.
            </contract_rules>
        """)
        result = build_coverage(prompt)
        assert result.has_contract_rules
        assert len(result.rules) == 2
        assert result.rules[0].rule_id == "R1"

    def test_all_unchecked_without_evidence(self, tmp_path):
        prompt = _make_prompt(tmp_path, """\
            <contract_rules>
            R1 - No evidence
            The system MUST do A.
            </contract_rules>
        """)
        result = build_coverage(prompt, stories_dir=tmp_path / "none", tests_dir=tmp_path / "none")
        assert result.rules[0].status == STATUS_UNCHECKED

    def test_waived_rule_via_waivers_section(self, tmp_path):
        prompt = _make_prompt(tmp_path, """\
            <contract_rules>
            R1 - Secret isolation
            The system MUST NOT log credentials.
            </contract_rules>
            <waivers>
            W1:
              Rule: R1
              Rationale: SDK handles secrets.
            </waivers>
        """)
        result = build_coverage(prompt)
        assert result.rules[0].status == STATUS_WAIVED
        assert result.rules[0].waiver == "W1"

    def test_waived_rule_via_coverage_block(self, tmp_path):
        prompt = _make_prompt(tmp_path, """\
            <contract_rules>
            R1 - Credentials
            The system MUST NOT expose API keys.
            </contract_rules>
            <coverage>
            R1: WAIVED W2
            </coverage>
        """)
        result = build_coverage(prompt)
        assert result.rules[0].status == STATUS_WAIVED
        assert result.rules[0].waiver == "W2"

    def test_summary_counts_correct(self, tmp_path):
        prompt = _make_prompt(tmp_path, """\
            <contract_rules>
            R1 - A
            The system MUST do A.
            R2 - B
            The system MUST do B.
            </contract_rules>
            <waivers>
            W1:
              Rule: R2
              Rationale: n/a
            </waivers>
        """)
        result = build_coverage(
            prompt,
            stories_dir=tmp_path / "no_stories",
            tests_dir=tmp_path / "no_tests",
        )
        summary = result.summary
        assert summary["total"] == 2
        assert summary["waived"] == 1
        assert summary["unchecked"] == 1

    def test_story_evidence_collected(self, tmp_path):
        prompt = _make_prompt(tmp_path, """\
            <contract_rules>
            R1 - First
            The system MUST do X.
            </contract_rules>
        """, name="foo_python.prompt")
        stories_dir = tmp_path / "stories"
        stories_dir.mkdir()
        story = stories_dir / "story__foo.md"
        story.write_text(
            "<!-- pdd-story-prompts: foo_python.prompt -->\n"
            "## Covers\n- R1: covers\n\n"
            "## Acceptance Criteria\n- Given X, when Y, then Z.\n",
            encoding="utf-8",
        )
        result = build_coverage(prompt, stories_dir=stories_dir, tests_dir=tmp_path / "none")
        assert result.rules[0].status == STATUS_STORY_ONLY
        assert "story__foo.md" in result.rules[0].stories

    def test_test_evidence_collected(self, tmp_path):
        prompt = _make_prompt(tmp_path, """\
            <contract_rules>
            R1 - First
            The system MUST do X.
            </contract_rules>
        """)
        tests_dir = tmp_path / "tests"
        tests_dir.mkdir()
        _make_test_file(tests_dir, "def test_R1_covers():\n    pass\n")
        result = build_coverage(prompt, stories_dir=tmp_path / "none", tests_dir=tests_dir)
        assert result.rules[0].status == STATUS_TEST_ONLY

    def test_checked_both_story_and_test(self, tmp_path):
        prompt = _make_prompt(tmp_path, """\
            <contract_rules>
            R1 - First
            The system MUST do X.
            </contract_rules>
        """, name="foo_python.prompt")
        stories_dir = tmp_path / "stories"
        stories_dir.mkdir()
        story = stories_dir / "story__foo.md"
        story.write_text(
            "<!-- pdd-story-prompts: foo_python.prompt -->\n"
            "## Covers\n- R1: covers\n\n"
            "## Acceptance Criteria\n- Given X, when Y, then Z.\n",
            encoding="utf-8",
        )
        tests_dir = tmp_path / "tests"
        tests_dir.mkdir()
        _make_test_file(tests_dir, "def test_R1_covers():\n    pass\n")
        result = build_coverage(prompt, stories_dir=stories_dir, tests_dir=tests_dir)
        assert result.rules[0].status == STATUS_CHECKED

    def test_failed_story_validation(self, tmp_path):
        prompt = _make_prompt(tmp_path, """\
            <contract_rules>
            R1 - First
            The system MUST do X.
            </contract_rules>
        """, name="foo_python.prompt")
        stories_dir = tmp_path / "stories"
        stories_dir.mkdir()
        (stories_dir / "story__bad.md").write_text(
            "<!-- pdd-story-prompts: foo_python.prompt -->\n"
            "## Covers\n"
            "- R1: covered without acceptance criteria\n",
            encoding="utf-8",
        )
        result = build_coverage(prompt, stories_dir=stories_dir, tests_dir=tmp_path / "none")
        assert result.rules[0].status == STATUS_FAILED
        assert result.rules[0].failures

    def test_failed_test_validation(self, tmp_path):
        prompt = _make_prompt(tmp_path, """\
            <contract_rules>
            R1 - First
            The system MUST do X.
            </contract_rules>
        """)
        tests_dir = tmp_path / "tests"
        tests_dir.mkdir()
        _make_test_file(tests_dir, "def test_R1_broken(:\n    pass\n")
        result = build_coverage(prompt, stories_dir=tmp_path / "none", tests_dir=tests_dir)
        assert result.rules[0].status == STATUS_FAILED
        assert result.rules[0].failures

    def test_as_dict_schema(self, tmp_path):
        prompt = _make_prompt(tmp_path, """\
            <contract_rules>
            R1 - A
            The system MUST do A.
            </contract_rules>
        """)
        d = build_coverage(prompt).as_dict()
        assert "path" in d
        assert "has_contract_rules" in d
        assert "rules" in d
        assert "summary" in d
        assert "error" in d


class TestBuildCoverageDirectory:
    def test_scans_all_prompt_files(self, tmp_path):
        for name in ["a_python.prompt", "b_python.prompt"]:
            (tmp_path / name).write_text(
                "<contract_rules>\nR1 - X\nMUST do.\n</contract_rules>",
                encoding="utf-8",
            )
        results = build_coverage_directory(tmp_path)
        assert len(results) == 2

    def test_skips_llm_prompts(self, tmp_path):
        (tmp_path / "foo_LLM.prompt").write_text("x", encoding="utf-8")
        (tmp_path / "bar_python.prompt").write_text(
            "<contract_rules>\nR1 - X\nMUST.\n</contract_rules>", encoding="utf-8"
        )
        results = build_coverage_directory(tmp_path)
        assert len(results) == 1

    def test_empty_directory_returns_empty_list(self, tmp_path):
        results = build_coverage_directory(tmp_path)
        assert results == []

    def test_recursive_scan(self, tmp_path):
        subdir = tmp_path / "sub"
        subdir.mkdir()
        (subdir / "foo_python.prompt").write_text(
            "<contract_rules>\nR1 - X\nMUST.\n</contract_rules>", encoding="utf-8"
        )
        results = build_coverage_directory(tmp_path)
        assert len(results) == 1


# ===========================================================================
# Full fixture integration
# ===========================================================================

class TestFixtureIntegration:
    """End-to-end tests using the canonical fixture files."""

    def test_refund_prompt_has_contracts(self):
        result = build_coverage(
            FIXTURES / "refund_payment_python.prompt",
            stories_dir=FIXTURES / "stories",
            tests_dir=FIXTURES / "fake_tests",
        )
        assert result.has_contract_rules
        assert result.error is None
        assert len(result.rules) == 6

    def test_r1_is_checked(self):
        result = build_coverage(
            FIXTURES / "refund_payment_python.prompt",
            stories_dir=FIXTURES / "stories",
            tests_dir=FIXTURES / "fake_tests",
        )
        r1 = next(r for r in result.rules if r.rule_id == "R1")
        assert r1.status == STATUS_CHECKED

    def test_r2_is_story_only(self):
        result = build_coverage(
            FIXTURES / "refund_payment_python.prompt",
            stories_dir=FIXTURES / "stories",
            tests_dir=FIXTURES / "fake_tests",
        )
        r2 = next(r for r in result.rules if r.rule_id == "R2")
        assert r2.status == STATUS_STORY_ONLY

    def test_r3_is_test_only(self):
        result = build_coverage(
            FIXTURES / "refund_payment_python.prompt",
            stories_dir=FIXTURES / "stories",
            tests_dir=FIXTURES / "fake_tests",
        )
        r3 = next(r for r in result.rules if r.rule_id == "R3")
        assert r3.status == STATUS_TEST_ONLY

    def test_r4_is_story_only(self):
        result = build_coverage(
            FIXTURES / "refund_payment_python.prompt",
            stories_dir=FIXTURES / "stories",
            tests_dir=FIXTURES / "fake_tests",
        )
        r4 = next(r for r in result.rules if r.rule_id == "R4")
        assert r4.status == STATUS_STORY_ONLY

    def test_r5_is_unchecked(self):
        result = build_coverage(
            FIXTURES / "refund_payment_python.prompt",
            stories_dir=FIXTURES / "stories",
            tests_dir=FIXTURES / "fake_tests",
        )
        r5 = next(r for r in result.rules if r.rule_id == "R5")
        assert r5.status == STATUS_UNCHECKED

    def test_r6_is_waived(self):
        result = build_coverage(
            FIXTURES / "refund_payment_python.prompt",
            stories_dir=FIXTURES / "stories",
            tests_dir=FIXTURES / "fake_tests",
        )
        r6 = next(r for r in result.rules if r.rule_id == "R6")
        assert r6.status == STATUS_WAIVED
        assert r6.waiver is not None

    def test_failed_fixture_has_failed_rules(self):
        result = build_coverage(
            FIXTURES / "failed_receipt_python.prompt",
            stories_dir=FIXTURES / "stories",
            tests_dir=FIXTURES / "fake_tests",
        )
        statuses = {rule.rule_id: rule.status for rule in result.rules}
        assert statuses["R1"] == STATUS_FAILED
        assert statuses["R7"] == STATUS_FAILED

    def test_legacy_prompt_safe(self):
        result = build_coverage(
            FIXTURES / "legacy_no_contracts_python.prompt",
            stories_dir=FIXTURES / "stories",
            tests_dir=FIXTURES / "fake_tests",
        )
        assert not result.has_contract_rules
        assert result.rules == []
        assert result.error is None

    def test_as_dict_all_keys_present(self):
        result = build_coverage(
            FIXTURES / "refund_payment_python.prompt",
            stories_dir=FIXTURES / "stories",
            tests_dir=FIXTURES / "fake_tests",
        )
        d = result.as_dict()
        assert set(d.keys()) >= {"path", "has_contract_rules", "rules", "summary", "error"}
        for rule_dict in d["rules"]:
            assert set(rule_dict.keys()) >= {
                "rule_id", "status", "stories", "tests", "waiver", "failures"
            }
        assert set(d["summary"].keys()) >= {
            "total", "checked", "story_only", "test_only", "unchecked", "waived", "failed"
        }

    def test_summary_totals_add_up(self):
        result = build_coverage(
            FIXTURES / "refund_payment_python.prompt",
            stories_dir=FIXTURES / "stories",
            tests_dir=FIXTURES / "fake_tests",
        )
        s = result.summary
        total_classified = (
            s["checked"] + s["story_only"] + s["test_only"]
            + s["unchecked"] + s["waived"] + s["failed"]
        )
        assert total_classified == s["total"]


# ===========================================================================
# Edge cases
# ===========================================================================

class TestEdgeCases:
    def test_empty_contract_rules_section(self, tmp_path):
        prompt = _make_prompt(tmp_path, "<contract_rules></contract_rules>")
        result = build_coverage(prompt)
        assert result.has_contract_rules
        assert result.rules == []

    def test_prompt_with_only_whitespace_contract_rules(self, tmp_path):
        prompt = _make_prompt(tmp_path, "<contract_rules>\n   \n</contract_rules>")
        result = build_coverage(prompt)
        assert result.has_contract_rules  # tag present → has_contract_rules True
        assert result.rules == []  # but no rules parsed

    def test_rule_coverage_as_dict(self):
        rc = RuleCoverage(rule_id="R1", status=STATUS_CHECKED,
                          stories=["s.md"], tests=["t"], waiver=None)
        d = rc.as_dict()
        assert d["rule_id"] == "R1"
        assert d["status"] == STATUS_CHECKED
        assert d["stories"] == ["s.md"]
        assert d["tests"] == ["t"]
        assert d["waiver"] is None

    def test_coverage_result_summary_property(self):
        cr = CoverageResult(path=Path("foo.prompt"), has_contract_rules=True, rules=[
            RuleCoverage("R1", STATUS_CHECKED),
            RuleCoverage("R2", STATUS_STORY_ONLY),
            RuleCoverage("R3", STATUS_TEST_ONLY),
            RuleCoverage("R4", STATUS_UNCHECKED),
            RuleCoverage("R5", STATUS_WAIVED),
            RuleCoverage("R6", STATUS_FAILED),
        ])
        s = cr.summary
        assert s["total"] == 6
        assert s["checked"] == 1
        assert s["story_only"] == 1
        assert s["test_only"] == 1
        assert s["unchecked"] == 1
        assert s["waived"] == 1
        assert s["failed"] == 1
