"""
Tests for cross-dev-unit story support (GitHub issue #1769).

Covers:
  Scenario 1 (8 cases): Cross-dev-unit story parsing — _parse_story_prompt_metadata()
  Scenario 2 (5 cases): Forward traceability — scan_story_evidence() with cross-unit stories
  Scenario 3 (5 cases): Inverse traceability — story → linked dev units + regression test IDs
  Scenario 4 (5 cases): Coverage separation — CoverageResult cross_unit_stories field (new)
  Scenario 5 (4 cases): Double-count prevention — build_coverage_directory global uniqueness
  Scenario 6 (6 cases): CLI output — pdd checkup coverage cross-dev-unit section (new)
  Scenario 7 (4 cases): Regression lane summary — one entry per cross-unit story (new)

Scenarios 4 and 6 test forthcoming implementation; they will fail with
AttributeError or assertion failures until issue #1769 is implemented.
"""
from __future__ import annotations

import json
import textwrap
from pathlib import Path

import pytest
from click.testing import CliRunner

from pdd.user_story_tests import _parse_story_prompt_metadata
from pdd.contract_ir import iter_covers_refs, rule_ids_from_covers
from pdd.coverage_contracts import (
    STATUS_CHECKED,
    STATUS_STORY_ONLY,
    STATUS_TEST_ONLY,
    STATUS_UNCHECKED,
    CoverageResult,
    RuleCoverage,
    _extract_markdown_section,
    _story_links_prompt,
    _rule_ids_from_covers,
    build_coverage,
    build_coverage_directory,
    scan_story_evidence,
    scan_test_evidence,
)
from pdd.commands.coverage import coverage_cmd

# ---------------------------------------------------------------------------
# Shared story and prompt templates
# ---------------------------------------------------------------------------

# Story that explicitly links two dev units with cross-module ## Covers syntax
_CROSS_UNIT_2_STORY = """\
<!-- pdd-story-prompts: alpha_python.prompt, beta_javascript.prompt -->

# Story: Cross-Unit Integration

As a user I can file a bug and get it routed then fixed across modules.

## Acceptance Criteria
- Given a bug report, when routed by alpha module, then beta module generates a fix.

## Covers
- alpha_python.prompt#R1: issue routing
- beta_javascript.prompt#R2: fix generation
"""

# Story linking three dev units
_CROSS_UNIT_3_STORY = """\
<!-- pdd-story-prompts: a_python.prompt, b_python.prompt, c_python.prompt -->

# Story: Three-Way Integration

## Acceptance Criteria
- Given input, when processed by all three units, then the output is correct.

## Covers
- a_python.prompt#R1: module A handling
- b_python.prompt#R2: module B transformation
- c_python.prompt#R3: module C output
"""

# Classic backward-compatible single-unit story
_SINGLE_UNIT_STORY = """\
<!-- pdd-story-prompts: alpha_python.prompt -->

# Story: Single-Unit Behavior

## Acceptance Criteria
- Given X, when Y, then Z.

## Covers
- R1: rule covered by single unit
"""

# Minimal prompt files with contract rules
_PROMPT_R1 = "<contract_rules>\nR1: The system MUST route issues correctly.\n</contract_rules>\n"
_PROMPT_R2 = "<contract_rules>\nR2: The system MUST generate fixes.\n</contract_rules>\n"


# ---------------------------------------------------------------------------
# Helpers
# ---------------------------------------------------------------------------

def _make_story(stories_dir: Path, content: str, name: str = "story__test.md") -> Path:
    p = stories_dir / name
    p.write_text(textwrap.dedent(content), encoding="utf-8")
    return p


def _make_prompt(directory: Path, content: str, name: str = "test_python.prompt") -> Path:
    p = directory / name
    p.write_text(textwrap.dedent(content), encoding="utf-8")
    return p


def _parse_cli_json(result, args: list[str]) -> dict:
    """Parse CLI JSON after preserving actionable Click failure diagnostics."""
    assert result.output.strip(), (
        "coverage CLI emitted no JSON\n"
        f"args={args!r}\n"
        f"exit_code={result.exit_code}\n"
        f"exception={result.exception!r}\n"
        f"stdout={result.stdout!r}\n"
        f"stderr={result.stderr!r}"
    )
    return json.loads(result.output)


# ===========================================================================
# Scenario 1: Cross-Dev-Unit Story Parsing (8 cases)
# Tests _parse_story_prompt_metadata() from pdd/user_story_tests.py
# ===========================================================================

class TestCrossUnitStoryParsing:
    """_parse_story_prompt_metadata preserves all linked prompt refs for cross-unit stories."""

    def test_single_prompt_returns_single_element(self):
        content = "<!-- pdd-story-prompts: alpha_python.prompt -->\n# Story"
        result = _parse_story_prompt_metadata(content)
        assert result == ["alpha_python.prompt"]

    def test_two_prompt_cross_unit_returns_two_elements(self):
        content = (
            "<!-- pdd-story-prompts: alpha_python.prompt, beta_javascript.prompt -->\n"
            "# Story"
        )
        result = _parse_story_prompt_metadata(content)
        assert result == ["alpha_python.prompt", "beta_javascript.prompt"]
        assert len(result) == 2

    def test_three_prompt_cross_unit_returns_three_elements(self):
        content = "<!-- pdd-story-prompts: a.prompt, b.prompt, c.prompt -->\n# Story"
        result = _parse_story_prompt_metadata(content)
        assert result == ["a.prompt", "b.prompt", "c.prompt"]
        assert len(result) == 3

    def test_path_qualified_refs_preserved_verbatim(self):
        content = (
            "<!-- pdd-story-prompts: "
            "prompts/alpha_python.prompt, prompts/beta_javascript.prompt -->"
        )
        result = _parse_story_prompt_metadata(content)
        assert result == ["prompts/alpha_python.prompt", "prompts/beta_javascript.prompt"]

    def test_whitespace_trimmed_from_each_ref(self):
        content = (
            "<!-- pdd-story-prompts:  alpha_python.prompt ,  beta_javascript.prompt  -->"
        )
        result = _parse_story_prompt_metadata(content)
        assert result == ["alpha_python.prompt", "beta_javascript.prompt"]

    def test_empty_metadata_returns_empty_list(self):
        content = "<!-- pdd-story-prompts: -->\n# Story"
        result = _parse_story_prompt_metadata(content)
        assert result == []

    def test_missing_metadata_returns_empty_list(self):
        content = "# Story without any pdd-story-prompts metadata"
        result = _parse_story_prompt_metadata(content)
        assert result == []

    def test_mixed_path_styles_both_preserved(self):
        """Path-qualified and basename refs may coexist in the same metadata comment."""
        content = (
            "<!-- pdd-story-prompts: "
            "prompts/alpha_python.prompt, beta_javascript.prompt -->"
        )
        result = _parse_story_prompt_metadata(content)
        assert "prompts/alpha_python.prompt" in result
        assert "beta_javascript.prompt" in result
        assert len(result) == 2


# ===========================================================================
# Scenario 2: Forward Traceability via scan_story_evidence() (5 cases)
# A cross-unit story must appear as evidence for EACH of its linked prompts.
# ===========================================================================

class TestForwardTraceabilityCrossUnit:
    """scan_story_evidence returns a cross-unit story for each of its linked dev units."""

    def test_cross_unit_story_appears_for_first_linked_prompt(self, tmp_path):
        stories_dir = tmp_path / "stories"
        stories_dir.mkdir()
        prompt_alpha = tmp_path / "alpha_python.prompt"
        prompt_alpha.write_text("", encoding="utf-8")

        _make_story(stories_dir, _CROSS_UNIT_2_STORY, name="story__cross.md")

        evidence = scan_story_evidence(stories_dir, prompt_alpha)
        assert "R1" in evidence, (
            "Cross-unit story must provide R1 evidence for alpha_python.prompt"
        )
        assert "story__cross.md" in evidence["R1"]

    def test_cross_unit_story_appears_for_second_linked_prompt(self, tmp_path):
        stories_dir = tmp_path / "stories"
        stories_dir.mkdir()
        prompt_beta = tmp_path / "beta_javascript.prompt"
        prompt_beta.write_text("", encoding="utf-8")

        _make_story(stories_dir, _CROSS_UNIT_2_STORY, name="story__cross.md")

        evidence = scan_story_evidence(stories_dir, prompt_beta)
        assert "R2" in evidence, (
            "Cross-unit story must provide R2 evidence for beta_javascript.prompt"
        )
        assert "story__cross.md" in evidence["R2"]

    def test_cross_unit_story_excluded_for_unlinked_prompt(self, tmp_path):
        stories_dir = tmp_path / "stories"
        stories_dir.mkdir()
        # gamma_python.prompt is NOT listed in the story's pdd-story-prompts
        prompt_gamma = tmp_path / "gamma_python.prompt"
        prompt_gamma.write_text("", encoding="utf-8")

        _make_story(stories_dir, _CROSS_UNIT_2_STORY, name="story__cross.md")

        evidence = scan_story_evidence(stories_dir, prompt_gamma)
        assert not evidence, "Cross-unit story must not bleed to unlinked prompts"

    def test_single_unit_story_does_not_bleed_to_unlinked_prompt(self, tmp_path):
        stories_dir = tmp_path / "stories"
        stories_dir.mkdir()
        prompt_beta = tmp_path / "beta_javascript.prompt"
        prompt_beta.write_text("", encoding="utf-8")

        _make_story(stories_dir, _SINGLE_UNIT_STORY, name="story__single.md")

        evidence = scan_story_evidence(stories_dir, prompt_beta)
        assert not evidence, (
            "Single-unit story must not appear as evidence for an unlinked prompt"
        )

    def test_cross_and_single_unit_stories_coexist_in_same_dir(self, tmp_path):
        """Both story types in one directory: each prompt sees only its own rules."""
        stories_dir = tmp_path / "stories"
        stories_dir.mkdir()
        prompt_alpha = tmp_path / "alpha_python.prompt"
        prompt_alpha.write_text("", encoding="utf-8")

        # Single-unit story covers R1 via bare rule ref for alpha
        _make_story(stories_dir, _SINGLE_UNIT_STORY, name="story__single.md")

        # Cross-unit story covers alpha_python.prompt#R2 and beta R2
        cross_story = """\
            <!-- pdd-story-prompts: alpha_python.prompt, beta_javascript.prompt -->
            ## Covers
            - alpha_python.prompt#R2: cross-unit alpha rule
            ## Acceptance Criteria
            - AC for cross-unit story
            """
        _make_story(stories_dir, cross_story, name="story__cross.md")

        evidence = scan_story_evidence(stories_dir, prompt_alpha)

        # Single-unit story's bare R1 shows up for alpha
        assert "R1" in evidence
        assert "story__single.md" in evidence["R1"]

        # Cross-unit story's R2 for alpha also shows up
        assert "R2" in evidence
        assert "story__cross.md" in evidence["R2"]

        # Cross-unit story must not wrongly appear under R1 for alpha
        assert "story__cross.md" not in evidence.get("R1", [])


# ===========================================================================
# Scenario 3: Inverse Traceability — Story → Dev Units + Test IDs (5 cases)
# Building-block tests: from a story, retrieve all linked dev units.
# ===========================================================================

class TestInverseTraceability:
    """Inverse direction: from a story file, retrieve all linked dev units."""

    def test_cross_unit_story_metadata_exposes_all_linked_prompts(self, tmp_path):
        """_parse_story_prompt_metadata is the building block for inverse traceability."""
        story_path = tmp_path / "story__cross.md"
        story_path.write_text(_CROSS_UNIT_2_STORY, encoding="utf-8")

        linked = _parse_story_prompt_metadata(story_path.read_text(encoding="utf-8"))

        assert "alpha_python.prompt" in linked
        assert "beta_javascript.prompt" in linked
        assert len(linked) == 2

    def test_single_unit_story_inverse_returns_exactly_one_prompt(self, tmp_path):
        story_path = tmp_path / "story__single.md"
        story_path.write_text(_SINGLE_UNIT_STORY, encoding="utf-8")

        linked = _parse_story_prompt_metadata(story_path.read_text(encoding="utf-8"))

        assert linked == ["alpha_python.prompt"]

    def test_covers_section_references_all_linked_dev_units(self, tmp_path):
        """The ## Covers block must reference every declared dev unit by prompt filename."""
        story_path = tmp_path / "story__cross.md"
        story_path.write_text(_CROSS_UNIT_2_STORY, encoding="utf-8")

        story_text = story_path.read_text(encoding="utf-8")
        covers_text = _extract_markdown_section(story_text, "Covers")
        refs = iter_covers_refs(covers_text)

        filenames = {ref.prompt_filename for ref in refs if ref.prompt_filename}
        assert "alpha_python.prompt" in filenames, (
            "## Covers must include a cross-module ref for alpha_python.prompt"
        )
        assert "beta_javascript.prompt" in filenames, (
            "## Covers must include a cross-module ref for beta_javascript.prompt"
        )

    def test_scanning_stories_dir_identifies_cross_unit_stories(self, tmp_path):
        """Iterating the stories directory reveals which stories link multiple dev units."""
        stories_dir = tmp_path / "stories"
        stories_dir.mkdir()

        _make_story(stories_dir, _CROSS_UNIT_2_STORY, name="story__cross.md")
        _make_story(stories_dir, _SINGLE_UNIT_STORY, name="story__single.md")

        cross_unit_names = []
        for story_path in sorted(stories_dir.rglob("story__*.md")):
            story_text = story_path.read_text(encoding="utf-8")
            linked = _parse_story_prompt_metadata(story_text)
            if len(linked) >= 2:
                cross_unit_names.append(story_path.name)

        assert cross_unit_names == ["story__cross.md"]

    def test_story_without_metadata_has_no_explicit_dev_unit_links(self, tmp_path):
        """A metadata-less story returns [] from _parse_story_prompt_metadata
        (it applies to the whole prompt set via scan_story_evidence, not a specific unit)."""
        story_path = tmp_path / "story__no_meta.md"
        story_path.write_text(
            "# Story Without Metadata\n\n## Acceptance Criteria\n- AC1\n",
            encoding="utf-8",
        )
        linked = _parse_story_prompt_metadata(story_path.read_text(encoding="utf-8"))
        assert linked == [], (
            "A metadata-less story must return [] — "
            "it applies to the entire prompt set, not specific dev units"
        )


# ===========================================================================
# Scenario 4: Coverage Separation in CoverageResult (5 cases)
# Tests CoverageResult.cross_unit_stories field — NEW FEATURE (issue #1769)
# These tests WILL FAIL until CoverageResult gains a cross_unit_stories field
# and build_coverage() populates it.
# ===========================================================================

class TestCoverageResultCrossUnitField:
    """CoverageResult must expose cross_unit_stories listing stories that link 2+ prompts."""

    def _setup(self, tmp_path: Path):
        stories_dir = tmp_path / "stories"
        stories_dir.mkdir()
        tests_dir = tmp_path / "tests"
        tests_dir.mkdir()
        prompt_path = tmp_path / "alpha_python.prompt"
        prompt_path.write_text(_PROMPT_R1, encoding="utf-8")
        _make_story(stories_dir, _CROSS_UNIT_2_STORY, name="story__cross.md")
        return prompt_path, stories_dir, tests_dir

    def test_cross_unit_story_listed_in_cross_unit_stories_field(self, tmp_path):
        """build_coverage must set CoverageResult.cross_unit_stories for cross-unit stories."""
        prompt_path, stories_dir, tests_dir = self._setup(tmp_path)
        result = build_coverage(prompt_path, stories_dir, tests_dir)
        assert hasattr(result, "cross_unit_stories"), (
            "CoverageResult must have a cross_unit_stories field (issue #1769). "
            "Add it as: cross_unit_stories: list[str] = field(default_factory=list)"
        )
        assert "story__cross.md" in result.cross_unit_stories

    def test_single_unit_story_absent_from_cross_unit_stories(self, tmp_path):
        """A single-unit story must NOT appear in CoverageResult.cross_unit_stories."""
        stories_dir = tmp_path / "stories"
        stories_dir.mkdir()
        tests_dir = tmp_path / "tests"
        tests_dir.mkdir()
        prompt_path = tmp_path / "alpha_python.prompt"
        prompt_path.write_text(_PROMPT_R1, encoding="utf-8")
        _make_story(stories_dir, _SINGLE_UNIT_STORY, name="story__single.md")

        result = build_coverage(prompt_path, stories_dir, tests_dir)
        assert hasattr(result, "cross_unit_stories"), (
            "CoverageResult must have a cross_unit_stories field (issue #1769)"
        )
        assert "story__single.md" not in result.cross_unit_stories

    def test_as_dict_includes_cross_unit_stories_key(self, tmp_path):
        """CoverageResult.as_dict() must include a 'cross_unit_stories' key."""
        prompt_path, stories_dir, tests_dir = self._setup(tmp_path)
        result = build_coverage(prompt_path, stories_dir, tests_dir)
        d = result.as_dict()
        assert "cross_unit_stories" in d, (
            "CoverageResult.as_dict() must contain 'cross_unit_stories' key (issue #1769)"
        )
        assert "story__cross.md" in d["cross_unit_stories"]

    def test_summary_rule_counts_not_inflated_by_cross_unit_story(self, tmp_path):
        """Coverage summary totals must not double-count a cross-unit story's rule."""
        prompt_path, stories_dir, tests_dir = self._setup(tmp_path)
        result = build_coverage(prompt_path, stories_dir, tests_dir)
        s = result.summary
        counted = (
            s["checked"] + s["story_only"] + s["test_only"]
            + s["unchecked"] + s["waived"] + s["failed"]
        )
        assert counted == s["total"], (
            f"Rule status counts must sum to total={s['total']} (no double-counting). "
            f"Got: {counted}"
        )

    def test_empty_cross_unit_stories_when_no_cross_unit_stories_present(self, tmp_path):
        """When only single-unit stories exist, cross_unit_stories must be an empty list."""
        stories_dir = tmp_path / "stories"
        stories_dir.mkdir()
        tests_dir = tmp_path / "tests"
        tests_dir.mkdir()
        prompt_path = tmp_path / "alpha_python.prompt"
        prompt_path.write_text(_PROMPT_R1, encoding="utf-8")
        _make_story(stories_dir, _SINGLE_UNIT_STORY, name="story__single.md")

        result = build_coverage(prompt_path, stories_dir, tests_dir)
        assert hasattr(result, "cross_unit_stories"), (
            "CoverageResult must have a cross_unit_stories field (issue #1769)"
        )
        assert result.cross_unit_stories == [], (
            "cross_unit_stories must be [] when no cross-unit stories are present"
        )


# ===========================================================================
# Scenario 5: Double-Count Prevention in build_coverage_directory() (4 cases)
# A cross-unit story linking N prompts is ONE story globally (unique filename),
# even though it is attributed to each linked prompt's CoverageResult.
# ===========================================================================

class TestDoubleCountPrevention:
    """Cross-unit story appears in N CoverageResult objects but is 1 unique story globally."""

    def _setup_two_prompts(self, tmp_path: Path):
        prompts_dir = tmp_path / "prompts"
        prompts_dir.mkdir()
        stories_dir = tmp_path / "stories"
        stories_dir.mkdir()
        tests_dir = tmp_path / "tests"
        tests_dir.mkdir()
        _make_prompt(prompts_dir, _PROMPT_R1, "alpha_python.prompt")
        _make_prompt(prompts_dir, _PROMPT_R2, "beta_javascript.prompt")
        _make_story(stories_dir, _CROSS_UNIT_2_STORY, name="story__cross.md")
        return prompts_dir, stories_dir, tests_dir

    def test_cross_unit_story_attributed_to_each_linked_prompt(self, tmp_path):
        """story__cross.md must appear in BOTH alpha and beta CoverageResult objects."""
        prompts_dir, stories_dir, tests_dir = self._setup_two_prompts(tmp_path)
        results = build_coverage_directory(prompts_dir, stories_dir, tests_dir)
        results_by_name = {r.path.name: r for r in results}

        alpha_stories = {
            s for rule in results_by_name["alpha_python.prompt"].rules for s in rule.stories
        }
        beta_stories = {
            s for rule in results_by_name["beta_javascript.prompt"].rules for s in rule.stories
        }

        assert "story__cross.md" in alpha_stories, (
            "Cross-unit story must be attributed to alpha_python.prompt"
        )
        assert "story__cross.md" in beta_stories, (
            "Cross-unit story must be attributed to beta_javascript.prompt"
        )

    def test_unique_story_count_globally_is_one(self, tmp_path):
        """Collecting all story filenames set-wise gives 1, not 2, for a cross-unit story."""
        prompts_dir, stories_dir, tests_dir = self._setup_two_prompts(tmp_path)
        results = build_coverage_directory(prompts_dir, stories_dir, tests_dir)

        all_unique_story_names: set[str] = set()
        for result in results:
            for rule in result.rules:
                all_unique_story_names.update(rule.stories)

        assert len(all_unique_story_names) == 1, (
            f"Expected 1 unique story globally, got {len(all_unique_story_names)}: "
            f"{all_unique_story_names}"
        )
        assert "story__cross.md" in all_unique_story_names

    def test_single_unit_stories_do_not_bleed_across_results(self, tmp_path):
        """Single-unit stories each appear in exactly one CoverageResult, not both."""
        prompts_dir = tmp_path / "prompts"
        prompts_dir.mkdir()
        stories_dir = tmp_path / "stories"
        stories_dir.mkdir()
        tests_dir = tmp_path / "tests"
        tests_dir.mkdir()

        _make_prompt(prompts_dir, _PROMPT_R1, "alpha_python.prompt")
        _make_prompt(prompts_dir, _PROMPT_R2, "beta_javascript.prompt")

        _make_story(
            stories_dir,
            """\
            <!-- pdd-story-prompts: alpha_python.prompt -->
            ## Covers
            - R1: alpha rule
            ## Acceptance Criteria
            - AC1
            """,
            name="story__alpha_only.md",
        )
        _make_story(
            stories_dir,
            """\
            <!-- pdd-story-prompts: beta_javascript.prompt -->
            ## Covers
            - R2: beta rule
            ## Acceptance Criteria
            - AC2
            """,
            name="story__beta_only.md",
        )

        results = build_coverage_directory(prompts_dir, stories_dir, tests_dir)
        results_by_name = {r.path.name: r for r in results}

        alpha_stories = {
            s for rule in results_by_name["alpha_python.prompt"].rules for s in rule.stories
        }
        beta_stories = {
            s for rule in results_by_name["beta_javascript.prompt"].rules for s in rule.stories
        }

        assert "story__alpha_only.md" in alpha_stories
        assert "story__beta_only.md" not in alpha_stories
        assert "story__beta_only.md" in beta_stories
        assert "story__alpha_only.md" not in beta_stories

    def test_three_prompt_cross_unit_story_is_one_unique_story(self, tmp_path):
        """A story linking 3 prompts must appear as 1 unique story globally, not 3."""
        prompts_dir = tmp_path / "prompts"
        prompts_dir.mkdir()
        stories_dir = tmp_path / "stories"
        stories_dir.mkdir()
        tests_dir = tmp_path / "tests"
        tests_dir.mkdir()

        for letter, rule in [("a", "R1"), ("b", "R2"), ("c", "R3")]:
            _make_prompt(
                prompts_dir,
                f"<contract_rules>\n{rule}: MUST do {letter}.\n</contract_rules>\n",
                f"{letter}_python.prompt",
            )

        _make_story(stories_dir, _CROSS_UNIT_3_STORY, name="story__three_unit.md")

        results = build_coverage_directory(prompts_dir, stories_dir, tests_dir)
        assert len(results) == 3, f"Expected 3 CoverageResult objects, got {len(results)}"

        all_unique_story_names: set[str] = set()
        for result in results:
            for rule in result.rules:
                all_unique_story_names.update(rule.stories)

        assert len(all_unique_story_names) == 1, (
            "Three-prompt cross-unit story must count as 1 unique story globally, not 3. "
            f"Got: {all_unique_story_names}"
        )
        assert "story__three_unit.md" in all_unique_story_names


# ===========================================================================
# Scenario 6: CLI Output — pdd checkup coverage (6 cases)
# Cases that test the new cross-dev-unit section in CLI output (issue #1769)
# will fail until the CLI is updated to render cross_unit_stories.
# ===========================================================================

class TestCLICrossUnitOutput:
    """CLI must show cross-dev-unit section and include cross_unit_stories in JSON."""

    def _setup_cli(self, tmp_path: Path):
        """One prompt with a cross-unit story (filename contains no coverage keywords)."""
        stories_dir = tmp_path / "stories"
        stories_dir.mkdir()
        tests_dir = tmp_path / "tests"
        tests_dir.mkdir()
        prompt_alpha = _make_prompt(tmp_path, _PROMPT_R1, "alpha_python.prompt")
        # Use a story name that contains no coverage section keywords so that
        # test_rich_table_shows_cross_dev_unit_section_when_applicable only passes
        # once the implementation explicitly adds a cross-dev-unit UI section.
        _make_story(stories_dir, _CROSS_UNIT_2_STORY, name="story__issue_routing_flow.md")
        return prompt_alpha, stories_dir, tests_dir

    def test_cli_exits_without_crash_for_cross_unit_story(self, tmp_path):
        """CLI must not crash (exit code 2+) when a cross-unit story is present."""
        prompt_alpha, stories_dir, tests_dir = self._setup_cli(tmp_path)
        runner = CliRunner()
        result = runner.invoke(
            coverage_cmd,
            [
                "--stories-dir", str(stories_dir),
                "--tests-dir", str(tests_dir),
                str(prompt_alpha),
            ],
        )
        assert result.exit_code in (0, 1), (
            f"CLI must not exit with code 2 for a valid cross-unit story. "
            f"Got: {result.exit_code}\nOutput:\n{result.output}"
        )

    def test_cli_output_contains_rule_ids_with_cross_unit_story(self, tmp_path):
        """Rule IDs must still be shown in the table when covered by a cross-unit story."""
        prompt_alpha, stories_dir, tests_dir = self._setup_cli(tmp_path)
        runner = CliRunner()
        result = runner.invoke(
            coverage_cmd,
            [
                "--stories-dir", str(stories_dir),
                "--tests-dir", str(tests_dir),
                str(prompt_alpha),
            ],
        )
        assert "R1" in result.output

    def test_json_total_prompts_not_inflated_by_cross_unit_story(self, tmp_path):
        """total_prompts in --json output must equal the number of .prompt files, not stories."""
        prompts_dir = tmp_path / "prompts"
        prompts_dir.mkdir()
        stories_dir = tmp_path / "stories"
        stories_dir.mkdir()
        tests_dir = tmp_path / "tests"
        tests_dir.mkdir()

        _make_prompt(prompts_dir, _PROMPT_R1, "alpha_python.prompt")
        _make_prompt(prompts_dir, _PROMPT_R2, "beta_javascript.prompt")
        _make_story(stories_dir, _CROSS_UNIT_2_STORY, name="story__cross.md")

        runner = CliRunner()
        args = [
            "--json",
            "--stories-dir", str(stories_dir),
            "--tests-dir", str(tests_dir),
            str(prompts_dir),
        ]
        result = runner.invoke(coverage_cmd, args)
        assert result.exit_code in (0, 1, 2)
        data = _parse_cli_json(result, args)
        # 2 prompt files → total_prompts must be 2
        assert data["total_prompts"] == 2, (
            f"total_prompts should be 2 (one per prompt file), got {data['total_prompts']}. "
            "Cross-unit story must not inflate this counter."
        )

    def test_json_results_count_matches_prompt_file_count(self, tmp_path):
        """Number of result items in --json equals actual .prompt file count."""
        prompts_dir = tmp_path / "prompts"
        prompts_dir.mkdir()
        stories_dir = tmp_path / "stories"
        stories_dir.mkdir()
        tests_dir = tmp_path / "tests"
        tests_dir.mkdir()

        _make_prompt(prompts_dir, _PROMPT_R1, "alpha_python.prompt")
        _make_prompt(prompts_dir, _PROMPT_R2, "beta_javascript.prompt")
        _make_story(stories_dir, _CROSS_UNIT_2_STORY, name="story__cross.md")

        runner = CliRunner()
        result = runner.invoke(
            coverage_cmd,
            [
                "--json",
                "--stories-dir", str(stories_dir),
                "--tests-dir", str(tests_dir),
                str(prompts_dir),
            ],
        )
        data = json.loads(result.output)
        assert len(data["results"]) == 2, (
            "results array must have one entry per prompt file, not one per story link"
        )

    def test_json_output_includes_cross_unit_stories_key(self, tmp_path):
        """Each result item in --json must include 'cross_unit_stories' (issue #1769)."""
        prompt_alpha, stories_dir, tests_dir = self._setup_cli(tmp_path)
        runner = CliRunner()
        args = [
            "--json",
            "--stories-dir", str(stories_dir),
            "--tests-dir", str(tests_dir),
            str(prompt_alpha),
        ]
        result = runner.invoke(coverage_cmd, args)
        assert result.exit_code in (0, 1)
        data = _parse_cli_json(result, args)
        items = data["results"]
        for item in items:
            assert "cross_unit_stories" in item, (
                "Each --json result item must include 'cross_unit_stories' (issue #1769). "
                f"Keys found: {list(item.keys())}"
            )

    def test_rich_table_shows_cross_dev_unit_section_when_applicable(self, tmp_path):
        """Rich table output must label cross-dev-unit coverage distinctly (issue #1769)."""
        prompt_alpha, stories_dir, tests_dir = self._setup_cli(tmp_path)
        runner = CliRunner()
        result = runner.invoke(
            coverage_cmd,
            [
                "--stories-dir", str(stories_dir),
                "--tests-dir", str(tests_dir),
                str(prompt_alpha),
            ],
        )
        assert result.exit_code in (0, 1)
        output_lower = result.output.lower()
        # The output must include a phrase specific to the cross-dev-unit section label.
        # "cross" or "linked" alone are too broad; require a compound term that can only
        # be emitted by the dedicated cross-dev-unit implementation (issue #1769).
        assert any(
            kw in output_lower
            for kw in ("cross-unit", "cross-dev-unit", "cross dev unit", "multi-unit",
                       "linked units", "cross unit")
        ), (
            "CLI output must include a cross-dev-unit section when cross-unit stories exist "
            "(issue #1769). "
            f"Output did not contain expected cross-unit section keywords.\n"
            f"Actual output:\n{result.output}"
        )


# ===========================================================================
# Scenario 7: Regression Lane Summary (4 cases)
# Cross-unit stories must appear as ONE entry with a linked_dev_units list.
# ===========================================================================

class TestRegressionLaneSummary:
    """A cross-unit story is one story entity covering multiple dev units."""

    def test_story_linking_two_prompts_is_cross_unit(self):
        """Baseline: any story with 2+ linked prompts is classified as cross-unit."""
        linked = _parse_story_prompt_metadata(_CROSS_UNIT_2_STORY)
        assert len(linked) >= 2, (
            "A story with two pdd-story-prompts entries must be classified as cross-unit"
        )

    def test_cross_unit_story_linked_dev_units_are_prompt_filenames(self):
        """All entries in the linked dev units list must be .prompt filenames."""
        linked = _parse_story_prompt_metadata(_CROSS_UNIT_2_STORY)
        assert all(p.endswith(".prompt") for p in linked), (
            "Each linked dev unit must be a prompt filename ending with '.prompt'"
        )

    def test_all_declared_dev_units_present_in_linked_list(self):
        """Every prompt declared in pdd-story-prompts appears in the linked list."""
        linked = _parse_story_prompt_metadata(_CROSS_UNIT_2_STORY)
        assert "alpha_python.prompt" in linked
        assert "beta_javascript.prompt" in linked

    def test_cross_unit_story_evidence_is_one_entity_covering_two_prompts(self, tmp_path):
        """
        The same story filename appears in BOTH prompts' evidence dicts.
        This confirms the story is a single entity, not two separate stories.
        The regression lane must report it once globally with a linked_dev_units list.
        """
        stories_dir = tmp_path / "stories"
        stories_dir.mkdir()
        prompt_alpha = tmp_path / "alpha_python.prompt"
        prompt_beta = tmp_path / "beta_javascript.prompt"
        prompt_alpha.write_text("", encoding="utf-8")
        prompt_beta.write_text("", encoding="utf-8")

        _make_story(stories_dir, _CROSS_UNIT_2_STORY, name="story__cross.md")

        alpha_evidence = scan_story_evidence(stories_dir, prompt_alpha)
        beta_evidence = scan_story_evidence(stories_dir, prompt_beta)

        alpha_story_names = {s for stories in alpha_evidence.values() for s in stories}
        beta_story_names = {s for stories in beta_evidence.values() for s in stories}

        # Same filename in both — one entity, two attributions
        assert "story__cross.md" in alpha_story_names, (
            "Cross-unit story must appear in alpha prompt's evidence"
        )
        assert "story__cross.md" in beta_story_names, (
            "Cross-unit story must appear in beta prompt's evidence"
        )
        shared = alpha_story_names & beta_story_names
        assert "story__cross.md" in shared, (
            "The story filename must be the SAME in both evidence dicts — "
            "it is one cross-unit story, not two separate stories. "
            "The regression lane summary must report it as one entry."
        )
