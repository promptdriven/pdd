"""
Integration tests for `pdd contracts check` using realistic prompt fixtures.

These tests exercise cross-cutting scenarios: combined defects in one prompt,
directory scanning with mixed files, story coverage validation against real
rule IDs, waiver handling, and the full JSON schema shape.

Unlike unit tests (test_contract_check.py) which test individual check
functions in isolation, these tests drive the CLI end-to-end and assert
on observable behaviour that users and CI systems would see.
"""
from __future__ import annotations

import json
from pathlib import Path

import pytest
from click.testing import CliRunner

from pdd import cli

FIXTURES = Path(__file__).parents[1] / "fixtures" / "contract_check"

# Realistic fixture paths
PAYMENT_CLEAN = FIXTURES / "payment_api_clean_python.prompt"
PAYMENT_ISSUES = FIXTURES / "payment_api_issues_python.prompt"
AUTH_CLEAN = FIXTURES / "auth_service_clean_python.prompt"
RATE_LIMITER_ISSUES = FIXTURES / "rate_limiter_issues_python.prompt"
STORY_PAYMENT_GOOD = FIXTURES / "story__payment_flow.md"
STORY_PAYMENT_BAD = FIXTURES / "story__payment_bad_refs.md"

# Waiver fixture paths
WAIVER_VALID = FIXTURES / "waiver_valid_python.prompt"
WAIVER_EXPIRED = FIXTURES / "waiver_expired_python.prompt"
WAIVER_MISSING_FIELDS = FIXTURES / "waiver_missing_fields_python.prompt"
WAIVER_REF_MISSING = FIXTURES / "waiver_ref_missing_python.prompt"

# Additional fixture paths
CAPABILITIES_NO_MODAL = FIXTURES / "capabilities_no_modal_python.prompt"
COVERAGE_UNCHECKED = FIXTURES / "coverage_unchecked_python.prompt"
NON_SEQUENTIAL = FIXTURES / "non_sequential_ids_python.prompt"


@pytest.fixture
def runner():
    return CliRunner()


def _invoke(runner: CliRunner, *args) -> object:
    return runner.invoke(
        cli.cli,
        ["--quiet", "contracts", "check", *args],
        catch_exceptions=False,
    )


def _json_invoke(runner: CliRunner, *args) -> object:
    return runner.invoke(
        cli.cli,
        ["--quiet", "contracts", "check", "--json", *args],
        catch_exceptions=False,
    )


def _issues(data: list, code: str | None = None) -> list:
    all_issues = [i for entry in data for i in entry["issues"]]
    if code:
        return [i for i in all_issues if i["code"] == code]
    return all_issues


# ---------------------------------------------------------------------------
# TestCleanRealisticPrompts
# ---------------------------------------------------------------------------

class TestCleanRealisticPrompts:
    """Fully-specified realistic prompts must produce zero issues."""

    def test_payment_api_clean_exits_zero(self, runner):
        result = _invoke(runner, str(PAYMENT_CLEAN))
        assert result.exit_code == 0

    def test_payment_api_clean_json_zero_counts(self, runner):
        result = _json_invoke(runner, str(PAYMENT_CLEAN))
        data = json.loads(result.output)
        assert data[0]["warn_count"] == 0
        assert data[0]["error_count"] == 0
        assert data[0]["issues"] == []

    def test_auth_service_clean_exits_zero(self, runner):
        result = _invoke(runner, str(AUTH_CLEAN))
        assert result.exit_code == 0

    def test_auth_service_with_waivers_exits_zero(self, runner):
        """Waiver W1 covers R4 MUST NOT — must suppress UNCOVERED_MUST_NOT."""
        result = _json_invoke(runner, str(AUTH_CLEAN))
        data = json.loads(result.output)
        uncovered = _issues(data, "UNCOVERED_MUST_NOT")
        assert uncovered == [], f"Unexpected UNCOVERED_MUST_NOT: {uncovered}"

    def test_auth_service_clean_json_zero_counts(self, runner):
        result = _json_invoke(runner, str(AUTH_CLEAN))
        data = json.loads(result.output)
        assert data[0]["warn_count"] == 0
        assert data[0]["error_count"] == 0


# ---------------------------------------------------------------------------
# TestPaymentApiIssues — combined defect prompt
# ---------------------------------------------------------------------------

class TestPaymentApiIssues:
    """payment_api_issues_python.prompt has DUPLICATE_ID, MISSING_MODAL,
    VAGUE_TERM, and UNCOVERED_MUST_NOT in one file."""

    def test_exits_nonzero(self, runner):
        result = _invoke(runner, str(PAYMENT_ISSUES))
        assert result.exit_code != 0

    def test_duplicate_id_detected(self, runner):
        result = _json_invoke(runner, str(PAYMENT_ISSUES))
        data = json.loads(result.output)
        dupes = _issues(data, "DUPLICATE_ID")
        assert len(dupes) >= 1
        assert any("R2" in i["rule_id"] or "R2" in i["line"] for i in dupes)

    def test_duplicate_id_is_error_not_warn(self, runner):
        result = _json_invoke(runner, str(PAYMENT_ISSUES))
        data = json.loads(result.output)
        dupes = _issues(data, "DUPLICATE_ID")
        assert all(i["level"] == "error" for i in dupes)

    def test_missing_modal_detected(self, runner):
        result = _json_invoke(runner, str(PAYMENT_ISSUES))
        data = json.loads(result.output)
        missing = _issues(data, "MISSING_MODAL")
        assert len(missing) >= 1

    def test_missing_modal_points_to_r4(self, runner):
        result = _json_invoke(runner, str(PAYMENT_ISSUES))
        data = json.loads(result.output)
        missing = _issues(data, "MISSING_MODAL")
        rule_ids = [i["rule_id"] for i in missing]
        assert "R4" in rule_ids

    def test_vague_terms_detected(self, runner):
        result = _json_invoke(runner, str(PAYMENT_ISSUES))
        data = json.loads(result.output)
        vague = _issues(data, "VAGUE_TERM")
        assert len(vague) >= 1
        terms_found = {i["term"] for i in vague}
        assert terms_found & {"reasonable", "valid", "successful"}

    def test_vague_terms_are_warnings_not_errors(self, runner):
        result = _json_invoke(runner, str(PAYMENT_ISSUES))
        data = json.loads(result.output)
        vague = _issues(data, "VAGUE_TERM")
        assert all(i["level"] == "warn" for i in vague)

    def test_uncovered_must_not_detected(self, runner):
        """R5 MUST NOT has no coverage entry — must flag UNCOVERED_MUST_NOT."""
        result = _json_invoke(runner, str(PAYMENT_ISSUES))
        data = json.loads(result.output)
        uncovered = _issues(data, "UNCOVERED_MUST_NOT")
        assert len(uncovered) >= 1

    def test_vague_term_has_suggestion(self, runner):
        result = _json_invoke(runner, str(PAYMENT_ISSUES))
        data = json.loads(result.output)
        vague = _issues(data, "VAGUE_TERM")
        assert all(i["suggestion"] != "" for i in vague)

    def test_strict_mode_exits_two(self, runner):
        result = _invoke(runner, "--strict", str(PAYMENT_ISSUES))
        assert result.exit_code == 2

    def test_strict_mode_all_issues_are_errors(self, runner):
        result = _json_invoke(runner, "--strict", str(PAYMENT_ISSUES))
        data = json.loads(result.output)
        all_issues = _issues(data)
        assert all(i["level"] == "error" for i in all_issues)

    def test_human_output_shows_issue_codes(self, runner):
        result = _invoke(runner, str(PAYMENT_ISSUES))
        assert "DUPLICATE_ID" in result.output
        assert "MISSING_MODAL" in result.output
        assert "VAGUE_TERM" in result.output

    def test_human_output_shows_rule_id(self, runner):
        result = _invoke(runner, str(PAYMENT_ISSUES))
        assert "R2" in result.output
        assert "R4" in result.output


# ---------------------------------------------------------------------------
# TestRateLimiterIssues — sequential + coverage gaps
# ---------------------------------------------------------------------------

class TestRateLimiterIssues:
    """rate_limiter_issues_python.prompt has NON_SEQUENTIAL_ID (R1,R2,R4),
    MISSING_MODAL (R4), VAGUE_TERM, UNKNOWN_COVERAGE_REF (R3), UNCOVERED_MUST_NOT."""

    def test_exits_nonzero(self, runner):
        result = _invoke(runner, str(RATE_LIMITER_ISSUES))
        assert result.exit_code != 0

    def test_non_sequential_id_detected(self, runner):
        result = _json_invoke(runner, str(RATE_LIMITER_ISSUES))
        data = json.loads(result.output)
        seq = _issues(data, "NON_SEQUENTIAL_ID")
        assert len(seq) >= 1

    def test_non_sequential_id_is_warning(self, runner):
        result = _json_invoke(runner, str(RATE_LIMITER_ISSUES))
        data = json.loads(result.output)
        seq = _issues(data, "NON_SEQUENTIAL_ID")
        assert all(i["level"] == "warn" for i in seq)

    def test_unknown_coverage_ref_detected(self, runner):
        """R3 is cited in <coverage> but not defined in <contract_rules>."""
        result = _json_invoke(runner, str(RATE_LIMITER_ISSUES))
        data = json.loads(result.output)
        unknown = _issues(data, "UNKNOWN_COVERAGE_REF")
        assert len(unknown) >= 1
        assert any("R3" in i["line"] or "R3" in i["message"] for i in unknown)

    def test_unknown_coverage_ref_is_error(self, runner):
        result = _json_invoke(runner, str(RATE_LIMITER_ISSUES))
        data = json.loads(result.output)
        unknown = _issues(data, "UNKNOWN_COVERAGE_REF")
        assert all(i["level"] == "error" for i in unknown)

    def test_vague_terms_flagged(self, runner):
        result = _json_invoke(runner, str(RATE_LIMITER_ISSUES))
        data = json.loads(result.output)
        vague = _issues(data, "VAGUE_TERM")
        terms = {i["term"] for i in vague}
        assert terms & {"reasonable", "recent", "safe"}

    def test_uncovered_must_not_flagged(self, runner):
        """R4 MUST NOT has no coverage entry."""
        result = _json_invoke(runner, str(RATE_LIMITER_ISSUES))
        data = json.loads(result.output)
        uncovered = _issues(data, "UNCOVERED_MUST_NOT")
        assert len(uncovered) >= 1

    def test_multiple_error_codes_present(self, runner):
        result = _json_invoke(runner, str(RATE_LIMITER_ISSUES))
        data = json.loads(result.output)
        codes = {i["code"] for i in _issues(data)}
        assert "UNKNOWN_COVERAGE_REF" in codes
        assert "VAGUE_TERM" in codes


# ---------------------------------------------------------------------------
# TestDirectoryIntegration
# ---------------------------------------------------------------------------

class TestDirectoryIntegration:
    """Directory scan over the fixtures folder returns mixed results."""

    def test_directory_scan_json_array(self, runner):
        result = _json_invoke(runner, str(FIXTURES))
        data = json.loads(result.output)
        assert isinstance(data, list)
        assert len(data) >= 5

    def test_clean_prompts_have_zero_issues_in_scan(self, runner):
        result = _json_invoke(runner, str(FIXTURES))
        data = json.loads(result.output)
        clean_entries = [
            e for e in data
            if Path(e["path"]).name in {
                "payment_api_clean_python.prompt",
                "auth_service_clean_python.prompt",
                "valid_contract_python.prompt",
            }
        ]
        assert len(clean_entries) == 3
        for entry in clean_entries:
            assert entry["error_count"] == 0, (
                f"{Path(entry['path']).name} has errors: "
                f"{[i['message'] for i in entry['issues'] if i['level']=='error']}"
            )

    def test_issue_prompts_have_findings_in_scan(self, runner):
        result = _json_invoke(runner, str(FIXTURES))
        data = json.loads(result.output)
        issue_entries = [
            e for e in data
            if Path(e["path"]).name in {
                "payment_api_issues_python.prompt",
                "rate_limiter_issues_python.prompt",
                "duplicate_ids_python.prompt",
            }
        ]
        assert len(issue_entries) == 3
        for entry in issue_entries:
            assert entry["warn_count"] + entry["error_count"] > 0, (
                f"{Path(entry['path']).name} unexpectedly clean"
            )

    def test_directory_scan_exit_nonzero(self, runner):
        result = _invoke(runner, str(FIXTURES))
        assert result.exit_code != 0

    def test_all_json_entries_have_required_keys(self, runner):
        result = _json_invoke(runner, str(FIXTURES))
        data = json.loads(result.output)
        for entry in data:
            for key in ("path", "warn_count", "error_count", "issues"):
                assert key in entry, f"Missing key '{key}' in {entry.get('path')}"

    def test_all_json_issues_have_required_fields(self, runner):
        result = _json_invoke(runner, str(FIXTURES))
        data = json.loads(result.output)
        all_issues = _issues(data)
        for issue in all_issues:
            for field in ("level", "code", "rule_id", "section",
                          "line", "message", "term", "suggestion", "interpretations"):
                assert field in issue, f"Issue missing field '{field}': {issue}"

    def test_legacy_prompt_in_directory_is_clean(self, runner):
        result = _json_invoke(runner, str(FIXTURES))
        data = json.loads(result.output)
        legacy = next(
            (e for e in data if "legacy_no_sections" in e["path"]), None
        )
        assert legacy is not None
        assert legacy["warn_count"] == 0
        assert legacy["error_count"] == 0


# ---------------------------------------------------------------------------
# TestStoryIntegration
# ---------------------------------------------------------------------------

class TestStoryIntegration:
    """Story ## Covers validation against realistic prompts."""

    def test_valid_story_covers_real_rule_ids(self, runner):
        result = _json_invoke(
            runner,
            "--stories", str(FIXTURES),
            str(PAYMENT_CLEAN),
        )
        data = json.loads(result.output)
        good_story = next(
            (e for e in data if "story__payment_flow" in e["path"]), None
        )
        assert good_story is not None
        assert good_story["warn_count"] == 0, (
            f"Good story has unexpected warnings: "
            f"{[i['message'] for i in good_story['issues']]}"
        )

    def test_bad_story_flags_unknown_rule_ids(self, runner):
        result = _json_invoke(
            runner,
            "--stories", str(FIXTURES),
            str(PAYMENT_CLEAN),
        )
        data = json.loads(result.output)
        bad_story = next(
            (e for e in data if "story__payment_bad_refs" in e["path"]), None
        )
        assert bad_story is not None
        unknown = [i for i in bad_story["issues"] if i["code"] == "UNKNOWN_STORY_REF"]
        assert len(unknown) >= 2  # R99 and R100

    def test_bad_story_unknown_refs_mention_rule_ids(self, runner):
        result = _json_invoke(
            runner,
            "--stories", str(FIXTURES),
            str(PAYMENT_CLEAN),
        )
        data = json.loads(result.output)
        bad_story = next(
            (e for e in data if "story__payment_bad_refs" in e["path"]), None
        )
        unknown = [i for i in bad_story["issues"] if i["code"] == "UNKNOWN_STORY_REF"]
        messages_combined = " ".join(i["message"] for i in unknown)
        assert "R99" in messages_combined or "R100" in messages_combined

    def test_story_scan_includes_prompt_results(self, runner):
        result = _json_invoke(
            runner,
            "--stories", str(FIXTURES),
            str(PAYMENT_CLEAN),
        )
        data = json.loads(result.output)
        paths = [Path(e["path"]).name for e in data]
        assert "payment_api_clean_python.prompt" in paths

    def test_stories_only_scans_story_md_not_prompts(self, runner):
        result = _json_invoke(
            runner,
            "--stories", str(FIXTURES),
            str(PAYMENT_CLEAN),
        )
        data = json.loads(result.output)
        story_entries = [e for e in data if "story__" in e["path"]]
        assert len(story_entries) >= 1
        for e in story_entries:
            assert e["path"].endswith(".md")


# ---------------------------------------------------------------------------
# TestJsonSchemaShape
# ---------------------------------------------------------------------------

class TestJsonSchemaShape:
    """Verify the exact JSON output shape matches what CI consumers expect."""

    def test_top_level_is_array(self, runner):
        result = _json_invoke(runner, str(PAYMENT_CLEAN))
        data = json.loads(result.output)
        assert isinstance(data, list)

    def test_path_is_string(self, runner):
        result = _json_invoke(runner, str(PAYMENT_CLEAN))
        data = json.loads(result.output)
        assert isinstance(data[0]["path"], str)

    def test_counts_are_ints(self, runner):
        result = _json_invoke(runner, str(PAYMENT_CLEAN))
        data = json.loads(result.output)
        assert isinstance(data[0]["warn_count"], int)
        assert isinstance(data[0]["error_count"], int)

    def test_issues_is_list(self, runner):
        result = _json_invoke(runner, str(PAYMENT_CLEAN))
        data = json.loads(result.output)
        assert isinstance(data[0]["issues"], list)

    def test_issue_level_values(self, runner):
        result = _json_invoke(runner, str(PAYMENT_ISSUES))
        data = json.loads(result.output)
        for issue in _issues(data):
            assert issue["level"] in ("warn", "error")

    def test_issue_interpretations_is_list(self, runner):
        result = _json_invoke(runner, str(PAYMENT_ISSUES))
        data = json.loads(result.output)
        for issue in _issues(data):
            assert isinstance(issue["interpretations"], list)

    def test_warn_plus_error_count_matches_issues_length(self, runner):
        result = _json_invoke(runner, str(PAYMENT_ISSUES))
        data = json.loads(result.output)
        for entry in data:
            actual_warns = sum(1 for i in entry["issues"] if i["level"] == "warn")
            actual_errors = sum(1 for i in entry["issues"] if i["level"] == "error")
            assert entry["warn_count"] == actual_warns
            assert entry["error_count"] == actual_errors

    def test_json_output_is_stdout_only(self, runner):
        """JSON must be on stdout; no update-check noise should contaminate it."""
        result = _json_invoke(runner, str(PAYMENT_CLEAN))
        # If this raises, stdout was contaminated with non-JSON
        json.loads(result.output)


# ---------------------------------------------------------------------------
# TestWaiverIntegration
# ---------------------------------------------------------------------------

class TestWaiverIntegration:
    """Waiver blocks: valid waivers suppress UNCOVERED_MUST_NOT; invalid
    waivers produce EXPIRED_WAIVER, MISSING_WAIVER_FIELDS, WAIVER_REF_MISSING."""

    def test_valid_waiver_exits_zero(self, runner):
        """W1 covers R3 MUST NOT with a future Expires date — must be clean."""
        result = _invoke(runner, str(WAIVER_VALID))
        assert result.exit_code == 0

    def test_valid_waiver_no_uncovered_must_not(self, runner):
        result = _json_invoke(runner, str(WAIVER_VALID))
        data = json.loads(result.output)
        uncovered = _issues(data, "UNCOVERED_MUST_NOT")
        assert uncovered == [], f"R3 MUST NOT should be covered by waiver W1: {uncovered}"

    def test_valid_waiver_no_waiver_issues(self, runner):
        result = _json_invoke(runner, str(WAIVER_VALID))
        data = json.loads(result.output)
        waiver_codes = {"EXPIRED_WAIVER", "MISSING_WAIVER_FIELDS", "WAIVER_REF_MISSING"}
        found = [i for i in _issues(data) if i["code"] in waiver_codes]
        assert found == []

    def test_expired_waiver_detected(self, runner):
        """W1 Expires: 2020-01-01 is in the past — must flag EXPIRED_WAIVER."""
        result = _json_invoke(runner, str(WAIVER_EXPIRED))
        data = json.loads(result.output)
        expired = _issues(data, "EXPIRED_WAIVER")
        assert len(expired) >= 1

    def test_expired_waiver_is_warning(self, runner):
        result = _json_invoke(runner, str(WAIVER_EXPIRED))
        data = json.loads(result.output)
        expired = _issues(data, "EXPIRED_WAIVER")
        assert all(i["level"] == "warn" for i in expired)

    def test_expired_waiver_mentions_waiver_id(self, runner):
        result = _json_invoke(runner, str(WAIVER_EXPIRED))
        data = json.loads(result.output)
        expired = _issues(data, "EXPIRED_WAIVER")
        combined = " ".join(i["message"] + i["line"] for i in expired)
        assert "W1" in combined

    def test_missing_waiver_fields_detected(self, runner):
        """W1 is missing Approved by and Expires fields."""
        result = _json_invoke(runner, str(WAIVER_MISSING_FIELDS))
        data = json.loads(result.output)
        missing = _issues(data, "MISSING_WAIVER_FIELDS")
        assert len(missing) >= 1

    def test_missing_waiver_fields_is_warning(self, runner):
        result = _json_invoke(runner, str(WAIVER_MISSING_FIELDS))
        data = json.loads(result.output)
        missing = _issues(data, "MISSING_WAIVER_FIELDS")
        assert all(i["level"] == "warn" for i in missing)

    def test_waiver_ref_missing_detected(self, runner):
        """Coverage says WAIVED W99 but W99 is not defined in <waivers>."""
        result = _json_invoke(runner, str(WAIVER_REF_MISSING))
        data = json.loads(result.output)
        ref_missing = _issues(data, "WAIVER_REF_MISSING")
        assert len(ref_missing) >= 1

    def test_waiver_ref_missing_is_error(self, runner):
        result = _json_invoke(runner, str(WAIVER_REF_MISSING))
        data = json.loads(result.output)
        ref_missing = _issues(data, "WAIVER_REF_MISSING")
        assert all(i["level"] == "error" for i in ref_missing)

    def test_waiver_ref_missing_mentions_waiver_id(self, runner):
        result = _json_invoke(runner, str(WAIVER_REF_MISSING))
        data = json.loads(result.output)
        ref_missing = _issues(data, "WAIVER_REF_MISSING")
        combined = " ".join(i["message"] + i["line"] for i in ref_missing)
        assert "W99" in combined

    def test_valid_waiver_json_zero_counts(self, runner):
        result = _json_invoke(runner, str(WAIVER_VALID))
        data = json.loads(result.output)
        assert data[0]["warn_count"] == 0
        assert data[0]["error_count"] == 0


# ---------------------------------------------------------------------------
# TestCapabilitiesAndCoverage
# ---------------------------------------------------------------------------

class TestCapabilitiesAndCoverage:
    """Capabilities section and coverage checks."""

    def test_capabilities_no_modal_detected(self, runner):
        """A capabilities line without MUST/MUST NOT/MAY/SHOULD must flag MISSING_MODAL."""
        result = _json_invoke(runner, str(CAPABILITIES_NO_MODAL))
        data = json.loads(result.output)
        missing = _issues(data, "MISSING_MODAL")
        assert len(missing) >= 1

    def test_capabilities_no_modal_is_warning(self, runner):
        result = _json_invoke(runner, str(CAPABILITIES_NO_MODAL))
        data = json.loads(result.output)
        missing = _issues(data, "MISSING_MODAL")
        assert all(i["level"] == "warn" for i in missing)

    def test_capabilities_with_modal_not_flagged(self, runner):
        """Lines that DO have MAY/MUST/MUST NOT must not be flagged."""
        result = _json_invoke(runner, str(CAPABILITIES_NO_MODAL))
        data = json.loads(result.output)
        missing = _issues(data, "MISSING_MODAL")
        flagged_lines = [i["line"] for i in missing]
        for line in flagged_lines:
            assert not any(
                modal in line.upper()
                for modal in ("MUST NOT", "MUST", "MAY", "SHOULD", "DOES NOT")
            )

    def test_coverage_unchecked_rule_detected(self, runner):
        """R2 coverage entry starts with TODO — must flag UNCHECKED_RULE."""
        result = _json_invoke(runner, str(COVERAGE_UNCHECKED))
        data = json.loads(result.output)
        unchecked = _issues(data, "UNCHECKED_RULE")
        assert len(unchecked) >= 1

    def test_coverage_unchecked_rule_is_warning(self, runner):
        result = _json_invoke(runner, str(COVERAGE_UNCHECKED))
        data = json.loads(result.output)
        unchecked = _issues(data, "UNCHECKED_RULE")
        assert all(i["level"] == "warn" for i in unchecked)

    def test_coverage_unchecked_mentions_rule(self, runner):
        result = _json_invoke(runner, str(COVERAGE_UNCHECKED))
        data = json.loads(result.output)
        unchecked = _issues(data, "UNCHECKED_RULE")
        combined = " ".join(i["message"] + i["line"] for i in unchecked)
        assert "R2" in combined

    def test_coverage_checked_rules_not_flagged(self, runner):
        """R1 and R3 have real coverage entries — only R2 must be flagged."""
        result = _json_invoke(runner, str(COVERAGE_UNCHECKED))
        data = json.loads(result.output)
        unchecked = _issues(data, "UNCHECKED_RULE")
        rule_ids = [i["rule_id"] for i in unchecked]
        assert "R1" not in rule_ids
        assert "R3" not in rule_ids


# ---------------------------------------------------------------------------
# TestExitCodeSemantics
# ---------------------------------------------------------------------------

class TestExitCodeSemantics:
    """Exit code contract: 0=clean, 1=warnings only, 2=errors."""

    def test_clean_prompt_exits_zero(self, runner):
        result = _invoke(runner, str(PAYMENT_CLEAN))
        assert result.exit_code == 0

    def test_warnings_only_exits_one(self, runner):
        """NON_SEQUENTIAL_ID is a warning only — must exit 1, not 2."""
        result = _invoke(runner, str(NON_SEQUENTIAL))
        assert result.exit_code == 1

    def test_error_present_exits_nonzero_and_not_one(self, runner):
        """DUPLICATE_ID is an error — must exit != 0 and != 1 (i.e., 2)."""
        result = _invoke(runner, str(PAYMENT_ISSUES))
        assert result.exit_code != 0
        assert result.exit_code != 1

    def test_strict_warnings_become_errors_exits_two(self, runner):
        """NON_SEQUENTIAL_ID is a warn; with --strict it becomes an error → exit 2."""
        result = _invoke(runner, "--strict", str(NON_SEQUENTIAL))
        assert result.exit_code == 2

    def test_json_exit_code_still_nonzero_with_issues(self, runner):
        """--json flag must not suppress the exit code."""
        result = _json_invoke(runner, str(PAYMENT_ISSUES))
        assert result.exit_code != 0

    def test_json_exit_code_zero_for_clean(self, runner):
        result = _json_invoke(runner, str(PAYMENT_CLEAN))
        assert result.exit_code == 0


# ---------------------------------------------------------------------------
# TestRecursiveStoryScanning
# ---------------------------------------------------------------------------

class TestRecursiveStoryScanning:
    """--stories must scan subdirectories recursively (rglob, not glob)."""

    def test_stories_in_subdirectory_are_found(self, runner, tmp_path):
        """Story files nested in a subdirectory must be included in output."""
        subdir = tmp_path / "sub"
        subdir.mkdir()
        story = subdir / "story__nested.md"
        story.write_text("# Nested story\n\n## Story\nAs a user.\n")
        result = _json_invoke(runner, "--stories", str(tmp_path), str(PAYMENT_CLEAN))
        data = json.loads(result.output)
        story_paths = [e["path"] for e in data if "story__nested" in e["path"]]
        assert len(story_paths) == 1, (
            f"Nested story not found in output. Paths: {[e['path'] for e in data]}"
        )

    def test_flat_and_nested_stories_both_found(self, runner, tmp_path):
        """Both top-level and subdirectory stories must appear in a single scan."""
        flat = tmp_path / "story__flat.md"
        flat.write_text("# Flat story\n\n## Story\nAs a user.\n")
        nested_dir = tmp_path / "module_a"
        nested_dir.mkdir()
        nested = nested_dir / "story__nested.md"
        nested.write_text("# Nested story\n\n## Story\nAs a user.\n")

        result = _json_invoke(runner, "--stories", str(tmp_path), str(PAYMENT_CLEAN))
        data = json.loads(result.output)
        story_names = {Path(e["path"]).name for e in data if "story__" in e["path"]}
        assert "story__flat.md" in story_names
        assert "story__nested.md" in story_names

    def test_non_story_md_files_not_scanned(self, runner, tmp_path):
        """Files not matching story__*.md must not appear in story results."""
        regular = tmp_path / "README.md"
        regular.write_text("# README\nThis is not a story.\n")
        story = tmp_path / "story__real.md"
        story.write_text("# Real story\n\n## Story\nAs a user.\n")

        result = _json_invoke(runner, "--stories", str(tmp_path), str(PAYMENT_CLEAN))
        data = json.loads(result.output)
        story_paths = [e["path"] for e in data]
        assert not any("README" in p for p in story_paths)

    def test_stories_json_with_stories_flag_is_valid_json(self, runner):
        """--json output when --stories is also passed must still be parseable."""
        result = _json_invoke(
            runner, "--stories", str(FIXTURES), str(PAYMENT_CLEAN)
        )
        data = json.loads(result.output)
        assert isinstance(data, list)

    def test_stories_results_contain_md_extension(self, runner):
        result = _json_invoke(
            runner, "--stories", str(FIXTURES), str(PAYMENT_CLEAN)
        )
        data = json.loads(result.output)
        story_entries = [e for e in data if "story__" in e["path"]]
        assert len(story_entries) >= 2
        for e in story_entries:
            assert e["path"].endswith(".md")


# ---------------------------------------------------------------------------
# TestStrictModeWithStories
# ---------------------------------------------------------------------------

class TestStrictModeWithStories:
    """--strict escalates warnings in both prompt and story results."""

    def test_strict_bad_story_exits_two(self, runner):
        """A story with UNKNOWN_STORY_REF warnings + --strict must exit 2."""
        result = _invoke(
            runner, "--strict", "--stories", str(FIXTURES), str(PAYMENT_CLEAN)
        )
        assert result.exit_code == 2

    def test_strict_bad_story_issues_are_errors(self, runner):
        result = _json_invoke(
            runner, "--strict", "--stories", str(FIXTURES), str(PAYMENT_CLEAN)
        )
        data = json.loads(result.output)
        bad_story = next(
            (e for e in data if "story__payment_bad_refs" in e["path"]), None
        )
        assert bad_story is not None
        for issue in bad_story["issues"]:
            assert issue["level"] == "error", (
                f"Expected error, got warn for: {issue['message']}"
            )

    def test_strict_good_story_still_exits_zero_if_all_clean(self, runner):
        """A fully clean prompt + clean story with --strict must still exit 0."""
        result = _invoke(runner, "--strict", str(PAYMENT_CLEAN))
        assert result.exit_code == 0

    def test_strict_escalates_non_sequential_in_prompt(self, runner):
        """NON_SEQUENTIAL_ID is warn by default; with --strict it becomes error."""
        result = _json_invoke(runner, "--strict", str(NON_SEQUENTIAL))
        data = json.loads(result.output)
        seq = _issues(data, "NON_SEQUENTIAL_ID")
        assert len(seq) >= 1
        assert all(i["level"] == "error" for i in seq)


# ---------------------------------------------------------------------------
# TestBundledPromptsNoErrors
# ---------------------------------------------------------------------------

class TestBundledPromptsNoErrors:
    """All real bundled pdd/prompts/*.prompt must produce zero errors."""

    def test_bundled_prompts_no_errors(self, runner):
        pdd_prompts = Path(__file__).parents[2] / "pdd" / "prompts"
        failures = []
        for p in sorted(pdd_prompts.rglob("*.prompt")):
            result = _json_invoke(runner, str(p))
            try:
                data = json.loads(result.output)
            except Exception:
                failures.append(f"{p.name}: non-JSON output")
                continue
            errors = [i for entry in data for i in entry["issues"]
                      if i["level"] == "error"]
            if errors:
                failures.append(
                    f"{p.name}: {[e['code'] + ' ' + e['message'] for e in errors]}"
                )
        assert failures == [], "Bundled prompts produced errors:\n" + "\n".join(failures)
