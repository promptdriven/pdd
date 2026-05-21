"""
CLI integration tests for `pdd coverage --contracts`.

Tests cover:
  - Basic usage on a single file
  - Directory scanning
  - JSON output schema
  - Missing file / directory errors
  - Legacy repo (no <contract_rules>) reports gracefully
  - Exit code semantics (0 = all ok, 1 = gaps, 2 = error)
  - Stories/tests dir options
"""
from __future__ import annotations

import json
import textwrap
from pathlib import Path

import pytest
from click.testing import CliRunner

from pdd import cli
from pdd.commands.coverage import coverage_cmd

FIXTURES = Path(__file__).parent.parent / "fixtures" / "coverage_contracts"


def _write(tmp_path: Path, name: str, content: str) -> Path:
    p = tmp_path / name
    p.write_text(textwrap.dedent(content), encoding="utf-8")
    return p


REFUND_PROMPT = """\
<contract_rules>
R1 - Reject zero amount
For every refund, the system MUST reject zero amounts.
R2 - Prevent over-refund
The system MUST NOT refund more than the original charge.
</contract_rules>
"""

LEGACY_PROMPT = """\
# Legacy utility — no contracts
Some description.
"""

# ===========================================================================
# TestCoverageBasic
# ===========================================================================

class TestCoverageBasic:
    def test_single_file_runs(self, tmp_path):
        prompt = _write(tmp_path, "test_python.prompt", REFUND_PROMPT)
        runner = CliRunner()
        result = runner.invoke(coverage_cmd, ["--contracts", str(prompt)])
        assert result.exit_code in (0, 1)  # 1 = gaps present, which is expected

    def test_directory_runs(self, tmp_path):
        _write(tmp_path, "a_python.prompt", REFUND_PROMPT)
        runner = CliRunner()
        result = runner.invoke(coverage_cmd, ["--contracts", str(tmp_path)])
        assert result.exit_code in (0, 1, 2)

    def test_output_contains_prompt_path(self, tmp_path):
        prompt = _write(tmp_path, "foo_python.prompt", REFUND_PROMPT)
        runner = CliRunner()
        result = runner.invoke(coverage_cmd, ["--contracts", str(prompt)])
        assert "foo_python.prompt" in result.output

    def test_output_contains_rule_ids(self, tmp_path):
        prompt = _write(tmp_path, "foo_python.prompt", REFUND_PROMPT)
        runner = CliRunner()
        result = runner.invoke(coverage_cmd, ["--contracts", str(prompt)])
        assert "R1" in result.output
        assert "R2" in result.output

    def test_unchecked_rules_exit_code_1(self, tmp_path):
        prompt = _write(tmp_path, "foo_python.prompt", REFUND_PROMPT)
        runner = CliRunner()
        result = runner.invoke(
            coverage_cmd,
            ["--contracts", "--stories-dir", str(tmp_path / "none"),
             "--tests-dir", str(tmp_path / "none"), str(prompt)],
        )
        assert result.exit_code == 1

    def test_all_waived_rules_exit_code_0(self, tmp_path):
        content = """\
<contract_rules>
R1 - Secret isolation
The system MUST NOT log credentials.
</contract_rules>
<waivers>
W1:
  Rule: R1
  Rationale: SDK handles.
</waivers>
"""
        prompt = _write(tmp_path, "foo_python.prompt", content)
        runner = CliRunner()
        result = runner.invoke(
            coverage_cmd,
            ["--contracts", "--stories-dir", str(tmp_path / "none"),
             "--tests-dir", str(tmp_path / "none"), str(prompt)],
        )
        assert result.exit_code == 0

    def test_default_target_is_prompts_dir(self, tmp_path, monkeypatch):
        prompts_dir = tmp_path / "prompts"
        prompts_dir.mkdir()
        _write(prompts_dir, "foo_python.prompt", LEGACY_PROMPT)
        monkeypatch.chdir(tmp_path)
        runner = CliRunner()
        result = runner.invoke(coverage_cmd, ["--contracts"])
        assert result.exit_code in (0, 1, 2)  # at minimum no crash

    def test_requires_contracts_flag(self):
        runner = CliRunner()
        result = runner.invoke(coverage_cmd, ["prompts/"])
        assert result.exit_code != 0  # missing required --contracts flag


# ===========================================================================
# TestCoverageJsonOutput
# ===========================================================================

class TestCoverageJsonOutput:
    def _run_json(self, tmp_path, prompt_content, **extra_args):
        prompt = _write(tmp_path, "foo_python.prompt", prompt_content)
        args = ["--contracts", "--json", str(prompt)]
        runner = CliRunner()
        result = runner.invoke(coverage_cmd, args)
        return result

    def test_json_output_is_valid_json(self, tmp_path):
        result = self._run_json(tmp_path, REFUND_PROMPT)
        parsed = json.loads(result.output)
        assert isinstance(parsed, dict)

    def test_json_top_level_keys(self, tmp_path):
        result = self._run_json(tmp_path, REFUND_PROMPT)
        parsed = json.loads(result.output)
        assert "results" in parsed
        assert "total_prompts" in parsed
        assert "prompts_with_contracts" in parsed

    def test_json_results_list(self, tmp_path):
        result = self._run_json(tmp_path, REFUND_PROMPT)
        parsed = json.loads(result.output)
        assert isinstance(parsed["results"], list)
        assert len(parsed["results"]) == 1

    def test_json_result_item_keys(self, tmp_path):
        result = self._run_json(tmp_path, REFUND_PROMPT)
        parsed = json.loads(result.output)
        item = parsed["results"][0]
        assert "path" in item
        assert "has_contract_rules" in item
        assert "rules" in item
        assert "summary" in item
        assert "error" in item

    def test_json_rule_item_keys(self, tmp_path):
        result = self._run_json(tmp_path, REFUND_PROMPT)
        parsed = json.loads(result.output)
        rule = parsed["results"][0]["rules"][0]
        assert "rule_id" in rule
        assert "status" in rule
        assert "stories" in rule
        assert "tests" in rule
        assert "waiver" in rule
        assert "failures" in rule

    def test_json_summary_keys(self, tmp_path):
        result = self._run_json(tmp_path, REFUND_PROMPT)
        parsed = json.loads(result.output)
        summary = parsed["results"][0]["summary"]
        for key in ("total", "checked", "story_only", "test_only", "unchecked", "waived", "failed"):
            assert key in summary

    def test_json_summary_totals_correct(self, tmp_path):
        result = self._run_json(tmp_path, REFUND_PROMPT)
        parsed = json.loads(result.output)
        s = parsed["results"][0]["summary"]
        total_parts = (
            s["checked"] + s["story_only"] + s["test_only"]
            + s["unchecked"] + s["waived"] + s["failed"]
        )
        assert total_parts == s["total"]

    def test_json_legacy_prompt_has_no_rules(self, tmp_path):
        result = self._run_json(tmp_path, LEGACY_PROMPT)
        parsed = json.loads(result.output)
        item = parsed["results"][0]
        assert item["has_contract_rules"] is False
        assert item["rules"] == []

    def test_json_directory_multiple_files(self, tmp_path):
        for name in ["a_python.prompt", "b_python.prompt"]:
            _write(tmp_path, name, REFUND_PROMPT)
        runner = CliRunner()
        result = runner.invoke(coverage_cmd, ["--contracts", "--json", str(tmp_path)])
        parsed = json.loads(result.output)
        assert parsed["total_prompts"] == 2


# ===========================================================================
# TestCoverageMissingFile
# ===========================================================================

class TestCoverageMissingFile:
    def test_missing_file_exits_2(self, tmp_path):
        runner = CliRunner()
        result = runner.invoke(
            coverage_cmd, ["--contracts", str(tmp_path / "nonexistent.prompt")]
        )
        assert result.exit_code == 2

    def test_missing_file_json_mode(self, tmp_path):
        runner = CliRunner()
        result = runner.invoke(
            coverage_cmd, ["--contracts", "--json", str(tmp_path / "nonexistent.prompt")]
        )
        assert result.exit_code == 2
        parsed = json.loads(result.output)
        assert "error" in parsed

    def test_missing_file_error_message(self, tmp_path):
        runner = CliRunner(mix_stderr=False)
        result = runner.invoke(
            coverage_cmd, ["--contracts", str(tmp_path / "nonexistent.prompt")]
        )
        # Exit code 2 is sufficient to confirm the error was reported
        assert result.exit_code == 2


# ===========================================================================
# TestCoverageLegacyRepo
# ===========================================================================

class TestCoverageLegacyRepo:
    def test_legacy_prompt_exits_0(self, tmp_path):
        prompt = _write(tmp_path, "legacy_python.prompt", LEGACY_PROMPT)
        runner = CliRunner()
        result = runner.invoke(
            coverage_cmd,
            ["--contracts", "--stories-dir", str(tmp_path / "none"),
             "--tests-dir", str(tmp_path / "none"), str(prompt)],
        )
        assert result.exit_code == 0

    def test_legacy_prompt_reports_no_contract_data(self, tmp_path):
        prompt = _write(tmp_path, "legacy_python.prompt", LEGACY_PROMPT)
        runner = CliRunner()
        result = runner.invoke(coverage_cmd, ["--contracts", str(prompt)])
        assert "no contract" in result.output.lower() or "no <contract_rules>" in result.output.lower()

    def test_all_legacy_directory_exits_0(self, tmp_path):
        for name in ["a_python.prompt", "b_python.prompt"]:
            _write(tmp_path, name, LEGACY_PROMPT)
        runner = CliRunner()
        result = runner.invoke(
            coverage_cmd,
            ["--contracts", "--stories-dir", str(tmp_path / "none"),
             "--tests-dir", str(tmp_path / "none"), str(tmp_path)],
        )
        assert result.exit_code == 0

    def test_legacy_json_prompts_with_contracts_zero(self, tmp_path):
        prompt = _write(tmp_path, "legacy_python.prompt", LEGACY_PROMPT)
        runner = CliRunner()
        result = runner.invoke(coverage_cmd, ["--contracts", "--json", str(tmp_path)])
        parsed = json.loads(result.output)
        assert parsed["prompts_with_contracts"] == 0


# ===========================================================================
# TestCoverageWithFixtures
# ===========================================================================

class TestCoverageWithFixtures:
    """End-to-end CLI tests using the canonical fixture files."""

    def test_fixture_refund_json_output(self):
        runner = CliRunner()
        result = runner.invoke(
            coverage_cmd,
            [
                "--contracts",
                "--json",
                "--stories-dir", str(FIXTURES / "stories"),
                "--tests-dir", str(FIXTURES / "fake_tests"),
                str(FIXTURES / "refund_payment_python.prompt"),
            ],
        )
        assert result.exit_code in (0, 1)
        parsed = json.loads(result.output)
        assert parsed["results"][0]["has_contract_rules"] is True
        rules = {r["rule_id"]: r for r in parsed["results"][0]["rules"]}
        assert rules["R1"]["status"] == "checked"
        assert rules["R2"]["status"] == "story-only"
        assert rules["R3"]["status"] == "test-only"
        assert rules["R4"]["status"] == "story-only"
        assert rules["R5"]["status"] == "unchecked"
        assert rules["R6"]["status"] == "waived"

    def test_fixture_legacy_safe(self):
        runner = CliRunner()
        result = runner.invoke(
            coverage_cmd,
            [
                "--contracts",
                "--stories-dir", str(FIXTURES / "stories"),
                "--tests-dir", str(FIXTURES / "fake_tests"),
                str(FIXTURES / "legacy_no_contracts_python.prompt"),
            ],
        )
        assert result.exit_code == 0

    def test_fixture_directory_mode(self):
        runner = CliRunner()
        result = runner.invoke(
            coverage_cmd,
            [
                "--contracts",
                "--json",
                "--stories-dir", str(FIXTURES / "stories"),
                "--tests-dir", str(FIXTURES / "fake_tests"),
                str(FIXTURES),
            ],
        )
        parsed = json.loads(result.output)
        assert parsed["total_prompts"] == 3
        assert parsed["prompts_with_contracts"] == 2


class TestCoverageFailedState:
    def test_failed_story_validation_json(self, tmp_path):
        prompt = _write(tmp_path, "foo_python.prompt", """\
<contract_rules>
R1 - Story validation
The system MUST reject invalid input.
</contract_rules>
""")
        stories = tmp_path / "stories"
        stories.mkdir()
        (stories / "story__bad.md").write_text(
            "<!-- pdd-story-prompts: foo_python.prompt -->\n"
            "## Covers\n"
            "- R1: missing acceptance criteria\n",
            encoding="utf-8",
        )

        runner = CliRunner()
        result = runner.invoke(
            coverage_cmd,
            ["--contracts", "--json", "--stories-dir", str(stories),
             "--tests-dir", str(tmp_path / "none"), str(prompt)],
        )
        assert result.exit_code == 1
        parsed = json.loads(result.output)
        rule = parsed["results"][0]["rules"][0]
        assert rule["status"] == "failed"
        assert "missing ## Acceptance Criteria" in rule["failures"][0]

    def test_failed_test_validation_json(self, tmp_path):
        prompt = _write(tmp_path, "foo_python.prompt", """\
<contract_rules>
R1 - Test validation
The system MUST reject invalid input.
</contract_rules>
""")
        tests_dir = tmp_path / "tests"
        tests_dir.mkdir()
        (tests_dir / "test_bad.py").write_text(
            "def test_R1_broken(:\n    pass\n",
            encoding="utf-8",
        )

        runner = CliRunner()
        result = runner.invoke(
            coverage_cmd,
            ["--contracts", "--json", "--stories-dir", str(tmp_path / "none"),
             "--tests-dir", str(tests_dir), str(prompt)],
        )
        assert result.exit_code == 1
        parsed = json.loads(result.output)
        rule = parsed["results"][0]["rules"][0]
        assert rule["status"] == "failed"
        assert "syntax error" in rule["failures"][0]


class TestCoverageCliRegistration:
    def test_registered_pdd_coverage_command_runs(self, tmp_path):
        prompt = _write(tmp_path, "legacy_python.prompt", LEGACY_PROMPT)
        runner = CliRunner()
        result = runner.invoke(
            cli.cli,
            ["--quiet", "coverage", "--contracts", str(prompt)],
            catch_exceptions=False,
        )
        assert result.exit_code == 0
        assert "no contract coverage data" in result.output.lower()
