"""Tests for pdd.commands.metadata (CLI wrapper around finalize_metadata).

Test plan (mirrors the spec in prompts/commands/metadata_python.prompt):

1. Module surface
   1a. metadata_group is a click.Group with name="metadata".
   1b. metadata_group registers a "finalize" subcommand.

2. Argument / option wiring (Click forwards values into finalize_metadata)
   2a. TARGET is required (missing TARGET fails with non-zero exit).
   2b. --language is forwarded as `language=...`.
   2c. --context is forwarded as `context_override=...`.
   2d. --dry-run is forwarded as `dry_run=True`.
   2e. Default `dry_run=False` when --dry-run is not passed.

3. Exit codes (git-plumbing style)
   3a. Normal mode + report produced => exit 0.
   3b. --dry-run + fingerprint_state != "current" => exit 1.
   3c. --dry-run + run_report_state == "stale" => exit 1.
   3d. --dry-run + everything current => exit 0.
   3e. Normal mode NEVER returns 1 even when drift exists (only writes & returns 0).

4. Human-readable output (non-JSON, non-quiet)
   4a. One-line header `metadata: <basename> [<language>]`.
   4b. Resolved paths listed with `[present]` or `[MISSING]` markers.
   4c. `fingerprint: <state>` and `run_report: <state>` lines printed.
   4d. `stale_components` shown when non-empty.
   4e. Normal mode appends `wrote fingerprint` when report.wrote_fingerprint True.
   4f. Normal mode appends `cleared stale run report` when cleared_run_report True.
   4g. Warnings prefixed with `warning:` at the end.

5. JSON output
   5a. --json emits a single JSON object parseable by `json.loads`.
   5b. JSON object contains every MetadataReport field.
   5c. Path values serialise to strings via default=str.
   5d. --quiet is ignored when --json is set (JSON still printed).

6. Quiet mode
   6a. --quiet suppresses human-readable output.
   6b. --quiet does not suppress JSON output.

7. Error handling
   7a. ValueError from finalize_metadata => stderr "error: ..." + exit 2.
   7b. Generic Exception from finalize_metadata => stderr "error: ..." + exit 2.
   7c. click.exceptions.Exit raised inside is re-raised (not swallowed).
   7d. click.Abort is re-raised.

8. Decorator absence (negative test)
   8a. Command is NOT decorated with @track_cost (would expect cost-tracking args).
   8b. Command is NOT decorated with @log_operation.
"""
from __future__ import annotations

import json
import sys
from dataclasses import dataclass, field
from pathlib import Path
from typing import Any, Dict, List
from unittest.mock import patch

import click
import pytest
from click.testing import CliRunner

# Ensure repo root on sys.path so `pdd.commands.metadata` is importable.
sys.path.insert(0, str(Path(__file__).resolve().parents[2]))

from pdd.commands.metadata import finalize, metadata_group


# ---------------------------------------------------------------------------
# Helpers
# ---------------------------------------------------------------------------


@dataclass
class FakeReport:
    """Stand-in for pdd.metadata_finalize.MetadataReport.

    Mirrors the real dataclass schema so dataclasses.asdict works on it.
    """

    basename: str = "demo"
    language: str = "python"
    paths: Dict[str, Any] = field(default_factory=lambda: {
        "prompt": Path("prompts/demo_python.prompt"),
        "code": Path("demo.py"),
        "example": Path("examples/demo_example.py"),
        "test": Path("tests/test_demo.py"),
    })
    files_present: Dict[str, bool] = field(default_factory=lambda: {
        "prompt": True, "code": True, "example": True, "test": False,
    })
    fingerprint_state: str = "current"
    run_report_state: str = "current"
    stale_components: List[str] = field(default_factory=list)
    wrote_fingerprint: bool = False
    cleared_run_report: bool = False
    warnings: List[str] = field(default_factory=list)
    dry_run: bool = False


def _invoke(*args: str, report: "FakeReport | None" = None,
            side_effect: "BaseException | None" = None,
            capture_call: "List[Dict[str, Any]] | None" = None):
    """Invoke the metadata CLI with finalize_metadata patched."""
    runner = CliRunner()

    def fake(**kwargs):
        if capture_call is not None:
            capture_call.append(kwargs)
        if side_effect is not None:
            raise side_effect
        return report if report is not None else FakeReport()

    with patch("pdd.metadata_finalize.finalize_metadata", side_effect=fake):
        return runner.invoke(metadata_group, list(args), catch_exceptions=False)


# ---------------------------------------------------------------------------
# 1. Module surface
# ---------------------------------------------------------------------------


def test_metadata_group_is_click_group():
    assert isinstance(metadata_group, click.Group)
    assert metadata_group.name == "metadata"


def test_metadata_group_has_finalize_subcommand():
    assert "finalize" in metadata_group.commands
    assert metadata_group.commands["finalize"] is finalize


# ---------------------------------------------------------------------------
# 2. Argument / option wiring
# ---------------------------------------------------------------------------


def test_target_is_required():
    runner = CliRunner()
    result = runner.invoke(metadata_group, ["finalize"])
    # Click returns exit code 2 for usage errors.
    assert result.exit_code != 0
    assert "Missing argument" in result.output or "Usage" in result.output


def test_language_option_forwarded():
    calls: List[Dict[str, Any]] = []
    _invoke("finalize", "foo", "--language", "typescript", capture_call=calls)
    assert calls[0]["language"] == "typescript"
    assert calls[0]["target"] == "foo"


def test_context_option_forwarded_as_context_override():
    calls: List[Dict[str, Any]] = []
    _invoke("finalize", "foo", "--context", "alt-context", capture_call=calls)
    assert calls[0]["context_override"] == "alt-context"


def test_dry_run_flag_forwarded():
    calls: List[Dict[str, Any]] = []
    _invoke("finalize", "foo", "--dry-run",
            report=FakeReport(dry_run=True, fingerprint_state="current"),
            capture_call=calls)
    assert calls[0]["dry_run"] is True


def test_dry_run_defaults_to_false():
    calls: List[Dict[str, Any]] = []
    _invoke("finalize", "foo", capture_call=calls)
    assert calls[0]["dry_run"] is False


# ---------------------------------------------------------------------------
# 3. Exit codes
# ---------------------------------------------------------------------------


def test_normal_mode_returns_zero_when_clean():
    result = _invoke("finalize", "foo",
                     report=FakeReport(fingerprint_state="current",
                                       run_report_state="current",
                                       wrote_fingerprint=True))
    assert result.exit_code == 0


def test_dry_run_drift_returns_one_when_fingerprint_not_current():
    result = _invoke("finalize", "foo", "--dry-run",
                     report=FakeReport(dry_run=True,
                                       fingerprint_state="stale",
                                       stale_components=["code"],
                                       run_report_state="missing"))
    assert result.exit_code == 1


def test_dry_run_drift_returns_one_when_run_report_stale():
    result = _invoke("finalize", "foo", "--dry-run",
                     report=FakeReport(dry_run=True,
                                       fingerprint_state="current",
                                       run_report_state="stale"))
    assert result.exit_code == 1


def test_dry_run_clean_returns_zero():
    result = _invoke("finalize", "foo", "--dry-run",
                     report=FakeReport(dry_run=True,
                                       fingerprint_state="current",
                                       run_report_state="current"))
    assert result.exit_code == 0


def test_normal_mode_never_returns_one_even_with_drift():
    # Normal-mode behavior: writes fingerprint, returns 0 regardless of input state.
    result = _invoke("finalize", "foo",
                     report=FakeReport(fingerprint_state="stale",
                                       stale_components=["code"],
                                       wrote_fingerprint=True))
    assert result.exit_code == 0


# ---------------------------------------------------------------------------
# 4. Human-readable output
# ---------------------------------------------------------------------------


def test_human_output_header_line():
    result = _invoke("finalize", "demo",
                     report=FakeReport(basename="demo", language="python",
                                       fingerprint_state="current",
                                       run_report_state="current"))
    assert "metadata: demo [python]" in result.output


def test_human_output_path_markers():
    result = _invoke("finalize", "foo",
                     report=FakeReport(
                         paths={"prompt": Path("p.prompt"), "code": Path("c.py")},
                         files_present={"prompt": True, "code": False},
                         fingerprint_state="current",
                         run_report_state="current",
                     ))
    assert "[present]" in result.output
    assert "[MISSING]" in result.output


def test_human_output_fingerprint_and_run_report_lines():
    result = _invoke("finalize", "foo",
                     report=FakeReport(fingerprint_state="missing",
                                       run_report_state="skipped"))
    assert "fingerprint: missing" in result.output
    assert "run_report: skipped" in result.output


def test_human_output_includes_stale_components():
    result = _invoke("finalize", "foo", "--dry-run",
                     report=FakeReport(dry_run=True,
                                       fingerprint_state="stale",
                                       stale_components=["code", "test"],
                                       run_report_state="missing"))
    assert "fingerprint: stale" in result.output
    assert "code" in result.output and "test" in result.output


def test_human_output_wrote_fingerprint_line_in_normal_mode():
    result = _invoke("finalize", "foo",
                     report=FakeReport(fingerprint_state="current",
                                       run_report_state="current",
                                       wrote_fingerprint=True))
    assert "wrote fingerprint" in result.output


def test_human_output_cleared_run_report_line():
    result = _invoke("finalize", "foo",
                     report=FakeReport(fingerprint_state="current",
                                       run_report_state="current",
                                       wrote_fingerprint=True,
                                       cleared_run_report=True))
    assert "cleared stale run report" in result.output


def test_human_output_warnings_prefixed():
    result = _invoke("finalize", "foo",
                     report=FakeReport(fingerprint_state="current",
                                       run_report_state="current",
                                       warnings=["something happened", "another note"]))
    assert "warning: something happened" in result.output
    assert "warning: another note" in result.output


def test_normal_mode_does_not_print_write_lines_when_not_written():
    result = _invoke("finalize", "foo",
                     report=FakeReport(fingerprint_state="current",
                                       run_report_state="current",
                                       wrote_fingerprint=False,
                                       cleared_run_report=False))
    assert "wrote fingerprint" not in result.output
    assert "cleared stale run report" not in result.output


# ---------------------------------------------------------------------------
# 5. JSON output
# ---------------------------------------------------------------------------


def test_json_output_is_parseable_object():
    result = _invoke("finalize", "foo", "--json",
                     report=FakeReport(fingerprint_state="current",
                                       run_report_state="current"))
    parsed = json.loads(result.output)
    assert isinstance(parsed, dict)


def test_json_output_contains_all_report_fields():
    result = _invoke("finalize", "foo", "--json",
                     report=FakeReport())
    parsed = json.loads(result.output)
    for field_name in (
        "basename", "language", "paths", "files_present",
        "fingerprint_state", "run_report_state", "stale_components",
        "wrote_fingerprint", "cleared_run_report", "warnings", "dry_run",
    ):
        assert field_name in parsed, f"missing JSON field: {field_name}"


def test_json_output_serialises_paths_as_strings():
    result = _invoke("finalize", "foo", "--json",
                     report=FakeReport(
                         paths={"prompt": Path("prompts/demo_python.prompt")},
                         files_present={"prompt": True},
                     ))
    parsed = json.loads(result.output)
    assert parsed["paths"]["prompt"] == "prompts/demo_python.prompt"


def test_json_output_does_not_emit_human_lines():
    result = _invoke("finalize", "foo", "--json",
                     report=FakeReport(fingerprint_state="current",
                                       run_report_state="current",
                                       wrote_fingerprint=True))
    # The human header should NOT be present in JSON mode.
    assert "metadata: " not in result.output
    assert "wrote fingerprint" not in result.output


def test_json_ignores_quiet_flag():
    """--quiet has no effect when --json is set; JSON is still emitted."""
    result = _invoke("finalize", "foo", "--json", "--quiet",
                     report=FakeReport(fingerprint_state="current",
                                       run_report_state="current"))
    parsed = json.loads(result.output)
    assert parsed["basename"] == "demo"


# ---------------------------------------------------------------------------
# 6. Quiet mode
# ---------------------------------------------------------------------------


def test_quiet_suppresses_human_output():
    result = _invoke("finalize", "foo", "--quiet",
                     report=FakeReport(fingerprint_state="current",
                                       run_report_state="current"))
    assert result.output == ""


# ---------------------------------------------------------------------------
# 7. Error handling
# ---------------------------------------------------------------------------


def test_value_error_results_in_exit_code_2_with_error_prefix():
    runner = CliRunner(mix_stderr=False)
    with patch(
        "pdd.metadata_finalize.finalize_metadata",
        side_effect=ValueError("bad target"),
    ):
        result = runner.invoke(metadata_group, ["finalize", "foo"], catch_exceptions=False)
    assert result.exit_code == 2
    assert "error: bad target" in result.stderr


def test_generic_exception_results_in_exit_code_2():
    runner = CliRunner(mix_stderr=False)
    with patch(
        "pdd.metadata_finalize.finalize_metadata",
        side_effect=RuntimeError("boom"),
    ):
        result = runner.invoke(metadata_group, ["finalize", "foo"], catch_exceptions=False)
    assert result.exit_code == 2
    assert "error: boom" in result.stderr


def test_click_exit_is_re_raised():
    """If finalize_metadata raises click.exceptions.Exit, the code propagates verbatim."""
    runner = CliRunner()
    with patch(
        "pdd.metadata_finalize.finalize_metadata",
        side_effect=click.exceptions.Exit(7),
    ):
        result = runner.invoke(metadata_group, ["finalize", "foo"], catch_exceptions=False)
    assert result.exit_code == 7


def test_click_abort_is_re_raised():
    runner = CliRunner()
    with patch(
        "pdd.metadata_finalize.finalize_metadata",
        side_effect=click.Abort(),
    ):
        result = runner.invoke(metadata_group, ["finalize", "foo"], catch_exceptions=False)
    # Click maps Abort -> exit code 1 by default in its standalone handler.
    assert result.exit_code == 1


# ---------------------------------------------------------------------------
# 8. Decorator absence (negative tests)
# ---------------------------------------------------------------------------


def test_finalize_command_has_no_cost_tracking_decorator():
    # @track_cost-decorated commands typically expose extra cost-related options
    # like --output-cost. Ensure no such option leaks in.
    option_names = {p.name for p in finalize.params if isinstance(p, click.Option)}
    assert "output_cost" not in option_names


def test_finalize_command_expected_options_only():
    """The finalize command exposes exactly the spec-defined options."""
    option_names = {p.name for p in finalize.params if isinstance(p, click.Option)}
    # `json_output` is the param name for the --json flag (since `json` is renamed).
    expected = {"dry_run", "json_output", "language", "context_override", "quiet"}
    assert option_names == expected
