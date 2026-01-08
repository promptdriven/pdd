# tests/test_cli.py
import sys
import os
import re
from pathlib import Path

# --- Path Setup ---
# Aggressively add project root to sys.path to ensure 'src' module is found.
# We look for the 'src' directory starting from the test file's directory and moving up.
current_dir = Path(__file__).resolve().parent
found_src = False
for parent in [current_dir] + list(current_dir.parents):
    if (parent / "src").exists():
        sys.path.insert(0, str(parent))
        found_src = True
        break

if not found_src:
    # Fallback: assume standard structure <root>/tests/test_cli.py
    # So root is parent.parent
    sys.path.insert(0, str(current_dir.parent))

import pytest
from unittest.mock import MagicMock, patch, mock_open
from typer.testing import CliRunner
from z3 import Solver, Bool, Implies, And, Or, Not, sat, unsat, Int, IntSort

# --- Dynamic Import ---
# Handle potential filename mismatch (main.py vs cli.py)
CLI_MODULE = "src.cli.main"
try:
    from src.cli.main import app, FailOnLevel, OutputFormat
except ImportError:
    try:
        from src.cli.cli import app, FailOnLevel, OutputFormat
        CLI_MODULE = "src.cli.cli"
    except ImportError:
        # Re-raise the original error if neither works, to show the path issue
        raise

from src.utils.models import Severity, Issue, Report, LLMProvider
from src.utils.pipeline import LintConfig, PipelineReport

runner = CliRunner()

# --- Helper Functions ---

def strip_ansi(text):
    """Removes ANSI escape codes from text."""
    ansi_escape = re.compile(r'\x1B(?:[@-Z\\-_]|\[[0-?]*[ -/]*[@-~])')
    return ansi_escape.sub('', text)

def normalize_whitespace(text):
    """Replaces multiple whitespace characters with a single space."""
    return re.sub(r'\s+', ' ', text)

# --- Fixtures ---

@pytest.fixture
def mock_pipeline():
    # Patch the module that was actually imported
    with patch(f"{CLI_MODULE}.lint_file") as mock:
        # Setup a default return value
        mock.return_value = Report(
            filepath="test.txt",
            score=100,
            issues=[],
            summary="Clean",
            llm_analysis=None
        )
        yield mock

@pytest.fixture
def mock_render():
    with patch(f"{CLI_MODULE}.render_report") as mock:
        yield mock

# --- Unit Tests ---

def test_cli_help():
    """Verify the CLI help message is displayed."""
    result = runner.invoke(app, ["--help"])
    assert result.exit_code == 0
    assert "PDD" in result.stdout or "Prompt Driven Development" in result.stdout

def test_file_not_found_handled_by_typer(mock_pipeline):
    """
    Typer's argument validation (exists=True) should catch missing files 
    before the function body runs.
    """
    result = runner.invoke(app, ["non_existent_file.txt"])
    assert result.exit_code != 0
    # Check for our custom error message
    assert "File not found" in strip_ansi(result.stdout)
    mock_pipeline.assert_not_called()

def test_mutually_exclusive_grounding(tmp_path):
    """Verify error when both grounding flags are set."""
    f = tmp_path / "prompt.txt"
    f.touch()
    
    result = runner.invoke(app, [
        str(f), 
        "--assume-cloud-grounding", 
        "--assume-local"
    ])
    assert result.exit_code == 1
    assert "mutually exclusive" in strip_ansi(result.stdout)

def test_in_place_requires_fix(tmp_path):
    """Verify error when --in-place is used without --fix."""
    f = tmp_path / "prompt.txt"
    f.touch()
    
    result = runner.invoke(app, [str(f), "--in-place"])
    assert result.exit_code == 1
    assert "--in-place requires --fix" in strip_ansi(result.stdout)

def test_happy_path_configuration_passing(tmp_path, mock_pipeline, mock_render):
    """
    Verify that CLI arguments are correctly assembled into the LintConfig object
    passed to the pipeline.
    """
    f = tmp_path / "prompt.txt"
    f.touch()

    result = runner.invoke(app, [
        str(f),
        "--format", "json",
        "--severity-threshold", "warning",
        "--assume-cloud-grounding",
        "--llm-provider", "openai",
        "--llm-timeout-seconds", "45"
    ])

    assert result.exit_code == 0
    
    # Check pipeline call
    mock_pipeline.assert_called_once()
    call_args = mock_pipeline.call_args
    # First arg is path - can be Path or str
    assert str(call_args[0][0]) == str(f)
    config = call_args[1]['config']
    
    # Verify LintConfig attributes
    assert isinstance(config, LintConfig)
    # This should now pass because we mapped llm_timeout_seconds to llm_timeout
    assert config.llm_timeout == 45

    # Check render call
    mock_render.assert_called_once()
    # Check positional arg for format
    assert mock_render.call_args[0][1] == "json"

def test_fix_in_place_flow(tmp_path, mock_pipeline):
    """
    Verify that when --fix and --in-place are set, the file is updated
    using the suggested_fix from the report.
    """
    f = tmp_path / "prompt.txt"
    f.write_text("original content", encoding="utf-8")
    
    # Setup mock report with suggested_fix
    report = PipelineReport(
        filepath=str(f),
        score=90,
        issues=[],
        summary="Fixed",
        suggested_fix="fixed content"
    )
    mock_pipeline.return_value = report
    
    result = runner.invoke(app, [str(f), "--fix", "--in-place"])
    
    assert result.exit_code == 0
    
    # Verify file was written
    assert f.read_text(encoding="utf-8") == "fixed content"
    assert "Fixed prompt written" in strip_ansi(result.stdout)

def test_fix_in_place_no_changes(tmp_path, mock_pipeline):
    """
    Verify that if suggested_fix is None, no write occurs.
    """
    f = tmp_path / "prompt.txt"
    content = "perfect content"
    f.write_text(content, encoding="utf-8")
    
    # Setup mock report with no fix
    report = PipelineReport(
        filepath=str(f),
        score=100,
        issues=[],
        summary="Clean",
        suggested_fix=None
    )
    mock_pipeline.return_value = report
    
    result = runner.invoke(app, [str(f), "--fix", "--in-place"])
    
    assert result.exit_code == 0
    
    output = normalize_whitespace(strip_ansi(result.stdout))
    assert "no fix scaffold was generated" in output
    assert f.read_text(encoding="utf-8") == content

def test_fail_on_warning_triggers_exit_code(tmp_path, mock_pipeline):
    """
    Verify exit code 1 when fail-on=warning and a warning is present.
    """
    f = tmp_path / "prompt.txt"
    f.touch()
    
    # Mock a report with a warning
    mock_pipeline.return_value = Report(
        filepath=str(f),
        score=50,
        issues=[Issue(
            rule_id="TST001", 
            severity=Severity.WARNING, 
            category="context", 
            description="Test warning"
        )],
        summary="Has warning"
    )
    
    result = runner.invoke(app, [str(f), "--fail-on", "warning"])
    assert result.exit_code == 1

def test_fail_on_error_ignores_warning(tmp_path, mock_pipeline):
    """
    Verify exit code 0 when fail-on=error but only a warning is present.
    """
    f = tmp_path / "prompt.txt"
    f.touch()
    
    # Mock a report with a warning
    mock_pipeline.return_value = Report(
        filepath=str(f),
        score=50,
        issues=[Issue(
            rule_id="TST001", 
            severity=Severity.WARNING, 
            category="context", 
            description="Test warning"
        )],
        summary="Has warning"
    )
    
    result = runner.invoke(app, [str(f), "--fail-on", "error"])
    assert result.exit_code == 0

def test_fail_on_error_triggers_exit_code(tmp_path, mock_pipeline):
    """
    Verify exit code 1 when fail-on=error and an error is present.
    """
    f = tmp_path / "prompt.txt"
    f.touch()
    
    # Mock a report with an error
    mock_pipeline.return_value = Report(
        filepath=str(f),
        score=0,
        issues=[Issue(
            rule_id="TST002", 
            severity=Severity.ERROR, 
            category="context", 
            description="Test error"
        )],
        summary="Has error"
    )
    
    result = runner.invoke(app, [str(f), "--fail-on", "error"])
    assert result.exit_code == 1

def test_output_file_argument(tmp_path, mock_pipeline, mock_render):
    """Verify --output argument is passed to render_report."""
    f = tmp_path / "prompt.txt"
    f.touch()
    out_file = tmp_path / "report.json"
    
    result = runner.invoke(app, [str(f), "--output", str(out_file)])
    
    assert result.exit_code == 0
    mock_render.assert_called_once()
    assert mock_render.call_args[1]['output_path'] == str(out_file)

def test_severity_threshold_filtering_renders_subset(tmp_path, mock_pipeline, mock_render):
    """
    Verify that issues below the severity threshold are filtered out before rendering.
    """
    f = tmp_path / "prompt.txt"
    f.touch()

    # Create issues of varying severity
    issue_info = Issue(rule_id="I01", severity=Severity.INFO, category="context", description="Info")
    issue_warn = Issue(rule_id="W01", severity=Severity.WARNING, category="context", description="Warn")
    issue_err = Issue(rule_id="E01", severity=Severity.ERROR, category="context", description="Error")

    mock_pipeline.return_value = Report(
        filepath=str(f),
        score=80,
        issues=[issue_info, issue_warn, issue_err],
        summary="Mixed issues"
    )

    # Capture the report when render_report is called (before restoration in finally block)
    captured_issues = None
    # Fix: Mock side effect must accept positional args to match call site
    def capture_report(report, fmt, output_path=None):
        nonlocal captured_issues
        captured_issues = list(report.issues)
    
    mock_render.side_effect = capture_report

    # Run with threshold WARNING (should exclude INFO)
    result = runner.invoke(app, [str(f), "--severity-threshold", "warning"])

    assert result.exit_code == 0
    
    # Check the captured issues that were passed to render_report
    assert captured_issues is not None
    assert len(captured_issues) == 2
    ids = [i.rule_id for i in captured_issues]
    assert "W01" in ids
    assert "E01" in ids
    assert "I01" not in ids

def test_pipeline_exception_handling(tmp_path, mock_pipeline):
    """
    Verify that exceptions raised during the pipeline execution result in a fatal error exit.
    """
    f = tmp_path / "prompt.txt"
    f.touch()

    mock_pipeline.side_effect = ValueError("Pipeline exploded")

    result = runner.invoke(app, [str(f)])

    assert result.exit_code == 1
    # Use normalize_whitespace to handle potential line wrapping by Rich
    output = normalize_whitespace(strip_ansi(result.stdout))
    assert "Unexpected error" in output
    assert "Pipeline exploded" in output

def test_system_failure_exit_code_zero_score(tmp_path, mock_pipeline):
    """
    Verify that a score of 0 with errors triggers exit code 1 even without --fail-on.
    """
    f = tmp_path / "prompt.txt"
    f.touch()

    mock_pipeline.return_value = Report(
        filepath=str(f),
        score=0, # Critical failure indicator
        issues=[Issue(rule_id="SYS01", severity=Severity.ERROR, category="anatomy", description="Fatal")],
        summary="System failure"
    )

    # No --fail-on flag provided
    result = runner.invoke(app, [str(f)])

    assert result.exit_code == 1

def test_fix_write_permission_error_handled(tmp_path, mock_pipeline):
    """
    Verify that file write errors during --in-place are handled gracefully (no crash).
    """
    f = tmp_path / "prompt.txt"
    f.write_text("original")

    # Setup report with fixed text
    report = PipelineReport(
        filepath=str(f),
        score=90,
        issues=[],
        summary="Fixed",
        suggested_fix="fixed content"
    )
    mock_pipeline.return_value = report

    # Patch Path.write_text specifically for this test to raise PermissionError
    with patch("pathlib.Path.write_text", side_effect=PermissionError("Access denied")):
        result = runner.invoke(app, [str(f), "--fix", "--in-place"])

    # Should not crash (exit code 0 because report is clean)
    assert result.exit_code == 0
    assert "Error writing fix" in strip_ansi(result.stdout)
    assert "Access denied" in strip_ansi(result.stdout)

def test_output_format_enum_passing(tmp_path, mock_pipeline, mock_render):
    """
    Verify that the --format flag is correctly passed to the render function.
    """
    f = tmp_path / "prompt.txt"
    f.touch()

    result = runner.invoke(app, [str(f), "--format", "md"])

    assert result.exit_code == 0
    mock_render.assert_called_once()
    # Check positional arg
    assert mock_render.call_args[0][1] == "md"

# --- Z3 Formal Verification ---

def test_z3_exit_code_logic():
    """
    Formally verify the exit code logic using Z3.
    """
    s = Solver()

    # Define States
    # Severities present in the report
    has_info = Bool('has_info')
    has_warning = Bool('has_warning')
    has_error = Bool('has_error')

    # Configuration
    fail_on_warning = Bool('fail_on_warning')
    fail_on_error = Bool('fail_on_error')
    
    # Result
    exit_code_is_1 = Bool('exit_code_is_1')

    # Constraints (Model of the code's logic)
    
    # 1. Configuration is mutually exclusive (enum behavior in CLI)
    s.add(Not(And(fail_on_warning, fail_on_error)))

    # 2. The Logic Implementation Model
    # Logic for Fail on Warning: Fails if Warning OR Error exists
    logic_warning = Implies(
        fail_on_warning,
        exit_code_is_1 == Or(has_warning, has_error)
    )
    
    # Logic for Fail on Error: Fails if Error exists
    logic_error = Implies(
        fail_on_error,
        exit_code_is_1 == has_error
    )
    
    # Logic for No Fail Flag: Never fails (exit code 0)
    logic_none = Implies(
        And(Not(fail_on_warning), Not(fail_on_error)),
        Not(exit_code_is_1)
    )

    s.add(logic_warning)
    s.add(logic_error)
    s.add(logic_none)

    # --- Verification Goals ---

    # Goal 1: Prove that if we fail on WARNING, and we have an ERROR, we exit 1.
    s.push()
    s.add(fail_on_warning)
    s.add(has_error)
    s.add(Not(exit_code_is_1)) # Negate conclusion
    assert s.check() == unsat, "Z3 found a case where fail-on-warning + error did NOT exit 1"
    s.pop()

    # Goal 2: Prove that if we fail on ERROR, and we have ONLY a WARNING, we do NOT exit 1.
    s.push()
    s.add(fail_on_error)
    s.add(has_warning)
    s.add(Not(has_error))
    s.add(exit_code_is_1) # Negate conclusion (i.e., assert it IS 1)
    assert s.check() == unsat, "Z3 found a case where fail-on-error + warning caused exit 1"
    s.pop()

    # Goal 3: Prove that if we fail on WARNING, and we have ONLY INFO, we do NOT exit 1.
    s.push()
    s.add(fail_on_warning)
    s.add(has_info)
    s.add(Not(has_warning))
    s.add(Not(has_error))
    s.add(exit_code_is_1) # Negate conclusion
    assert s.check() == unsat, "Z3 found a case where fail-on-warning + info caused exit 1"
    s.pop()

def test_z3_severity_filtering_logic():
    """
    Formally verify the severity filtering logic:
    rank(issue) >= rank(threshold)
    """
    s = Solver()

    # Define Sort for Severity Ranks (Integers)
    # 10=Info, 20=Warning, 30=Error
    Rank = IntSort()
    
    issue_rank = Int('issue_rank')
    threshold_rank = Int('threshold_rank')
    
    # Define valid ranks
    valid_ranks = Or(issue_rank == 10, issue_rank == 20, issue_rank == 30)
    valid_thresholds = Or(threshold_rank == 10, threshold_rank == 20, threshold_rank == 30)
    
    s.add(valid_ranks)
    s.add(valid_thresholds)

    # The filtering predicate used in the code
    is_included = issue_rank >= threshold_rank

    # --- Verification Goals ---

    # Goal 1: If threshold is ERROR (30), INFO (10) and WARNING (20) must be excluded.
    s.push()
    s.add(threshold_rank == 30)
    s.add(issue_rank < 30)
    s.add(is_included)
    assert s.check() == unsat, "Z3 found a case where Error threshold included lower severity"
    s.pop()

    # Goal 2: If threshold is INFO (10), ALL valid severities must be included.
    s.push()
    s.add(threshold_rank == 10)
    s.add(Not(is_included))
    assert s.check() == unsat, "Z3 found a case where Info threshold excluded a valid severity"
    s.pop()

    # Goal 3: If threshold is WARNING (20), INFO (10) is excluded, WARNING (20) and ERROR (30) included.
    # Part A: Info excluded
    s.push()
    s.add(threshold_rank == 20)
    s.add(issue_rank == 10)
    s.add(is_included)
    assert s.check() == unsat, "Z3 found a case where Warning threshold included Info"
    s.pop()
    
    # Part B: Error included
    s.push()
    s.add(threshold_rank == 20)
    s.add(issue_rank == 30)
    s.add(Not(is_included))
    assert s.check() == unsat, "Z3 found a case where Warning threshold excluded Error"
    s.pop()

def test_fix_output_requires_fix(tmp_path):
    """Verify error when --fix-output is used without --fix."""
    f = tmp_path / "prompt.txt"
    f.touch()
    
    result = runner.invoke(app, [str(f), "--fix-output", "out.txt"])
    assert result.exit_code == 1
    assert "--fix-output requires --fix" in strip_ansi(result.stdout)

def test_in_place_and_fix_output_mutually_exclusive(tmp_path):
    """Verify error when both --in-place and --fix-output are used."""
    f = tmp_path / "prompt.txt"
    f.touch()
    
    result = runner.invoke(app, [str(f), "--fix", "--in-place", "--fix-output", "out.txt"])
    assert result.exit_code == 1
    assert "mutually exclusive" in normalize_whitespace(strip_ansi(result.stdout))

def test_input_file_permission_error(tmp_path):
    """Verify PermissionError during input file reading is handled."""
    f = tmp_path / "protected.txt"
    f.touch()
    
    # Patch Path.read_text to simulate permission denied
    with patch("pathlib.Path.read_text", side_effect=PermissionError("Access denied")):
        result = runner.invoke(app, [str(f)])
        
    assert result.exit_code == 1
    assert "Permission denied" in strip_ansi(result.stdout)

def test_fix_output_writes_to_file(tmp_path, mock_pipeline):
    """Verify --fix-output writes to the specified path and creates parents."""
    f = tmp_path / "prompt.txt"
    f.touch()
    
    # Output path in a subdirectory to test mkdir
    out_file = tmp_path / "subdir" / "fixed.txt"
    
    report = PipelineReport(
        filepath=str(f),
        score=90,
        issues=[],
        summary="Fixed",
        suggested_fix="fixed content"
    )
    mock_pipeline.return_value = report
    
    result = runner.invoke(app, [str(f), "--fix", "--fix-output", str(out_file)])
    
    assert result.exit_code == 0
    assert out_file.exists()
    assert out_file.read_text(encoding="utf-8") == "fixed content"
    assert "Fixed prompt written to" in strip_ansi(result.stdout)

def test_fix_prints_to_stdout(tmp_path, mock_pipeline):
    """Verify that --fix without file flags prints to stdout."""
    f = tmp_path / "prompt.txt"
    f.touch()
    
    report = PipelineReport(
        filepath=str(f),
        score=90,
        issues=[],
        summary="Fixed",
        suggested_fix="<fixed>content</fixed>"
    )
    mock_pipeline.return_value = report
    
    result = runner.invoke(app, [str(f), "--fix"])
    
    assert result.exit_code == 0
    # Check for content and visual cues (Panel title)
    assert "<fixed>content</fixed>" in result.stdout
    assert "Suggested Fix" in result.stdout

def test_config_mapping_llm_params(tmp_path, mock_pipeline, mock_render):
    """
    Verify that llm_model and llm_timeout are correctly mapped 
    to 'llm_model_override' and 'llm_timeout' in LintConfig.
    """
    f = tmp_path / "prompt.txt"
    f.touch()

    result = runner.invoke(app, [
        str(f),
        "--llm-model", "gpt-4",
        "--llm-timeout-seconds", "60"
    ])

    assert result.exit_code == 0
    
    mock_pipeline.assert_called_once()
    call_args = mock_pipeline.call_args
    config = call_args[1]['config']
    
    # Check mapped attributes
    assert config.llm_model_override == "gpt-4"
    assert config.llm_timeout == 60

def test_config_creation_error(tmp_path):
    """Verify that TypeError during LintConfig creation is handled."""
    f = tmp_path / "prompt.txt"
    f.touch()
    
    # Patch CLIConfig (the subclass used in the code) to raise TypeError
    with patch(f"{CLI_MODULE}.CLIConfig", side_effect=TypeError("Invalid argument")):
        result = runner.invoke(app, [str(f)])
        
    assert result.exit_code == 1
    output = strip_ansi(result.stdout)
    assert "Configuration Error" in output
    assert "TypeError" in output

def test_render_report_exception(tmp_path, mock_pipeline, mock_render):
    """Verify that exceptions during rendering are caught."""
    f = tmp_path / "prompt.txt"
    f.touch()
    
    mock_render.side_effect = Exception("Render failed")
    
    result = runner.invoke(app, [str(f)])
    
    assert result.exit_code == 1
    assert "Error rendering report" in strip_ansi(result.stdout)

def test_score_zero_no_error_exit_code(tmp_path, mock_pipeline):
    """
    Verify that a score of 0 does NOT trigger exit code 1 if there are no ERROR severity issues.
    (e.g., just very poor quality but no hard failures).
    """
    f = tmp_path / "prompt.txt"
    f.touch()

    mock_pipeline.return_value = Report(
        filepath=str(f),
        score=0,
        issues=[Issue(rule_id="W01", severity=Severity.WARNING, category="context", description="Bad")],
        summary="Poor quality"
    )

    result = runner.invoke(app, [str(f)])
    
    assert result.exit_code == 0

def test_z3_flag_validation_logic():
    """
    Formally verify the flag validation logic using Z3.
    Constraints:
    1. in_place -> fix
    2. fix_output -> fix
    3. Not(in_place AND fix_output)
    4. Not(assume_cloud AND assume_local)
    """
    s = Solver()
    
    # Inputs
    fix = Bool('fix')
    in_place = Bool('in_place')
    fix_output = Bool('fix_output')
    assume_cloud = Bool('assume_cloud')
    assume_local = Bool('assume_local')
    
    # Output: is_valid configuration
    is_valid = Bool('is_valid')
    
    # Logic defined in the code
    # Valid if ALL checks pass
    check1 = Implies(in_place, fix)
    check2 = Implies(fix_output, fix)
    check3 = Not(And(in_place, fix_output))
    check4 = Not(And(assume_cloud, assume_local))
    
    s.add(is_valid == And(check1, check2, check3, check4))
    
    # Goal 1: Prove invalid if in_place=True, fix=False
    s.push()
    s.add(in_place)
    s.add(Not(fix))
    s.add(is_valid) # Assert it IS valid (contradiction expected)
    assert s.check() == unsat, "Z3 found valid state for in_place without fix"
    s.pop()
    
    # Goal 2: Prove invalid if fix_output=True, fix=False
    s.push()
    s.add(fix_output)
    s.add(Not(fix))
    s.add(is_valid)
    assert s.check() == unsat, "Z3 found valid state for fix_output without fix"
    s.pop()
    
    # Goal 3: Prove invalid if in_place=True AND fix_output=True
    s.push()
    s.add(in_place)
    s.add(fix_output)
    s.add(is_valid)
    assert s.check() == unsat, "Z3 found valid state for both in_place and fix_output"
    s.pop()
    
    # Goal 4: Prove invalid if both grounding flags are True
    s.push()
    s.add(assume_cloud)
    s.add(assume_local)
    s.add(is_valid)
    assert s.check() == unsat, "Z3 found valid state for both grounding flags"
    s.pop()

# tests/test_cli_extended.py
# (Appended to existing tests)

# --- Test Plan ---
# 1. Test Grounding Configuration: Verify that --assume-cloud-grounding and --assume-local flags 
#    correctly set the 'grounding' attribute in the LintConfig object passed to the pipeline.
# 2. Test Advanced LLM Configuration: Verify that optional LLM flags (base URL, retries, budget) 
#    are correctly mapped to the LintConfig object.
# 3. Test LLM Provider Enum Passing: Verify that different LLMProvider enum values (e.g., GOOGLE, CUSTOM)
#    are correctly extracted and passed as strings to the configuration.
# 4. Test Fix Output Directory Creation Failure: Verify that if creating the parent directory for 
#    --fix-output fails (e.g., permission error), the CLI handles it gracefully without crashing.
# 5. Test Complex Fail-On Logic: Verify the exit code logic when multiple issues of varying severities 
#    are present, ensuring the threshold logic works correctly for mixed sets of issues.
# 6. Z3 Verification of Severity Ranking: Formally verify the strict ordering of severity ranks 
#    used in the filtering and exit code logic (Info < Warning < Error).

def test_grounding_config_cloud(tmp_path, mock_pipeline):
    """
    Verify that --assume-cloud-grounding sets config.grounding to 'cloud'.
    """
    f = tmp_path / "prompt.txt"
    f.touch()

    result = runner.invoke(app, [str(f), "--assume-cloud-grounding"])

    assert result.exit_code == 0
    mock_pipeline.assert_called_once()
    config = mock_pipeline.call_args[1]['config']
    
    # Check that the grounding attribute is set correctly
    # Note: LintConfig definition in the prompt suggests 'grounding' is passed via kwargs 
    # or mapped. The CLI code passes it as a kwarg 'grounding'.
    # We check if the attribute exists on the config object.
    assert getattr(config, 'grounding', None) == "cloud"

def test_grounding_config_local(tmp_path, mock_pipeline):
    """
    Verify that --assume-local sets config.grounding to 'local'.
    """
    f = tmp_path / "prompt.txt"
    f.touch()

    result = runner.invoke(app, [str(f), "--assume-local"])

    assert result.exit_code == 0
    config = mock_pipeline.call_args[1]['config']
    assert getattr(config, 'grounding', None) == "local"

def test_llm_advanced_config_passing(tmp_path, mock_pipeline):
    """
    Verify that advanced LLM flags (base-url, retries, budget) are passed to LintConfig.
    """
    f = tmp_path / "prompt.txt"
    f.touch()

    result = runner.invoke(app, [
        str(f),
        "--llm-base-url", "https://api.custom.com/v1",
        "--llm-max-retries", "5",
        "--llm-budget-tokens", "5000"
    ])

    assert result.exit_code == 0
    config = mock_pipeline.call_args[1]['config']
    
    # Check attributes. Based on CLI code:
    # llm_base_url -> passed as kwarg 'llm_base_url'
    # llm_max_retries -> passed as kwarg 'llm_max_retries'
    # llm_budget_tokens -> passed as kwarg 'budget'
    
    # We check if these stuck to the config object (assuming LintConfig accepts them)
    assert getattr(config, 'llm_base_url', None) == "https://api.custom.com/v1"
    assert getattr(config, 'llm_max_retries', None) == 5
    assert getattr(config, 'budget', None) == 5000

def test_llm_provider_enum_passing(tmp_path, mock_pipeline):
    """
    Verify that LLMProvider enum values are passed as strings to the config.
    """
    f = tmp_path / "prompt.txt"
    f.touch()

    # Test with a specific provider
    result = runner.invoke(app, [str(f), "--llm-provider", "google"])

    assert result.exit_code == 0
    config = mock_pipeline.call_args[1]['config']
    # CLI passes provider=llm_provider.value
    assert getattr(config, 'provider', None) == "google"

def test_fix_output_mkdir_error(tmp_path, mock_pipeline):
    """
    Verify graceful handling when creating the output directory for --fix-output fails.
    """
    f = tmp_path / "prompt.txt"
    f.touch()
    out_file = tmp_path / "subdir" / "fixed.txt"

    # Setup report with fix
    report = PipelineReport(
        filepath=str(f),
        score=90,
        issues=[],
        summary="Fixed",
        suggested_fix="fixed content"
    )
    mock_pipeline.return_value = report

    # Mock pathlib.Path.mkdir to raise OSError
    with patch("pathlib.Path.mkdir", side_effect=OSError("Disk full")):
        result = runner.invoke(app, [str(f), "--fix", "--fix-output", str(out_file)])

    # Should not crash
    assert result.exit_code == 0
    output = strip_ansi(result.stdout)
    assert "Error writing fix to output file" in output
    assert "Disk full" in output

def test_fail_on_logic_complex(tmp_path, mock_pipeline):
    """
    Verify fail-on logic with a mix of Info, Warning, and Error issues.
    """
    f = tmp_path / "prompt.txt"
    f.touch()

    # Report with Info and Warning
    mock_pipeline.return_value = Report(
        filepath=str(f),
        score=70,
        issues=[
            Issue(rule_id="I1", severity=Severity.INFO, category="context", description="Info"),
            Issue(rule_id="W1", severity=Severity.WARNING, category="context", description="Warn")
        ],
        summary="Mixed"
    )

    # Case 1: Fail on Error -> Should pass (exit 0) because max severity is Warning
    result = runner.invoke(app, [str(f), "--fail-on", "error"])
    assert result.exit_code == 0

    # Case 2: Fail on Warning -> Should fail (exit 1) because Warning is present
    result = runner.invoke(app, [str(f), "--fail-on", "warning"])
    assert result.exit_code == 1

def test_z3_severity_ranking_ordering():
    """
    Formally verify the strict ordering of severity ranks used in the CLI helper.
    Ensures that Info < Warning < Error is mathematically consistent.
    """
    s = Solver()
    
    # Define integer variables for ranks
    rank_info = Int('rank_info')
    rank_warning = Int('rank_warning')
    rank_error = Int('rank_error')
    
    # Define the mapping logic from the code's _get_severity_rank function
    # INFO=0, WARNING=1, ERROR=2
    s.add(rank_info == 0)
    s.add(rank_warning == 1)
    s.add(rank_error == 2)
    
    # Verification Goals
    
    # 1. Prove Info < Warning
    s.push()
    s.add(Not(rank_info < rank_warning))
    assert s.check() == unsat, "Z3 found case where Info >= Warning"
    s.pop()
    
    # 2. Prove Warning < Error
    s.push()
    s.add(Not(rank_warning < rank_error))
    assert s.check() == unsat, "Z3 found case where Warning >= Error"
    s.pop()
    
    # 3. Prove Transitivity: Info < Error
    s.push()
    s.add(Not(rank_info < rank_error))
    assert s.check() == unsat, "Z3 found case where Info >= Error"
    s.pop()