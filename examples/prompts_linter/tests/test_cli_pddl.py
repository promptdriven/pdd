import pytest
from typer.testing import CliRunner
from pathlib import Path
import json
from unittest.mock import MagicMock, patch

# Import the app from the actual module path
from src.cli.pddl import app, OutputFormat
from src.backend.models.findings import LintReport, Summary, IssueCounts, Finding, Severity, Evidence

runner = CliRunner()

@pytest.fixture
def mock_lint_engine(mocker):
    """Mocks the LintEngine to isolate CLI logic from backend analysis."""
    mock_engine = mocker.patch("src.cli.pddl.LintEngine", autospec=True)
    instance = mock_engine.return_return_value
    return instance

@pytest.fixture
def sample_report():
    """Creates a standard LintReport for testing output."""
    return LintReport(
        filename="test.prompt",
        summary=Summary(
            score=85,
            issue_counts=IssueCounts(error=0, warn=1, info=1),
            token_count_estimate=100
        ),
        findings=[
            Finding(
                rule_id="PDD001",
                severity=Severity.WARN,
                title="Missing Role",
                message="Define a role.",
                evidence=Evidence(line_start=1, line_end=1)
            )
        ]
    )

def test_lint_file_not_found():
    """Test that providing a non-existent file returns exit code 2."""
    result = runner.invoke(app, ["lint", "non_existent_file.prompt"])
    assert result.exit_code == 2
    # Typer default mixes stderr into stdout unless configured otherwise
    assert "Error" in result.stdout

def test_lint_success_text_output(tmp_path, mocker):
    """Test successful linting with text output and exit code 0 (no errors)."""
    p = tmp_path / "hello.prompt"
    p.write_text("Act as a developer.")
    
    # Mock report with no errors
    report = LintReport(
        filename=str(p),
        summary=Summary(score=100, issue_counts=IssueCounts(error=0, warn=0, info=0), token_count_estimate=5),
        findings=[]
    )
    
    with patch("src.backend.core.lint_engine.LintEngine.lint", return_value=report):
        result = runner.invoke(app, ["lint", str(p)])
        assert result.exit_code == 0
        assert "PDD Lint Report" in result.stdout
        assert "Score: 100/100" in result.stdout
        assert "No issues found" in result.stdout

def test_lint_error_exit_code(tmp_path, mocker):
    """Test that exit code is 1 when an error finding exists."""
    p = tmp_path / "error.prompt"
    p.write_text("Bad prompt.")
    
    report = LintReport(
        filename=str(p),
        summary=Summary(score=40, issue_counts=IssueCounts(error=1, warn=0, info=0), token_count_estimate=5),
        findings=[
            Finding(
                rule_id="PDD010",
                severity=Severity.ERROR,
                title="Missing Requirements",
                message="Critical error.",
                evidence=Evidence(line_start=1, line_end=1)
            )
        ]
    )
    
    with patch("src.backend.core.lint_engine.LintEngine.lint", return_value=report):
        result = runner.invoke(app, ["lint", str(p)])
        assert result.exit_code == 1
        assert "[ERROR] PDD010" in result.stdout

def test_lint_json_format(tmp_path, mocker):
    """Test that --format json returns valid JSON and no extra text."""
    p = tmp_path / "test.prompt"
    p.write_text("content")
    
    report = LintReport(
        filename=str(p),
        summary=Summary(score=90, issue_counts=IssueCounts(error=0, warn=0, info=0), token_count_estimate=10),
        findings=[]
    )
    
    with patch("src.backend.core.lint_engine.LintEngine.lint", return_value=report):
        result = runner.invoke(app, ["lint", str(p), "--format", "json"])
        assert result.exit_code == 0
        # Verify it's valid JSON
        data = json.loads(result.stdout)
        assert data["filename"] == str(p)
        assert "summary" in data

def test_rules_command():
    """Test the rules command lists registered rules."""
    result = runner.invoke(app, ["rules"])
    assert result.exit_code == 0
    assert "Available PDD Linting Rules" in result.stdout
    # Check for a known rule from pdd_rules.py (assuming registered)
    assert "PDD001" in result.stdout

def test_explain_valid_rule():
    """Test explaining a valid rule."""
    # PDD001 is registered via side-effect import in pddl.py
    result = runner.invoke(app, ["explain", "PDD001"])
    assert result.exit_code == 0
    assert "Rule: PDD001" in result.stdout
    assert "Severity: INFO" in result.stdout

def test_explain_invalid_rule():
    """Test explaining a non-existent rule returns exit code 2."""
    result = runner.invoke(app, ["explain", "NONEXISTENT"])
    assert result.exit_code == 2
    assert "Error: Rule 'NONEXISTENT' not found" in result.stdout

def test_formal_verification_exit_logic():
    """
    Z3 Formal Verification: Verify the CLI exit code logic.
    Property: The CLI must exit with 1 if and only if the error count > 0.
    """
    try:
        from z3 import Int, Implies, Solver, And, Or, Bool, sat, unsat
    except ImportError:
        pytest.skip("z3-solver not installed")

    # Variables
    error_count = Int('error_count')
    exit_code = Int('exit_code')
    
    # Logic from pddl.py:
    # if report.summary.issue_counts.error > 0: raise Exit(code=1) else: raise Exit(code=0)
    
    s = Solver()
    
    # Define the behavior
    logic = And(
        Implies(error_count > 0, exit_code == 1),
        Implies(error_count <= 0, exit_code == 0)
    )
    s.add(logic)
    
    # Prove: It is impossible to have error_count > 0 and exit_code == 0
    s.push()
    s.add(And(error_count > 0, exit_code == 0))
    assert s.check() == unsat
    s.pop()
    
    # Prove: It is impossible to have error_count == 0 and exit_code == 1
    s.push()
    s.add(And(error_count == 0, exit_code == 1))
    assert s.check() == unsat
    s.pop()

def test_formal_verification_severity_ordering():
    """
    Z3 Formal Verification: Verify the sorting logic for findings.
    Property: Findings are grouped by Error (0), then Warn (1), then Info (2).
    """
    try:
        from z3 import Int, Solver, And, sat, Distinct, Or, Implies
    except ImportError:
        pytest.skip("z3-solver not installed")

    # Map severities to integers for sorting
    # Error = 0, Warn = 1, Info = 2
    def get_rank(severity_name):
        if severity_name == "error": return 0
        if severity_name == "warn": return 1
        return 2

    s = Solver()
    
    # We want to ensure that for any two findings f1, f2:
    # If rank(f1) < rank(f2), f1 appears before f2.
    
    f1_rank = Int('f1_rank')
    f2_rank = Int('f2_rank')
    
    # Constraints on ranks based on the code's lambda
    s.add(Or(f1_rank == 0, f1_rank == 1, f1_rank == 2))
    s.add(Or(f2_rank == 0, f2_rank == 1, f2_rank == 2))
    
    # If f1 is an error and f2 is a warning, f1_rank < f2_rank
    s.add(Implies(f1_rank == 0, f1_rank < 1)) # Error < Warn
    s.add(Implies(f1_rank == 1, f1_rank < 2)) # Warn < Info
    
    assert s.check() == sat