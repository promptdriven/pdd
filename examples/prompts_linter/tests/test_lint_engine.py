"""
Tests for the LintEngine module.
"""
import pytest
from unittest.mock import MagicMock, patch
from src.backend.core.lint_engine import LintEngine
from src.backend.models.findings import Finding, Severity, Evidence, LintReport, Summary
from src.backend.core.include_resolver import ResolutionResult

@pytest.fixture
def engine():
    return LintEngine()

@pytest.fixture
def mock_parsed_prompt():
    mock = MagicMock()
    mock.syntax_errors = []
    return mock

def test_lint_basic_orchestration(engine, mock_parsed_prompt):
    """Tests the standard successful path of the lint engine."""
    with patch.object(engine.parser, 'parse', return_value=mock_parsed_prompt):
        # We also need to mock registry rules because the engine loads them
        # engine.registry is actually default_registry imported.
        # We can mock get_all_rules on the imported object.
        from src.backend.rules.registry import default_registry
        
        mock_rule = MagicMock()
        mock_rule.rule_id = "test-rule"
        # Mock .check() or .analyze()
        mock_rule.check.return_value = [
            Finding(rule_id="test-rule", title="Test Rule", message="test", severity=Severity.INFO, evidence=Evidence(line_start=1, line_end=1))
        ]
        # Make it look like an object with rule_id attribute
        mock_rule.analyze.return_value = mock_rule.check.return_value

        with patch.object(default_registry, 'get_all_rules', return_value=[mock_rule]):
            report = engine.lint("some content", file_path="test.pdd")
            
            assert isinstance(report, LintReport)
            assert report.filename == "test.pdd"
            assert len(report.findings) == 1
            assert report.findings[0].rule_id == "test-rule"
            assert report.summary.score > 0

def test_lint_parser_failure(engine):
    """Tests that a critical parser failure returns a 0-score report."""
    with patch.object(engine.parser, 'parse', side_effect=RuntimeError("Parser Crash")):
        report = engine.lint("invalid content")
        
        assert len(report.findings) == 1
        assert report.findings[0].rule_id == "parser_critical_error"
        assert report.findings[0].severity == Severity.ERROR
        assert report.summary.score == 0 # Force failure score? Or calculation?
        # In current implementation, score calculation for 1 error: 100 - 15 = 85.
        # But parser error logic in lint_engine returns score=0 explicitly.
        assert report.summary.score == 0

def test_lint_include_resolution(engine, mock_parsed_prompt):
    """Tests that include resolution updates stats and findings."""
    res_result = ResolutionResult(
        resolved_files=["file1.txt"],
        total_tokens=500,
        findings=[Finding(rule_id="inc", title="Inc Err", message="inc", severity=Severity.WARN, evidence=Evidence(line_start=1, line_end=1))]
    )
    
    with patch.object(engine.parser, 'parse', return_value=mock_parsed_prompt), \
         patch.object(engine.resolver, 'resolve', return_value=res_result):
        
        report = engine.lint("content", options={"resolve_includes": True})
        
        assert report.summary.token_count_estimate == 500
        assert len(report.findings) == 1
        assert report.findings[0].rule_id == "inc"

def test_lint_rule_crash_handling(engine, mock_parsed_prompt):
    """Tests that a crashing rule adds a warning but doesn't stop the engine."""
    mock_rule_ok = MagicMock()
    mock_rule_ok.rule_id = "ok-rule"
    mock_rule_ok.check.return_value = []
    
    mock_rule_crash = MagicMock()
    mock_rule_crash.rule_id = "crash-rule"
    mock_rule_crash.check.side_effect = Exception("Boom")
    
    from src.backend.rules.registry import default_registry
    with patch.object(engine.parser, 'parse', return_value=mock_parsed_prompt), \
         patch.object(default_registry, 'get_all_rules', return_value=[mock_rule_crash, mock_rule_ok]):

        report = engine.lint("content")
        
        # Should have 1 finding for the crash
        assert len(report.findings) == 1
        assert report.findings[0].rule_id == "internal_linter_error"
        assert report.findings[0].severity == Severity.WARN

def test_lint_disabled_rules(engine, mock_parsed_prompt):
    """Tests that rules in the disabled_rules option are not executed."""
    mock_rule = MagicMock()
    mock_rule.rule_id = "disabled-rule"
    
    from src.backend.rules.registry import default_registry
    with patch.object(engine.parser, 'parse', return_value=mock_parsed_prompt), \
         patch.object(default_registry, 'get_all_rules', return_value=[mock_rule]):

        engine.lint("content", options={"disabled_rules": ["disabled-rule"]})
        
        # Should NOT have called check/analyze
        mock_rule.check.assert_not_called()
        mock_rule.analyze.assert_not_called()

def test_scoring_logic_properties_z3():
    """
    Formally verify the scoring algorithm logic.
    """
    try:
        from z3 import Int, Solver, If, unsat
    except ImportError:
        pytest.skip("z3-solver not installed")

    s = Solver()

    # Variables
    num_errors = Int('num_errors')
    num_warns = Int('num_warns')
    num_infos = Int('num_infos')

    # Constraints
    s.add(num_errors >= 0, num_warns >= 0, num_infos >= 0)

    # Logic from lint_engine
    def get_score_expr(e, w, i):
        err_deduct = e * 15
        warn_deduct = w * 7
        info_deduct = i * 2

        # Caps logic (min(val, cap))
        # Logic: if val > cap then cap else val
        actual_err = If(err_deduct > 45, 45, err_deduct)
        actual_warn = If(warn_deduct > 35, 35, warn_deduct)
        actual_info = If(info_deduct > 20, 20, info_deduct)

        raw_score = 100 - (actual_err + actual_warn + actual_info)
        return If(raw_score < 0, 0, raw_score)

    score = get_score_expr(num_errors, num_warns, num_infos)

    # Prop 1: Score <= 100
    s.push()
    s.add(score > 100)
    assert s.check() == unsat

    # Prop 2: Score >= 0
    s.pop()
    s.push()
    s.add(score < 0)
    assert s.check() == unsat
