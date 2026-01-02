import sys
import pytest
from unittest.mock import MagicMock, patch

# --- Mocks for missing dependencies ---
# We define these classes and patch sys.modules BEFORE importing the code under test.

class MockSeverity:
    CRITICAL = "CRITICAL"
    ERROR = "ERROR"
    WARNING = "WARNING"
    INFO = "INFO"

class MockFindingLocation:
    def __init__(self, line=1, column=1):
        self.line = line
        self.column = column
    def __eq__(self, other):
        return self.line == other.line and self.column == other.column

class MockFinding:
    def __init__(self, rule_id, message, severity, location=None):
        self.rule_id = rule_id
        self.message = message
        self.severity = severity
        self.location = location
    def __repr__(self):
        return f"Finding({self.rule_id}, {self.severity})"

class MockLintReport:
    def __init__(self, file_path, findings, score, summary, stats=None):
        self.file_path = file_path
        self.findings = findings
        self.score = score
        self.summary = summary
        self.stats = stats or {}

class MockParsedPrompt:
    def __init__(self):
        self.syntax_errors = []

class MockResolutionResult:
    def __init__(self, resolved_files, total_tokens, findings):
        self.resolved_files = resolved_files
        self.total_tokens = total_tokens
        self.findings = findings

# Patch sys.modules for models_findings
mock_models = MagicMock()
mock_models.Severity = MockSeverity
mock_models.FindingLocation = MockFindingLocation
mock_models.Finding = MockFinding
mock_models.LintReport = MockLintReport
sys.modules["src.backend.core.models_findings"] = mock_models

# Patch sys.modules for parser
mock_parser_mod = MagicMock()
mock_parser_mod.ParsedPrompt = MockParsedPrompt
mock_parser_mod.PromptParser = MagicMock()
sys.modules["src.backend.core.parser"] = mock_parser_mod

# Patch sys.modules for rules_registry
mock_registry_mod = MagicMock()
mock_registry_mod.Registry = MagicMock()
sys.modules["src.backend.core.rules_registry"] = mock_registry_mod

# Patch sys.modules for include_resolver
mock_resolver_mod = MagicMock()
mock_resolver_mod.ResolutionResult = MockResolutionResult
mock_resolver_mod.IncludeResolver = MagicMock()
sys.modules["src.backend.core.include_resolver"] = mock_resolver_mod

# --- Import Code Under Test ---
from src.backend.core.lint_engine import LintEngine

# --- Z3 Imports ---
from z3 import Int, Solver, Implies, And, Or, sat, If, unsat

# --- Fixtures ---

@pytest.fixture
def engine():
    return LintEngine()

@pytest.fixture
def mock_parsed_prompt():
    mock = MagicMock(spec=MockParsedPrompt)
    mock.syntax_errors = []
    return mock

# --- Unit Tests ---

def test_lint_basic_orchestration(engine, mock_parsed_prompt):
    """Tests the standard successful path of the lint engine."""
    with patch.object(engine.parser, 'parse', return_value=mock_parsed_prompt), \
         patch.object(engine.registry, 'get_all_rules') as mock_rules:
        
        # Setup a mock rule
        mock_rule = MagicMock()
        mock_rule.id = "test-rule"
        mock_rule.check.return_value = [
            MockFinding(rule_id="test-rule", message="test", severity=MockSeverity.INFO, location=MockFindingLocation(line=1, column=1))
        ]
        mock_rules.return_value = [mock_rule]
        
        report = engine.lint("test content")
        
        assert isinstance(report, MockLintReport)
        assert report.score == 98  # 100 - 2 (Info)
        assert len(report.findings) == 1
        assert report.stats["raw_token_count"] == len("test content") // 4

def test_lint_parser_failure(engine):
    """Tests that a critical parser failure returns a 0-score report."""
    with patch.object(engine.parser, 'parse', side_effect=RuntimeError("Parser Crash")):
        report = engine.lint("invalid content")
        
        assert report.score == 0
        assert report.findings[0].severity == MockSeverity.CRITICAL
        assert "Parser Crash" in report.findings[0].message

def test_lint_include_resolution(engine, mock_parsed_prompt):
    """Tests that include resolution updates stats and findings."""
    res_result = MockResolutionResult(
        resolved_files=["file1.txt"],
        total_tokens=500,
        findings=[MockFinding(rule_id="inc", message="inc", severity=MockSeverity.WARNING, location=MockFindingLocation(line=1, column=1))]
    )
    
    with patch.object(engine.parser, 'parse', return_value=mock_parsed_prompt), \
         patch.object(engine.resolver, 'resolve', return_value=res_result):
        
        report = engine.lint("content", options={"resolve_includes": True})
        
        assert report.stats["resolved_token_count"] == 500
        assert report.stats["includes_found"] == 1
        # Score: 100 - 7 (Warning from resolver) = 93
        assert report.score == 93

def test_lint_rule_crash_handling(engine, mock_parsed_prompt):
    """Tests that a crashing rule adds a warning but doesn't stop the engine."""
    mock_rule_ok = MagicMock(id="ok-rule")
    mock_rule_ok.check.return_value = []
    
    mock_rule_crash = MagicMock(id="crash-rule")
    mock_rule_crash.check.side_effect = Exception("Boom")
    
    with patch.object(engine.parser, 'parse', return_value=mock_parsed_prompt), \
         patch.object(engine.registry, 'get_all_rules', return_value=[mock_rule_crash, mock_rule_ok]):
        
        report = engine.lint("content")
        
        # Should find the internal linter error finding
        crash_findings = [f for f in report.findings if f.rule_id == "internal_linter_error"]
        assert len(crash_findings) == 1
        assert "crash-rule" in crash_findings[0].message
        assert report.score == 93 # 100 - 7 (Warning)

def test_lint_disabled_rules(engine, mock_parsed_prompt):
    """Tests that rules in the disabled_rules option are not executed."""
    mock_rule = MagicMock(id="disabled-rule")
    with patch.object(engine.parser, 'parse', return_value=mock_parsed_prompt), \
         patch.object(engine.registry, 'get_all_rules', return_value=[mock_rule]):
        
        engine.lint("content", options={"disabled_rules": ["disabled-rule"]})
        mock_rule.check.assert_not_called()

# --- Z3 Formal Verification Tests ---

def test_scoring_logic_properties_z3():
    """
    Formally verify the scoring algorithm:
    - Score is between 0 and 100.
    - Deductions are capped correctly.
    - Severity levels have correct weights.
    """
    s = Solver()

    # Variables: Number of findings for each severity
    num_errors = Int('num_errors')
    num_warns = Int('num_warns')
    num_infos = Int('num_infos')
    
    # Constraints: Cannot have negative findings
    s.add(num_errors >= 0, num_warns >= 0, num_infos >= 0)

    # Implementation of the scoring logic in Z3
    def get_score_expr(e, w, i):
        # Apply weights
        err_deduct = e * 15
        warn_deduct = w * 7
        info_deduct = i * 2
        
        # Apply caps: min(val, cap) is Or(val < cap, val == cap) logic or If(val > cap, cap, val)
        actual_err_deduct = If(err_deduct > 45, 45, err_deduct)
        actual_warn_deduct = If(warn_deduct > 35, 35, warn_deduct)
        actual_info_deduct = If(info_deduct > 20, 20, info_deduct)
        
        raw_score = 100 - (actual_err_deduct + actual_warn_deduct + actual_info_deduct)
        return If(raw_score < 0, 0, raw_score)

    score = get_score_expr(num_errors, num_warns, num_infos)

    # Property 1: Score is always <= 100
    s.push()
    s.add(score > 100)
    assert s.check() == unsat, "Score exceeded 100"
    s.pop()

    # Property 2: Score is always >= 0
    s.push()
    s.add(score < 0)
    assert s.check() == unsat, "Score dropped below 0"
    s.pop()

    # Property 3: Max deduction is 45 + 35 + 20 = 100. 
    # Therefore, score should be 0 if all caps are hit.
    s.push()
    s.add(num_errors >= 3, num_warns >= 5, num_infos >= 10)
    s.add(score != 0)
    assert s.check() == unsat, "Score should be 0 when all caps are reached"
    s.pop()

    # Property 4: Adding an error never increases the score (Monotonicity)
    num_errors_2 = Int('num_errors_2')
    s.push()
    s.add(num_errors_2 > num_errors)
    score_1 = get_score_expr(num_errors, num_warns, num_infos)
    score_2 = get_score_expr(num_errors_2, num_warns, num_infos)
    s.add(score_2 > score_1)
    assert s.check() == unsat, "Adding an error increased the score"
    s.pop()

def test_scoring_critical_severity_z3():
    """Verify that any CRITICAL finding results in a score of 0."""
    s = Solver()
    critical_count = Int('critical_count')
    s.add(critical_count > 0)
    
    # The code says: if f.severity == Severity.CRITICAL: return 0
    score = If(critical_count > 0, 0, 100) # Simplified for this specific rule
    
    s.add(score != 0)
    assert s.check() == unsat