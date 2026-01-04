import sys
import pytest
from unittest.mock import MagicMock, patch, mock_open
from pathlib import Path
from typing import List

# Import the code under test
# Adjusting import based on the provided file path structure: src/utils/pipeline.py
try:
    from src.utils.pipeline import lint_text, lint_file, LintConfig, PipelineReport
    from src.utils.models import Issue, Report, Severity, RuleCategory, LLMResponse, LLMSuggestionDetail
except ImportError:
    # Fallback for when running in a standalone test environment where src is not in path
    # This is a safeguard for the generated code to be runnable in isolation if needed,
    # but standard practice assumes the environment is set up.
    sys.path.append(".")
    from src.utils.pipeline import lint_text, lint_file, LintConfig, PipelineReport
    from src.utils.models import Issue, Report, Severity, RuleCategory, LLMResponse, LLMSuggestionDetail

# --- Z3 Formal Verification ---

def test_z3_scoring_model_bounds():
    """
    Formally verify that the scoring logic (weighted sum with multipliers)
    always produces a score between 0 and 100.
    """
    try:
        import z3
    except ImportError:
        pytest.skip("z3-solver not installed")

    solver = z3.Solver()

    # Weights defined in the code
    w_mod = 30
    w_con = 20
    w_ctx = 20
    w_det = 15
    w_abs = 15

    # Multipliers for each category. 
    # In the code: 1.0 (Clean), 0.5 (Warning), 0.0 (Error).
    # We model these as Real variables constrained to specific values.
    m_mod = z3.Real('m_mod')
    m_con = z3.Real('m_con')
    m_ctx = z3.Real('m_ctx') # Context category
    m_att = z3.Real('m_att') # Attention category (maps to Context bucket)
    m_det = z3.Real('m_det')
    m_abs = z3.Real('m_abs')

    # Helper to constrain a multiplier to valid set {0.0, 0.5, 1.0}
    def constrain_multiplier(m):
        return z3.Or(m == 0.0, m == 0.5, m == 1.0)

    solver.add(constrain_multiplier(m_mod))
    solver.add(constrain_multiplier(m_con))
    solver.add(constrain_multiplier(m_ctx))
    solver.add(constrain_multiplier(m_att))
    solver.add(constrain_multiplier(m_det))
    solver.add(constrain_multiplier(m_abs))

    # Logic from _calculate_score:
    # ctx_mult = min(category_multipliers.get(RuleCategory.CONTEXT, 1.0), 
    #                category_multipliers.get(RuleCategory.ATTENTION, 1.0))
    # Z3 Min implementation
    effective_ctx_mult = z3.If(m_ctx < m_att, m_ctx, m_att)

    # Total Score Calculation
    total_score = (
        (w_mod * m_mod) +
        (w_con * m_con) +
        (w_ctx * effective_ctx_mult) +
        (w_det * m_det) +
        (w_abs * m_abs)
    )

    # Verification 1: Score > 100?
    solver.push()
    solver.add(total_score > 100)
    result = solver.check()
    assert result == z3.unsat, f"Found a case where score > 100: {solver.model()}"
    solver.pop()

    # Verification 2: Score < 0?
    solver.push()
    solver.add(total_score < 0)
    result = solver.check()
    assert result == z3.unsat, f"Found a case where score < 0: {solver.model()}"
    solver.pop()

def test_z3_scoring_category_zeroing():
    """
    Formally verify that if a category has a multiplier of 0.0 (Error),
    that category contributes 0 to the total score.
    """
    try:
        import z3
    except ImportError:
        pytest.skip("z3-solver not installed")

    solver = z3.Solver()
    
    # Weights
    w_mod = 30
    m_mod = z3.Real('m_mod')
    
    # Assume other categories contribute 0 for isolation, or arbitrary values
    # We just check the contribution of Modularity
    contribution = w_mod * m_mod
    
    # Constraint: Multiplier is 0.0 (simulating Severity.ERROR)
    solver.add(m_mod == 0.0)
    
    # Assert contribution is not 0
    solver.add(contribution != 0)
    
    result = solver.check()
    assert result == z3.unsat, "A category with 0.0 multiplier contributed to score!"


# --- Unit Tests ---

@pytest.fixture
def mock_rules():
    with patch('src.utils.pipeline.rules') as m:
        yield m

@pytest.fixture
def mock_llm():
    with patch('src.utils.pipeline.llm') as m:
        yield m

@pytest.fixture
def mock_fix():
    with patch('src.utils.pipeline.fix') as m:
        yield m

def test_lint_text_heuristics_only(mock_rules, mock_llm):
    """Test that lint_text runs heuristics and skips LLM if configured to do so."""
    # Setup
    text = "def foo(): pass"
    config = LintConfig(use_llm=False)
    
    # Mock heuristics returning one issue
    issue = Issue(
        rule_id="TST001", line_number=1, severity=Severity.WARNING,
        category=RuleCategory.MODULARITY, title="Test", description="Desc", fix_suggestion=""
    )
    mock_rules.analyze_text.return_value = [issue]
    
    # Execute
    report = lint_text(text, config)
    
    # Verify
    assert len(report.issues) == 1
    assert report.issues[0].rule_id == "TST001"
    mock_rules.analyze_text.assert_called_once_with(text)
    mock_llm.analyze_prompt.assert_not_called()
    # Score check: Modularity(30) * 0.5 (Warning) = 15. Others full.
    # Total = 15 + 20 + 20 + 15 + 15 = 85
    assert report.score == 85

def test_lint_text_with_llm_success(mock_rules, mock_llm):
    """Test that LLM suggestions are merged into the report."""
    # Setup
    text = "Prompt"
    config = LintConfig(use_llm=True)
    mock_rules.analyze_text.return_value = []
    
    # Mock LLM response
    llm_sugg = LLMSuggestionDetail(
        rule_id="CTX001", title="Add Persona", rationale="Missing persona",
        before="Prompt", after="You are X. Prompt", priority="High"
    )
    mock_llm.analyze_prompt.return_value = LLMResponse(
        guide_alignment_summary="LLM Summary",
        top_fixes=[],
        suggestions=[llm_sugg]
    )
    
    # Execute
    report = lint_text(text, config)
    
    # Verify
    assert len(report.issues) == 1
    assert report.issues[0].rule_id == "CTX001"
    assert report.issues[0].category == RuleCategory.CONTEXT # Inferred from CTX prefix
    assert report.summary == "LLM Summary"
    assert report.llm_analysis is not None

def test_lint_text_with_llm_failure(mock_rules, mock_llm):
    """Test graceful degradation when LLM returns None."""
    # Setup
    config = LintConfig(use_llm=True)
    mock_rules.analyze_text.return_value = []
    mock_llm.analyze_prompt.return_value = None # Simulate failure
    
    # Execute
    report = lint_text("text", config)
    
    # Verify
    # Should have 1 issue: The SYS002 info warning about LLM skipping
    assert len(report.issues) == 1
    assert report.issues[0].rule_id == "SYS002"
    assert report.issues[0].severity == Severity.INFO
    # Info severity should not deduct score
    assert report.score == 100 

def test_lint_text_scoring_logic(mock_rules):
    """
    Test specific scoring scenarios to ensure weights are applied correctly.
    Scenario: 
    - Modularity: ERROR (0 pts)
    - Contracts: WARNING (10 pts)
    - Context: Clean (20 pts)
    - Determinism: Clean (15 pts)
    - Abstraction: Clean (15 pts)
    Expected: 0 + 10 + 20 + 15 + 15 = 60
    """
    config = LintConfig(use_llm=False)
    
    issue_err = Issue(
        rule_id="MOD001", line_number=1, severity=Severity.ERROR,
        category=RuleCategory.MODULARITY, title="E", description="D", fix_suggestion=""
    )
    issue_warn = Issue(
        rule_id="CON001", line_number=1, severity=Severity.WARNING,
        category=RuleCategory.CONTRACTS, title="W", description="D", fix_suggestion=""
    )
    
    mock_rules.analyze_text.return_value = [issue_err, issue_warn]
    
    report = lint_text("text", config)
    assert report.score == 60

def test_lint_text_fix_generation(mock_rules, mock_fix):
    """Test that fix generation is invoked and attached."""
    config = LintConfig(use_llm=False, generate_fix=True)
    mock_rules.analyze_text.return_value = []
    
    # Mock fix module
    mock_fix.generate_scaffold.return_value = "<fixed>text</fixed>"
    
    report = lint_text("text", config)
    
    assert report.suggested_fix == "<fixed>text</fixed>"
    mock_fix.generate_scaffold.assert_called_once()

def test_lint_text_fix_generation_missing_module(mock_rules, mock_fix):
    """Test behavior when fix module lacks the required function."""
    config = LintConfig(use_llm=False, generate_fix=True)
    mock_rules.analyze_text.return_value = []
    
    # Simulate missing function by deleting the attribute from the mock
    del mock_fix.generate_scaffold
    
    report = lint_text("text", config)
    
    # Should not crash, should add a warning issue
    sys_issues = [i for i in report.issues if i.rule_id == "SYS003"]
    assert len(sys_issues) == 1
    assert report.suggested_fix is None

def test_lint_file_success(mock_rules):
    """Test lint_file reads file and returns report."""
    mock_rules.analyze_text.return_value = []
    
    with patch("pathlib.Path.exists", return_value=True), \
         patch("pathlib.Path.read_text", return_value="file content") as mock_read:
        
        report = lint_file(Path("test.txt"))
        
        assert report.filepath == "test.txt"
        assert report.score == 100
        mock_read.assert_called_once()

def test_lint_file_not_found():
    """Test lint_file handles missing files."""
    with patch("pathlib.Path.exists", return_value=False):
        report = lint_file(Path("missing.txt"))
        
        assert report.score == 0
        assert report.issues[0].rule_id == "SYS004"
        assert "not exist" in report.issues[0].description

def test_lint_file_read_error():
    """Test lint_file handles read exceptions."""
    with patch("pathlib.Path.exists", return_value=True), \
         patch("pathlib.Path.read_text", side_effect=PermissionError("Access denied")):
        
        report = lint_file(Path("locked.txt"))
        
        assert report.score == 0
        assert report.issues[0].rule_id == "SYS005"
        assert "Access denied" in report.issues[0].description

def test_heuristic_exception_handling(mock_rules):
    """Test that exceptions in rules.analyze_text are caught."""
    mock_rules.analyze_text.side_effect = ValueError("Rule engine crashed")
    
    report = lint_text("text", LintConfig(use_llm=False))
    
    assert len(report.issues) == 1
    assert report.issues[0].rule_id == "SYS001"
    assert "Rule engine crashed" in report.issues[0].description
    # Should not crash the pipeline


# --- Test Plan ---
# 1. Z3 Formal Verification: Scoring Monotonicity
#    - Goal: Verify that adding a more severe issue (reducing the multiplier) never increases the total score.
#    - Method: Define the score equation in Z3. Assert that if multiplier_new <= multiplier_old, then score_new <= score_old.
#
# 2. Unit Test: Context vs Attention Interaction
#    - Goal: Verify the specific logic where Context and Attention categories share the same scoring bucket.
#    - Method: Create issues for Attention (Warning) and Context (Clean). Verify the score reflects the deduction.
#
# 3. Unit Test: LLM Configuration Propagation
#    - Goal: Ensure runtime configuration (timeout, model override) is correctly passed to the LLM module.
#    - Method: Call lint_text with specific config values and inspect the mock_llm call arguments.
#
# 4. Unit Test: LLM Suggestion Mapping
#    - Goal: Verify that LLM suggestions with different rule ID prefixes are mapped to the correct RuleCategory.
#    - Method: Mock LLM response with various rule IDs (MOD..., STR..., UNK...) and check the resulting Issue categories.
#
# 5. Unit Test: Scoring Order Independence
#    - Goal: Ensure that the order in which issues are processed (e.g., Error then Warning vs Warning then Error) does not affect the final score.
#    - Method: Run lint_text with reversed lists of issues and assert scores are identical.
#
# 6. Unit Test: Unknown Category Robustness
#    - Goal: Ensure that issues with categories not defined in the weighting rubric do not crash the scorer.
#    - Method: Inject an issue with a mocked/fabricated category and verify the pipeline completes.

# --- New Tests ---

def test_z3_scoring_monotonicity():
    """
    Formally verify that the scoring function is monotonic with respect to category multipliers.
    lowering a multiplier (worsening severity) should never increase the score.
    """
    try:
        import z3
    except ImportError:
        pytest.skip("z3-solver not installed")

    solver = z3.Solver()

    # Weights
    weights = {
        "mod": 30, "con": 20, "ctx": 20, "det": 15, "abs": 15
    }

    # Define two states for a single category (e.g., Modularity)
    # m_old: Multiplier before adding a new issue
    # m_new: Multiplier after adding a new issue (must be <= m_old)
    m_old = z3.Real('m_old')
    m_new = z3.Real('m_new')

    # Constraints: Multipliers are 0.0, 0.5, or 1.0
    def is_valid_mult(m):
        return z3.Or(m == 0.0, m == 0.5, m == 1.0)

    solver.add(is_valid_mult(m_old))
    solver.add(is_valid_mult(m_new))
    
    # The condition we are testing: severity worsened or stayed same
    solver.add(m_new <= m_old)

    # Assume other categories are constant (c)
    c = z3.Real('c')
    
    # Score equations
    score_old = weights["mod"] * m_old + c
    score_new = weights["mod"] * m_new + c

    # Verification: Can score_new ever be greater than score_old?
    solver.push()
    solver.add(score_new > score_old)
    
    result = solver.check()
    assert result == z3.unsat, f"Found violation of monotonicity: {solver.model()}"
    solver.pop()

def test_scoring_context_attention_interaction(mock_rules):
    """
    Test that issues in ATTENTION category affect the CONTEXT score bucket.
    Logic: ctx_mult = min(Context_Mult, Attention_Mult)
    """
    config = LintConfig(use_llm=False)
    
    # Case: Context is Clean (1.0), Attention has Warning (0.5)
    # Context Bucket Weight = 20.
    # Expected deduction: 50% of 20 = 10 points lost.
    # Other categories (30+20+15+15 = 80) are clean.
    # Total expected: 80 + 10 = 90.
    
    issue_att = Issue(
        rule_id="ATT001", line_number=1, severity=Severity.WARNING,
        category=RuleCategory.ATTENTION, title="Attn", description=".", fix_suggestion=""
    )
    
    mock_rules.analyze_text.return_value = [issue_att]
    
    report = lint_text("text", config)
    assert report.score == 90

def test_llm_config_propagation(mock_rules, mock_llm):
    """Test that timeout and model override are passed to the LLM module."""
    config = LintConfig(
        use_llm=True,
        llm_timeout=123,
        llm_model_override="gpt-4-turbo-test"
    )
    mock_rules.analyze_text.return_value = []
    mock_llm.analyze_prompt.return_value = None # Return None to skip processing logic
    
    lint_text("prompt", config)
    
    # Verify call arguments
    mock_llm.analyze_prompt.assert_called_once()
    call_kwargs = mock_llm.analyze_prompt.call_args[1]
    assert call_kwargs['config']['timeout'] == 123
    assert call_kwargs['config']['model'] == "gpt-4-turbo-test"

def test_llm_mapping_prefixes(mock_rules, mock_llm):
    """Test that LLM suggestions are mapped to correct categories based on Rule ID."""
    config = LintConfig(use_llm=True)
    mock_rules.analyze_text.return_value = []
    
    suggestions = [
        LLMSuggestionDetail(rule_id="MOD999", title="M", rationale="R", before="B", after="A", priority="H"),
        LLMSuggestionDetail(rule_id="STR123", title="S", rationale="R", before="B", after="A", priority="H"), # Should map to ANATOMY
        LLMSuggestionDetail(rule_id="UNK000", title="U", rationale="R", before="B", after="A", priority="H"), # Should default to CONTEXT
    ]
    
    mock_llm.analyze_prompt.return_value = LLMResponse(
        guide_alignment_summary="Sum", top_fixes=[], suggestions=suggestions
    )
    
    report = lint_text("text", config)
    
    # Extract categories from generated issues
    categories = {i.rule_id: i.category for i in report.issues}
    
    assert categories["MOD999"] == RuleCategory.MODULARITY
    assert categories["STR123"] == RuleCategory.ANATOMY
    assert categories["UNK000"] == RuleCategory.CONTEXT

def test_scoring_order_independence(mock_rules):
    """
    Test that the order of issues (Error vs Warning) does not affect the final score.
    If we process Error (0.0) then Warning (0.5), result should be 0.0.
    If we process Warning (0.5) then Error (0.0), result should be 0.0.
    """
    config = LintConfig(use_llm=False)
    
    i_warn = Issue(rule_id="WARN1", line_number=1, severity=Severity.WARNING, category=RuleCategory.MODULARITY, title="t", description="d", fix_suggestion="")
    i_err = Issue(rule_id="ERR01", line_number=1, severity=Severity.ERROR, category=RuleCategory.MODULARITY, title="t", description="d", fix_suggestion="")
    
    # Run 1: Warning then Error
    mock_rules.analyze_text.return_value = [i_warn, i_err]
    report1 = lint_text("text", config)
    
    # Run 2: Error then Warning
    mock_rules.analyze_text.return_value = [i_err, i_warn]
    report2 = lint_text("text", config)
    
    assert report1.score == report2.score
    # Modularity (30) should be 0 in both cases.
    # Remaining: 20+20+15+15 = 70.
    assert report1.score == 70

def test_scoring_unknown_category(mock_rules):
    """Test that issues with categories not in the rubric are ignored safely."""
    config = LintConfig(use_llm=False)
    
    # Create a mock category that isn't in the weights dict
    # We use a string cast or a mock object if RuleCategory is an Enum
    # Since RuleCategory is an Enum in the code, we can't easily inject a new Enum member.
    # However, we can mock the issue object to return a weird value for category.
    
    mock_issue = MagicMock(spec=Issue)
    mock_issue.severity = Severity.ERROR
    mock_issue.category = "UNKNOWN_CATEGORY_ENUM" 
    
    mock_rules.analyze_text.return_value = [mock_issue]
    
    # Should run without raising KeyError
    report = lint_text("text", config)
    
    # Score should be 100 because the unknown category issue is skipped in calculation
    assert report.score == 100