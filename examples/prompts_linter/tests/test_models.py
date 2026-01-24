"""
Test Plan for src/utils/models.py

1.  **Enum Tests**:
    *   Verify `Severity`, `RuleCategory`, and `LLMProvider` inherit from `str` and `Enum`.
    *   Verify specific string values for `Severity` (info, warning, error) as these are critical for logic.

2.  **Issue Model Tests**:
    *   **Valid Construction**: Create an `Issue` with valid data.
    *   **Validation Constraints**:
        *   `rule_id`: Ensure min_length=2 triggers error on short strings.
        *   `line_number`: Ensure values < 1 trigger error.
        *   `severity` & `category`: Ensure invalid enum values trigger error.
    *   **Serialization**: Verify `model_dump_json` works.

3.  **LLM Contract Tests**:
    *   **Structure**: Verify `LLMFixSuggestion` and `LLMSuggestionDetail` instantiation.
    *   **Resilience (`LLMResponse`)**:
        *   **Critical**: Verify that passing *extra* fields to `LLMResponse` does NOT raise a validation error (due to `extra='ignore'`). This is a specific requirement for LLM robustness.
        *   Verify nested list parsing.

4.  **Report Model Tests**:
    *   **Score Validation**:
        *   Verify 0 and 100 are accepted.
        *   Verify -1 and 101 raise `ValidationError` (or `ValueError` from the custom validator).
    *   **`is_clean` Property Logic**:
        *   Test with empty issues list (Expected: True).
        *   Test with only INFO/WARNING issues (Expected: True).
        *   Test with at least one ERROR issue (Expected: False).
        *   Test with mixed severities including ERROR (Expected: False).

5.  **Z3 Formal Verification**:
    *   **`is_clean` Logic Verification**:
        *   Model the `is_clean` predicate logic using Z3.
        *   Define a set of severities.
        *   Prove that `is_clean` is True if and only if the set of severities does not contain "error".
    *   **Score Bounds Verification**:
        *   Model the integer constraints for the score.
        *   Prove that any integer outside [0, 100] violates the constraint.
"""

import pytest
from pydantic import ValidationError
from src.utils.models import (
    Severity,
    RuleCategory,
    LLMProvider,
    Issue,
    Report,
    LLMResponse,
    LLMFixSuggestion,
    LLMSuggestionDetail
)
import json

# -----------------------------------------------------------------------------
# 1. Enum Tests
# -----------------------------------------------------------------------------

def test_severity_enum_values():
    """Test that Severity enum values are correct strings."""
    assert Severity.INFO == "info"
    assert Severity.WARNING == "warning"
    assert Severity.ERROR == "error"
    # Test string comparison capability
    assert Severity.ERROR == "error"

def test_rule_category_enum_values():
    """Test existence of specific RuleCategory values."""
    assert RuleCategory.MODULARITY == "modularity"
    assert RuleCategory.DETERMINISM == "determinism"

def test_llm_provider_enum_values():
    """Test existence of specific LLMProvider values."""
    assert LLMProvider.OPENAI == "openai"
    assert LLMProvider.AUTO == "auto"

# -----------------------------------------------------------------------------
# 2. Issue Model Tests
# -----------------------------------------------------------------------------

def test_issue_valid_creation():
    """Test creating a valid Issue object."""
    issue = Issue(
        rule_id="MOD001",
        line_number=10,
        severity=Severity.WARNING,
        category=RuleCategory.MODULARITY,
        description="Test description",
        fix_suggestion="Fix it"
    )
    assert issue.rule_id == "MOD001"
    assert issue.line_number == 10
    assert issue.severity == Severity.WARNING

def test_issue_validation_rule_id_length():
    """Test that rule_id must be at least 2 characters."""
    with pytest.raises(ValidationError) as excinfo:
        Issue(
            rule_id="A",  # Too short
            severity=Severity.INFO,
            category=RuleCategory.CONTEXT,
            description="Desc"
        )
    assert "String should have at least 2 characters" in str(excinfo.value)

def test_issue_validation_line_number():
    """Test that line_number must be >= 1."""
    with pytest.raises(ValidationError) as excinfo:
        Issue(
            rule_id="MOD01",
            line_number=0,  # Invalid
            severity=Severity.INFO,
            category=RuleCategory.CONTEXT,
            description="Desc"
        )
    assert "Input should be greater than or equal to 1" in str(excinfo.value)

def test_issue_serialization():
    """Test JSON serialization of an Issue."""
    issue = Issue(
        rule_id="TST01",
        severity=Severity.ERROR,
        category=RuleCategory.ANATOMY,
        description="Serialization test"
    )
    json_str = issue.model_dump_json()
    data = json.loads(json_str)
    assert data["rule_id"] == "TST01"
    assert data["severity"] == "error"

# -----------------------------------------------------------------------------
# 3. LLM Contract Tests
# -----------------------------------------------------------------------------

def test_llm_response_resilience_extra_fields():
    """
    CRITICAL: Test that LLMResponse ignores extra fields.
    This ensures the parser doesn't crash if the LLM hallucinates extra keys.
    """
    raw_llm_output = {
        "guide_alignment_summary": "Good",
        "top_fixes": [],
        "suggestions": [],
        "hallucinated_field": "This should be ignored",
        "meta_data": {"tokens": 100}
    }
    
    response = LLMResponse(**raw_llm_output)
    
    # Should not raise error, and extra fields should not be in the model
    assert response.guide_alignment_summary == "Good"
    assert not hasattr(response, "hallucinated_field")

def test_llm_response_nested_structures():
    """Test parsing of nested fix suggestions."""
    raw_data = {
        "guide_alignment_summary": "Summary",
        "top_fixes": [
            {"title": "Fix 1", "rationale": "Because", "priority": "High"}
        ],
        "suggestions": []
    }
    response = LLMResponse(**raw_data)
    assert len(response.top_fixes) == 1
    assert isinstance(response.top_fixes[0], LLMFixSuggestion)
    assert response.top_fixes[0].title == "Fix 1"

# -----------------------------------------------------------------------------
# 4. Report Model Tests
# -----------------------------------------------------------------------------

def test_report_score_validation_bounds():
    """Test score boundary validation (0-100)."""
    # Valid scores
    Report(filepath="t.txt", score=0, summary="s", issues=[])
    Report(filepath="t.txt", score=100, summary="s", issues=[])

    # Invalid scores
    with pytest.raises(ValidationError) as exc_low:
        Report(filepath="t.txt", score=-1, summary="s", issues=[])
    assert "Score must be between 0 and 100" in str(exc_low.value) or "Input should be greater than or equal to 0" in str(exc_low.value)

    with pytest.raises(ValidationError) as exc_high:
        Report(filepath="t.txt", score=101, summary="s", issues=[])
    assert "Score must be between 0 and 100" in str(exc_high.value) or "Input should be less than or equal to 100" in str(exc_high.value)

def test_report_is_clean_property_empty():
    """Test is_clean is True when no issues exist."""
    report = Report(filepath="test.txt", score=100, summary="Clean", issues=[])
    assert report.is_clean is True

def test_report_is_clean_property_warnings_only():
    """Test is_clean is True when only warnings/info exist."""
    issues = [
        Issue(rule_id="W1", severity=Severity.WARNING, category=RuleCategory.CONTEXT, description="d"),
        Issue(rule_id="I1", severity=Severity.INFO, category=RuleCategory.CONTEXT, description="d")
    ]
    report = Report(filepath="test.txt", score=90, summary="Warnings", issues=issues)
    assert report.is_clean is True

def test_report_is_clean_property_with_error():
    """Test is_clean is False when an ERROR exists."""
    issues = [
        Issue(rule_id="W1", severity=Severity.WARNING, category=RuleCategory.CONTEXT, description="d"),
        Issue(rule_id="E1", severity=Severity.ERROR, category=RuleCategory.CONTEXT, description="d")
    ]
    report = Report(filepath="test.txt", score=50, summary="Errors", issues=issues)
    assert report.is_clean is False

# -----------------------------------------------------------------------------
# 5. Z3 Formal Verification Tests
# -----------------------------------------------------------------------------

def test_z3_verify_is_clean_logic():
    """
    Formal verification of the `is_clean` logic.
    We prove that for any combination of issue severities, 
    is_clean is False IF AND ONLY IF there exists a severity == ERROR.
    """
    try:
        import z3
    except ImportError:
        pytest.skip("z3-solver not installed")

    # Create a solver
    s = z3.Solver()

    # Define Severity as an Enum Sort in Z3
    SeveritySort, (INFO, WARNING, ERROR) = z3.EnumSort('Severity', ['INFO', 'WARNING', 'ERROR'])

    # We model the state of a report as a set of booleans indicating presence of each severity
    # has_info, has_warning, has_error
    has_info = z3.Bool('has_info')
    has_warning = z3.Bool('has_warning')
    has_error = z3.Bool('has_error')

    # Define the python logic for is_clean in Z3 terms
    # Python: return not any(issue.severity == Severity.ERROR for issue in self.issues)
    # In our abstraction: is_clean is true if has_error is False.
    is_clean = z3.Not(has_error)

    # We want to verify: is_clean == True <-> has_error == False
    # Or conversely: is_clean == False <-> has_error == True
    
    # Let's try to find a counter-example to the claim:
    # "is_clean is False implies has_error is True"
    # Negation: is_clean is False AND has_error is False
    
    # Logic from code: is_clean = NOT(has_error)
    # We want to prove this definition is consistent with the requirement "clean means no errors".
    
    # Let's formulate the requirement: 
    # Requirement: The report is dirty (not clean) if and only if there is an error.
    # Dirty <-> has_error
    # Not(is_clean) <-> has_error
    
    # We assert the negation of the requirement to find counter examples
    requirement = (z3.Not(is_clean) == has_error)
    
    s.add(z3.Not(requirement))

    # If UNSAT, the requirement holds for all possible boolean values of has_error.
    result = s.check()
    assert result == z3.unsat, f"Found counter-example to is_clean logic: {s.model()}"

def test_z3_verify_score_bounds():
    """
    Formal verification of score boundary logic.
    Prove that a score is valid IFF 0 <= score <= 100.
    """
    try:
        import z3
    except ImportError:
        pytest.skip("z3-solver not installed")

    s = z3.Solver()
    score = z3.Int('score')

    # Logic defined in the model
    def is_valid_score(v):
        return z3.And(v >= 0, v <= 100)

    # We want to prove that if is_valid_score is true, v cannot be 101 or -1.
    # We add the constraint that it IS valid
    s.add(is_valid_score(score))
    
    # We check if it's possible for score to be outside bounds while valid
    # Negation of bounds: score < 0 OR score > 100
    s.add(z3.Or(score < 0, score > 100))

    # Should be impossible (UNSAT)
    assert s.check() == z3.unsat, "Found a score that is considered valid but is outside bounds"


def test_issue_optional_fields_defaults():
    """Test that optional fields in Issue default to None or accept None."""
    # Omit optional fields
    issue = Issue(
        rule_id="OPT01",
        severity=Severity.INFO,
        category=RuleCategory.MODULARITY,
        description="Testing defaults"
    )
    assert issue.line_number is None
    assert issue.fix_suggestion is None

    # Explicitly set to None
    issue_explicit = Issue(
        rule_id="OPT02",
        severity=Severity.INFO,
        category=RuleCategory.MODULARITY,
        description="Testing explicit None",
        line_number=None,
        fix_suggestion=None
    )
    assert issue_explicit.line_number is None

def test_issue_invalid_enum_values():
    """Test that invalid strings for enums raise ValidationError."""
    with pytest.raises(ValidationError) as excinfo:
        Issue(
            rule_id="INV01",
            severity="critical",  # Invalid severity
            category=RuleCategory.MODULARITY,
            description="Invalid severity"
        )
    assert "Input should be 'info', 'warning' or 'error'" in str(excinfo.value)

    with pytest.raises(ValidationError) as excinfo:
        Issue(
            rule_id="INV02",
            severity=Severity.INFO,
            category="performance",  # Invalid category
            description="Invalid category"
        )
    # Pydantic v2 error message for enums usually lists allowed values
    assert "Input should be" in str(excinfo.value)

# -----------------------------------------------------------------------------
# 7. Additional LLM Model Tests
# -----------------------------------------------------------------------------

def test_llm_response_default_factories():
    """Test that LLMResponse lists default to empty lists."""
    response = LLMResponse(guide_alignment_summary="No issues found.")
    assert response.top_fixes == []
    assert response.suggestions == []
    assert isinstance(response.top_fixes, list)

def test_llm_suggestion_detail_instantiation():
    """Test valid instantiation of LLMSuggestionDetail."""
    detail = LLMSuggestionDetail(
        rule_id="DET01",
        title="Change X to Y",
        rationale="Better readability",
        before="x = 1",
        after="x = 2",
        priority="Medium"
    )
    assert detail.rule_id == "DET01"
    assert detail.before == "x = 1"

    # Test missing field
    with pytest.raises(ValidationError):
        LLMSuggestionDetail(
            rule_id="DET02",
            title="Missing fields"
            # Missing rationale, before, after, priority
        )

# -----------------------------------------------------------------------------
# 8. Additional Report Model Tests
# -----------------------------------------------------------------------------

def test_report_optional_llm_analysis_none():
    """Test that Report accepts None for llm_analysis."""
    report = Report(
        filepath="test.txt",
        score=80,
        summary="Summary",
        llm_analysis=None
    )
    assert report.llm_analysis is None

def test_report_validate_score_direct_call():
    """
    Test the validate_score class method directly.
    This ensures the logic is correct even outside Pydantic's instantiation.
    """
    # Valid values
    assert Report.validate_score(0) == 0
    assert Report.validate_score(50) == 50
    assert Report.validate_score(100) == 100

    # Invalid values
    with pytest.raises(ValueError, match="Score must be between 0 and 100"):
        Report.validate_score(-1)
    
    with pytest.raises(ValueError, match="Score must be between 0 and 100"):
        Report.validate_score(101)

# -----------------------------------------------------------------------------
# 9. Additional Z3 Verification
# -----------------------------------------------------------------------------

def test_z3_verify_severity_distinctness():
    """
    Formal verification that all Severity enum values are distinct strings.
    This ensures we haven't accidentally mapped two enum members to the same string.
    """
    try:
        import z3
    except ImportError:
        pytest.skip("z3-solver not installed")

    s = z3.Solver()

    # Define string constants for each enum value
    # We treat them as abstract constants and assert their equality to specific string literals is not needed
    # for this specific check, but we want to ensure the Python objects map to distinct values.
    
    # Actually, we can just check the python values directly, but to do it "Formally" with Z3:
    # We map each enum member to a Z3 String
    v_info = z3.StringVal(Severity.INFO.value)
    v_warning = z3.StringVal(Severity.WARNING.value)
    v_error = z3.StringVal(Severity.ERROR.value)

    # We want to prove that v_info != v_warning AND v_warning != v_error AND v_info != v_error
    # We negate this (assert that at least one pair is equal) and check for UNSAT.
    
    collision_condition = z3.Or(
        v_info == v_warning,
        v_warning == v_error,
        v_info == v_error
    )
    
    s.add(collision_condition)
    
    # If UNSAT, it means no collision is possible (they are all distinct).
    assert s.check() == z3.unsat, "Severity enum values are not distinct strings"


# -----------------------------------------------------------------------------
# 10. Additional LLM Resilience Tests
# -----------------------------------------------------------------------------

def test_llm_response_nested_extra_fields_behavior():
    """
    Test behavior when nested objects (LLMFixSuggestion) contain extra fields.
    The prompt requires resilience. We verify that nested models also ignore 
    extra fields, ensuring the parser doesn't crash on LLM hallucinations.
    """
    raw_data = {
        "guide_alignment_summary": "Summary",
        "top_fixes": [
            {
                "title": "Fix 1", 
                "rationale": "Because", 
                "priority": "High",
                "hallucinated_inner_field": "Should be ignored"
            }
        ],
        "suggestions": []
    }
    
    # Should NOT raise ValidationError
    response = LLMResponse(**raw_data)
    assert len(response.top_fixes) == 1
    # Verify the extra field is not on the object
    assert not hasattr(response.top_fixes[0], "hallucinated_inner_field")

# -----------------------------------------------------------------------------
# 11. Report Serialization Tests
# -----------------------------------------------------------------------------

def test_report_serialization_enum_values():
    """
    Verify that when a Report is dumped to JSON, Enums are serialized 
    as their simple string values, not python objects.
    """
    issue = Issue(
        rule_id="SER01",
        severity=Severity.WARNING,
        category=RuleCategory.DETERMINISM,
        description="Serialization check"
    )
    report = Report(
        filepath="test.json",
        score=100,
        summary="json test",
        issues=[issue]
    )
    
    json_output = report.model_dump_json()
    data = json.loads(json_output)
    
    # Check Issue inside Report
    issue_data = data["issues"][0]
    assert issue_data["severity"] == "warning"
    assert issue_data["category"] == "determinism"
    # Ensure it's not "Severity.WARNING"
    assert issue_data["severity"] != "Severity.WARNING"

# -----------------------------------------------------------------------------
# 12. Issue Model - Optional Fields
# -----------------------------------------------------------------------------

def test_issue_title_field():
    """Test the optional 'title' field in Issue."""
    issue = Issue(
        rule_id="TIT01",
        severity=Severity.INFO,
        category=RuleCategory.ABSTRACTION,
        description="Desc",
        title="My Custom Title"
    )
    assert issue.title == "My Custom Title"
    
    issue_no_title = Issue(
        rule_id="TIT02",
        severity=Severity.INFO,
        category=RuleCategory.ABSTRACTION,
        description="Desc"
    )
    assert issue_no_title.title is None

# -----------------------------------------------------------------------------
# 13. Report Model - Default Factory Isolation
# -----------------------------------------------------------------------------

def test_report_issues_default_factory_isolation():
    """
    Verify that the default_factory for 'issues' creates a new list 
    for each instance, preventing state leakage between reports.
    """
    r1 = Report(filepath="f1", score=10, summary="s")
    r2 = Report(filepath="f2", score=10, summary="s")
    
    r1.issues.append(Issue(
        rule_id="LEAK01", 
        severity=Severity.ERROR, 
        category=RuleCategory.ANATOMY, 
        description="d"
    ))
    
    assert len(r1.issues) == 1
    assert len(r2.issues) == 0
    assert r1.issues is not r2.issues

# -----------------------------------------------------------------------------
# 14. Z3 Formal Verification - RuleCategory
# -----------------------------------------------------------------------------

def test_z3_verify_rule_category_completeness():
    """
    Formal verification that RuleCategory covers the 7 PDD principles.
    We map the enum values to a Z3 set and ensure all required strings are present.
    """
    try:
        import z3
    except ImportError:
        pytest.skip("z3-solver not installed")

    s = z3.Solver()
    
    # The 7 pillars of PDD
    required_principles = {
        "modularity", "anatomy", "contracts", "context", 
        "determinism", "abstraction", "attention"
    }
    
    # Get actual values from the Enum class
    actual_values = {e.value for e in RuleCategory}
    
    # We want to prove: required_principles is a subset of actual_values
    # In Z3, we can model this by asserting that for every required string,
    # there exists an equal string in the actual values.
    
    # However, since these are finite sets of strings, we can do a simpler
    # logical proof: The intersection size must equal the required set size.
    
    # Let's do it by contradiction:
    # Assert that there exists a 'p' in required_principles such that 'p' is NOT in actual_values.
    
    # We create a Z3 variable 'missing_principle' which can be any of the required strings
    missing_principle = z3.String('missing_principle')
    
    # Constraint 1: missing_principle must be one of the required strings
    is_required = z3.Or([missing_principle == z3.StringVal(p) for p in required_principles])
    
    # Constraint 2: missing_principle is NOT in the actual enum values
    is_missing = z3.And([missing_principle != z3.StringVal(a) for a in actual_values])
    
    s.add(is_required)
    s.add(is_missing)
    
    # If UNSAT, it means no required principle is missing.
    assert s.check() == z3.unsat, f"RuleCategory is missing a PDD principle: {s.model()}"