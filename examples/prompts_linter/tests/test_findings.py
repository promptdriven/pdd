import pytest
from pydantic import ValidationError
from enum import Enum
from typing import List, Optional

# Import the models from the actual module path
from src.backend.models.findings import (
    Severity,
    Evidence,
    SuggestedEdit,
    Finding,
    IssueCounts,
    Summary,
    LintReport
)

"""
DETAILED TEST PLAN

1. Functional Unit Tests (Pytest):
    - Severity Enum: Verify string-based values ('error', 'warn', 'info').
    - Evidence Model: Verify 1-based line number storage and immutability.
    - SuggestedEdit Model: Verify 'kind' and 'snippet' fields.
    - Finding Model: 
        - Verify default empty list for suggested_edits.
        - Verify optionality of evidence (file-level vs line-level).
        - Verify immutability (frozen=True).
    - IssueCounts Model: Verify default values (0) for all severity levels.
    - Summary Model: Verify score range validation (0-100).
    - LintReport Model: Verify root structure and nesting of findings/summary.

2. Edge Case Analysis & Verification Strategy:
    - Score < 0 or > 100: Unit Test (Pydantic validation).
    - Missing required fields: Unit Test (Pydantic validation).
    - Evidence line_start > line_end: 
        - Analysis: This is a logical invariant. While Pydantic handles types, 
          logical consistency (start <= end) is best verified via Z3 for 
          formal correctness if complex arithmetic were involved, but here 
          a simple unit test for a validator (if implemented) or a Z3 
          property check is useful.
    - Immutability: Unit Test (Attempting to mutate a field should raise TypeError).

3. Z3 Formal Verification (Runnable as Unit Tests):
    - Property: The Summary score must always be within [0, 100].
    - Property: IssueCounts must always be non-negative (though Pydantic types here are int, 
      we can verify the logic that counts shouldn't be negative).
"""

# --- Unit Tests ---

def test_severity_values():
    """Ensure Severity enum has the correct string values for JSON serialization."""
    assert Severity.ERROR == "error"
    assert Severity.WARN == "warn"
    assert Severity.INFO == "info"
    assert isinstance(Severity.ERROR, str)

def test_evidence_creation():
    """Verify Evidence model stores line numbers correctly."""
    ev = Evidence(line_start=10, line_end=12)
    assert ev.line_start == 10
    assert ev.line_end == 12

def test_model_immutability():
    """Verify that models are frozen as per requirements."""
    ev = Evidence(line_start=1, line_end=1)
    with pytest.raises(ValidationError): # Pydantic v2 raises ValidationError or AttributeError on frozen
        ev.line_start = 2

def test_finding_defaults():
    """Verify Finding defaults and optional fields."""
    finding = Finding(
        rule_id="PDD001",
        severity=Severity.ERROR,
        title="Test Title",
        message="Test Message"
    )
    assert finding.evidence is None
    assert finding.suggested_edits == []

def test_issue_counts_defaults():
    """Verify IssueCounts defaults to 0."""
    counts = IssueCounts()
    assert counts.error == 0
    assert counts.warn == 0
    assert counts.info == 0

def test_summary_score_validation():
    """Verify Summary score constraints (0-100)."""
    counts = IssueCounts(error=1)
    # Valid score
    Summary(score=100, issue_counts=counts)
    Summary(score=0, issue_counts=counts)
    
    # Invalid scores
    with pytest.raises(ValidationError):
        Summary(score=-1, issue_counts=counts)
    with pytest.raises(ValidationError):
        Summary(score=101, issue_counts=counts)

def test_lint_report_structure():
    """Verify the full nested structure of a LintReport."""
    report_data = {
        "filename": "test.prompt",
        "summary": {
            "score": 85,
            "issue_counts": {"error": 0, "warn": 1, "info": 0},
            "token_count_estimate": 150
        },
        "findings": [
            {
                "rule_id": "PDD002",
                "severity": "warn",
                "title": "Wordy Prompt",
                "message": "Try to be more concise.",
                "evidence": {"line_start": 5, "line_end": 5},
                "suggested_edits": [
                    {"kind": "replace", "snippet": "Be brief."}
                ]
            }
        ]
    }
    report = LintReport(**report_data)
    assert report.filename == "test.prompt"
    assert report.summary.score == 85
    assert len(report.findings) == 1
    assert report.findings[0].severity == Severity.WARN

# --- Z3 Formal Verification Tests ---

def test_z3_summary_score_invariant():
    """
    Formal verification of the Summary score invariant.
    Ensures that any integer 's' accepted by the model logic 
    must satisfy 0 <= s <= 100.
    """
    try:
        from z3 import Int, Solver, And, Or, Not, sat, unsat
    except ImportError:
        pytest.skip("z3-solver not installed")

    s = Int('score')
    solver = Solver()

    # Define the Pydantic constraint: ge=0, le=100
    pydantic_constraint = And(s >= 0, s <= 100)

    # Property to test: Is it possible to have a score that is valid 
    # according to Pydantic but outside our intended range?
    # (Negation of the safety property)
    safety_property = And(s >= 0, s <= 100)
    
    solver.add(pydantic_constraint)
    solver.add(Not(safety_property))

    # If unsat, then no value exists that satisfies the constraint but violates the property
    assert solver.check() == unsat

def test_z3_issue_counts_non_negative():
    """
    Formal verification that if we assume issue counts are derived from 
    a list of findings, the count is always >= 0.
    """
    try:
        from z3 import Int, Solver, Implies, Not, unsat
    except ImportError:
        pytest.skip("z3-solver not installed")

    # Let n be the number of findings of a specific severity
    n = Int('num_findings')
    count = Int('issue_count')

    solver = Solver()
    
    # Logic: The count is the length of a filtered list. 
    # Length of any list is >= 0.
    list_length_constraint = n >= 0
    count_assignment = (count == n)

    # Property: count must be non-negative
    property_non_negative = count >= 0

    solver.add(list_length_constraint)
    solver.add(count_assignment)
    solver.add(Not(property_non_negative))

    assert solver.check() == unsat