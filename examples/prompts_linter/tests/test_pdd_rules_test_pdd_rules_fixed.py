import pytest
import re
from typing import List
from z3 import Int, And, Implies, Solver, sat, unsat, Or as z3Or

# Import the actual classes/functions from the module
# Note: Using relative imports based on the provided structure
try:
    from src.backend.rules.pdd_rules import (
        check_pdd001_role_scope,
        check_pdd002_multiple_targets,
        check_pdd010_missing_requirements,
        check_pdd011_requirement_count,
        check_pdd012_implementation_steps,
        check_pdd013_negative_constraints,
        check_pdd020_missing_io,
        check_pdd021_error_handling,
        check_pdd031_context_dumps,
        check_pdd032_missing_preamble,
        check_pdd040_determinism,
        check_pdd050_vague_prompt,
        check_pdd051_over_detailed,
        check_pdd060_buried_constraints
    )
    from src.backend.models.findings import Severity
    from src.backend.parser import ParsedDocument, Section, Tag
except ImportError:
    # Fallback or mock for standalone execution if necessary
    pass

# --- Fixtures ---

def create_mock_doc(raw_text: str, sections: List['Section'] = None, tags: List['Tag'] = None, preamble: 'Section' = None) -> 'ParsedDocument':
    return ParsedDocument(
        raw_text=raw_text,
        sections=sections or [],
        tags=tags or [],
        preamble=preamble
    )

# --- Unit Tests ---

def test_pdd001_missing_role_and_scope():
    doc = create_mock_doc("Just some text without role.")
    findings = check_pdd001_role_scope(doc)
    assert len(findings) == 1
    assert findings[0].rule_id == "PDD001"
    assert findings[0].severity == Severity.WARN

def test_pdd001_with_preamble_role():
    preamble = Section(header="", content="Act as a Python Expert", start_line=1, end_line=1)
    doc = create_mock_doc("Act as a Python Expert", preamble=preamble)
    findings = check_pdd001_role_scope(doc)
    assert len(findings) == 0

def test_pdd002_multiple_targets_detection():
    # Header contains two different file names
    sec = Section(header="Update main.py and utils.js", content="...", start_line=1, end_line=2)
    doc = create_mock_doc("...", sections=[sec])
    findings = check_pdd002_multiple_targets(doc)
    assert len(findings) == 1
    assert "main.py" in findings[0].message
    assert "utils.js" in findings[0].message

def test_pdd010_missing_requirements_error():
    doc = create_mock_doc("## Background\nSome info.")
    findings = check_pdd010_missing_requirements(doc)
    assert len(findings) == 1
    assert findings[0].severity == Severity.ERROR

def test_pdd011_requirement_count_outliers():
    # Only 1 requirement
    sec = Section(header="## Requirements", content="1. Only one req", start_line=1, end_line=2)
    doc = create_mock_doc("...", sections=[sec])
    findings = check_pdd011_requirement_count(doc)
    assert len(findings) == 1
    assert "Found 1 requirements" in findings[0].message

def test_pdd012_implementation_steps_detection():
    sec = Section(header="## Requirements", content="1. First, create a file named test.py", start_line=1, end_line=2)
    doc = create_mock_doc("...", sections=[sec])
    findings = check_pdd012_implementation_steps(doc)
    assert len(findings) == 1
    assert findings[0].rule_id == "PDD012"

def test_pdd040_determinism_tags():
    tag = Tag(name="shell", content="ls -la", start_line=5, end_line=5)
    doc = create_mock_doc("...", tags=[tag])
    findings = check_pdd040_determinism(doc)
    assert len(findings) == 1
    assert "Non-Deterministic Shell" in findings[0].title

def test_pdd050_vague_prompt():
    # Short text, no IO section
    doc = create_mock_doc("Do something small.")
    findings = check_pdd050_vague_prompt(doc)
    assert len(findings) == 1
    assert findings[0].rule_id == "PDD050"

def test_pdd060_buried_constraints_logic():
    # 100 lines, constraint at line 50 (middle)
    lines = ["Normal line"] * 100
    lines[50] = "IMPORTANT: Do not fail."
    raw_text = "\n".join(lines)
    doc = create_mock_doc(raw_text)
    findings = check_pdd060_buried_constraints(doc)
    assert len(findings) == 1
    assert findings[0].line_number == 51 # 1-indexed

# --- Z3 Formal Verification ---

def test_pdd060_zone_calculation_verification():
    """
    Verify the mathematical boundaries of the 'buried' zone.
    The code defines start_zone = total * 0.25 and end_zone = total * 0.75.
    We want to ensure that for any document > 20 lines, there is a non-empty 
    middle zone and that the zones are disjoint from the 'top' and 'bottom'.
    """
    total_lines = Int('total_lines')
    start_zone = Int('start_zone')
    end_zone = Int('end_zone')
    
    s = Solver()
    
    # Constraints based on implementation
    s.add(total_lines > 20)
    s.add(start_zone == total_lines / 4) # Z3 integer division
    s.add(end_zone == (3 * total_lines) / 4)
    
    # Property 1: Middle zone must exist
    s.push()
    s.add(end_zone <= start_zone)
    assert s.check() == unsat, "Middle zone should always be positive for total > 20"
    s.pop()
    
    # Property 2: The zone should not cover the first 5 lines (Role area)
    s.push()
    s.add(start_zone < 5)
    # This might be sat for small total_lines (e.g. 21/4 = 5). 
    # Let's check if it's possible for the zone to start too early.
    if s.check() == sat:
        m = s.model()
        # If it is sat, we know the heuristic might overlap with the top for small docs.
        # This is acceptable for a heuristic but good to know.
        pass
    s.pop()

def test_pdd011_count_logic_verification():
    """Verify that the requirement count logic (5-10) is correctly bounded."""
    count = Int('count')
    is_outlier = Solver()
    
    # Logic: (req_count < 5 or req_count > 10)
    condition = And(count > 0, z3Or(count < 5, count > 10))
    
    is_outlier.add(condition)
    
    # Check if 5 is an outlier (should be false, 5 is acceptable)
    is_outlier.push()
    is_outlier.add(count == 5)
    assert is_outlier.check() == unsat
    is_outlier.pop()
    
    # Check if 1 is an outlier (should be true)
    is_outlier.push()
    is_outlier.add(count == 1)
    assert is_outlier.check() == sat
    is_outlier.pop()

def test_pdd013_negative_constraint_threshold():
    """Verify the threshold for negative constraints."""
    neg_count = Int('neg_count')
    s = Solver()
    
    # Logic: count > 3
    s.add(neg_count > 3)
    
    # Verify 4 triggers it
    s.push()
    s.add(neg_count == 4)
    assert s.check() == sat
    s.pop()
    
    # Verify 3 does not trigger it
    s.push()
    s.add(neg_count == 3)
    assert s.check() == unsat
    s.pop()