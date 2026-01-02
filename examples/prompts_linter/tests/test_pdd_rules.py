import sys
import pytest
import re
from typing import List, Optional, Any
from dataclasses import dataclass, field
from enum import Enum
from z3 import Int, And, Implies, Solver, sat, unsat, Or as z3Or
from unittest.mock import MagicMock

# --- Mocks for Dependencies ---
# We define these before importing the code_under_test to satisfy its imports

class Severity(Enum):
    ERROR = "error"
    WARN = "warn"
    INFO = "info"

@dataclass
class SuggestedEdit:
    description: str
    new_text: str
    line_number: int

@dataclass
class Finding:
    rule_id: str
    severity: Severity
    title: str
    message: str
    line_number: int
    suggested_edit: Optional[SuggestedEdit] = None

@dataclass
class Section:
    header: str
    content: str
    start_line: int = 1
    end_line: int = 1

@dataclass
class Tag:
    name: str
    content: str
    start_line: int = 1
    end_line: int = 1
    attributes: dict = field(default_factory=dict)

@dataclass
class ParsedDocument:
    raw_text: str
    sections: List[Section] = field(default_factory=list)
    tags: List[Tag] = field(default_factory=list)
    preamble: Optional[Section] = None

# Mock Registry
class MockRegistry:
    def register_rule(self, func):
        return func

# Inject mocks into sys.modules
module_findings = type(sys)("src.backend.models.findings")
module_findings.Severity = Severity
module_findings.Finding = Finding
module_findings.SuggestedEdit = SuggestedEdit
sys.modules["src.backend.models.findings"] = module_findings

module_parser = type(sys)("src.backend.core.parser")
module_parser.ParsedDocument = ParsedDocument
module_parser.Section = Section
module_parser.Tag = Tag
sys.modules["src.backend.core.parser"] = module_parser

module_registry = type(sys)("src.backend.rules.registry")
module_registry.RuleRegistry = MockRegistry
sys.modules["src.backend.rules.registry"] = module_registry

# Now we can import the code under test
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
except ImportError:
    pass

# --- Fixtures ---

def create_mock_doc(raw_text: str, sections: List[Section] = None, tags: List[Tag] = None, preamble: Section = None) -> ParsedDocument:
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
    doc = create_mock_doc("Do something small.")
    findings = check_pdd050_vague_prompt(doc)
    assert len(findings) == 1
    assert findings[0].rule_id == "PDD050"

def test_pdd060_buried_constraints_logic():
    lines = ["Normal line"] * 100
    lines[50] = "IMPORTANT: Do not fail."
    raw_text = "\n".join(lines)
    doc = create_mock_doc(raw_text)
    findings = check_pdd060_buried_constraints(doc)
    assert len(findings) == 1
    assert findings[0].line_number == 51

# --- Z3 Formal Verification ---

def test_pdd060_zone_calculation_verification():
    total_lines = Int('total_lines')
    start_zone = Int('start_zone')
    end_zone = Int('end_zone')
    s = Solver()
    s.add(total_lines > 20)
    s.add(start_zone == total_lines / 4)
    s.add(end_zone == (3 * total_lines) / 4)
    s.push()
    s.add(end_zone <= start_zone)
    assert s.check() == unsat, "Middle zone should always be positive for total > 20"
    s.pop()
    s.push()
    s.add(start_zone < 5)
    if s.check() == sat:
        pass
    s.pop()

def test_pdd011_count_logic_verification():
    count = Int('count')
    is_outlier = Solver()
    condition = And(count > 0, z3Or(count < 5, count > 10))
    is_outlier.add(condition)
    is_outlier.push()
    is_outlier.add(count == 5)
    assert is_outlier.check() == unsat
    is_outlier.pop()
    is_outlier.push()
    is_outlier.add(count == 4)
    assert is_outlier.check() == sat
    is_outlier.pop()

def test_pdd013_negative_constraint_threshold():
    neg_count = Int('neg_count')
    s = Solver()
    s.add(neg_count > 3)
    s.push()
    s.add(neg_count == 4)
    assert s.check() == sat
    s.pop()
    s.push()
    s.add(neg_count == 3)
    assert s.check() == unsat
    s.pop()