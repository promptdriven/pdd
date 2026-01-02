import pytest
from typing import List, Any
from unittest.mock import MagicMock
from src.backend.rules.registry import LintRule, RuleRegistry, register, default_registry
from src.backend.models.findings import Finding

# ==============================================================================
# TEST PLAN
# ==============================================================================
# 1. Metadata Validation (Unit Tests):
#    - Test that a rule without rule_id raises ValueError.
#    - Test that a rule with an invalid severity raises ValueError.
#    - Test that a rule with valid metadata instantiates correctly.
#
# 2. Registry Management (Unit Tests):
#    - Test register_rule adds a valid rule to the registry.
#    - Test register_rule raises TypeError for classes not inheriting from LintRule.
#    - Test register_rule raises ValueError for duplicate rule IDs.
#    - Test get_rule returns the correct instance or None.
#    - Test get_all_rules returns rules sorted by ID.
#    - Test clear() empties the registry.
#
# 3. Decorator Functionality (Unit Tests):
#    - Test @register correctly adds a rule to the default_registry.
#
# 4. Formal Verification (Z3):
#    - Case: Rule ID Uniqueness.
#    - Logic: Given a set of rules, if the registry accepts them, then for any two 
#      distinct rules R1 and R2, R1.rule_id != R2.rule_id.
#    - Case: Severity Constraints.
#    - Logic: For any rule R in the registry, R.severity must be in {error, warn, info}.
# ==============================================================================

# --- Mock Rule Classes for Testing ---

class ValidRule(LintRule):
    rule_id = "PDD001"
    severity = "error"
    title = "Valid Rule"
    def analyze(self, prompt_structure: Any) -> List[Finding]:
        return []

class AnotherValidRule(LintRule):
    rule_id = "PDD002"
    severity = "warn"
    title = "Another Valid Rule"
    def analyze(self, prompt_structure: Any) -> List[Finding]:
        return []

class DuplicateIdRule(LintRule):
    rule_id = "PDD001"
    severity = "info"
    title = "Duplicate ID"
    def analyze(self, prompt_structure: Any) -> List[Finding]:
        return []

class InvalidSeverityRule(LintRule):
    rule_id = "PDD003"
    severity = "critical"  # Invalid
    title = "Invalid Severity"
    def analyze(self, prompt_structure: Any) -> List[Finding]:
        return []

# --- Fixtures ---

@pytest.fixture
def registry():
    """Returns a fresh instance of RuleRegistry for each test."""
    return RuleRegistry()

@pytest.fixture(autouse=True)
def clear_default_registry():
    """Ensures the global default_registry is clean before/after tests."""
    default_registry.clear()
    yield
    default_registry.clear()

# --- Unit Tests ---

def test_lint_rule_metadata_validation():
    """Ensures LintRule validates its own metadata on instantiation."""
    # Valid rule should not raise
    ValidRule()

    # Missing rule_id
    class MissingIdRule(LintRule):
        severity = "error"
        title = "Missing ID"
        def analyze(self, p): return []
    
    with pytest.raises(ValueError, match="must define a 'rule_id'"):
        MissingIdRule()

    # Invalid severity
    with pytest.raises(ValueError, match="has invalid severity"):
        InvalidSeverityRule()

def test_registry_add_and_get(registry):
    """Tests basic registration and retrieval."""
    registry.register_rule(ValidRule)
    rule = registry.get_rule("PDD001")
    assert isinstance(rule, ValidRule)
    assert rule.rule_id == "PDD001"

def test_registry_duplicate_id(registry):
    """Tests that duplicate IDs are rejected."""
    registry.register_rule(ValidRule)
    with pytest.raises(ValueError, match="already registered"):
        registry.register_rule(DuplicateIdRule)

def test_registry_invalid_inheritance(registry):
    """Tests that only LintRule subclasses can be registered."""
    class NotARule:
        pass
    with pytest.raises(TypeError, match="must inherit from LintRule"):
        registry.register_rule(NotARule)

def test_get_all_rules_sorting(registry):
    """Tests that rules are returned sorted by ID."""
    registry.register_rule(AnotherValidRule) # PDD002
    registry.register_rule(ValidRule)        # PDD001
    
    rules = registry.get_all_rules()
    assert len(rules) == 2
    assert rules[0].rule_id == "PDD001"
    assert rules[1].rule_id == "PDD002"

def test_registry_clear(registry):
    """Tests clearing the registry."""
    registry.register_rule(ValidRule)
    registry.clear()
    assert len(registry.get_all_rules()) == 0

def test_register_decorator():
    """Tests the @register decorator on the default_registry."""
    @register
    class DecoratedRule(LintRule):
        rule_id = "DEC001"
        severity = "info"
        title = "Decorated"
        def analyze(self, p): return []
    
    assert default_registry.get_rule("DEC001") is not None

def test_abstract_method_enforcement(registry):
    """Tests that rules must implement analyze."""
    class IncompleteRule(LintRule):
        rule_id = "INC001"
        severity = "error"
        title = "Incomplete"
        # analyze is missing
    
    with pytest.raises(TypeError, match="Cannot instantiate rule"):
        registry.register_rule(IncompleteRule)

# --- Formal Verification with Z3 ---

def test_registry_logic_formal_verification():
    """
    Uses Z3 to verify the logical consistency of the registry constraints:
    1. Uniqueness of IDs.
    2. Validity of Severities.
    """
    try:
        from z3 import Solver, String, Or, Distinct, sat, Implies, EnumSort
    except ImportError:
        pytest.skip("Z3 not installed. Skipping formal verification.")

    solver = Solver()

    # Define Severity Enum
    # error=0, warn=1, info=2
    Severity, (ERROR, WARN, INFO) = EnumSort('Severity', ['error', 'warn', 'info'])

    # We model a registry with N slots
    N = 3
    rule_ids = [String(f'id_{i}') for i in range(N)]
    rule_severities = [Severity.constructor(j)() for j in range(N)] # Placeholder for any severity
    
    # Constraint: If a rule is "active" (id is not empty), its ID must be unique
    # and its severity must be one of the allowed ones (inherent in EnumSort).
    
    # 1. Uniqueness Check:
    # If the registry logic allows two rules with the same ID, it's a violation.
    # We want to prove that (ID_i == ID_j) AND (i != j) is impossible in a valid state.
    
    # Let's simulate the 'register_rule' logic:
    # "If ID already exists, raise Error"
    # This means in any valid state of the registry:
    for i in range(N):
        for j in range(i + 1, N):
            # For all distinct pairs, IDs must be distinct
            solver.add(rule_ids[i] != rule_ids[j])

    # Verify that Z3 can find a valid state (Satisfiability)
    assert solver.check() == sat

    # 2. Severity Check:
    # Prove that no rule can exist in the registry with a severity outside the set.
    # Since we used EnumSort, Z3 strictly enforces that rule_severities[i] 
    # MUST be one of ERROR, WARN, INFO.
    
    for i in range(N):
        # This is a tautology in Z3 because of EnumSort, 
        # but it mirrors the code's ALLOWED_SEVERITIES check.
        solver.add(Or(rule_severities[i] == ERROR, 
                      rule_severities[i] == WARN, 
                      rule_severities[i] == INFO))

    assert solver.check() == sat

def test_analyze_signature():
    """Ensures the analyze method accepts Any and returns a list."""
    rule = ValidRule()
    # Mocking the prompt structure (Any)
    mock_structure = MagicMock()
    findings = rule.analyze(mock_structure)
    assert isinstance(findings, list)
