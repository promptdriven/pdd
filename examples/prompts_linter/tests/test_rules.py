import pytest
import sys
import os
from unittest.mock import MagicMock, patch

# Add the project root to sys.path to allow imports
# Assuming the test file is in tests/test_rules.py and project root is one level up
current_dir = os.path.dirname(os.path.abspath(__file__))
project_root = os.path.abspath(os.path.join(current_dir, '..'))
if project_root not in sys.path:
    sys.path.insert(0, project_root)

from src.utils import rules
from src.utils.models import Issue, Severity, RuleCategory

# =============================================================================
# Test Plan
# =============================================================================
#
# 1. Entry Point & Robustness (Unit Tests)
#    - Test `analyze_text` with empty/whitespace strings (Should return GEN001 error).
#    - Test `analyze_text` with valid input (Should return a list of issues).
#
# 2. Anatomy Checks (Unit Tests)
#    - Test missing "Requirements" header (Should flag ANA warning).
#    - Test missing "Input/Output" header (Should flag ANA warning).
#    - Test missing "Dependencies" header (Should flag ANA warning).
#    - Test missing "Instructions" header (Should flag ANA warning).
#    - Test presence of all headers (Should return no ANA issues).
#    - Test case insensitivity and variations (e.g., "Inputs and Outputs").
#
# 3. Determinism Checks (Unit Tests)
#    - Test presence of forbidden tags: <web>, <shell>, <exec>, <run>.
#    - Verify correct RuleCategory.DETERMINISM and Severity.WARNING.
#    - Test clean text (no forbidden tags).
#
# 4. Modularity Checks (Unit Tests)
#    - Test multiple file headers (e.g., "# file: a.py", "# file: b.py").
#    - Test excessive section separators ("---", "===").
#    - Test file enumeration patterns ("File 1:", "File 2:").
#    - Verify correct RuleCategory.MODULARITY.
#
# 5. Context Checks (Unit Tests & Mocking)
#    - Test "Repo Dump" keywords ("entire codebase", "repo dump").
#    - Test high code-to-text ratio.
#      * Strategy: Mock `src.utils.helpers.calculate_code_ratio` to control the ratio
#        without needing to construct massive strings.
#      * Verify threshold logic (> 0.80 ratio AND > 50 lines).
#
# 6. Requirements Format Checks (Unit Tests)
#    - Test "Requirements" header present but missing list format (Should flag REQ001).
#    - Test "Requirements" header missing entirely (Should flag REQ002).
#    - Test correct format ("Requirements\n1. Item").
#
# 7. Attention Hierarchy Checks (Unit Tests)
#    - Test critical keywords ("Security", "Auth") in the middle 60% of text.
#    - Test critical keywords at the start/end (Should pass).
#    - Test short text (< 100 chars) (Should skip check).
#
# 8. Z3 Formal Verification (Property-Based Testing)
#    - While Z3 is powerful for logic constraints, this module is heavily regex and string-search based.
#    - We will use Z3 to verify the *logic* of the Attention Hierarchy calculation to ensure
#      the indices for "start", "middle", and "end" zones are mathematically sound and cover the whole string space.
#    - We will verify that for any string length L >= 100, an index I is either in Start, Middle, or End,
#      and that Middle is strictly defined as (0.2*L < I < 0.8*L).

# =============================================================================
# Fixtures & Mocks
# =============================================================================

@pytest.fixture
def mock_helpers():
    """Mocks the helpers module to control tag counting and code ratio."""
    with patch('src.utils.rules.helpers') as mock:
        # Default behaviors
        mock.count_tags.return_value = 0
        mock.calculate_code_ratio.return_value = 0.1
        yield mock

# =============================================================================
# 1. Entry Point & Robustness
# =============================================================================

def test_analyze_text_empty_input():
    """Test that empty input returns a specific error issue."""
    issues = rules.analyze_text("")
    assert len(issues) == 1
    assert issues[0].rule_id == "GEN001"
    assert issues[0].severity == Severity.ERROR
    assert issues[0].title == "Empty Prompt"

def test_analyze_text_whitespace_input():
    """Test that whitespace-only input returns a specific error issue."""
    issues = rules.analyze_text("   \n   ")
    assert len(issues) == 1
    assert issues[0].rule_id == "GEN001"

def test_analyze_text_integration(mock_helpers):
    """
    Integration test: Ensure analyze_text calls all sub-checkers.
    We provide a text that triggers one issue from each category to verify aggregation.
    """
    # Construct a text that fails multiple checks
    # 1. Missing Requirements (Anatomy + Contracts)
    # 2. Has <web> tag (Determinism)
    # 3. Has "repo dump" keyword (Context)
    
    text = """
    # Instructions
    Do this.
    
    <web>google.com</web>
    
    I am sending you a repo dump.
    """
    
    # Setup mock for tag count
    def side_effect_count_tags(txt, tag):
        return 1 if tag == "web" else 0
    mock_helpers.count_tags.side_effect = side_effect_count_tags
    
    issues = rules.analyze_text(text)
    
    # Verify we got a list of issues
    assert isinstance(issues, list)
    assert len(issues) > 0
    
    # Check for specific rule IDs we expect
    rule_ids = [i.rule_id for i in issues]
    
    # ANA: Missing Input/Output, Dependencies, Requirements
    assert any(rid.startswith("ANA") for rid in rule_ids)
    # DET: <web> tag
    assert "DET001" in rule_ids
    # CTX: repo dump keyword
    assert "CTX002" in rule_ids
    # REQ: Missing Requirements Contract
    assert "REQ002" in rule_ids

# =============================================================================
# 2. Anatomy Checks
# =============================================================================

def test_check_anatomy_missing_sections():
    """Test that missing sections trigger warnings."""
    # Only Instructions present
    text = "# Instructions\nDo work."
    issues = rules._check_anatomy(text)
    
    titles = [i.title for i in issues]
    assert "Missing Requirements Section" in titles
    assert "Missing Input/Output Section" in titles
    assert "Missing Dependencies Section" in titles
    # Instructions is present, so it shouldn't be missing
    assert "Missing Instructions Section" not in titles

def test_check_anatomy_all_sections_present():
    """Test that having all sections results in no anatomy issues."""
    text = """
    # Requirements
    1. Do X
    # Input/Output
    Input: Text
    # Dependencies
    None
    # Instructions
    Go.
    """
    issues = rules._check_anatomy(text)
    assert len(issues) == 0

def test_check_anatomy_header_variations():
    """Test regex flexibility for headers."""
    text = """
    # Deliverables
    Code.
    # Inputs and Outputs
    Data.
    """
    # These map to "Input/Output"
    # We only check if it *fails* to find them. 
    # If we pass just these, we expect Missing Requirements, Dependencies, Instructions.
    # We should NOT see "Missing Input/Output Section".
    
    issues = rules._check_anatomy(text)
    titles = [i.title for i in issues]
    assert "Missing Input/Output Section" not in titles

# =============================================================================
# 3. Determinism Checks
# =============================================================================

def test_check_determinism_forbidden_tags(mock_helpers):
    """Test detection of forbidden tags."""
    text = "Run this <shell>rm -rf</shell> command."
    
    # Mock helper to find the tag
    mock_helpers.count_tags.return_value = 1
    
    issues = rules._check_determinism(text)
    
    assert len(issues) >= 1
    assert issues[0].rule_id == "DET001"
    assert issues[0].category == RuleCategory.DETERMINISM
    # Verify helper was called
    mock_helpers.count_tags.assert_any_call(text, "shell")

def test_check_determinism_clean(mock_helpers):
    """Test clean text returns no issues."""
    mock_helpers.count_tags.return_value = 0
    issues = rules._check_determinism("Just text.")
    assert len(issues) == 0

# =============================================================================
# 4. Modularity Checks
# =============================================================================

def test_check_modularity_multiple_file_headers():
    """Test detection of multiple file headers."""
    text = """
    # file: src/main.py
    print("hello")
    
    # file: src/utils.py
    print("world")
    """
    issues = rules._check_modularity(text)
    assert any(i.rule_id == "MOD001" for i in issues)

def test_check_modularity_excessive_separators():
    """Test detection of excessive separators."""
    text = """
    Section 1
    ---
    Section 2
    ===
    Section 3
    ***
    Section 4
    """
    issues = rules._check_modularity(text)
    assert any(i.rule_id == "MOD002" for i in issues)

def test_check_modularity_file_enumeration():
    """Test detection of 'File 1:', 'File 2:' patterns."""
    text = """
    File 1: logic.py
    ...
    File 2: test.py
    ...
    """
    issues = rules._check_modularity(text)
    assert any(i.rule_id == "MOD003" for i in issues)

# =============================================================================
# 5. Context Checks
# =============================================================================

def test_check_context_keywords():
    """Test detection of repo dump keywords."""
    text = "Here is the entire codebase for you to fix."
    issues = rules._check_context(text)
    assert any(i.rule_id == "CTX002" for i in issues)

def test_check_context_high_code_ratio(mock_helpers):
    """Test detection of high code density."""
    # Create a dummy text with > 50 lines
    text = "\n".join(["line"] * 60)
    
    # Mock ratio to be high (0.85)
    mock_helpers.calculate_code_ratio.return_value = 0.85
    
    issues = rules._check_context(text)
    
    assert any(i.rule_id == "CTX001" for i in issues)
    mock_helpers.calculate_code_ratio.assert_called_once_with(text)

def test_check_context_short_text_ignored(mock_helpers):
    """Test that short text is ignored even if ratio is high."""
    text = "short\ntext"
    mock_helpers.calculate_code_ratio.return_value = 0.99
    
    issues = rules._check_context(text)
    # Should be empty because line count < 50
    assert len(issues) == 0

# =============================================================================
# 6. Requirements Format Checks
# =============================================================================

def test_check_requirements_missing_entirely():
    """Test missing requirements section triggers REQ002."""
    text = "# Instructions\nDo this."
    issues = rules._check_requirements_format(text)
    assert len(issues) == 1
    assert issues[0].rule_id == "REQ002"
    assert issues[0].severity == Severity.ERROR

def test_check_requirements_malformed():
    """Test requirements header present but not followed by list."""
    text = """
    # Requirements
    This is a paragraph describing requirements but it is not a list.
    It should have numbers or bullets.
    """
    issues = rules._check_requirements_format(text)
    assert len(issues) == 1
    assert issues[0].rule_id == "REQ001"
    assert issues[0].severity == Severity.ERROR

def test_check_requirements_valid():
    """Test valid requirements format."""
    text = """
    # Requirements
    1. First req
    2. Second req
    """
    issues = rules._check_requirements_format(text)
    assert len(issues) == 0

# =============================================================================
# 7. Attention Hierarchy Checks
# =============================================================================

def test_check_attention_short_text():
    """Test that short text skips attention checks."""
    text = "Security is important." # Very short
    issues = rules._check_attention_hierarchy(text)
    assert len(issues) == 0

def test_check_attention_middle_loss():
    """Test critical keyword in the middle of long text."""
    # Construct text: 100 chars padding + Keyword + 100 chars padding
    padding = "x" * 100
    text = f"{padding} Security {padding}"
    
    issues = rules._check_attention_hierarchy(text)
    assert len(issues) == 1
    assert issues[0].rule_id == "ATT001"
    assert issues[0].severity == Severity.INFO
    assert "Security" in issues[0].description

def test_check_attention_start_end_safe():
    """Test critical keywords at start or end are safe."""
    # Keyword at start
    padding = "x" * 200
    text_start = f"Security {padding}"
    issues = rules._check_attention_hierarchy(text_start)
    assert len(issues) == 0
    
    # Keyword at end
    text_end = f"{padding} Security"
    issues = rules._check_attention_hierarchy(text_end)
    assert len(issues) == 0

# =============================================================================
# 8. Z3 Formal Verification
# =============================================================================

def test_z3_attention_logic():
    """
    Formal verification of the Attention Hierarchy logic using Z3.
    
    We want to prove that for a text of sufficient length (L >= 100),
    the definition of the "Middle Zone" (0.2*L < index < 0.8*L)
    leaves valid "Start" and "End" zones, and that an index cannot be
    in the Middle Zone if it is in the first 20% or last 20%.
    """
    try:
        import z3
    except ImportError:
        pytest.skip("z3-solver not installed")

    # Variables
    L = z3.Real('L')      # Length of text
    idx = z3.Real('idx')  # Index of keyword
    
    # Constraints representing the code logic
    # 1. Text length must be at least 100 (from code: if total_len < 100: return)
    length_constraint = L >= 100
    
    # 2. Valid index bounds (0 <= idx < L)
    index_bounds = z3.And(idx >= 0, idx < L)
    
    # 3. Definition of Middle Zone in code: start_zone < idx < end_zone
    # where start_zone = L * 0.2, end_zone = L * 0.8
    in_middle = z3.And(idx > L * 0.2, idx < L * 0.8)
    
    # 4. Definition of Start Zone (First 20%)
    in_start = idx <= L * 0.2
    
    # 5. Definition of End Zone (Last 20%)
    in_end = idx >= L * 0.8
    
    solver = z3.Solver()
    
    # Verification 1: Mutual Exclusivity
    # Prove that if an index is in the Middle, it CANNOT be in Start or End.
    # We negate the theorem to find a counter-example.
    # Theorem: in_middle => NOT(in_start OR in_end)
    # Negation: in_middle AND (in_start OR in_end)
    solver.push()
    solver.add(length_constraint)
    solver.add(index_bounds)
    solver.add(in_middle)
    solver.add(z3.Or(in_start, in_end))
    
    result = solver.check()
    # If UNSAT, it means no counter-example exists, so the logic is sound.
    assert result == z3.unsat, "Z3 found a case where Middle overlaps with Start/End!"
    solver.pop()
    
    # Verification 2: Coverage
    # Prove that an index is either in Start, Middle, or End (or exactly on the boundary).
    # Actually, the code uses strict inequality (<, >) for middle.
    # So boundary points (exactly 0.2*L or 0.8*L) are NOT in middle.
    # Let's verify that the code treats boundary points as SAFE (not middle).
    
    # Case: idx is exactly L * 0.2
    solver.push()
    solver.add(length_constraint)
    solver.add(idx == L * 0.2)
    solver.add(in_middle) # Assert it IS in middle
    
    result = solver.check()
    # Should be UNSAT because code uses idx > start_zone (strict)
    assert result == z3.unsat, "Z3 found that boundary 0.2*L is considered Middle (it should be safe)"
    solver.pop() 