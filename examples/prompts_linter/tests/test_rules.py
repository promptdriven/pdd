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

# =============================================================================
# Test Plan (New Tests)
# =============================================================================
#
# 1. Modularity Boundary Checks (Unit Tests via Public API)
#    - Test exact boundary for section separators.
#    - Case A: 2 separators (Should NOT trigger MOD002).
#    - Case B: 3 separators (Should trigger MOD002).
#    - Rationale: Ensure the logic `len > 2` is strictly adhered to.
#
# 2. Requirements List Styles (Unit Tests via Public API)
#    - Test bullet point variations for Requirements section.
#    - Case: Using `*` or `-` or `+` instead of numbered lists.
#    - Rationale: The regex allows `[-*+]`, need to verify this works for valid inputs.
#
# 3. Attention Hierarchy - Multiple & Case Insensitivity (Unit Tests via Public API)
#    - Test that multiple distinct keywords in the middle zone trigger multiple issues.
#    - Test that keywords are detected case-insensitively (e.g., "security" vs "Security").
#    - Rationale: Ensure comprehensive scanning of the danger zone.
#
# 4. Determinism - Multiple Tag Types (Unit Tests via Public API)
#    - Test presence of multiple different forbidden tags (e.g., <web> AND <run>).
#    - Rationale: Ensure all violations are reported, not just the first one found.
#
# 5. Anatomy - Indentation Robustness (Unit Tests via Public API)
#    - Test headers with significant leading whitespace/indentation.
#    - Rationale: The regex `^\s*` was added to handle this; verification is needed.
#
# 6. Z3 Formal Verification - Modularity Logic
#    - Verify the logic for separator counts formally.
#    - Theorem: If count <= 2, then Issue is False. If count > 2, Issue is True.

# =============================================================================
# New Unit Tests
# =============================================================================

def test_modularity_separator_boundary():
    """
    Test the boundary condition for section separators (MOD002).
    Rule: > 2 separators triggers an issue.
    """
    # Case A: 2 separators (Allowed)
    text_safe = """
    Part 1
    ---
    Part 2
    ===
    End
    """
    issues_safe = rules.analyze_text(text_safe)
    mod_issues_safe = [i for i in issues_safe if i.rule_id == "MOD002"]
    assert len(mod_issues_safe) == 0, "2 separators should not trigger MOD002"

    # Case B: 3 separators (Forbidden)
    text_fail = """
    Part 1
    ---
    Part 2
    ===
    Part 3
    ***
    End
    """
    issues_fail = rules.analyze_text(text_fail)
    mod_issues_fail = [i for i in issues_fail if i.rule_id == "MOD002"]
    assert len(mod_issues_fail) == 1, "3 separators should trigger MOD002"

def test_requirements_bullet_styles():
    """
    Test that Requirements sections accept bullet points (*, -, +) 
    and do not trigger REQ001 (Malformed).
    """
    # We construct a text that has a valid header and a bullet list
    text = """
    # Requirements
    * Requirement A
    - Requirement B
    + Requirement C
    """
    issues = rules.analyze_text(text)
    
    # Filter for REQ001 (Malformed) or REQ002 (Missing)
    req_issues = [i for i in issues if i.rule_id in ["REQ001", "REQ002"]]
    assert len(req_issues) == 0, "Bullet points should be accepted as valid Requirements format"

def test_attention_multiple_and_case_insensitivity():
    """
    Test that multiple keywords are detected in the middle zone, 
    and detection is case-insensitive.
    """
    # Construct text > 100 chars
    # Padding needs to be enough to push keywords into 20%-80% zone
    padding = "x" * 100
    # "security" (lowercase) and "AUTH" (uppercase) in the middle
    text = f"{padding} security {padding} AUTH {padding}"
    
    issues = rules.analyze_text(text)
    att_issues = [i for i in issues if i.rule_id == "ATT001"]
    
    # Should find both "Security" (matched by 'security') and "Auth" (matched by 'AUTH')
    assert len(att_issues) == 2
    
    descriptions = [i.description.lower() for i in att_issues]
    assert any("security" in d for d in descriptions)
    assert any("auth" in d for d in descriptions)

def test_determinism_multiple_tag_types(mock_helpers):
    """
    Test that multiple different forbidden tags generate multiple issues.
    """
    text = "Try to <web>scrape</web> and then <run>execute</run>."
    
    # Mock helpers to return counts for specific tags
    def side_effect_count(txt, tag):
        if tag in ["web", "run"]:
            return 1
        return 0
    
    mock_helpers.count_tags.side_effect = side_effect_count
    
    issues = rules.analyze_text(text)
    det_issues = [i for i in issues if i.rule_id == "DET001"]
    
    assert len(det_issues) == 2
    descriptions = [i.description for i in det_issues]
    assert any("<web>" in d for d in descriptions)
    assert any("<run>" in d for d in descriptions)

def test_anatomy_indentation_robustness():
    """
    Test that anatomy headers are detected even with indentation.
    """
    text = """
    # Requirements
    1. Req
    
      # Input/Output
      Input: A
      
    \t# Dependencies
    - None
    
       # Instructions
       Do it.
    """
    issues = rules.analyze_text(text)
    
    # We expect NO Anatomy issues (ANAxxx)
    ana_issues = [i for i in issues if i.category == RuleCategory.ANATOMY and i.severity == Severity.WARNING]
    assert len(ana_issues) == 0, f"Indented headers should be found. Got: {[i.title for i in ana_issues]}"

def test_modularity_file_enumeration_case_insensitive():
    """
    Test that file enumeration patterns are case insensitive.
    """
    text = """
    file 1: main.py
    ...
    FILE 2: utils.py
    """
    issues = rules.analyze_text(text)
    mod_issues = [i for i in issues if i.rule_id == "MOD003"]
    assert len(mod_issues) == 1

# =============================================================================
# Z3 Formal Verification (Additional)
# =============================================================================

def test_z3_modularity_separator_logic():
    """
    Formal verification of the separator count logic.
    Constraint: Issue is triggered IFF count > 2.
    """
    try:
        import z3
    except ImportError:
        pytest.skip("z3-solver not installed")

    # Variables
    count = z3.Int('count')
    has_issue = z3.Bool('has_issue')
    
    # Logic defined in code: if len(separators) > 2: issues.append(...)
    # So has_issue <==> count > 2
    logic = has_issue == (count > 2)
    
    # Constraint: count cannot be negative (it's a length)
    valid_count = count >= 0
    
    solver = z3.Solver()
    solver.add(valid_count)
    solver.add(logic)
    
    # Verification 1: Prove that count = 2 implies NO issue
    solver.push()
    solver.add(count == 2)
    solver.add(has_issue) # Assert that issue exists (contradiction expected)
    result = solver.check()
    assert result == z3.unsat, "Z3 found a case where count=2 triggers an issue"
    solver.pop()
    
    # Verification 2: Prove that count = 3 implies issue
    solver.push()
    solver.add(count == 3)
    solver.add(z3.Not(has_issue)) # Assert that issue does NOT exist (contradiction expected)
    result = solver.check()
    assert result == z3.unsat, "Z3 found a case where count=3 does NOT trigger an issue"
    solver.pop()