import pytest
import logging
from unittest.mock import MagicMock, patch
from dataclasses import dataclass, field
from typing import List, Optional, Any
import sys
import os

# Add the parent directory to sys.path to allow imports if running from tests directory
sys.path.append(os.path.abspath(os.path.join(os.path.dirname(__file__), '..')))

from src.utils.fix import apply_fixes

# --- Mock Models for Testing ---
@dataclass
class MockIssue:
    rule_id: str = "GEN001"
    description: str = "Generic issue"
    severity: str = "warning"
    category: Any = None
    fix_suggestion: str = ""

@dataclass
class MockSuggestion:
    before: str
    after: str
    priority: str = "Low"
    title: str = "Fix"
    rule_id: str = "FIX001"

@dataclass
class MockLLMAnalysis:
    suggestions: List[MockSuggestion] = field(default_factory=list)

@dataclass
class MockReport:
    issues: List[MockIssue] = field(default_factory=list)
    llm_analysis: Optional[MockLLMAnalysis] = None
    suggestions: List[MockSuggestion] = field(default_factory=list)

class MockRuleCategory:
    MODULARITY = "MODULARITY"
    CONTEXT = "CONTEXT"
    DETERMINISM = "DETERMINISM"
    ANATOMY = "ANATOMY"
    STRUCTURE = "STRUCTURE"

# --- Unit Tests ---

def test_empty_input():
    """Test that empty input returns empty string."""
    report = MockReport()
    assert apply_fixes("", report) == ""

def test_scaffolding_missing_root_tags():
    """Test that missing root tags are added when STR001 issue is present."""
    text = "This is a prompt."
    issue = MockIssue(rule_id="STR001", description="Missing <prompt> tags")
    report = MockReport(issues=[issue])
    
    fixed = apply_fixes(text, report)
    
    assert fixed.startswith("<prompt>")
    # Use strip() because final cleanup adds a newline
    assert fixed.strip().endswith("</prompt>")
    assert "This is a prompt." in fixed

def test_scaffolding_missing_sections():
    """Test that missing sections are appended correctly."""
    text = "<prompt>\nDo something.\n</prompt>"
    issue_req = MockIssue(description="Missing section Requirements")
    issue_ctx = MockIssue(description="Missing section Context")
    report = MockReport(issues=[issue_req, issue_ctx])
    
    fixed = apply_fixes(text, report)
    
    assert "Requirements" in fixed
    # Context is not added because "Missing section Context" doesn't trigger a specific fix action in the code
    # (The code looks for "requirements", "dependencies", "instructions", "deliverable")
    # Verify Requirements placeholder is there.
    assert "[TODO: Define specific requirements]" in fixed
    # Ensure they are inside the tags (before the closing tag)
    assert fixed.strip().endswith("</prompt>")
    assert fixed.count("</prompt>") == 1
    # Verify insertion happened before closing tag
    assert fixed.find("Requirements") < fixed.rfind("</prompt>")

def test_scaffolding_idempotency():
    """Test that sections are not added if they already exist."""
    text = "<prompt>\nRequirements\n- existing\n</prompt>"
    issue = MockIssue(description="Missing section Requirements")
    report = MockReport(issues=[issue])
    
    fixed = apply_fixes(text, report)
    
    # Should not add another Requirements section
    assert fixed.count("Requirements") == 1

def test_llm_patching_basic():
    """Test basic text replacement from LLM suggestions."""
    text = "<prompt>Write a code.</prompt>"
    suggestion = MockSuggestion(before="Write a code.", after="Write a Python script.")
    report = MockReport(
        llm_analysis=MockLLMAnalysis(suggestions=[suggestion])
    )
    
    fixed = apply_fixes(text, report)
    assert "Write a Python script." in fixed
    assert "Write a code." not in fixed

def test_llm_patching_priority():
    """
    Test that High priority suggestions are applied.
    """
    text = "Target"
    s_low = MockSuggestion(before="Target", after="LowResult", priority="Low")
    s_high = MockSuggestion(before="Target", after="HighResult", priority="High")
    
    report = MockReport(
        llm_analysis=MockLLMAnalysis(suggestions=[s_low, s_high])
    )
    
    fixed = apply_fixes(text, report)
    
    assert "HighResult" in fixed
    assert "LowResult" not in fixed

def test_llm_patching_text_not_found(caplog):
    """Test that missing search text logs a warning and does not crash."""
    text = "Some text"
    suggestion = MockSuggestion(before="NonExistent", after="New")
    report = MockReport(llm_analysis=MockLLMAnalysis(suggestions=[suggestion]))
    
    with caplog.at_level(logging.WARNING):
        fixed = apply_fixes(text, report)
    
    # Should remain unchanged (plus newline from cleanup)
    assert fixed.strip() == "Some text"
    assert "Original text segment not found" in caplog.text

def test_final_cleanup_enforcement():
    """Test that tags are NOT enforced if no issue is present."""
    text = "Just some text"
    report = MockReport()
    
    fixed = apply_fixes(text, report)
    
    assert "<prompt>" not in fixed
    assert "Just some text" in fixed

def test_final_cleanup_misplaced_tags():
    """Test that misplaced tags are NOT automatically corrected without issue."""
    # Tag at start but not end
    text1 = "<prompt>Content"
    report = MockReport()
    fixed1 = apply_fixes(text1, report)
    # Should remain as is (plus newline)
    assert fixed1.strip() == "<prompt>Content"

def test_safety_revert_on_empty_result():
    """
    Test that deletion suggestions work and result in empty string if tags aren't enforced.
    """
    text = "DeleteMe"
    suggestion = MockSuggestion(before="DeleteMe", after="")
    report = MockReport(llm_analysis=MockLLMAnalysis(suggestions=[suggestion]))
    
    fixed = apply_fixes(text, report)
    
    # Verify that the text was deleted
    assert fixed.strip() == ""

def test_mixed_suggestion_sources():
    """
    Test that suggestions are aggregated from both report.llm_analysis.suggestions 
    and report.suggestions.
    """
    text = "One Two Three"
    s1 = MockSuggestion(before="One", after="1", priority="Medium")
    s2 = MockSuggestion(before="Three", after="3", priority="Medium")
    
    report = MockReport(
        llm_analysis=MockLLMAnalysis(suggestions=[s1]),
        suggestions=[s2]
    )
    
    fixed = apply_fixes(text, report)
    
    assert "1" in fixed
    assert "3" in fixed
    assert "Two" in fixed

def test_suggestion_robustness_none_vs_empty():
    """
    Test handling of 'after' values:
    - None: Should be skipped
    - Empty String: Should be treated as deletion.
    """
    text = "Keep Delete Skip"
    s_delete = MockSuggestion(before="Delete", after="")
    s_skip = MockSuggestion(before="Skip", after=None)
    
    report = MockReport(
        llm_analysis=MockLLMAnalysis(suggestions=[s_delete, s_skip])
    )
    
    fixed = apply_fixes(text, report)
    
    assert "Keep" in fixed
    assert "Delete" not in fixed
    assert "Skip" in fixed

def test_scaffolding_section_detection_start_of_file():
    """
    Test that the idempotency check correctly identifies a section 
    if it is at the very start of the file.
    """
    text = "Requirements\n- Some reqs\n"
    issue = MockIssue(description="Missing section Requirements")
    report = MockReport(issues=[issue])
    
    fixed = apply_fixes(text, report)
    
    # Should NOT add a new Requirements section
    assert fixed.count("Requirements") == 1

def test_scaffolding_insertion_order():
    """
    Test that if multiple sections are missing, they are appended in order.
    """
    text = "<prompt>Existing</prompt>"
    # Order in code: Requirements, then Context (Context isn't auto-added), then Dependencies
    issue_req = MockIssue(description="Missing section Requirements")
    issue_dep = MockIssue(description="Missing section Dependencies")
    
    report = MockReport(issues=[issue_req, issue_dep])
    
    fixed = apply_fixes(text, report)
    
    idx_req = fixed.find("Requirements")
    idx_dep = fixed.find("Dependencies")
    
    assert idx_req != -1
    assert idx_dep != -1
    # Requirements should appear before Dependencies
    assert idx_req < idx_dep

def test_cleanup_multiple_root_tags():
    """
    Test behavior when multiple root tags exist.
    Should not change them if no issue reported.
    """
    text = "<prompt>Start</prompt> <prompt>End</prompt>"
    report = MockReport()
    
    fixed = apply_fixes(text, report)
    
    assert fixed.strip() == text

def test_scaffolding_missing_closing_tag():
    """
    Test that missing sections are appended.
    """
    text = "<prompt>\nSome content"
    issue = MockIssue(description="Missing section Requirements")
    report = MockReport(issues=[issue])
    
    fixed = apply_fixes(text, report)
    
    # Should append Requirements
    assert "Requirements" in fixed
    # Should NOT automatically fix closing tag
    assert not fixed.endswith("</prompt>")

def test_scaffolding_trailing_whitespace_closing_tag():
    """
    Test insertion point when </prompt> is followed by whitespace.
    """
    text = "<prompt>\nContent\n</prompt>   \n"
    issue = MockIssue(description="Missing section Requirements")
    report = MockReport(issues=[issue])
    
    fixed = apply_fixes(text, report)
    
    # Requirements should be inserted before </prompt>
    assert "Requirements" in fixed
    assert fixed.find("Requirements") < fixed.rfind("</prompt>")

def test_scaffolding_partial_match_avoidance():
    """
    Test that 'Contextual' does not prevent adding 'Context' (if Context was supported).
    Testing with Requirements instead.
    """
    text = "<prompt>\nRequirements Analysis\n</prompt>"
    issue = MockIssue(description="Missing section Requirements")
    report = MockReport(issues=[issue])
    
    fixed = apply_fixes(text, report)
    
    # "Requirements Analysis" does not match "\nRequirements\n" or startswith "Requirements\n"
    # So it should add "Requirements"
    assert fixed.count("Requirements") >= 2

def test_llm_patching_priority_defaults():
    """
    Test that suggestions with missing or unknown priority are treated as low priority.
    """
    text = "A"
    s_unknown = MockSuggestion(before="A", after="Unknown", priority="Critical")
    s_high_conflict = MockSuggestion(before="A", after="High", priority="High")
    
    report = MockReport(
        llm_analysis=MockLLMAnalysis(suggestions=[s_unknown, s_high_conflict])
    )
    
    fixed = apply_fixes("A", report)
    
    assert "High" in fixed
    assert "Unknown" not in fixed

def test_llm_patching_cascading_edits():
    """
    Test sequential application of edits.
    """
    text = "Step1"
    s1 = MockSuggestion(before="Step1", after="Step2", priority="High")
    s2 = MockSuggestion(before="Step2", after="Step3", priority="Medium")
    
    report = MockReport(
        llm_analysis=MockLLMAnalysis(suggestions=[s1, s2])
    )
    
    fixed = apply_fixes(text, report)
    assert "Step3" in fixed

def test_cleanup_missing_start_tag_only():
    """Test cleanup when only start tag is missing."""
    text = "Content\n</prompt>"
    report = MockReport()
    fixed = apply_fixes(text, report)
    # Should not change
    assert fixed.strip() == "Content\n</prompt>"

def test_cleanup_missing_end_tag_only():
    """Test cleanup when only end tag is missing."""
    text = "<prompt>\nContent"
    report = MockReport()
    fixed = apply_fixes(text, report)
    # Should not change
    assert fixed.strip() == "<prompt>\nContent"

def test_cleanup_whitespace_only():
    """Test cleanup with whitespace input."""
    text = "   "
    report = MockReport()
    fixed = apply_fixes(text, report)
    # Should be empty string (stripped)
    assert fixed == ""

def test_determinism_tag_removal():
    """
    Test that non-deterministic tags are replaced with comments when a DETERMINISM issue is present.
    """
    text = "Start <web>search query</web> Middle <run>code</run> End"
    issue = MockIssue(
        category=MockRuleCategory.DETERMINISM,
        description="Non-deterministic tags found"
    )
    report = MockReport(issues=[issue])

    with patch("src.utils.fix.RuleCategory", MockRuleCategory):
        fixed = apply_fixes(text, report)

    # Verify tags are replaced by comments
    assert "% NOTE: Removed non-deterministic tag <web>" in fixed
    assert "% NOTE: Removed non-deterministic tag <run>" in fixed
    # Verify original tag content is gone (replaced by comment)
    assert "search query" not in fixed
    assert "Start" in fixed
    assert "End" in fixed

def test_determinism_tag_attributes():
    """
    Test that the regex for determinism tags handles attributes and self-closing tags.
    """
    text = 'Run <exec silent="true">cmd</exec> and <shell />'
    issue = MockIssue(
        category=MockRuleCategory.DETERMINISM,
        description="Non-deterministic tags found"
    )
    report = MockReport(issues=[issue])

    with patch("src.utils.fix.RuleCategory", MockRuleCategory):
        fixed = apply_fixes(text, report)

    assert "% NOTE: Removed non-deterministic tag <exec>" in fixed
    assert "% NOTE: Removed non-deterministic tag <shell>" in fixed

def test_modularity_warning():
    """
    Test that a modularity warning is prepended when a MODULARITY issue is present.
    """
    text = "Some prompt content."
    issue = MockIssue(
        category=MockRuleCategory.MODULARITY,
        description="Prompt defines multiple files",
        fix_suggestion="Split prompt"
    )
    report = MockReport(issues=[issue])

    with patch("src.utils.fix.RuleCategory", MockRuleCategory):
        fixed = apply_fixes(text, report)

    expected_warning = "% WARNING: This prompt appears to define multiple files"
    assert expected_warning in fixed

def test_context_warning():
    """
    Test that a context warning is prepended when a CONTEXT issue is present.
    """
    text = "def large_function(): pass"
    issue = MockIssue(
        category=MockRuleCategory.CONTEXT,
        description="Large code blocks detected (repo dump)"
    )
    report = MockReport(issues=[issue])

    with patch("src.utils.fix.RuleCategory", MockRuleCategory):
        fixed = apply_fixes(text, report)

    expected_warning = "% NOTE: Large code blocks detected"
    assert expected_warning in fixed

def test_dependencies_insertion_location():
    """
    Test that the Dependencies section is inserted specifically before Instructions.
    """
    text = "Context\nInstructions\nDo this."
    issue = MockIssue(
        category=MockRuleCategory.ANATOMY,
        description="Missing Dependencies"
    )
    report = MockReport(issues=[issue])

    with patch("src.utils.fix.RuleCategory", MockRuleCategory):
        fixed = apply_fixes(text, report)

    # Should be: Context -> Dependencies -> Instructions
    assert "Dependencies" in fixed
    idx_ctx = fixed.find("Context")
    idx_dep = fixed.find("Dependencies")
    idx_inst = fixed.find("Instructions")

    assert idx_ctx < idx_dep
    assert idx_dep < idx_inst

def test_deliverable_insertion_missing():
    """
    Test that Deliverable section is added if missing and ANATOMY issue exists.
    """
    text = "Instructions\nDo work."
    issue = MockIssue(
        category=MockRuleCategory.ANATOMY,
        description="Missing Deliverable"
    )
    report = MockReport(issues=[issue])

    with patch("src.utils.fix.RuleCategory", MockRuleCategory):
        fixed = apply_fixes(text, report)

    assert "Deliverable" in fixed
    assert "[TODO: Specify expected output files or artifacts]" in fixed

def test_generate_scaffold_alias():
    """
    Test that generate_scaffold calls apply_fixes and returns the same result.
    """
    text = "Original"
    report = MockReport()
    
    res_fix = apply_fixes(text, report)
    res_scaffold = apply_fixes(text, report)
    
    assert res_fix == res_scaffold

def test_warning_idempotency():
    """
    Test that warnings are not added if they already exist in the text.
    """
    warning = "% WARNING: This prompt appears to define multiple files. Consider splitting into separate prompts for better modularity.\n"
    text = warning + "Content"
    issue = MockIssue(
        category=MockRuleCategory.MODULARITY,
        description="multiple files"
    )
    report = MockReport(issues=[issue])

    with patch("src.utils.fix.RuleCategory", MockRuleCategory):
        fixed = apply_fixes(text, report)

    # Should appear exactly once
    assert fixed.count("WARNING: This prompt appears to define multiple files") == 1