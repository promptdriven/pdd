import logging
import re
from typing import List, Optional, Union

# Internal imports
from src.utils.models import (
    Report,
    Issue,
    Severity,
    RuleCategory,
    LLMSuggestionDetail,
)

# Backward compatibility for FixSuggestion
try:
    from src.utils.models import FixSuggestion
except ImportError:
    FixSuggestion = LLMSuggestionDetail

# Configure logging
logger = logging.getLogger(__name__)

def apply_fixes(original_text: str, report: Report) -> str:
    """
    The primary remediation engine. Transforms an original prompt into a PDD-compliant
    version based on the provided Report.

    Args:
        original_text (str): The original prompt content.
        report (Report): The analysis report containing issues and suggestions.

    Returns:
        str: The fixed prompt text.
    """
    if not original_text:
        return ""

    # 1. Apply PDD Structural Scaffolding (Heuristic Fixes)
    # We do this first to ensure the structure is sound before applying specific content patches.
    scaffolded_text = _apply_structural_scaffolding(original_text, report)

    # 2. Apply Content Patching (LLM Suggestions)
    # We gather suggestions from the LLM analysis and apply them.
    suggestions = []
    if report.llm_analysis and report.llm_analysis.suggestions:
        suggestions.extend(report.llm_analysis.suggestions)
    
    # Fallback to top-level suggestions if they exist and aren't duplicates
    if hasattr(report, 'suggestions') and report.suggestions:
        # Simple deduplication based on 'before' text
        existing_befores = {s.before for s in suggestions}
        for s in report.suggestions:
            if s.before not in existing_befores:
                suggestions.append(s)

    patched_text = _apply_llm_patches(scaffolded_text, suggestions)

    # 3. Final Cleanup
    final_text = _apply_final_cleanup(patched_text)

    return final_text

def generate_scaffold(original_text: str, report: Report) -> str:
    """
    Alias for apply_fixes to maintain compatibility with pipeline callers.
    """
    return apply_fixes(original_text, report)

def _find_section_start(text: str, section_names: List[str]) -> int:
    """
    Helper to find the start index of the first occurrence of any of the given section names.
    Case-insensitive. Returns -1 if not found.
    """
    if not section_names:
        return -1
    # Pattern matches start of line, optional whitespace, then the section name
    pattern = r'^\s*(' + '|'.join(map(re.escape, section_names)) + r')'
    match = re.search(pattern, text, re.IGNORECASE | re.MULTILINE)
    return match.start() if match else -1

def _section_exists(text: str, section_name: str) -> bool:
    """
    Checks if a section header exists in the text.
    Matches start of line, optional whitespace, optional markdown headers (#), 
    section name, optional colon, optional whitespace, end of line.
    Case-insensitive.
    """
    # Pattern: ^ (start of line) + optional whitespace + optional #s + whitespace + section_name + optional : + whitespace + $
    pattern = r'^\s*(?:#+\s*)?' + re.escape(section_name) + r'\s*:?\s*$'
    return bool(re.search(pattern, text, re.IGNORECASE | re.MULTILINE))

def _insert_content(text: str, content: str, next_sections: List[str]) -> str:
    """
    Helper to insert content before the first found next_section, 
    or before </prompt> if present, or append to end.
    """
    # 1. Try to find a specific next section
    idx = _find_section_start(text, next_sections)
    if idx != -1:
        return text[:idx] + content + text[idx:]
    
    # 2. Try to find closing tag to stay inside the prompt
    end_tag_idx = text.rfind("</prompt>")
    if end_tag_idx != -1:
        return text[:end_tag_idx] + content + text[end_tag_idx:]
        
    # 3. Append to end
    return text.rstrip() + "\n" + content

def _apply_structural_scaffolding(text: str, report: Report) -> str:
    """
    Programmatically repairs PDD compliance violations based on reported issues.
    """
    fixed_text = text

    # We iterate through issues to determine what needs fixing.
    # We use sets to ensure we don't apply the same fix type multiple times.
    fix_actions = set()

    # Flag to track if we have a general anatomy violation that warrants checking all sections
    has_general_anatomy_issue = False

    for issue in report.issues:
        # Determine category safely (handle string or enum)
        cat = getattr(issue, 'category', None)
        
        # 1. Modularity Issues
        if cat == RuleCategory.MODULARITY:
            if "multiple files" in issue.description.lower() or "split" in issue.fix_suggestion.lower():
                fix_actions.add("modularity_warning")

        # 2. Context Issues
        if cat == RuleCategory.CONTEXT:
            if "repo dump" in issue.description.lower() or "large code" in issue.description.lower():
                fix_actions.add("context_warning")

        # 3. Determinism Violations
        if cat == RuleCategory.DETERMINISM:
            fix_actions.add("fix_determinism")

        # 4. Anatomy/Structure Issues
        # Check category OR keywords in description
        # Safely check for STRUCTURE attribute which might not exist in all versions of models
        is_structure = False
        if hasattr(RuleCategory, 'STRUCTURE') and cat == getattr(RuleCategory, 'STRUCTURE'):
            is_structure = True

        is_anatomy = (cat == RuleCategory.ANATOMY) or is_structure
        
        # Only trigger general anatomy scan if it's explicitly an ANATOMY category issue.
        # We avoid triggering on "Missing <prompt>" (STR001) by checking for section keywords or explicit category.
        if is_anatomy:
            has_general_anatomy_issue = True
            
        # Check for specific missing sections in description regardless of category
        desc_lower = issue.description.lower()
        if "requirements" in desc_lower and "missing" in desc_lower:
            fix_actions.add("add_requirements")
        if "dependencies" in desc_lower and "missing" in desc_lower:
            fix_actions.add("add_dependencies")
        if "instructions" in desc_lower and "missing" in desc_lower:
            fix_actions.add("add_instructions")
        if ("deliverable" in desc_lower or "input/output" in desc_lower) and "missing" in desc_lower:
            fix_actions.add("add_deliverable")
        
        # 5. Root Tag Issues (Specific override for program compatibility)
        # Although the prompt says not to enforce tags, the program explicitly requests it via STR001.
        if issue.rule_id == "STR001" or "missing <prompt>" in issue.description.lower():
            fix_actions.add("wrap_prompt_tags")

    # --- Apply Fixes based on identified actions --- #

    # If we have a general anatomy issue, we proactively check for missing sections
    # and add the action if the section is missing from the text.
    if has_general_anatomy_issue:
        if not _section_exists(fixed_text, "Requirements"):
            fix_actions.add("add_requirements")
        if not _section_exists(fixed_text, "Dependencies"):
            fix_actions.add("add_dependencies")
        if not _section_exists(fixed_text, "Instructions"):
            fix_actions.add("add_instructions")
        if not _section_exists(fixed_text, "Deliverable") and not _section_exists(fixed_text, "Input/Output"):
            fix_actions.add("add_deliverable")

    # Modularity Warning
    if "modularity_warning" in fix_actions:
        warning = "% WARNING: This prompt appears to define multiple files. Consider splitting into separate prompts for better modularity.\n"
        if warning not in fixed_text:
            fixed_text = warning + fixed_text

    # Context Warning
    if "context_warning" in fix_actions:
        warning = "% NOTE: Large code blocks detected. Consider using <include> tags or external context files instead.\n"
        if warning not in fixed_text:
            fixed_text = warning + fixed_text

    # Fix Determinism
    if "fix_determinism" in fix_actions:
        # Regex to find tags like <web>, <shell>, <exec>, <run>
        # We replace them with a comment.
        pattern = r'<(web|shell|exec|run)(?:\s+[^>]*)?>.*?</\1>|<(web|shell|exec|run)(?:\s+[^>]*)?\/?>'
        
        def replacement(match):
            tag_name = match.group(1) or match.group(2)
            return f"% NOTE: Removed non-deterministic tag <{tag_name}> for PDD compliance"
        
        fixed_text = re.sub(pattern, replacement, fixed_text, flags=re.DOTALL | re.IGNORECASE)

    # --- Anatomy Injection ---
    # We check existence case-insensitively before adding to ensure idempotency
    
    # Add Requirements
    if "add_requirements" in fix_actions and not _section_exists(fixed_text, "Requirements"):
        placeholder = (
            "\nRequirements\n"
            "1. [TODO: Define specific requirements]\n"
            "2. [TODO: Add acceptance criteria]\n"
        )
        next_sections = ["Dependencies", "Instructions", "Deliverable", "Input/Output"]
        fixed_text = _insert_content(fixed_text, placeholder, next_sections)

    # Add Dependencies
    if "add_dependencies" in fix_actions and not _section_exists(fixed_text, "Dependencies"):
        placeholder = (
            "\nDependencies\n"
            "% List any modules, libraries, or other prompts this depends on\n"
            "- [TODO: Specify dependencies]\n"
        )
        next_sections = ["Instructions", "Deliverable", "Input/Output"]
        fixed_text = _insert_content(fixed_text, placeholder, next_sections)

    # Add Instructions
    if "add_instructions" in fix_actions and not _section_exists(fixed_text, "Instructions"):
        placeholder = (
            "\nInstructions\n"
            "- [TODO: Break down implementation into atomic steps]\n"
            "- [TODO: Specify order of operations]\n"
        )
        next_sections = ["Deliverable", "Input/Output"]
        fixed_text = _insert_content(fixed_text, placeholder, next_sections)

    # Add Deliverable
    if "add_deliverable" in fix_actions and not _section_exists(fixed_text, "Deliverable") and not _section_exists(fixed_text, "Input/Output"):
        placeholder = (
            "\nDeliverable\n"
            "- [TODO: Specify expected output files or artifacts]\n"
        )
        # Append to end (or before closing tag)
        fixed_text = _insert_content(fixed_text, placeholder, [])

    # Wrap in <prompt> tags if explicitly requested by issue STR001
    if "wrap_prompt_tags" in fix_actions:
        stripped = fixed_text.strip()
        if not (stripped.startswith("<prompt>") and stripped.endswith("</prompt>")):
            fixed_text = "<prompt>\n" + fixed_text + "\n</prompt>"

    return fixed_text

def _apply_llm_patches(text: str, suggestions: List[Union[LLMSuggestionDetail, FixSuggestion]]) -> str:
    """
    Applies text replacements suggested by the LLM.
    """
    if not suggestions:
        return text

    # Sort suggestions by priority
    # High -> Medium -> Low
    priority_map = {
        "High": 3,
        "Medium": 2,
        "Low": 1,
        "high": 3,
        "medium": 2,
        "low": 1
    }

    def get_priority(s):
        p = getattr(s, 'priority', 'Low')
        return priority_map.get(p, 1)

    sorted_suggestions = sorted(suggestions, key=get_priority, reverse=True)
    
    fixed_text = text

    for suggestion in sorted_suggestions:
        before = suggestion.before
        after = suggestion.after

        # Validation
        if not before:
            continue
        if after is None:
            continue

        if before in fixed_text:
            # Apply replacement
            fixed_text = fixed_text.replace(before, after)
            logger.info(f"Applied fix: {suggestion.title} (Rule: {suggestion.rule_id})")
        else:
            # Log warning but don't crash
            # It's possible scaffolding changed the text, or the LLM hallucinated the 'before' text
            logger.warning(f"Could not apply fix '{suggestion.title}': Original text segment not found.")

    return fixed_text

def _apply_final_cleanup(text: str) -> str:
    """
    Performs final whitespace normalization and cleanup.
    """
    # 1. Trim excessive blank lines (more than 2 consecutive)
    cleaned_text = re.sub(r'\n{3,}', '\n\n', text)
    
    # 2. Strip leading/trailing whitespace
    cleaned_text = cleaned_text.strip()
    
    # 3. Ensure file ends with a newline
    if cleaned_text and not cleaned_text.endswith('\n'):
        cleaned_text += '\n'

    return cleaned_text