import re
import sys
import os
import textwrap
from typing import List, Pattern, Dict

# Internal imports based on the prompt description
from src.utils.models import Issue, Severity, RuleCategory
from src.utils import helpers

# =============================================================================
# Constants & Regex Patterns
# =============================================================================

# Anatomy: Required Section Headers
# Using flexible regex to catch variations (e.g., "Inputs and Outputs", "Deliverables")
# Updated to handle leading whitespace (^\s*)
ANATOMY_PATTERNS = {
    "Requirements": re.compile(r"(?im)^\s*#*\s*Requirements\b"),
    "Input/Output": re.compile(r"(?im)^\s*#*\s*(Inputs?|Outputs?|Inputs?\s+(and|&|/)\s+Outputs?|Deliverables?)\b"),
    "Dependencies": re.compile(r"(?im)^\s*#*\s*Dependencies\b"),
    "Instructions": re.compile(r"(?im)^\s*#*\s*Instructions\b"),
}

# Determinism: Forbidden Tags
NON_DETERMINISTIC_TAGS = ["web", "shell", "exec", "run"]

# Modularity: Indicators of multiple files
# Matches "# file: path/to/file.ext" or "// file: ..."
# Updated to handle leading whitespace
MULTI_FILE_HEADER_PATTERN = re.compile(r"(?im)^\s*(?:#|//|--)\s*file:\s*[\w./-]+")
# Matches section separators often used to split files in one prompt
SECTION_SEPARATOR_PATTERN = re.compile(r"(?m)^\s*[-=*]{3,}\s*$")
# Matches "File 1:", "File 2:" patterns
FILE_ENUMERATION_PATTERN = re.compile(r"(?im)^\s*File\s+\d+:")

# Context: Repo Dump Keywords
DUMP_KEYWORDS = [
    "entire codebase", 
    "full codebase", 
    "all files", 
    "complete source code", 
    "repo dump"
]

# Requirements: Strict Format (Header followed by list item)
# Looks for "Requirements" header, optional whitespace/newlines, then a list marker (1. or -)
# Updated to handle leading whitespace
STRICT_REQ_PATTERN = re.compile(r"(?im)^\s*#*\s*Requirements\s*\n+\s*(?:[-*+]|\d+\.)")

# Attention: Critical Keywords
ATTENTION_KEYWORDS = ["Security", "Auth", "Constraint", "Safety", "Privacy"]

# =============================================================================
# Main Entry Point
# =============================================================================

def analyze_text(text: str) -> List[Issue]:
    """
    Analyzes the prompt text using heuristic rules to identify PDD compliance issues.
    
    Args:
        text (str): The raw prompt content.
        
    Returns:
        List[Issue]: A list of identified issues.
    """
    issues: List[Issue] = []

    # 0. Robustness Check
    if not text or not text.strip():
        return [
            Issue(
                rule_id="GEN001",
                title="Empty Prompt",
                description="The prompt content is empty.",
                severity=Severity.ERROR,
                category=RuleCategory.ANATOMY
            )
        ]

    # Run all checks
    issues.extend(_check_anatomy(text))
    issues.extend(_check_determinism(text))
    issues.extend(_check_modularity(text))
    issues.extend(_check_context(text))
    issues.extend(_check_requirements_format(text))
    issues.extend(_check_attention_hierarchy(text))

    return issues


# =============================================================================
# Rule Implementations
# =============================================================================

def _check_anatomy(text: str) -> List[Issue]:
    """
    Checks for the presence of key structural sections.
    Rule Category: ANATOMY
    """
    issues = []
    
    for section_name, pattern in ANATOMY_PATTERNS.items():
        if not pattern.search(text):
            # Find the index of the key to generate a stable ID (1-based)
            rule_idx = list(ANATOMY_PATTERNS.keys()).index(section_name) + 1
            issues.append(Issue(
                rule_id=f"ANA00{rule_idx}",
                title=f"Missing {section_name} Section",
                description=f"The prompt is missing a '{section_name}' section header.",
                severity=Severity.WARNING,
                category=RuleCategory.ANATOMY
            ))
            
    return issues


def _check_determinism(text: str) -> List[Issue]:
    """
    Checks for non-deterministic tags that imply external access.
    Rule Category: DETERMINISM
    """
    issues = []
    
    for tag in NON_DETERMINISTIC_TAGS:
        # Use helper to count tags to ensure we handle XML parsing logic consistently
        count = helpers.count_tags(text, tag)
        if count > 0:
            issues.append(Issue(
                rule_id="DET001",
                title="Non-Deterministic Tag Detected",
                description=f"Found <{tag}> tag. PDD prompts should be self-contained and deterministic.",
                severity=Severity.WARNING,
                category=RuleCategory.DETERMINISM
            ))
            
    return issues


def _check_modularity(text: str) -> List[Issue]:
    """
    Detects patterns indicating the prompt defines multiple modules/files.
    Rule Category: MODULARITY
    """
    issues = []
    
    # Check 1: Explicit file headers in code blocks
    file_headers = MULTI_FILE_HEADER_PATTERN.findall(text)
    if len(set(file_headers)) > 1:
        issues.append(Issue(
            rule_id="MOD001",
            title="Multiple File Definitions",
            description="Detected multiple file headers (e.g., '# file: ...'). A PDD prompt should define a single module.",
            severity=Severity.WARNING,
            category=RuleCategory.MODULARITY
        ))

    # Check 2: Hard separators (often used to split files)
    # We only flag if there are multiple separators, as one might be a footer.
    separators = SECTION_SEPARATOR_PATTERN.findall(text)
    if len(separators) > 2:
        issues.append(Issue(
            rule_id="MOD002",
            title="Excessive Section Separators",
            description="Detected multiple '---' or '===' separators, suggesting multiple file definitions.",
            severity=Severity.WARNING,
            category=RuleCategory.MODULARITY
        ))

    # Check 3: Enumeration of files
    if len(FILE_ENUMERATION_PATTERN.findall(text)) > 1:
        issues.append(Issue(
            rule_id="MOD003",
            title="Multiple Deliverables Detected",
            description="Detected patterns like 'File 1:', 'File 2:'. Ensure the prompt focuses on one unit of work.",
            severity=Severity.WARNING,
            category=RuleCategory.MODULARITY
        ))

    return issues


def _check_context(text: str) -> List[Issue]:
    """
    Analyzes code-to-text ratio and keywords to detect 'Repo Dumps'.
    Rule Category: CONTEXT
    """
    issues = []
    
    # Check 1: Code Ratio Heuristic
    # We only run this on prompts of sufficient length to avoid false positives on short snippets
    line_count = len(text.splitlines())
    if line_count > 50:
        ratio = helpers.calculate_code_ratio(text)
        # Threshold: 80% code is very high for a prompt that should contain instructions
        if ratio > 0.80:
            issues.append(Issue(
                rule_id="CTX001",
                title="High Code Density (Potential Repo Dump)",
                description=f"Code-to-text ratio is {ratio:.2f}. Large blocks of code should be referenced via <include> tags, not pasted directly.",
                severity=Severity.WARNING,
                category=RuleCategory.CONTEXT
            ))

    # Check 2: Dump Keywords
    lower_text = text.lower()
    for keyword in DUMP_KEYWORDS:
        if keyword in lower_text:
            issues.append(Issue(
                rule_id="CTX002",
                title="Repo Dump Keyword Detected",
                description=f"Found phrase '{keyword}'. Avoid dumping entire codebases into the context window.",
                severity=Severity.WARNING,
                category=RuleCategory.CONTEXT
            ))
            
    return issues


def _check_requirements_format(text: str) -> List[Issue]:
    """
    Validates that the Requirements section exists and follows a list format.
    Rule Category: CONTRACTS (Mapped from Requirements)
    """
    issues = []
    
    # Note: _check_anatomy checks for the header existence. 
    # This checks for the specific *format* (Header + List).
    
    # If the header exists but the strict pattern fails, it means the format is wrong
    has_header = ANATOMY_PATTERNS["Requirements"].search(text)
    has_strict_format = STRICT_REQ_PATTERN.search(text)
    
    if has_header and not has_strict_format:
        issues.append(Issue(
            rule_id="REQ001",
            title="Malformed Requirements Section",
            description="The 'Requirements' section must be immediately followed by a numbered list (1.) or bullet points (-).",
            severity=Severity.ERROR,
            category=RuleCategory.CONTRACTS
        ))
    elif not has_header:
        # If header is missing entirely, Anatomy check handles the warning, 
        # but Contracts category treats missing requirements as a critical Error.
        issues.append(Issue(
            rule_id="REQ002",
            title="Missing Requirements Contract",
            description="A 'Requirements' section is mandatory for PDD contracts.",
            severity=Severity.ERROR,
            category=RuleCategory.CONTRACTS
        ))

    return issues


def _check_attention_hierarchy(text: str) -> List[Issue]:
    """
    Checks if critical keywords appear in the 'Middle Loss' zone (middle 60% of text).
    Rule Category: ATTENTION
    """
    issues = []
    total_len = len(text)
    
    if total_len < 100:
        return issues

    lower_text = text.lower()
    
    # Define the "Middle" zone
    start_zone = total_len * 0.2
    end_zone = total_len * 0.8
    
    for keyword in ATTENTION_KEYWORDS:
        # Find all occurrences
        keyword_lower = keyword.lower()
        start_index = 0
        
        while True:
            idx = lower_text.find(keyword_lower, start_index)
            if idx == -1:
                break
                
            # Check if in the middle zone
            if start_zone < idx < end_zone:
                issues.append(Issue(
                    rule_id="ATT001",
                    title="Critical Keyword in Middle Context",
                    description=f"The keyword '{keyword}' appears in the middle 60% of the prompt. LLMs may pay less attention here. Move critical constraints to the start or end.",
                    severity=Severity.INFO,
                    category=RuleCategory.ATTENTION
                ))
                # Break after finding one instance to avoid spamming the same issue for the same keyword
                break
            
            start_index = idx + 1
            
    return issues

# =============================================================================
# Demonstration / CLI Entry Point
# =============================================================================

def print_issues(title: str, issues: list):
    """Helper to pretty-print a list of issues."""
    print(f"\n{'='*60}")
    print(f"ANALYSIS: {title}")
    print(f"{'='*60}")
    
    if not issues:
        print("✅ No issues found! The prompt looks compliant.")
        return

    print(f"Found {len(issues)} issue(s):\n")
    for i, issue in enumerate(issues, 1):
        # Determine icon based on severity
        icon = "🔴" if issue.severity == Severity.ERROR else \
               "🟠" if issue.severity == Severity.WARNING else "🔵"
        
        print(f"{i}. {icon} [{issue.rule_id}] {issue.title}")
        print(f"   Category: {issue.category.value}")
        print(f"   Details:  {issue.description}")
        print("-" * 40)

def main():
    """
    Demonstrates the usage of rules.analyze_text() on various prompt examples.
    """
    
    # -------------------------------------------------------------------------
    # Example 1: A Compliant PDD Prompt
    # -------------------------------------------------------------------------
    # This prompt follows the PDD structure: Requirements, I/O, Dependencies, Instructions.
    compliant_prompt = textwrap.dedent("""
    # Requirements
    1. Create a function that adds two numbers.
    2. Handle type errors gracefully.

    # Input/Output
    - Input: Two integers
    - Output: Integer sum

    # Dependencies
    - None

    # Instructions
    Please implement the `add` function in Python.
    Ensure you add type hints.
    """)

    issues_1 = analyze_text(compliant_prompt)
    print_issues("Compliant Prompt", issues_1)


    # -------------------------------------------------------------------------
    # Example 2: A Non-Deterministic Prompt
    # -------------------------------------------------------------------------
    # This prompt uses forbidden tags like [Error: firecrawl-py package not installed. Cannot scrape and <run>.
    non_deterministic_prompt = textwrap.dedent("""
    # Requirements
    1. Fetch the latest stock prices.

    # Instructions
    <web>https://finance.yahoo.com]
    
    Please <run>python script.py</run> to verify the data.
    """)

    issues_2 = analyze_text(non_deterministic_prompt)
    print_issues("Non-Deterministic Prompt", issues_2)


    # -------------------------------------------------------------------------
    # Example 3: A "Repo Dump" Prompt
    # -------------------------------------------------------------------------
    # This prompt dumps a massive amount of code directly into the context
    # instead of using <include> tags, and lacks structure.
    
    # Generating fake code lines to trigger the ratio check
    fake_code = "\n".join([f"    def function_{i}(): pass" for i in range(60)])
    
    repo_dump_prompt = f"""
    Here is the entire codebase for you to fix.
    
    {fake_code}
    
    Fix the bugs in the full codebase.
    """

    issues_3 = analyze_text(repo_dump_prompt)
    print_issues("Repo Dump Prompt", issues_3)


    # -------------------------------------------------------------------------
    # Example 4: Broken Anatomy & Modularity Violations
    # -------------------------------------------------------------------------
    # This prompt tries to define multiple files and misses required sections.
    broken_prompt = textwrap.dedent("""
    # file: src/main.py
    print("Hello")
    
    ---
    
    # file: src/utils.py
    def help(): pass
    
    Just write these files for me.
    """)

    issues_4 = analyze_text(broken_prompt)
    print_issues("Broken Anatomy & Modularity", issues_4)

if __name__ == "__main__":
    main()