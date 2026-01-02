"""
src/backend/rules/pdd_rules.py

This module contains the concrete implementations of the linting rules defined in the
Prompt-Driven Development (PDD) specification. It analyzes the parsed prompt structure
and emits Finding objects when violations are detected.
"""

import re
from typing import List, Optional

# Assuming these imports based on the provided context and standard project structure
from ..models.findings import Finding, Severity, SuggestedEdit, Evidence
from ..rules.registry import default_registry as registry
from ..core.parser import ParsedDocument, Section, Tag

# Initialize the registry instance that will be imported by the engine

# --- Helper Functions ---

def _create_finding(
    rule_id: str,
    severity: Severity,
    title: str,
    message: str,
    line_number: int,
    suggestion: Optional[str] = None
) -> Finding:
    """Helper to construct a Finding object with a suggested edit."""
    edits = []
    if suggestion:
        edits.append(SuggestedEdit(
            kind="replace",
            snippet=suggestion
        ))
    
    evidence = Evidence(line_start=line_number, line_end=line_number)
    
    return Finding(
        rule_id=rule_id,
        severity=severity,
        title=title,
        message=message,
        evidence=evidence,
        suggested_edits=edits
    )

def _find_section(doc: ParsedDocument, keywords: List[str]) -> Optional[Section]:
    """Case-insensitive search for a section header containing any of the keywords."""
    for section in doc.sections:
        header_lower = section.header.lower()
        if any(k.lower() in header_lower for k in keywords):
            return section
    return None

# --- Rule Implementations ---

# -----------------------------------------------------------------------------
# PDD001: Structure - Role & Scope
# -----------------------------------------------------------------------------
@registry.register_rule
def check_pdd001_role_scope(doc: ParsedDocument) -> List[Finding]:
    """
    Detect missing Role & Scope.
    Checks the first non-comment block or looks for explicit headers.
    """
    findings = []
    
    # Heuristic: Look for "Role" or "Scope" in section headers
    role_section = _find_section(doc, ["Role", "Scope", "Context"])
    
    # Heuristic: If no explicit section, check the preamble (text before first header)
    has_preamble_keywords = False
    if doc.preamble:
        content_lower = doc.preamble.content.lower()
        if "act as a" in content_lower or "you are a" in content_lower or "role:" in content_lower:
            has_preamble_keywords = True

    if not role_section and not has_preamble_keywords:
        findings.append(_create_finding(
            rule_id="PDD001",
            severity=Severity.WARN,
            title="Missing Role & Scope",
            message="The prompt lacks a clear definition of the AI's role or the scope of the task. "
                    "Start with 'Act as a...' or define a '## Role' section.",
            line_number=1,
            suggestion="## Role\nAct as a Senior Python Developer.\n\n## Scope\nImplement the user authentication module."
        ))
        
    return findings

# -----------------------------------------------------------------------------
# PDD002: Structure - Multiple Targets
# -----------------------------------------------------------------------------
@registry.register_rule
def check_pdd002_multiple_targets(doc: ParsedDocument) -> List[Finding]:
    """
    Detect multiple unrelated target files.
    Heuristic: Counts distinct file paths mentioned in XML tags or headers that look like targets.
    """
    findings = []
    # This is a heuristic. We look for file-like patterns in headers or specific target tags if they existed.
    # For this implementation, we'll scan for multiple distinct file extensions in headers.
    
    file_pattern = re.compile(r'\b[\w\-/]+\.(py|js|ts|html|css|java|go|rs)\b')
    found_files = set()
    
    for section in doc.sections:
        matches = file_pattern.findall(section.header)
        for m in matches:
            # We actually want the full match, findall with groups returns the group.
            # Let's iterate matches on the string directly.
            for match in file_pattern.finditer(section.header):
                found_files.add(match.group(0))

    if len(found_files) > 1:
        findings.append(_create_finding(
            rule_id="PDD002",
            severity=Severity.WARN,
            title="Multiple Target Files Detected",
            message=f"PDD encourages 'One prompt = one module'. Detected potential targets: {', '.join(found_files)}.",
            line_number=1, # Global warning
            suggestion=None
        ))
    return findings

# -----------------------------------------------------------------------------
# PDD010: Requirements - Missing Section
# -----------------------------------------------------------------------------
@registry.register_rule
def check_pdd010_missing_requirements(doc: ParsedDocument) -> List[Finding]:
    """Detect missing Requirements section (Error)."""
    findings = []
    req_section = _find_section(doc, ["Requirement", "Spec", "Acceptance Criteria"])
    
    if not req_section:
        findings.append(_create_finding(
            rule_id="PDD010",
            severity=Severity.ERROR,
            title="Missing Requirements Section",
            message="No section header found containing 'Requirements', 'Specs', or 'Acceptance Criteria'.",
            line_number=len(doc.raw_text.splitlines()), # Point to end of file
            suggestion="\n## Requirements\n1. [ ] The system must..."
        ))
    return findings

# -----------------------------------------------------------------------------
# PDD011: Requirements - Count Outliers
# -----------------------------------------------------------------------------
@registry.register_rule
def check_pdd011_requirement_count(doc: ParsedDocument) -> List[Finding]:
    """Detect requirement count outliers (<5 or >10)."""
    findings = []
    req_section = _find_section(doc, ["Requirement", "Spec"])
    
    if req_section:
        # Count lines starting with numbers, bullets, or checkboxes
        lines = req_section.content.strip().split('\n')
        req_count = 0
        for line in lines:
            stripped = line.strip()
            if re.match(r'^(\d+\.|- |\* |\[\s?x?\s?\])', stripped):
                req_count += 1
        
        # Prompt spec: <5 or >10
        if req_count > 0 and (req_count < 5 or req_count > 10):
            findings.append(_create_finding(
                rule_id="PDD011",
                severity=Severity.WARN,
                title="Requirement Count Outlier",
                message=f"Found {req_count} requirements. PDD suggests keeping requirements between 5 and 10 for optimal focus.",
                line_number=req_section.start_line,
                suggestion=None
            ))
    return findings

# -----------------------------------------------------------------------------
# PDD012: Requirements - Implementation Steps
# -----------------------------------------------------------------------------
@registry.register_rule
def check_pdd012_implementation_steps(doc: ParsedDocument) -> List[Finding]:
    """Detect implementation steps disguised as requirements."""
    findings = []
    req_section = _find_section(doc, ["Requirement", "Spec"])
    
    if req_section:
        lines = req_section.content.strip().split('\n')
        for i, line in enumerate(lines):
            lower_line = line.lower()
            # Keywords indicating imperative implementation steps rather than behavioral requirements
            if any(x in lower_line for x in ["first, ", "then, ", "create a file named", "import the library"]):
                findings.append(_create_finding(
                    rule_id="PDD012",
                    severity=Severity.WARN,
                    title="Implementation Step in Requirements",
                    message="Requirements should describe *what*, not *how*. Avoid imperative steps like 'First, do X'.",
                    line_number=req_section.start_line + i + 1, # Approx line
                    suggestion=line.replace("First, create", "The system must have")
                ))
    return findings

# -----------------------------------------------------------------------------
# PDD013: Requirements - Negative Constraints
# -----------------------------------------------------------------------------
@registry.register_rule
def check_pdd013_negative_constraints(doc: ParsedDocument) -> List[Finding]:
    """Detect excess negative constraints."""
    findings = []
    req_section = _find_section(doc, ["Requirement", "Spec"])
    
    if req_section:
        negatives = ["not", "never", "don't", "cannot", "shouldn't"]
        count = 0
        content_lower = req_section.content.lower()
        for word in negatives:
            count += content_lower.count(f" {word} ")
            
        if count > 3:
            findings.append(_create_finding(
                rule_id="PDD013",
                severity=Severity.INFO,
                title="Excess Negative Constraints",
                message=f"Found {count} negative constraints. LLMs struggle with negation. Try rephrasing positively.",
                line_number=req_section.start_line,
                suggestion=None
            ))
    return findings

# -----------------------------------------------------------------------------
# PDD020: IO - Missing Section
# -----------------------------------------------------------------------------
@registry.register_rule
def check_pdd020_missing_io(doc: ParsedDocument) -> List[Finding]:
    """Detect missing Inputs/Outputs section."""
    findings = []
    # Look for sections like "Interface", "Input", "Output", "API"
    io_section = _find_section(doc, ["Input", "Output", "Interface", "API", "Signature"])
    
    if not io_section:
        findings.append(_create_finding(
            rule_id="PDD020",
            severity=Severity.WARN,
            title="Missing Inputs/Outputs",
            message="No section defining the Interface, Inputs, or Outputs found. Explicitly define data structures.",
            line_number=len(doc.raw_text.splitlines()),
            suggestion="\n## Interface\nInput: `UserDict`\nOutput: `bool`"
        ))
    return findings

# -----------------------------------------------------------------------------
# PDD021: IO - Error Handling
# -----------------------------------------------------------------------------
@registry.register_rule
def check_pdd021_error_handling(doc: ParsedDocument) -> List[Finding]:
    """Detect missing error-handling contract."""
    findings = []
    # Scan whole doc for error keywords
    error_keywords = ["error", "exception", "raise", "try", "catch", "fail"]
    has_error_mention = any(k in doc.raw_text.lower() for k in error_keywords)
    
    if not has_error_mention:
        findings.append(_create_finding(
            rule_id="PDD021",
            severity=Severity.INFO,
            title="Missing Error Handling Contract",
            message="No mention of errors or exceptions found. Define how the code should handle failure states.",
            line_number=1,
            suggestion="## Requirements\n... \n- [ ] Raise `ValueError` if input is empty."
        ))
    return findings

# -----------------------------------------------------------------------------
# PDD030: Context - Unreferenced Dependencies
# -----------------------------------------------------------------------------
@registry.register_rule
def check_pdd030_unreferenced_deps(doc: ParsedDocument) -> List[Finding]:
    """Detect dependencies referenced in text without XML includes."""
    findings = []
    # Heuristic: Look for "see file X" or "in X.py" where X is not in <include> tags
    # 1. Gather included files
    included_files = set()
    for tag in doc.tags:
        if tag.name == "include" or tag.name == "context":
            # Assuming tag.attributes or content holds the filename
            included_files.add(tag.content.strip())

    # 2. Scan text for file references
    file_ref_regex = re.compile(r'\b([a-zA-Z0-9_\-/]+\.(py|js|ts|json|md))\b')
    
    for section in doc.sections:
        for match in file_ref_regex.finditer(section.content):
            filename = match.group(1)
            # Ignore common config files or the prompt itself if named
            if filename not in included_files and filename != "package.json" and filename != "requirements.txt":
                findings.append(_create_finding(
                    rule_id="PDD030",
                    severity=Severity.WARN,
                    title="Unreferenced Dependency",
                    message=f"File '{filename}' is referenced in text but not included via <include> tags.",
                    line_number=section.start_line, # Approximate
                    suggestion=f"<include>{filename}</include>"
                ))
                
    return findings

# -----------------------------------------------------------------------------
# PDD031: Context - Context Dumps
# -----------------------------------------------------------------------------
@registry.register_rule
def check_pdd031_context_dumps(doc: ParsedDocument) -> List[Finding]:
    """Detect context dumps (large includes)."""
    findings = []
    for tag in doc.tags:
        if tag.name in ["include", "context"]:
            # If the content inside the tag is huge
            if len(tag.content.splitlines()) > 300:
                findings.append(_create_finding(
                    rule_id="PDD031",
                    severity=Severity.WARN,
                    title="Large Context Dump",
                    message=f"Context block (lines {tag.start_line}-{tag.end_line}) is very large (>300 lines). "
                            "Summarize or reference specific interfaces instead.",
                    line_number=tag.start_line,
                    suggestion=None
                ))
    return findings

# -----------------------------------------------------------------------------
# PDD032: Context - Missing Shared Preamble
# -----------------------------------------------------------------------------
@registry.register_rule
def check_pdd032_missing_preamble(doc: ParsedDocument) -> List[Finding]:
    """Detect missing shared preamble (heuristic)."""
    findings = []
    # Heuristic: Check if there is a <meta> or <rules> tag, or an include named "preamble"
    has_preamble = False
    
    # Check tags
    for tag in doc.tags:
        if tag.name in ["meta", "rules", "preamble"]:
            has_preamble = True
        if "preamble" in tag.content.lower():
            has_preamble = True
            
    if not has_preamble:
        findings.append(_create_finding(
            rule_id="PDD032",
            severity=Severity.INFO,
            title="Missing Shared Preamble",
            message="Consider using a shared preamble (e.g., <include>_preamble.md</include>) for project-wide rules.",
            line_number=1,
            suggestion="<include>context/_preamble.md</include>"
        ))
    return findings

# -----------------------------------------------------------------------------
# PDD040: Determinism - Shell/Web Tags
# -----------------------------------------------------------------------------
@registry.register_rule
def check_pdd040_determinism(doc: ParsedDocument) -> List[Finding]:
    """Detect <shell> or <web> tags."""
    findings = []
    for tag in doc.tags:
        if tag.name in ["shell", "bash", "sh", "cmd"]:
            findings.append(_create_finding(
                rule_id="PDD040",
                severity=Severity.WARN,
                title="Non-Deterministic Shell Command",
                message=f"Avoid `<{tag.name}>` tags. Shell output can change. Provide static file contents instead.",
                line_number=tag.start_line,
                suggestion=None
            ))
        if tag.name in ["web", "fetch", "url"]:
            findings.append(_create_finding(
                rule_id="PDD040",
                severity=Severity.WARN,
                title="Non-Deterministic Web Access",
                message=f"Avoid `<{tag.name}>` tags. Web content changes. Paste the specific content needed.",
                line_number=tag.start_line,
                suggestion=None
            ))
    return findings

# -----------------------------------------------------------------------------
# PDD050: Size - Vague Prompts
# -----------------------------------------------------------------------------
@registry.register_rule
def check_pdd050_vague_prompt(doc: ParsedDocument) -> List[Finding]:
    """Detect vague prompts (small + missing IO)."""
    findings = []
    line_count = len(doc.raw_text.splitlines())
    io_section = _find_section(doc, ["Input", "Output", "Interface"])
    
    if line_count < 10 and not io_section:
        findings.append(_create_finding(
            rule_id="PDD050",
            severity=Severity.WARN,
            title="Prompt Too Vague",
            message="Prompt is very short (<10 lines) and lacks an I/O definition. Add specific requirements.",
            line_number=1,
            suggestion=None
        ))
    return findings

# -----------------------------------------------------------------------------
# PDD051: Size - Over-detailed Prompts
# -----------------------------------------------------------------------------
@registry.register_rule
def check_pdd051_over_detailed(doc: ParsedDocument) -> List[Finding]:
    """Detect over-detailed prompts."""
    findings = []
    # Heuristic: Word count > 2000 (approx 3-4 pages of text)
    word_count = len(doc.raw_text.split())
    
    if word_count > 2000:
        findings.append(_create_finding(
            rule_id="PDD051",
            severity=Severity.WARN,
            title="Prompt Too Large",
            message=f"Prompt is approx {word_count} words. Large prompts confuse models. Split into smaller tasks.",
            line_number=1,
            suggestion=None
        ))
    return findings

# -----------------------------------------------------------------------------
# PDD060: Attention - Buried Constraints
# -----------------------------------------------------------------------------
@registry.register_rule
def check_pdd060_buried_constraints(doc: ParsedDocument) -> List[Finding]:
    """Detect critical constraints buried mid-prompt."""
    findings = []
    # Heuristic: Look for "IMPORTANT", "CRITICAL", "NOTE:" in the middle 50% of the document
    lines = doc.raw_text.splitlines()
    total_lines = len(lines)
    
    if total_lines > 20:
        start_zone = int(total_lines * 0.25)
        end_zone = int(total_lines * 0.75)
        
        for i in range(start_zone, end_zone):
            line = lines[i]
            if any(k in line for k in ["IMPORTANT:", "CRITICAL:", "MUST NOT"]):
                findings.append(_create_finding(
                    rule_id="PDD060",
                    severity=Severity.INFO,

                    title="Buried Critical Constraint",
                    message="Critical constraints found in the middle of the prompt. Move to the top (Role) or bottom (Requirements).",
                    line_number=i + 1,
                    suggestion=None
                ))
    return findings
