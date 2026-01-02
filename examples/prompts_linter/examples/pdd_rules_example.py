import sys
import os
import types
import importlib.util
from dataclasses import dataclass
from typing import List, Optional

# ==========================================
# 1. Mock Dependencies
# ==========================================
# The pdd_rules module relies on project-specific dependencies (models, parser).
# To make this example runnable standalone without the full project tree,
# we mock these dependencies before importing the module.

@dataclass
class SuggestedEdit:
    description: str
    new_text: str
    line_number: int

@dataclass
class Finding:
    rule_id: str
    severity: str
    title: str
    message: str
    line_number: int
    suggested_edit: Optional[SuggestedEdit] = None

class Severity:
    WARN = "WARN"
    ERROR = "ERROR"
    INFO = "INFO"

@dataclass
class Tag:
    name: str
    content: str
    start_line: int
    end_line: int

@dataclass
class Section:
    header: str
    content: str
    start_line: int

@dataclass
class ParsedDocument:
    raw_text: str
    sections: List[Section]
    tags: List[Tag]
    preamble: Optional[Section] = None

class RuleRegistry:
    def __init__(self):
        self.rules = []
    def register(self, func):
        self.rules.append(func)
        return func

# Create a mock package structure in sys.modules so relative imports work
# (e.g., "from ..models.findings import Finding")
src = types.ModuleType("src")
src.backend = types.ModuleType("src.backend")
src.backend.models = types.ModuleType("src.backend.models")
src.backend.models.findings = types.ModuleType("src.backend.models.findings")
src.backend.rules = types.ModuleType("src.backend.rules")
src.backend.rules.registry = types.ModuleType("src.backend.rules.registry")
src.backend.parser = types.ModuleType("src.backend.parser")

# Assign mocks to the modules
src.backend.models.findings.Finding = Finding
src.backend.models.findings.Severity = Severity
src.backend.models.findings.SuggestedEdit = SuggestedEdit
src.backend.rules.registry.RuleRegistry = RuleRegistry
src.backend.parser.ParsedDocument = ParsedDocument
src.backend.parser.Section = Section
src.backend.parser.Tag = Tag

# Register modules in sys.modules
sys.modules["src"] = src
sys.modules["src.backend"] = src.backend
sys.modules["src.backend.models"] = src.backend.models
sys.modules["src.backend.models.findings"] = src.backend.models.findings
sys.modules["src.backend.rules"] = src.backend.rules
sys.modules["src.backend.rules.registry"] = src.backend.rules.registry
sys.modules["src.backend.parser"] = src.backend.parser

# ==========================================
# 2. Import the Target Module
# ==========================================

# Construct the path to the module relative to this script
# Script location: examples/pdd_rules_example.py
# Module location: src/backend/rules/pdd_rules.py
current_dir = os.path.dirname(os.path.abspath(__file__))
module_path = os.path.abspath(os.path.join(current_dir, "../src/backend/rules/pdd_rules.py"))

if not os.path.exists(module_path):
    print(f"Error: Could not find module at {module_path}")
    sys.exit(1)

# Load the module dynamically
spec = importlib.util.spec_from_file_location("src.backend.rules.pdd_rules", module_path)
pdd_rules = importlib.util.module_from_spec(spec)
sys.modules["src.backend.rules.pdd_rules"] = pdd_rules
spec.loader.exec_module(pdd_rules)

# ==========================================
# 3. Usage Demonstration
# ==========================================

def main():
    """
    Demonstrates how to use the pdd_rules module to analyze a parsed document.
    """
    print(f"Loaded pdd_rules from: {module_path}")

    # 1. Create a sample ParsedDocument that violates several PDD rules.
    #    - PDD001: Missing Role/Scope
    #    - PDD040: Use of <shell> tags
    #    - PDD050: Prompt too vague (short + no IO)
    
    sample_raw_text = """
    Just do the thing.
    <shell>rm -rf /</shell>
    """
    
    doc = ParsedDocument(
        raw_text=sample_raw_text,
        sections=[
            Section(header="Misc", content="Just do the thing.", start_line=1)
        ],
        tags=[
            Tag(name="shell", content="rm -rf /", start_line=3, end_line=3)
        ],
        preamble=None
    )

    print("\nAnalyzing document for PDD violations...")
    
    # 2. Access the registry where rules are stored.
    #    The module instantiates 'registry = RuleRegistry()' at the top level.
    registry = pdd_rules.registry
    
    all_findings = []
    
    # 3. Iterate through registered rules and execute them.
    #    Each rule function accepts a ParsedDocument and returns List[Finding].
    for rule_func in registry.rules:
        try:
            findings = rule_func(doc)
            if findings:
                all_findings.extend(findings)
        except Exception as e:
            print(f"Error running rule {rule_func.__name__}: {e}")

    # 4. Display the results.
    print(f"\nFound {len(all_findings)} findings:\n")
    
    for i, finding in enumerate(all_findings, 1):
        print(f"{i}. [{finding.severity}] {finding.rule_id}: {finding.title}")
        print(f"   Line: {finding.line_number}")
        print(f"   Message: {finding.message}")
        if finding.suggested_edit:
            print(f"   Suggestion: {finding.suggested_edit.new_text}")
        print("")
