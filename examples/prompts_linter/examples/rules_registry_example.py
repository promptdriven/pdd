import sys
import os
from typing import Any, List

# -----------------------------------------------------------------------------
# Path Setup (Boilerplate to ensure imports work for this example)
# -----------------------------------------------------------------------------
# We need to add the project root to sys.path to import src.backend modules.
# Assuming this script is in <project_root>/examples/
current_dir = os.path.dirname(os.path.abspath(__file__))
project_root = os.path.abspath(os.path.join(current_dir, ".."))
if project_root not in sys.path:
    sys.path.insert(0, project_root)

# -----------------------------------------------------------------------------
# Mocking Dependencies
# -----------------------------------------------------------------------------
# The registry module imports 'src.backend.models.findings'.
# Since we might run this example in isolation without the full backend,
# we mock the Finding class here if it doesn't exist, or import it if it does.
try:
    from src.backend.models.findings import Finding
except ImportError:
    # Mock Finding class for demonstration purposes if the real one isn't found
    class Finding:
        def __init__(self, rule_id: str, message: str, line: int = 0):
            self.rule_id = rule_id
            self.message = message
            self.line = line
        
        def __repr__(self):
            return f"Finding(rule='{self.rule_id}', msg='{self.message}')"
    
    # Inject mock into sys.modules so registry.py can import it
    import types
    m = types.ModuleType('src.backend.models.findings')
    m.Finding = Finding
    sys.modules['src.backend.models.findings'] = m
    
    # Also ensure parent packages exist
    sys.modules['src'] = types.ModuleType('src')
    sys.modules['src.backend'] = types.ModuleType('src.backend')
    sys.modules['src.backend.models'] = types.ModuleType('src.backend.models')


# -----------------------------------------------------------------------------
# Actual Usage Example
# -----------------------------------------------------------------------------
from src.backend.rules.registry import LintRule, register, default_registry, ALLOWED_SEVERITIES

if __name__ == "__main__":
    print("=== 1. Defining and Registering Rules ===\n")

    # Example 1: Defining a rule using the @register decorator
    # This is the standard way to add rules to the system.
    @register
    class NoEmptyPromptRule(LintRule):
        rule_id = "PDD001"
        severity = "error"
        title = "Prompt Content Missing"

        def analyze(self, prompt_structure: Any) -> List[Finding]:
            """
            Checks if the prompt content is empty.
            """
            findings = []
            # Assuming prompt_structure is a dict with a 'content' key
            content = prompt_structure.get("content", "")
            
            if not content or not content.strip():
                findings.append(Finding(
                    rule_id=self.rule_id,
                    message="The prompt content cannot be empty."
                ))
            
            return findings

    print(f"Registered rule: {NoEmptyPromptRule.title} ({NoEmptyPromptRule.rule_id})")


    # Example 2: Defining a rule manually (without decorator)
    class TodoInPromptRule(LintRule):
        rule_id = "PDD002"
        severity = "warn"
        title = "TODO Detected"

        def analyze(self, prompt_structure: Any) -> List[Finding]:
            findings = []
            content = prompt_structure.get("content", "")
            
            if "TODO" in content:
                findings.append(Finding(
                    rule_id=self.rule_id,
                    message="Found a TODO comment in the prompt."
                ))
            return findings

    # Manually registering the rule
    default_registry.register_rule(TodoInPromptRule)
    print(f"Registered rule: {TodoInPromptRule.title} ({TodoInPromptRule.rule_id})")


    print("\n=== 2. Validating Rule Metadata ===\n")

    try:
        # Attempting to register a rule with an invalid severity
        @register
        class InvalidSeverityRule(LintRule):
            rule_id = "PDD003"
            severity = "critical"  # 'critical' is not in ALLOWED_SEVERITIES
            title = "Invalid Severity Test"

            def analyze(self, _): return []

    except ValueError as e:
        print(f"Caught expected validation error: {e}")


    try:
        # Attempting to register a duplicate ID
        @register
        class DuplicateIdRule(LintRule):
            rule_id = "PDD001"  # Already taken by NoEmptyPromptRule
            severity = "info"
            title = "Duplicate ID Test"

            def analyze(self, _): return []

    except ValueError as e:
        print(f"Caught expected duplicate error: {e}")


    print("\n=== 3. Running Analysis ===\n")

    # Mock input data representing a parsed prompt
    mock_prompt_good = {"content": "This is a valid prompt."}
    mock_prompt_bad = {"content": ""}  # Triggers PDD001
    mock_prompt_warn = {"content": "Finish this later. TODO: Add more details."} # Triggers PDD002

    # Retrieve all rules from the registry
    all_rules = default_registry.get_all_rules()

    print(f"Analyzing 'Good' Prompt with {len(all_rules)} rules...")
    findings_good = []
    for rule in all_rules:
        findings_good.extend(rule.analyze(mock_prompt_good))
    print(f"Findings: {findings_good}")  # Should be empty

    print(f"\nAnalyzing 'Bad' Prompt (Empty)...")
    findings_bad = []
    for rule in all_rules:
        findings_bad.extend(rule.analyze(mock_prompt_bad))
    for f in findings_bad:
        print(f" - Found: {f}")

    print(f"\nAnalyzing 'Warn' Prompt (TODO)...")
    findings_warn = []
    for rule in all_rules:
        findings_warn.extend(rule.analyze(mock_prompt_warn))
    for f in findings_warn:
        print(f" - Found: {f}")


    print("\n=== 4. Registry Management ===\n")

    # Retrieve a specific rule
    specific_rule = default_registry.get_rule("PDD001")
    if specific_rule:
        print(f"Successfully retrieved specific rule: {specific_rule.title}")

    # Clearing the registry (useful for unit tests)
    default_registry.clear()
    print(f"Registry cleared. Count: {len(default_registry.get_all_rules())}")