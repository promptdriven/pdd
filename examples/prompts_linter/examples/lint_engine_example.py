import sys
import os
import logging
from unittest.mock import MagicMock

# --- Setup Path for Imports ---
# Add the project root to sys.path to allow importing from src.backend
# This assumes the script is run from the 'examples' directory or similar relative structure.
current_dir = os.path.dirname(os.path.abspath(__file__))
project_root = os.path.abspath(os.path.join(current_dir, "../../"))
if project_root not in sys.path:
    sys.path.insert(0, project_root)

# --- Mocking Dependencies for the Example ---
# Since the actual dependencies (parser, rules_registry, etc.) might not exist 
# in this standalone example context, we mock them to make the script runnable.
# In a real environment, these would be actual imports.

# Mock the internal dependencies used by LintEngine
# We create a dummy module structure to satisfy the import
class MockModule:
    pass

engine_module = MockModule()
sys.modules["src.backend.core.lint_engine"] = engine_module

# Mock Finding and Severity
class MockSeverity:
    CRITICAL = "CRITICAL"
    ERROR = "ERROR"
    WARNING = "WARNING"
    INFO = "INFO"

class MockFinding:
    def __init__(self, rule_id, message, severity, location=None):
        self.rule_id = rule_id
        self.message = message
        self.severity = severity
        self.location = location

class MockLintReport:
    def __init__(self, file_path, findings, score, summary, stats=None):
        self.file_path = file_path
        self.findings = findings
        self.score = score
        self.summary = summary
        self.stats = stats

    def __str__(self):
        return (f"Report for {self.file_path}\n"
                f"Score: {self.score}\n"
                f"Summary: {self.summary}\n"
                f"Findings: {len(self.findings)}")

# Inject mocks into the module namespace so LintEngine can use them
engine_module.Severity = MockSeverity
engine_module.Finding = MockFinding
engine_module.LintReport = MockLintReport
engine_module.FindingLocation = MagicMock()

# Mock the Parser
mock_parser = MagicMock()
mock_parsed_prompt = MagicMock()
mock_parsed_prompt.syntax_errors = []
mock_parser.parse.return_value = mock_parsed_prompt
engine_module.PromptParser = MagicMock(return_value=mock_parser)

# Mock the Registry
mock_rule = MagicMock()
mock_rule.id = "example_rule"
mock_rule.check.return_value = [
    MockFinding("example_rule", "This is a test warning", MockSeverity.WARNING)
]
mock_registry = MagicMock()
mock_registry.get_all_rules.return_value = [mock_rule]
engine_module.Registry = MagicMock(return_value=mock_registry)

# Mock the Resolver
mock_resolver = MagicMock()
mock_res_result = MagicMock()
mock_res_result.findings = []
mock_res_result.total_tokens = 150
mock_res_result.resolved_files = ["header.prompt"]
mock_resolver.resolve.return_value = mock_res_result
engine_module.IncludeResolver = MagicMock(return_value=mock_resolver)

# Define the LintEngine class if it's not actually importable, 
# or import it if the environment is set up.
try:
    from src.backend.core.lint_engine import LintEngine
except ImportError:
    # Fallback definition for demonstration if the file doesn't exist
    class LintEngine:
        def lint(self, content, file_path, options=None):
            options = options or {}
            disabled = options.get("disabled_rules", [])
            findings = []
            if "example_rule" not in disabled:
                findings = mock_rule.check()
            
            score = 100 if not findings else 80
            stats = {"includes": 1 if options.get("resolve_includes") else 0}
            return MockLintReport(file_path, findings, score, "Summary", stats)

def main():
    """Main execution function for the LintEngine example."""
    # Configure logging to see engine output
    logging.basicConfig(level=logging.INFO)
    
    print("--- Initializing Lint Engine ---")
    engine = LintEngine()

    # Define a sample prompt content
    sample_prompt = """
    <system>
    You are a helpful assistant.
    </system>
    <include>header.prompt</include>
    <user>
    Explain quantum physics.
    </user>
    """

    print("\n--- Scenario 1: Basic Linting (No Include Resolution) ---")
    # By default, resolve_includes is False
    report = engine.lint(
        content=sample_prompt,
        file_path="my_prompt.pdd",
        options={"resolve_includes": False}
    )
    
    print(report)
    print(f"Stats: {report.stats}")

    print("\n--- Scenario 2: Linting with Include Resolution ---")
    # Enable include resolution to check external file references
    report_with_includes = engine.lint(
        content=sample_prompt,
        file_path="my_prompt.pdd",
        options={"resolve_includes": True}
    )

    print(report_with_includes)
    print(f"Stats: {report_with_includes.stats}")
    # Note: In the mock above, we simulated finding 1 include file.

    print("\n--- Scenario 3: Handling Disabled Rules ---")
    # Disable the specific rule we mocked earlier
    report_disabled = engine.lint(
        content=sample_prompt,
        file_path="my_prompt.pdd",
        options={
            "resolve_includes": False,
            "disabled_rules": ["example_rule"]
        }
    )
    
    print(f"Findings count (should be 0): {len(report_disabled.findings)}")
    print(f"Score (should be 100): {report_disabled.score}")

if __name__ == "__main__":
    main()