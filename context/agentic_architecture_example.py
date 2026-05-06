"""Example showing how to use run_agentic_architecture for GitHub issue-based architecture generation."""

import sys
from pathlib import Path
from unittest.mock import patch, MagicMock

# Add the project root to sys.path
project_root = Path(__file__).resolve().parent.parent
sys.path.append(str(project_root))

from pdd.agentic_architecture import run_agentic_architecture


def main():
    """Demonstrate the agentic architecture workflow with a mocked GitHub issue."""

    issue_url = "https://github.com/example/repo/issues/42"

    print(f"Running agentic architecture workflow for: {issue_url}")
    print("-" * 60)

    with patch("pdd.agentic_architecture.run_agentic_architecture_orchestrator") as mock_orchestrator:
        mock_orchestrator.return_value = (
            True,
            "Architecture generated. Created architecture.json with 6 modules.",
            2.50,
            "anthropic",
            ["architecture.json", "architecture_diagram.html"],
        )

        # Default discovery: walks up from cwd through Tier A (.pddrc/.pdd/),
        # Tier B (sources/ + PRD/spec markdown), Tier C (.git).
        success, message, cost, model, output_files = run_agentic_architecture(
            issue_url=issue_url,
            verbose=True,
            quiet=False,
        )

        print("\n--- Default-discovery result ---")
        print(f"Success       : {success}")
        print(f"Message       : {message}")

        # Explicit override: pin the project root, bypassing marker discovery.
        # Use this when cwd is a self-contained pdd project nested inside an
        # unrelated outer git repo (CLI: pdd generate --project-root <path> <issue-url>).
        nested_project = Path("/tmp/example-pdd-project")
        nested_project.mkdir(parents=True, exist_ok=True)

        success, message, cost, model, output_files = run_agentic_architecture(
            issue_url=issue_url,
            verbose=False,
            quiet=True,
            project_root=str(nested_project),
        )

        print("\n--- Explicit-override result ---")
        print(f"Success       : {success}")
        print(f"Project root  : {nested_project}")
        print(f"Cost          : ${cost:.2f}")
        print(f"Model Used    : {model}")
        print(f"Output Files  : {output_files}")
        print(f"Message       : {message}")


if __name__ == "__main__":
    main()
