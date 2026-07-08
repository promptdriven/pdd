from __future__ import annotations

import json
import os
import sys
from pathlib import Path
from unittest.mock import patch
from rich.console import Console

# Ensure we can import the pdd package
sys.path.insert(0, str(Path(__file__).resolve().parent.parent))

from pdd.agentic_sync import run_agentic_sync, run_global_sync

console = Console()

def setup_mock_project(project_dir: Path) -> tuple[Path, Path]:
    """
    Helper to set up a mock PDD project structure inside `./output`
    for the sync runner to analyze.
    """
    prompts_dir = project_dir / "prompts"
    prompts_dir.mkdir(parents=True, exist_ok=True)

    # 1. Create a mock architecture.json
    architecture_data = {
        "modules": [
            {
                "filename": "math_helper_python.prompt",
                "filepath": "math_helper.py",
                "reason":"Core math operations utility",
                "dependencies": []
            },
            {
                "filename": "calculator_python.prompt",
                "filepath": "calculator.py",
                "reason": "High-level calculator wrapper",
                "dependencies": ["math_helper_python.prompt"]
            }
        ]
    }
    arch_path = project_dir / "architecture.json"
    arch_path.write_text(json.dumps(architecture_data, indent=2), encoding="utf-8")

    # 2. Create a mock .pddrc file
    pddrc_data = {
        "version": "1.0",
        "contexts": {
            "default": {
                "defaults": {
                    "generate_output_path": "./",
                    "default_language": "python"
                }
            }
        }
    }
    pddrc_path = project_dir / ".pddrc"
    pddrc_path.write_text(json.dumps(pddrc_data, indent=2), encoding="utf-8")

    # 3. Create mock prompt files
    (prompts_dir / "math_helper_python.prompt").write_text(
        """<pdd-reason>Provides basic sum and multiply capabilities.</pdd-reason>
        <pdd-interface>{"type": "module"}</pdd-interface>
        """, encoding="utf-8"
    )
    (prompts_dir / "calculator_python.prompt").write_text(
        """<pdd-reason>Calculates complex equations.</pdd-reason>
        <pdd-interface>{"type": "module"}</pdd-interface>
        <include>prompts/math_helper_python.prompt</include>
        """, encoding="utf-8"
    )

    return arch_path, pddrc_path


def main() -> None:
    # Define our output directory structure
    output_dir = Path("./output").resolve()
    output_dir.mkdir(parents=True, exist_ok=True)

    console.print("[bold blue]Setting up mock project workspace...[/bold blue]")
    arch_path, pddrc_path = setup_mock_project(output_dir)
    
    # Temporarily change directory to output_dir so path discovery locates the mock files
    original_cwd = os.getcwd()
    os.chdir(output_dir)

    try:
        # =====================================================================
        # Workflow 1: run_global_sync
        # =====================================================================
        console.print("\n[bold green]--- Testing run_global_sync (Dry Run) ---[/bold green]")
        
        # run_global_sync performs a Tier 1 (prompt staleness) analysis of all
        # modules declared in the architecture config.
        success, msg, cost, model = run_global_sync(
            verbose=True,
            quiet=False,
            dry_run=True,          # Dry run prevents actual file writes / LLM regeneration
            budget=10.0,
            skip_verify=True,
            skip_tests=True,
            agentic_mode=True
        )
        
        console.print(f"[bold]Success:" , success)
        console.print(f"[bold]Message:[" , msg)
        console.print(f"[bold]LLM Cost:" , f"${cost:.4f}")
        console.print(f"[bold]Model Engine:" , model)

        # =====================================================================
        # Workflow 2: run_agentic_sync (GitHub Issue Driven)
        # =====================================================================
        console.print("\n[bold green]--- Testing run_agentic_sync (Dry Run with mocked Git/GH CLI) ---[/bold green]")
        
        # Since run_agentic_sync queries the GitHub API using `gh`, we mock
        # those external dependencies so the example runs flawlessly headless.
        mock_issue_data = {
            "title": "Support square root function in Calculator",
            "body": "Please modify math_helper and calculator to support sqrt operations.",
            "comments_url": "https://api.github.com/repos/example/repo/issues/1/comments"
        }

        with patch("pdd.agentic_sync._check_gh_cli", return_value=True),
             patch("pdd.agentic_sync._run_gh_command") as mock_gh,
             patch("pdd.agentic_sync.run_agentic_task") as mock_ll:

            # Mock the GitHub API response for fetching issue detail and comments
            mock_gh.side_effect = [
                (True, json.dumps(mock_issue_data)),  # Repo Issue fetch
                (True, "[]")                           # Comments fetch
            ]
            
            # Mock the Module Identification LLM output response
            mock_ll.return_value = (
                True,
                "MODULES_TO_SYNC: [\"math_helper_python\", \"calculator_python\"]\nDEPS_VALID: true",
                0.015,  # mock cost
                "mock-gpt-4o"
            )

            # Execute issue URL sync orchestration in dry_run mode
            success_issue, msg_issue, cost_issue, model_issue = run_agentic_sync(
                issue_url="https://github.com/example/repo/issues/1",
                dry_run=True,
                quiet=False,
                verbose=True,
                use_github_state=False  # Do not attempt to post update comments back to GitHub
            )

            console.print(f"[bold]Success:" , success_issue)
            console.print(f"[bold]Message:" , msg_issue)
            console.print(f"[bold]Total Accumulated Cost:" , f"${cost_issue:.4f}")
            console.print(f"[bold]Model Engine:" , model_issue)

    finally:
        # Restore original working directory
        os.chdir(original_cwd)
        console.print("\n[bold blue]Example run completed safely.[/bold blue]")


if __name__ == "__main__":
    main()