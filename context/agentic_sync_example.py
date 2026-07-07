from __future__ import annotations

import json
import os
import sys
from pathlib import Path
from unittest.mock import patch, MagicMock

# Ensure the parent directory is in the sys.path so 'pdd' can be imported
sys.path.insert(0, str(Path(__file__).resolve().parent.parent))

from pdd.agentic_sync import run_agentic_sync, run_global_sync

def setup_mock_project(output_dir: Path) -> None:
    """
    Creates a minimal, valid PDD project structure with an architecture.json
    and a sample prompt file in the temporary output directory.
    """
    prompts_dir = output_dir / "prompts"
    prompts_dir.mkdir(parents=True, exist_ok=True)

    # 1. Create a minimal mock .pddrc
    pddrc_content = {
        "version": "1.0",
        "contexts": {
            "default": {
                "defaults": {
                    "generate_output_path": "src/",
                    "test_output_path": "tests/",
                    "default_language": "python"
                }
            }
        }
    }
    (output_dir / ".pddrc").write_text(json.dumps(pddrc_content, indent=2), encoding="utf-8")

    # 2. Create a mock architecture.json with one registered module
    architecture_content = {
        "modules": [
            {
                "filename": "calc_python.prompt",
                "filepath": "src/calc.py",
                "reason": "Performs basic mathematical operations.",
                "dependencies": [],
                "interface": {
                    "type": "module",
                    "module": {
                        "functions": [
                            {
                                "name": "add_numbers",
                                "signature": "def add_numbers(a: int, b: int) -> int:"
                            }
                        ]
                    }
                }
            }
        ]
    }
    (output_dir / "architecture.json").write_text(json.dumps(architecture_content, indent=2), encoding="utf-8")

    # 3. Create the matching prompt file
    prompt_content = """<pdd-reason>Basic math operations.</pdd-reason>\n<pdd-interface>\n{\n  "type": "module",\n  "module": {\n    "functions": [{"name": "add_numbers", "signature": "def add_numbers(a: int, b: int) -> int:"}]\n  }\n}\n</pdd-interface>\n"""
    (prompts_dir / "calc_python.prompt").write_text(prompt_content, encoding="utf-8")


def run_example() -> None:
    """
    Demonstrates agentic sync execution flows.

    How run_agentic_sync works:
        1. Parses the GitHub issue URL.
        2. Fetches the issue details and comments via 'gh api'.
        3. Identifies modules needing changes (using deterministic branch diff or LLM).
        4. Validates architecture dependencies.
        5. Runs dry-run preflights.
        6. Parallel syncs modules via AsyncSyncRunner.

    Input Parameters for run_agentic_sync:
        issue_url (str): The target GitHub issue URL.
        verbose (bool): Prints raw logs, prompt previews, and costs.
        quiet (bool): Suppresses non-essential console outputs.
        budget (float): Maximum dollar budget for LLM operations.
        dry_run (bool): Evaluates the plan and validation without performing writes.
        use_github_state (bool): Writes progress logs as comments on the issue.

    Returns:
        Tuple[bool, str, float, str]: (success, message, total_cost, model_used)
    """
    output_dir = Path("./output").resolve()
    if output_dir.exists():
        import shutil
        shutil.rmtree(output_dir)
    output_dir.mkdir(parents=True, exist_ok=True)

    print(f"[Setup] Generating temporary PDD project in: {output_dir}")
    setup_mock_project(output_dir)

    # Mock the issue payload returned by 'gh api'
    mock_issue_payload = {
        "title": "Fix calculator addition logic",
        "body": "The addition function in calc_python should support negative floats.",
        "comments_url": "https://api.github.com/repos/example/pdd-project/issues/101/comments"
    }

    # Setup the subprocess run mock targeting standard git, gh, and child dry-runs
    def mock_subprocess_run(args, **kwargs):
        cmd = " ".join(args) if isinstance(args, list) else str(args)
        response = MagicMock()
        response.returncode = 0
        
        if "api repos/" in cmd:
            response.stdout = json.dumps(mock_issue_payload)
        elif "api" in cmd and "comments" in cmd:
            response.stdout = json.dumps([])
        elif "rev-parse" in cmd:
            response.stdout = "main"
        elif "diff" in cmd:
            response.stdout = "prompts/calc_python.prompt"
        elif "dry-run" in cmd:
            response.stdout = "Dry run successful"
        else:
            response.stdout = ""
        return response

    print("\n--- Running run_agentic_sync() (Dry-Run Mode) ---")

    # Patch environmental and subprocess prerequisites to guarantee execution in any CI environment
    with patch("pdd.agentic_sync._check_gh_cli", return_value=True), \
         patch("pdd.agentic_sync._run_gh_command", return_value=(True, json.dumps(mock_issue_payload))), \
         patch("pdd.agentic_sync._find_project_root", return_value=output_dir), \
         patch("pdd.agentic_sync._run_single_dry_run", return_value=(True, "")), \
         patch("pdd.agentic_sync.subprocess.run", side_effect=mock_subprocess_run):

        success, message, cost, model = run_agentic_sync(
            issue_url="https://github.com/example/pdd-project/issues/101",
            verbose=False,
            quiet=False,
            budget=10.0,
            dry_run=True,
            use_github_state=False
        )

        print("\n[Result] run_agentic_sync output:")
        print(f"  Success:      {success}")
        print(f"  Message:      {message}")
        print(f"  Cost (USD):   ${cost:.4f}")
        print(f"  Model Used:   {model}")


    print("\n--- Running run_global_sync() (Dry-Run Mode) ---")

    with patch("pdd.agentic_sync._find_project_root", return_value=output_dir), \
         patch("pdd.agentic_sync._run_single_dry_run", return_value=(True, "")), \
         patch("pdd.agentic_sync.subprocess.run", side_effect=mock_subprocess_run):

        success, message, cost, model = run_global_sync(
            verbose=False,
            quiet=False,
            budget=5.0,
            dry_run=True
        )

        print("\n[Result] run_global_sync output:")
        print(f"  Success:      {success}")
        print(f"  Message:      {message}")
        print(f"  Cost (USD):   ${cost:.4f}")
        print(f"  Model Used:   {model}")

    # Clean up temporary output directory
    import shutil
    shutil.rmtree(output_dir, ignore_errors=True)
    print("\n[Cleanup] Cleaned up temporary directory.")


if __name__ == "__main__":
    run_example()