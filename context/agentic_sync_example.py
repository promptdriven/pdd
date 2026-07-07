from __future__ import annotations

import json
import os
import shutil
import sys
from pathlib import Path
from unittest.mock import patch, MagicMock

from rich.console import Console

# Import the target orchestration functions from the agentic_sync module
from pdd.agentic_sync import run_agentic_sync, run_global_sync

console = Console()


def create_mock_workspace(base_dir: Path) -> None:
    """Create a mock workspace with a standard architecture.json, .pddrc, and prompts."""
    base_dir.mkdir(parents=True, exist_ok=True)

    # 1. Create a mock .pddrc project configuration
    pddrc_content = {
        "version": "1.0",
        "contexts": {
            "default": {
                "defaults": {
                    "generate_output_path": "src/",
                    "test_output_path": "tests/",
                    "prompts_dir": "prompts/",
                    "default_language": "python"
                }
            }
        }
    }
    pddrc_file = base_dir / ".pddrc"
    pddrc_file.write_text(json.dumps(pddrc_content, indent=2), encoding="utf-8")

    # 2. Create a mock architecture.json describing project modules
    architecture_content = {
        "modules": [
            {
                "filename": "calculator_python.prompt",
                "filepath": "src/calculator.py",
                "reason": "Core arithmetic service",
                "dependencies": [],
                "tags": ["module", "python"]
            }
        ]
    }
    arch_file = base_dir / "architecture.json"
    arch_file.write_text(json.dumps(architecture_content, indent=2), encoding="utf-8")

    # 3. Create a mock prompt file
    prompts_dir = base_dir / "prompts"
    prompts_dir.mkdir(parents=True, exist_ok=True)
    prompt_file = prompts_dir / "calculator_python.prompt"
    prompt_file.write_text(
        "<pdd-reason>Performs simple calculations.</pdd-reason>\n"
        "<pdd-interface>\n"
        "{\n"
        '  "type": "module",\n'
        '  "module": {\n'
        '    "functions": [{"name": "add", "signature": "(a: int, b: int) -> int"}]\n'
        "  }\n"
        "}\n"
        "</pdd-interface>\n",
        encoding="utf-8"
    )


def mock_subprocess_run(args: list[str], **kwargs: any) -> MagicMock:
    """Mock git and gh command execution for deterministic runs."""
    cmd_str = " ".join(str(arg) for arg in args)
    mock_res = MagicMock()
    mock_res.returncode = 0

    if "git rev-parse --abbrev-ref HEAD" in cmd_str:
        mock_res.stdout = "change/issue-42\n"
    elif "git diff" in cmd_str:
        # Mock changed files from the branch diff to detect our module
        mock_res.stdout = "prompts/calculator_python.prompt\n"
    elif "git show" in cmd_str:
        # Mock architecture lookup from origin branch
        mock_res.stdout = "{}"
    elif "gh api" in cmd_str:
        # Mock GitHub Issue payload
        mock_res.stdout = json.dumps({
            "title": "Implement addition functionality",
            "body": "Add support for simple addition in calculator_python.prompt",
            "comments_url": "https://api.github.com/repos/example/repo/issues/42/comments"
        })
    else:
        mock_res.stdout = ""

    return mock_res


def main() -> None:
    # Setup isolated mock project directory under ./output
    output_dir = Path("./output").resolve()
    if output_dir.exists():
        shutil.rmtree(output_dir)
    create_mock_workspace(output_dir)

    console.print(f"[bold blue]Created Mock Project Workspace at:[/bold blue] {output_dir}\n")

    # Change active directory to mock project so that path discovery works natively
    original_cwd = Path.cwd()
    os.chdir(output_dir)

    # Patch necessary subprocesses and CLI availability checks
    with patch("pdd.agentic_sync.shutil.which", return_value="/usr/bin/gh"), \
         patch("pdd.agentic_sync.subprocess.run", side_effect=mock_subprocess_run), \
         patch("pdd.agentic_sync._run_single_dry_run", return_value=(True, "")):

        # -------------------------------------------------------------
        # Demo 1: Project-Wide Tier 1 Global Sync (Dry-Run Mode)
        # -------------------------------------------------------------
        console.print("[bold green]--- 1. Executing Global Sync (Dry Run) ---[/bold green]")
        success, msg, cost, mode = run_global_sync(
            dry_run=True,
            verbose=False,
            quiet=False
        )

        console.print(f"Success  : [cyan]{success}[/cyan]")
        console.print(f"Message  : [cyan]{msg}[/cyan]")
        console.print(f"Total Cost : [cyan]${cost:.5f}[/cyan]")
        console.print(f"Mode     : [cyan]{mode}[/cyan]\n")

        # -------------------------------------------------------------
        # Demo 2: GitHub Issue-driven Parallel Sync (Dry-Run Mode)
        # -------------------------------------------------------------
        console.print("[bold green]--- 2. Executing Agentic Sync from Issue URL (Dry Run) ---[/bold green]")
        issue_url = "https://github.com/example/repo/issues/42"
        
        success, msg, cost, model = run_agentic_sync(
            issue_url=issue_url,
            dry_run=True,
            use_github_state=False,  # Set local-only mode to prevent hitting remote APIs
            quiet=False,
            verbose=False
        )

        console.print(f"Success   : [cyan]{success}[/cyan]")
        console.print(f"Message   : [cyan]{msg}[/cyan]")
        console.print(f"Total Cost: [cyan]${cost:.5f}[/cyan]")
        console.print(f"Model Used: [cyan]{model or 'global-sync'}[/cyan]\n")

    # Restore the original current working directory and clean up
    os.chdir(original_cwd)
    shutil.rmtree(output_dir, ignore_errors=True)
    console.print("[bold blue]Cleaned up temporary workspace files.[/bold blue]")


if __name__ == "__main__":
    main()