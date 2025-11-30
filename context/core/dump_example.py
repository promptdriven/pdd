#!/usr/bin/env python3
"""
Example usage of the pdd.core.dump module.

This module provides core dump generation and replay logic for PDD CLI debugging.
It captures execution context, errors, and environment information to help
reproduce and diagnose issues.

Key functions demonstrated:
- _write_core_dump: Writes a JSON core dump file for a CLI run
- _github_config: Checks for GitHub issue posting configuration
- _post_issue_to_github: Posts an issue to GitHub
- _write_replay_script: Creates a shell script to replay a command
- _build_issue_markdown: Builds GitHub issue title and markdown body
"""

import os
import sys
import json
import tempfile
from pathlib import Path
from unittest.mock import MagicMock

# Import the functions from the dump module
from pdd.core.dump import (
    _write_core_dump,
    _github_config,
    _post_issue_to_github,
    _write_replay_script,
    _build_issue_markdown,
)

# Ensure output directory exists (relative to this script)
OUTPUT_DIR = Path("./output")
OUTPUT_DIR.mkdir(parents=True, exist_ok=True)


def example_write_core_dump():
    """
    Demonstrates _write_core_dump function.
    
    This function writes a JSON core dump file when --core-dump is enabled.
    
    Parameters (via click.Context):
        ctx: click.Context
            The Click context object containing:
            - ctx.obj["core_dump"]: bool - Whether core dump is enabled
            - ctx.obj["force"]: bool - Force overwrite flag
            - ctx.obj["strength"]: float - AI model strength (0.0-1.0)
            - ctx.obj["temperature"]: float - AI model temperature
            - ctx.obj["time"]: float - Reasoning allocation (0.0-1.0)
            - ctx.obj["verbose"]: bool - Verbose output flag
            - ctx.obj["quiet"]: bool - Quiet output flag
            - ctx.obj["local"]: bool - Local execution flag
            - ctx.obj["context"]: str - Context name override
            - ctx.obj["output_cost"]: str - Cost tracking CSV path
            - ctx.obj["review_examples"]: bool - Review examples flag
        
        normalized_results: List[Any]
            List of result tuples from command execution.
            Each tuple contains: (result_data, cost: float, model_name: str)
            - cost: Estimated cost in USD (e.g., 0.05 for 5 cents)
            - model_name: Name of the AI model used (e.g., "gpt-4")
        
        invoked_subcommands: List[str]
            List of subcommand names that were invoked (e.g., ["generate", "test"])
        
        total_cost: float
            Total accumulated cost in USD for all operations
    
    Output:
        Creates a JSON file at .pdd/core_dumps/pdd-core-YYYYMMDDTHHMMSSZ.json
        containing execution context, errors, and environment information.
    
    Returns:
        None
    """
    # Create a mock Click context
    ctx = MagicMock()
    ctx.obj = {
        "core_dump": True,  # Enable core dump
        "force": True,
        "strength": 0.8,
        "temperature": 0.0,
        "time": 0.25,
        "verbose": False,
        "quiet": False,
        "local": True,
        "context": None,
        "output_cost": None,
        "review_examples": False,
    }
    
    # Simulate command results: (result_data, cost_in_usd, model_name)
    normalized_results = [
        ({"status": "success"}, 0.0025, "gpt-4"),  # $0.0025 cost
        ({"status": "success"}, 0.0015, "gpt-3.5-turbo"),  # $0.0015 cost
    ]
    
    invoked_subcommands = ["generate", "test"]
    total_cost = 0.004  # Total cost in USD
    
    # Change to output directory temporarily for core dump creation
    original_cwd = os.getcwd()
    os.chdir(OUTPUT_DIR)
    
    _write_core_dump(ctx, normalized_results, invoked_subcommands, total_cost)
    
    os.chdir(original_cwd)
    
    # Check if core dump was created
    core_dump_dir = OUTPUT_DIR / ".pdd" / "core_dumps"
    if core_dump_dir.exists():
        dumps = list(core_dump_dir.glob("pdd-core-*.json"))
        if dumps:
            print(f"Core dump created: {dumps[-1]}")
            with open(dumps[-1]) as f:
                content = json.load(f)
            print(f"  Schema version: {content.get('schema_version')}")
            print(f"  Total cost: ${content.get('total_cost', 0):.6f}")
            print(f"  Steps: {len(content.get('steps', []))}")


def example_github_config():
    """
    Demonstrates _github_config function.
    
    Checks for GitHub issue posting configuration via environment variables.
    
    Environment Variables Required:
        PDD_GITHUB_TOKEN: str
            GitHub personal access token with 'repo' scope for creating issues.
        PDD_GITHUB_REPO: str
            Repository name in format "owner/repo" (e.g., "promptdriven/pdd")
    
    Returns:
        Optional[Tuple[str, str]]:
            - (token, repo) tuple if both environment variables are set
            - None if either variable is missing
    
    Example return values:
        ("ghp_xxxx...", "promptdriven/pdd")  # When configured
        None  # When not configured
    """
    # Check current configuration
    result = _github_config()
    
    if result is None:
        print("GitHub issue posting is NOT configured.")
        print("To enable, set these environment variables:")
        print("  export PDD_GITHUB_TOKEN='your-github-token'")
        print("  export PDD_GITHUB_REPO='owner/repo'")
    else:
        token, repo = result
        print(f"GitHub issue posting is configured for: {repo}")
        print(f"Token: {token[:10]}..." if len(token) > 10 else f"Token: {token}")


def example_write_replay_script():
    """
    Demonstrates _write_replay_script function.
    
    Creates a shell script to replay the original command from a core dump.
    
    Parameters:
        core_path: Path
            Path to the core dump JSON file. The replay script will be
            created alongside it with a .replay.sh extension.
        
        payload: Dict[str, Any]
            Core dump payload containing:
            - cwd: str - Original working directory path
            - argv: List[str] - Original CLI arguments (without 'pdd' binary)
            - environment: Dict[str, str] - Environment variables to restore
    
    Returns:
        Optional[Path]:
            - Path to the created replay script if successful
            - None if cwd or argv are missing from payload
    
    Output:
        Creates an executable bash script at {core_path}.replay.sh containing:
        - Shebang and strict mode settings
        - cd command to original working directory
        - export commands for environment variables
        - pdd command with original arguments
    """
    # Create a sample core dump file
    core_path = OUTPUT_DIR / "sample-core-dump.json"
    
    # Sample payload simulating a core dump
    payload = {
        "cwd": str(OUTPUT_DIR.absolute()),
        "argv": ["--force", "generate", "calculator_python.prompt"],
        "environment": {
            "PDD_GENERATE_OUTPUT_PATH": "./src/",
            "VIRTUAL_ENV": "/path/to/venv",
        },
    }
    
    # Write the sample core dump
    core_path.write_text(json.dumps(payload, indent=2))
    
    # Generate the replay script
    replay_path = _write_replay_script(core_path, payload)
    
    if replay_path:
        print(f"Replay script created: {replay_path}")
        print("\nScript contents:")
        print("-" * 40)
        print(replay_path.read_text())
        print("-" * 40)
    else:
        print("Failed to create replay script (missing cwd or argv)")


def example_build_issue_markdown():
    """
    Demonstrates _build_issue_markdown function.
    
    Builds a GitHub issue title and markdown body from a core dump payload.
    
    Parameters:
        payload: Dict[str, Any]
            Core dump payload containing:
            - platform: Dict with system, release, version, python keys
            - invoked_subcommands: List[str] - Commands that were run
            - argv: List[str] - CLI arguments
            - cwd: str - Working directory
            - total_cost: float - Total cost in USD
            - errors: List[Dict] - Error information with command, type, traceback
            - pdd_version: str - PDD version string
        
        description: str
            User-provided description of what went wrong.
            If empty, a placeholder message is used.
        
        core_path: Path
            Path to the core dump file (shown in issue body).
        
        replay_path: Optional[Path]
            Path to replay script (currently not shown in issue body,
            but reproduction commands are included inline).
        
        attachments: List[str]
            List of file paths to mention as relevant inputs/outputs.
    
    Returns:
        Tuple[str, str]:
            - title: str - Issue title like "[core-dump] generate failed on Darwin"
            - body: str - Full markdown body with:
                - Core dump file reference
                - "What happened" section with description
                - "Environment" section with platform/version details
                - "Reproduction" section with commands to reproduce
                - "Errors" section with tracebacks (if any)
                - "Attachments" section (if any)
                - "Raw core dump (JSON)" section (truncated at 8000 chars)
    """
    # Sample payload
    payload = {
        "schema_version": 1,
        "pdd_version": "0.0.74",
        "timestamp_utc": "20250101T120000Z",
        "argv": ["--force", "generate", "calculator_python.prompt"],
        "cwd": "/home/user/project",
        "platform": {
            "system": "Linux",
            "release": "5.15.0",
            "version": "#1 SMP",
            "python": "3.11.0",
        },
        "invoked_subcommands": ["generate"],
        "total_cost": 0.0025,
        "steps": [
            {"step": 1, "command": "generate", "cost": 0.0025, "model": "gpt-4"}
        ],
        "errors": [
            {
                "command": "generate",
                "type": "ValueError",
                "traceback": "Traceback (most recent call last):\n  File 'generate.py', line 42\nValueError: Invalid prompt format",
            }
        ],
        "environment": {"PDD_GENERATE_OUTPUT_PATH": "./src/"},
    }
    
    description = "The generate command failed when processing a prompt with special characters."
    core_path = OUTPUT_DIR / "pdd-core-20250101T120000Z.json"
    replay_path = OUTPUT_DIR / "pdd-core-20250101T120000Z.replay.sh"
    attachments = ["prompts/calculator_python.prompt", "errors.log"]
    
    title, body = _build_issue_markdown(
        payload, description, core_path, replay_path, attachments
    )
    
    print(f"Issue Title: {title}")
    print("\nIssue Body Preview (first 500 chars):")
    print("-" * 40)
    print(body[:500])
    print("...")
    print("-" * 40)
    
    # Save full issue body to file for inspection
    issue_file = OUTPUT_DIR / "sample_github_issue.md"
    issue_file.write_text(f"# {title}\n\n{body}")
    print(f"\nFull issue saved to: {issue_file}")


def example_post_issue_to_github():
    """
    Demonstrates _post_issue_to_github function.
    
    Posts an issue to GitHub using the GitHub API.
    
    Parameters:
        token: str
            GitHub personal access token with 'repo' scope.
            Must have permission to create issues in the target repository.
        
        repo: str
            Repository in "owner/repo" format (e.g., "promptdriven/pdd").
        
        title: str
            Issue title (e.g., "[core-dump] generate failed on Darwin").
        
        body: str
            Full markdown body of the issue.
    
    Returns:
        Optional[str]:
            - URL of the created issue on success (e.g., "https://github.com/owner/repo/issues/123")
            - None on failure (network error, auth error, etc.)
    
    Note:
        This example shows the function signature but does not actually
        post to GitHub to avoid creating test issues.
    """
    print("_post_issue_to_github function signature:")
    print("  _post_issue_to_github(token: str, repo: str, title: str, body: str) -> Optional[str]")
    print()
    print("Example usage (not executed to avoid creating test issues):")
    print('  url = _post_issue_to_github(')
    print('      token="ghp_xxxxxxxxxxxx",')
    print('      repo="promptdriven/pdd",')
    print('      title="[core-dump] generate failed on Darwin",')
    print('      body="## What happened\\n\\nThe command crashed..."')
    print('  )')
    print('  if url:')
    print('      print(f"Issue created: {url}")')
    print('  else:')
    print('      print("Failed to create issue")')


if __name__ == "__main__":
    print("=" * 60)
    print("PDD Core Dump Module Examples")
    print("=" * 60)
    
    print("\n1. Writing a Core Dump")
    print("-" * 40)
    example_write_core_dump()
    
    print("\n2. Checking GitHub Configuration")
    print("-" * 40)
    example_github_config()
    
    print("\n3. Creating a Replay Script")
    print("-" * 40)
    example_write_replay_script()
    
    print("\n4. Building GitHub Issue Markdown")
    print("-" * 40)
    example_build_issue_markdown()
    
    print("\n5. Posting Issue to GitHub (Demo Only)")
    print("-" * 40)
    example_post_issue_to_github()
    
    print("\n" + "=" * 60)
    print("Examples completed. Check ./output/ for generated files.")
    print("=" * 60)
