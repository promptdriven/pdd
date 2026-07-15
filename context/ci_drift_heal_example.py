"""Example demonstrating the provider-free execution contract of pdd.ci_drift_heal.\n\nThis script creates a disposable project fixture in a temporary directory,\nisolates configuration from the ambient user environment, registers a mock\nprompt module, and runs a safe dry-run drift detection.\n\nInputs:\n    - None (the script dynamically provisions all temporary fixtures).\n\nOutputs:\n    - Exit code 0 and a success message if the dry-run executes successfully.\n    - Non-zero exit code matching the dry-run return on failure.\n"""

from __future__ import annotations

import os
import subprocess
import sys
import tempfile
from pathlib import Path

# Enforce no bytecode generation before imports are processed
sys.dont_write_bytecode = True
os.environ["PYTHONDONTWRITEBYTECODE"] = "1"

# Make the local `pdd` package importable regardless of current working directory
sys.path.insert(0, str(Path(__file__).resolve().parents[1]))

import pdd.ci_drift_heal as drift


def build_isolated_fixture(workspace: Path) -> None:
    """Build a minimal, valid PDD project fixture inside the workspace."""
    # Write a minimal .pddrc configuration marker
    (workspace / ".pddrc").write_text(
        "# PDD project configuration marker\n", encoding="utf-8"
    )

    # Create directory structure for prompts
    prompts_dir = workspace / "prompts"
    prompts_dir.mkdir(parents=True, exist_ok=True)

    # Add a mock prompt matching PDD naming convention
    mock_prompt_content = """<pdd-reason>Mock reason for demo module.</pdd-reason>\n<pdd-interface>\n{\n  "type": "module",\n  "module": {\n    "functions": []\n  }\n}\n</pdd-interface>\n\n% Prompt instructions begin here.\n"""
    (prompts_dir / "demo_module_python.prompt").write_text(
        mock_prompt_content, encoding="utf-8"
    )

    # Initialize a clean, isolated Git repository
    subprocess.run(["git", "init", "-q"], cwd=workspace, check=True)
    subprocess.run(
        ["git", "config", "user.name", "PDD Example User"],
        cwd=workspace,
        check=True,
    )
    subprocess.run(
        ["git", "config", "user.email", "example@pdd.local"],
        cwd=workspace,
        check=True,
    )
    subprocess.run(["git", "add", "."], cwd=workspace, check=True)
    subprocess.run(
        ["git", "commit", "-m", "initial commit", "--no-verify"],
        cwd=workspace,
        check=True,
    )


def run_example() -> None:
    """Main runner orchestrating workspace setup and isolated main invocation."""
    print("Setting up isolated project workspace...")

    with tempfile.TemporaryDirectory(prefix="pdd_ci_drift_") as tmpdir:
        workspace_path = Path(tmpdir).resolve()
        build_isolated_fixture(workspace_path)

        # Securely isolate the child execution context
        isolated_env = os.environ.copy()
        isolated_env.update(
            {
                "HOME": str(workspace_path),
                "XDG_CONFIG_HOME": str(workspace_path / ".config"),
                "GIT_CONFIG_NOGLOBAL": "1",
                "GIT_CONFIG_NOSYSTEM": "1",
                # Strip ambient developer credentials
                "ANTHROPIC_API_KEY": "",
                "OPENAI_API_KEY": "",
                "AWS_ACCESS_KEY_ID": "",
                "AWS_SECRET_ACCESS_KEY": "",
                "AZURE_OPENAI_API_KEY": "",
            }
        )

        # Cache CWD and change to the isolated workspace root
        old_cwd = Path.cwd()
        os.chdir(workspace_path)

        print("Executing pdd.ci_drift_heal.main in dry_run mode...")
        try:
            # Call public main interface strictly utilizing keyword dry_run=True
            exit_code = drift.main(
                modules=None,
                budget_cap=None,
                skip_ci=False,
                diff_base=None,
                dry_run=True,
                as_json=False,
            )
        finally:
            # Safely restore previous CWD
            os.chdir(old_cwd)

        # Evaluate and act on exit code
        if exit_code != 0:
            print(f"ci_drift_heal example failed with exit code: {exit_code}")
            sys.exit(exit_code)

        print("ci_drift_heal example completed successfully.")


if __name__ == "__main__":
    run_example()