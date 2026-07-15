"""Example demonstrating how to use the pdd.ci_drift_heal module.

This script sets up an isolated disposable workspace, creates a mock PDD module
with valid configuration and a mock fingerprint, and executes the `main` entry
point in `dry_run=True` mode to detect any drift safely.
"""

from __future__ import annotations

import json
import os
import subprocess
import sys
import tempfile
from pathlib import Path
from unittest.mock import patch

# Force Python to avoid writing bytecode files during execution
sys.dont_write_bytecode = True

# Isolate the environment entirely to prevent leakage of ambient configurations
CLEAN_ENV = {
    "PATH": os.environ.get("PATH", ""),
    "PYTHONDONTWRITEBYTECODE": "1",
    "GIT_CONFIG_NOSYSTEM": "1",
    "GIT_ATTR_NOSYSTEM": "1",
}


def create_mock_project(workspace: Path) -> None:
    """Create a minimum viable mock PDD project structure in the workspace.

    Args:
        workspace: Path to the root of the temporary workspace.
    """
    # 1. Initialize Git repository
    subprocess.run(["git", "init", "-q"], cwd=workspace, check=True)
    subprocess.run(["git", "config", "user.name", "PDD Test"], cwd=workspace, check=True)
    subprocess.run(["git", "config", "user.email", "test@pdd.local"], cwd=workspace, check=True)

    # 2. Create standard PDD project markers and directories
    (workspace / ".pddrc").write_text("# Mock PDD Project Config\n", encoding="utf-8")
    
    prompts_dir = workspace / "prompts"
    prompts_dir.mkdir(parents=True, exist_ok=True)
    
    meta_dir = workspace / ".pdd/meta"
    meta_dir.mkdir(parents=True, exist_ok=True)

    # 3. Create a valid mock prompt module
    prompt_content = """<pdd-reason>Mock reason for demo_module.</pdd-reason>
<pdd-interface>{\"type\": \"module\"}</pdd-interface>
% Mock prompt instructions
"""
    (prompts_dir / "demo_module_python.prompt").write_text(prompt_content, encoding="utf-8")

    # 4. Create a corresponding mock fingerprint JSON
    fingerprint = {
        "basename": "demo_module",
        "language": "python",
        "command": "verify",
        "prompt_hash": "e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855",
        "code_hash": "e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855",
        "test_files": {},
        "cost": 0.0,
    }
    (meta_dir / "demo_module_python.json").write_text(
        json.dumps(fingerprint, indent=2), encoding="utf-8"
    )

    # Commit the mock structure so it is visible to Git tracking
    subprocess.run(["git", "add", "."], cwd=workspace, check=True)
    subprocess.run(["git", "commit", "-m", "initial commit", "-q"], cwd=workspace, check=True)


def main() -> None:
    # 1. Create a safe temporary directory to avoid mutating the source repository
    with tempfile.TemporaryDirectory(prefix="pdd_ci_drift_heal_demo_") as tmp_dir:
        workspace_path = Path(tmp_dir).resolve()
        
        # Configure localized environment variables for process isolation
        CLEAN_ENV["HOME"] = str(workspace_path / "home")
        CLEAN_ENV["XDG_CONFIG_HOME"] = str(workspace_path / "xdg")
        Path(CLEAN_ENV["HOME"]).mkdir()
        Path(CLEAN_ENV["XDG_CONFIG_HOME"]).mkdir()

        # Build mock repository structure
        create_mock_project(workspace_path)

        # Ensure our PDD package location is discoverable
        sys.path.insert(0, str(Path(__file__).resolve().parents[1]))

        # Import the module under demonstration
        from pdd.ci_drift_heal import main as run_drift_heal

        # 2. Execute dry-run with mock assertions
        # We patch build_report to ensure a stable, provider-free response
        mock_report = {
            "ok": True,
            "consumer": "ci-heal",
            "summary": {
                "metadata_stale": 0,
                "conflicts": 0,
                "unbaselined": 0,
                "failures": 0,
            },
            "units": [
                {
                    "basename": "demo_module",
                    "language": "python",
                    "classification": "synced",
                }
            ],
        }

        print(f"Executing dry-run ci_drift_heal inside {workspace_path}...")

        with patch("pdd.continuous_sync.build_report", return_value=mock_report), \
             patch.dict(os.environ, CLEAN_ENV, clear=True), \
             patch("os.getcwd", return_value=str(workspace_path)):
            
            exit_code = run_drift_heal(
                modules=["demo_module"],
                budget_cap=10.0,
                skip_ci=True,
                dry_run=True,
            )

        if exit_code != 0:
            print(f"ci_drift_heal dry-run failed with exit code: {exit_code}")
            sys.exit(exit_code)

        print("ci_drift_heal example completed successfully")


if __name__ == "__main__":
    main()