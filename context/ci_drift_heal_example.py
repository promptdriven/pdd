"""Example demonstrating the usage of `pdd.ci_drift_heal` in dry-run mode.

This script constructs an isolated workspace containing a temporary PDD module
and triggers `pdd.ci_drift_heal.main` with `dry_run=True` to safe-test
drift detection.

Inputs:
    - No external credentials or interactive inputs required.
    - Creates a temporary directory mimicking a real repository structure.

Outputs:
    - Standard console output summarising detected modules and stale metadata metrics.
    - Exits 0 on success, or propagates any non-zero exit code from the runner.
"""

from __future__ import annotations

import json
import os
import subprocess
import sys
import tempfile
from pathlib import Path

# Ensure bytecode generation is disabled during import and execution
sys.dont_write_bytecode = True

# Make the local `pdd` package importable regardless of current working directory
sys.path.insert(0, str(Path(__file__).resolve().parents[1]))

import pdd.ci_drift_heal as drift


def setup_isolated_workspace(root: Path) -> None:
    """Sets up a minimal, valid PDD workspace inside a temporary directory."""
    # 1. Initialize a dummy git repository to satisfy git rev-parse demands
    subprocess.run(["git", "init", "-q"], cwd=root, check=True)
    subprocess.run(["git", "config", "user.name", "PDD-CI-Test"], cwd=root, check=True)
    subprocess.run(["git", "config", "user.email", "ci@pdd.local"], cwd=root, check=True)

    # 2. Write workspace configuration marker (.pddrc)
    (root / ".pddrc").write_text("# PDD configuration marker\n", encoding="utf-8")

    # 3. Write a mock architecture specification
    arch_data = {
        "modules": [
            {
                "basename": "calculator",
                "language": "python",
                "filepath": "calculator.py",
                "filename": "calculator_python.prompt",
                "reason": "Provides basic arithmetic logic.",
                "dependencies": [],
                "tags": ["module", "python"],
                "interface": {
                    "type": "module",
                    "module": {
                        "functions": [
                            {"name": "add", "signature": "(a: int, b: int) -> int"}
                        ]
                    }
                }
            }
        ]
    }
    (root / "architecture.json").write_text(json.dumps(arch_data, indent=2), encoding="utf-8")

    # 4. Create prompt files matching the PDD discovery conventions
    prompts_dir = root / "prompts"
    prompts_dir.mkdir(parents=True, exist_ok=True)
    
    prompt_content = """<pdd-reason>Provides basic arithmetic logic.</pdd-reason>
<pdd-interface>
{
  "type": "module",
  "module": {
    "functions": [
      {"name": "add", "signature": "(a: int, b: int) -> int"}
    ]
  }
}
</pdd-interface>

% Prompt instructions begin here...
"""
    (prompts_dir / "calculator_python.prompt").write_text(prompt_content, encoding="utf-8")

    # 5. Create the corresponding code file
    code_file = root / "calculator.py"
    code_file.write_text("""from __future__ import annotations

def add(a: int, b: int) -> int:
    \"\"\"Sum two integers.\"\"\"
    return a + b
""", encoding="utf-8")

    # 6. Commit files to set HEAD and satisfy git checkout/show requirements
    subprocess.run(["git", "add", "."], cwd=root, check=True)
    subprocess.run(["git", "commit", "-m", "initial commit", "-q"], cwd=root, check=True)


def main() -> int:
    # Build isolated context in a temporary directory
    with tempfile.TemporaryDirectory(prefix="pdd_ci_drift_") as tmp_dir:
        workspace_root = Path(tmp_dir).resolve()
        setup_isolated_workspace(workspace_root)

        # Enforce an isolated execution environment
        custom_env = os.environ.copy()
        custom_env["PYTHONDONTWRITEBYTECODE"] = "1"
        custom_env["HOME"] = str(workspace_root)
        
        # Override the current working directory temporarily to scope execution
        original_cwd = os.getcwd()
        os.chdir(workspace_root)

        print(f"Executing dry-run drift check in: {workspace_root}")

        try:
            # Execute main drift-heal entrance on dry_run mode.
            # Inputs:
            #   - modules: List of target basenames (or None for all)
            #   - budget_cap: Cumulative execution budget threshold (None for unlimited)
            #   - skip_ci: Boolean indicating push-to-main or PR execution style
            #   - diff_base: Git revision base target (None for relative to HEAD)
            #   - dry_run: Explicitly pass True to skip writing updates
            exit_code = drift.main(
                modules=["calculator"],
                budget_cap=10.0,
                skip_ci=True,
                diff_base=None,
                dry_run=True,
            )
        finally:
            os.chdir(original_cwd)

        if exit_code != 0:
            print(f"ci_drift_heal execution returned non-zero exit code: {exit_code}")
            return exit_code

        print("ci_drift_heal example completed successfully.")
        return 0


if __name__ == "__main__":
    sys.exit(main())