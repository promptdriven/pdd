from __future__ import annotations

import os
import sys
import subprocess
from pathlib import Path
from typing import List, Optional

# Ensure the project root is in the path for imports
# The module is located at pdd/ci_drift_heal.py
project_root = Path(__file__).resolve().parent.parent
sys.path.append(str(project_root))

from pdd.ci_drift_heal import main, detect_drift, heal_module, _build_ci_env

def run_ci_auto_heal_example():
    """
    Demonstrates the full lifecycle of a PDD CI Auto-Heal run.
    
    The process consists of:
    1. Detection: Finding modules where code and prompts are out of sync.
    2. Healing: Running 'pdd update' or 'pdd sync' to fix the drift.
    3. Verification: Running structural and churn gates (internal to heal_module).
    4. Commitment: Pushing successful fixes back to the repository.
    """

    # Setup environment for the example
    # PDD_PATH is already set. We simulate a CI environment configuration.
    os.environ["PDD_HEAL_PROMPT_CHURN_MAX_RATIO"] = "5.0"
    os.environ["PDD_HEAL_INVARIANTS_SKIP"] = "fenced_blocks"  # Example of skipping a strict gate
    
    # Create a temporary directory for costs tracking
    output_dir = Path("./output")
    output_dir.mkdir(exist_ok=True)
    cost_csv = output_dir / "example_costs.csv"

    print("--- Scenario 1: Using the high-level main entry point ---")
    # This is how you would typically call it from a CI script (e.g., GitHub Action).
    #
    # modules: List of basenames to check (None = all).
    # budget_cap: Max dollars to spend on LLM calls (float).
    # skip_ci: Pair with diff_base — `skip_ci=False` + `diff_base="origin/<base>...HEAD"`
    #     is PR mode (heal commits run CI; the main loop also enforces the
    #     "skipped module suppresses commit" guard). `skip_ci=True` +
    #     `diff_base="HEAD~1"` is push-to-main mode (commits carry `[skip ci]`;
    #     partial failures are non-blocking). Do NOT mix them — PR diff_base with
    #     skip_ci=True silently relaxes the PR safety guard.
    # diff_base: Git ref to compare against for drift direction. Required in CI:
    #     without it (or if the git diff lookup fails — shallow checkout,
    #     missing ref), the phantom "no run_report" crash filter cannot run in
    #     detect_drift and falls back to the heal_module guard. That guard now
    #     fails closed (returns False) when touched-state is unknown, so the
    #     module is recorded as failed and the heal exits non-zero — surfacing
    #     the configuration error loudly instead of silently dropping real
    #     drift.

    # PR-trigger shape:
    exit_code = main(
        modules=["auth_logic", "data_parser"],
        budget_cap=2.50,
        skip_ci=False,
        diff_base="origin/main...HEAD",
    )
    print(f"Main execution returned exit code: {exit_code}")

    print("\n--- Scenario 2: Granular control using detect_drift and heal_module ---")

    # 1. Detection Phase
    # returns (prompt_drifts, example_drifts). Always pass diff_base when
    # available — the clean-CI reclassification and phantom-crash filter
    # both require it.
    prompt_drifts, example_drifts = detect_drift(
        modules=None, diff_base="origin/main...HEAD"
    )
    
    print(f"Detected {len(prompt_drifts)} prompt drifts and {len(example_drifts)} example drifts.")

    # 2. Healing Phase (Individual modules)
    if prompt_drifts:
        # Prepare the standard CI environment dictionary
        env = _build_ci_env(str(cost_csv))
        
        # Take the first detected drift for demonstration
        target_drift = prompt_drifts[0]
        print(f"Attempting to heal module: {target_drift.basename}")
        
        # heal_module returns:
        # True: Success
        # False: Failed gates or subprocess error
        # None: Intentionally skipped by policy
        success = heal_module(target_drift, env)
        
        if success:
            print(f"Successfully healed {target_drift.basename}")
        elif success is False:
            print(f"Failed to heal {target_drift.basename} (likely tripped a safety gate)")
        else:
            print(f"Healing skipped for {target_drift.basename} based on configuration")

    print("\n--- Cleanup ---")
    if cost_csv.exists():
        cost_csv.unlink()
    print("Example run completed.")

if __name__ == "__main__":
    # Ensure we are in a git repo for the module to function correctly
    try:
        subprocess.run(["git", "rev-parse", "--is-inside-work-tree"], 
                       capture_output=True, check=True)
        run_ci_auto_heal_example()
    except (subprocess.CalledProcessError, FileNotFoundError):
        print("This example must be run inside a Git repository.")