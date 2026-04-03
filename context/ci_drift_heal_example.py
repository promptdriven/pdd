"""
Example demonstrating usage of the ci_drift_heal module for PDD CI drift detection
and auto-healing.

This module provides:
- detect_drift(): Scans PDD modules for prompt/example drift (no LLM calls)
- heal_module(): Runs pdd update/sync subprocess to heal a drifted module
- commit_and_push(): Stages, commits, and pushes healed changes via git
- main(): Full orchestration with budget cap and skip-ci support

All external dependencies (PDD internals, subprocess, git) are mocked so this
example runs standalone without a real PDD project.
"""

from __future__ import annotations

import sys
from pathlib import Path
from unittest.mock import patch, MagicMock

# Add project root to path
project_root = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(project_root))

from pdd.ci_drift_heal import (
    DriftInfo,
    detect_drift,
    heal_module,
    commit_and_push,
    main,
)


def demonstrate_drift_info():
    """Show how to create and inspect DriftInfo dataclass instances."""
    print("=== DriftInfo Dataclass ===")

    prompt_drift = DriftInfo(
        basename="auth_service",
        language="python",
        operation="update",
        reason="Prompt hash changed since last sync",
    )
    print(f"Prompt drift: {prompt_drift.basename} ({prompt_drift.operation})")
    print(f"  Reason: {prompt_drift.reason}")

    example_drift = DriftInfo(
        basename="user_api",
        language="python",
        operation="example",
        reason="Example file out of date",
    )
    print(f"Example drift: {example_drift.basename} ({example_drift.operation})")
    print(f"  Reason: {example_drift.reason}")
    print()


def demonstrate_detect_drift():
    """Show detect_drift() with mocked PDD internals.

    detect_drift() scans all prompt files, infers module identity,
    and calls sync_determine_operation to determine if each module
    needs updating. Returns two lists: prompt drifts and example drifts.
    """
    print("=== detect_drift() ===")

    # Mock the internal PDD dependencies
    mock_decision_update = MagicMock()
    mock_decision_update.operation = "update"
    mock_decision_update.reason = "Prompt changed"

    mock_decision_example = MagicMock()
    mock_decision_example.operation = "example"
    mock_decision_example.reason = "Example stale"

    mock_decision_ok = MagicMock()
    mock_decision_ok.operation = "none"

    # Map basenames to decisions
    decisions = {
        "auth": mock_decision_update,
        "api": mock_decision_example,
        "utils": mock_decision_ok,
    }

    def fake_sync_determine(basename, language, target_coverage, log_mode):
        """Simulate sync_determine_operation results."""
        return decisions.get(basename, mock_decision_ok)

    def fake_infer_identity(path):
        """Extract basename and language from prompt path."""
        name = Path(path).stem  # e.g. "auth_python"
        parts = name.rsplit("_", 1)
        return parts[0], parts[1] if len(parts) > 1 else "python"

    mock_prompt_files = [
        Path("prompts/auth_python.prompt"),
        Path("prompts/api_python.prompt"),
        Path("prompts/utils_python.prompt"),
    ]

    with patch("pdd.user_story_tests.discover_prompt_files", return_value=mock_prompt_files), \
         patch("pdd.operation_log.infer_module_identity", side_effect=fake_infer_identity), \
         patch("pdd.sync_determine_operation.sync_determine_operation", side_effect=fake_sync_determine):
        prompt_drifts, example_drifts = detect_drift()

    print(f"Prompt drifts found: {len(prompt_drifts)}")
    for d in prompt_drifts:
        print(f"  - {d.basename} ({d.language}): {d.reason}")

    print(f"Example drifts found: {len(example_drifts)}")
    for d in example_drifts:
        print(f"  - {d.basename} ({d.language}): {d.reason}")
    print()

    # With module filter — only check 'auth'
    print("--- With module filter ['auth'] ---")
    with patch("pdd.user_story_tests.discover_prompt_files", return_value=mock_prompt_files), \
         patch("pdd.operation_log.infer_module_identity", side_effect=fake_infer_identity), \
         patch("pdd.sync_determine_operation.sync_determine_operation", side_effect=fake_sync_determine):
        prompt_drifts, example_drifts = detect_drift(modules=["auth"])

    print(f"Prompt drifts: {len(prompt_drifts)}, Example drifts: {len(example_drifts)}")
    print()


def demonstrate_heal_module():
    """Show heal_module() with mocked subprocess.

    heal_module() runs 'pdd update <basename>' for prompt drift
    or 'pdd sync <basename>' for example drift.
    Environment includes PDD_FORCE=1, CI=1, NO_COLOR=1, and
    PDD_OUTPUT_COST_PATH for cost tracking.
    """
    print("=== heal_module() ===")

    env = {
        "PDD_FORCE": "1",
        "CI": "1",
        "NO_COLOR": "1",
        "PDD_OUTPUT_COST_PATH": "/tmp/cost.csv",
    }

    drift = DriftInfo(
        basename="auth_service",
        language="python",
        operation="update",
        reason="Prompt changed",
    )

    # Mock subprocess.run to simulate successful healing
    mock_result = MagicMock()
    mock_result.returncode = 0
    mock_result.stdout = "Healed successfully"
    mock_result.stderr = ""

    with patch("pdd.ci_drift_heal.subprocess.run", return_value=mock_result) as mock_run:
        success = heal_module(drift, env)

    print(f"Heal result for {drift.basename}: {'success' if success else 'failed'}")
    # Verify the correct command was invoked
    called_cmd = mock_run.call_args[0][0]
    print(f"Command used: {' '.join(called_cmd)}")
    print()

    # Demonstrate example drift healing
    example_drift = DriftInfo(
        basename="user_api",
        language="python",
        operation="example",
        reason="Example stale",
    )

    with patch("pdd.ci_drift_heal.subprocess.run", return_value=mock_result):
        success = heal_module(example_drift, env)

    print(f"Heal result for {example_drift.basename}: {'success' if success else 'failed'}")
    print()


def demonstrate_commit_and_push():
    """Show commit_and_push() with mocked git commands.

    Stages .pdd/, prompts/, examples/ directories, commits with a
    descriptive message, and pushes to the current branch.
    When skip_ci=True, prepends [skip ci] to commit message.
    """
    print("=== commit_and_push() ===")

    mock_result = MagicMock()
    mock_result.returncode = 0
    mock_result.stdout = ""
    mock_result.stderr = ""

    # Simulate that .pdd/ and prompts/ exist
    with patch("pdd.ci_drift_heal.subprocess.run", return_value=mock_result), \
         patch("pdd.ci_drift_heal.Path.exists", return_value=True):
        # diff --cached returns 1 meaning there ARE staged changes
        def side_effect_run(cmd, **kwargs):
            result = MagicMock()
            result.returncode = 1 if cmd == ["git", "diff", "--cached", "--quiet"] else 0
            result.stdout = ""
            result.stderr = ""
            return result

        with patch("pdd.ci_drift_heal.subprocess.run", side_effect=side_effect_run):
            success = commit_and_push(["auth_service", "user_api"], skip_ci=False)
            print(f"Commit & push (no skip-ci): {'success' if success else 'failed'}")

            success = commit_and_push(["auth_service"], skip_ci=True)
            print(f"Commit & push (skip-ci): {'success' if success else 'failed'}")

    # Empty module list
    success = commit_and_push([])
    print(f"Commit with empty list: {'success' if success else 'failed'}")
    print()


def demonstrate_main():
    """Show main() orchestration with mocked dependencies.

    main() coordinates detection, healing, and commit phases.
    Parameters:
      modules: Optional list of basenames to limit scope
      budget_cap: Maximum LLM cost in dollars for healing operations
      skip_ci: If True, prepend [skip ci] to commit message
    Returns exit code 0 on success, 1 on failure.
    """
    print("=== main() — No Drift Scenario ===")

    # Scenario 1: No drift detected
    with patch("pdd.ci_drift_heal.detect_drift", return_value=([], [])):
        exit_code = main(modules=["calculator"])

    print(f"Exit code: {exit_code}")
    print()

    # Scenario 2: Drift detected and healed
    print("=== main() — Drift Detected & Healed ===")
    prompt_drifts = [
        DriftInfo("auth", "python", "update", "Prompt changed"),
    ]
    example_drifts = [
        DriftInfo("api", "python", "example", "Example stale"),
    ]

    mock_subprocess = MagicMock()
    mock_subprocess.returncode = 0
    mock_subprocess.stdout = ""
    mock_subprocess.stderr = ""

    with patch("pdd.ci_drift_heal.detect_drift", return_value=(prompt_drifts, example_drifts)), \
         patch("pdd.ci_drift_heal.heal_module", return_value=True), \
         patch("pdd.ci_drift_heal.commit_and_push", return_value=True), \
         patch("pdd.ci_drift_heal.tempfile.mkstemp", return_value=(5, "/tmp/fake_cost.csv")), \
         patch("pdd.ci_drift_heal.os.close"), \
         patch("pdd.ci_drift_heal.os.unlink"), \
         patch("pdd.ci_drift_heal.Path.write_text"):
        exit_code = main(modules=["auth", "api"], budget_cap=5.0, skip_ci=True)

    print(f"Exit code: {exit_code}")
    print()

    # Scenario 3: Budget cap exceeded
    print("=== main() — Budget Cap Exceeded ===")
    many_drifts_prompt = [
        DriftInfo("mod1", "python", "update", "Changed"),
        DriftInfo("mod2", "python", "update", "Changed"),
    ]

    def heal_with_cost(drift, env):
        """Simulate healing that costs money."""
        return True

    def parse_cost_high(csv_path):
        """Return high cost to trigger budget cap."""
        return 3.0

    with patch("pdd.ci_drift_heal.detect_drift", return_value=(many_drifts_prompt, [])), \
         patch("pdd.ci_drift_heal.heal_module", side_effect=heal_with_cost), \
         patch("pdd.ci_drift_heal._parse_cost_from_csv", side_effect=parse_cost_high), \
         patch("pdd.ci_drift_heal.commit_and_push", return_value=True), \
         patch("pdd.ci_drift_heal.tempfile.mkstemp", return_value=(5, "/tmp/fake_cost.csv")), \
         patch("pdd.ci_drift_heal.os.close"), \
         patch("pdd.ci_drift_heal.os.unlink"), \
         patch("pdd.ci_drift_heal.Path.write_text"):
        exit_code = main(budget_cap=2.0)

    print(f"Exit code: {exit_code}")
    print()


if __name__ == "__main__":
    demonstrate_drift_info()
    demonstrate_detect_drift()
    demonstrate_heal_module()
    demonstrate_commit_and_push()
    demonstrate_main()
    print("All demonstrations completed successfully.")
