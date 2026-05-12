"""
Example demonstrating how to use the ci_drift_heal module.

This module is designed to run in CI pipelines to detect and auto-heal
prompt/example drift in PDD modules. It exposes:

    - DriftInfo: dataclass describing a per-module drift descriptor.
    - HealResult: dataclass describing the outcome of a single heal attempt.
    - PromptRevertError: raised when a prompt cannot be safely reverted.
    - detect_drift(modules, diff_base) -> (prompt_drifts, example_drifts):
        Returns two lists of DriftInfo. The first lists modules whose
        operation is "update"; the second lists everything else
        (example / auto-deps / verify / generate / test / crash).
    - heal_module(drift, env) -> Optional[bool]:
        Heals one drifted module. Returns True (success), False (failure),
        or None (skipped via PDD_HEAL_SYNC_SKIP_MODULES bypass).
    - commit_and_push(healed_modules, skip_ci, checkpoint) -> bool:
        git add/commit/push after a successful heal pass.
    - main(modules, budget_cap, skip_ci, diff_base) -> int:
        CLI entry point. 0 on success (incl. no drift), 1 on failure.

This example mocks every external interaction (subprocess, git, LLMs) so
it is safe to run on any machine without a real PDD workspace.
"""

import os
import sys
from pathlib import Path
from unittest.mock import patch

# Ensure the local pdd package is importable regardless of cwd.
sys.path.insert(0, os.path.join(os.path.dirname(__file__), ".."))

from pdd import ci_drift_heal
from pdd.ci_drift_heal import (
    DriftInfo,
    HealResult,
    PromptRevertError,
)


def demonstrate_drift_info():
    """DriftInfo is a dataclass that captures everything needed to heal a module."""
    print("--- DriftInfo dataclass ---")
    drift = DriftInfo(
        basename="example_module",
        language="python",
        operation="update",
        reason="Code changed without prompt changes",
        code_path="/repo/pdd/example_module.py",
        prompt_path=None,
    )
    print(f"  basename={drift.basename}")
    print(f"  language={drift.language}")
    print(f"  operation={drift.operation}")
    print(f"  reason={drift.reason}")
    print(f"  code_path={drift.code_path}")
    print(f"  estimated_cost={drift.estimated_cost}  (defaults to 0.0)")
    print(f"  extras={drift.extras}  (defaults to empty dict)")


def demonstrate_heal_result():
    """HealResult summarises the outcome of one heal attempt."""
    print()
    print("--- HealResult dataclass ---")
    ok = HealResult(basename="widget", success=True, cost=0.0123, error="")
    bad = HealResult(basename="widget", success=False, error="example regen failed")
    print(f"  success: {ok}")
    print(f"  failure: {bad}")


def demonstrate_detect_drift_no_drift():
    """detect_drift returns ([], []) when nothing has drifted."""
    print()
    print("--- detect_drift (no drift case) ---")

    # Pretend there are no prompt files to discover. detect_drift then
    # has nothing to iterate over and returns two empty lists.
    with patch.object(ci_drift_heal, "_discover_prompt_files", return_value=[]):
        prompt_drifts, example_drifts = ci_drift_heal.detect_drift(
            modules=None, diff_base=None
        )
    print(f"  prompt_drifts={prompt_drifts}")
    print(f"  example_drifts={example_drifts}")
    assert prompt_drifts == [] and example_drifts == [], "expected empty lists"


def demonstrate_detect_drift_with_decision():
    """detect_drift collects modules whose sync_determine_operation reports drift."""
    print()
    print("--- detect_drift (mocked sync_determine_operation) ---")

    fake_prompt = Path("/tmp/fake/prompts/widget_python.prompt")

    def fake_identify(path):
        return ("widget", "python")

    def fake_paths(basename, language):
        return {
            "prompt": Path("/tmp/fake/prompts/widget_python.prompt"),
            "code": Path("/tmp/fake/pdd/widget.py"),
            "example": None,
            "test": None,
        }

    def fake_decision(basename, language):
        return {"operation": "update", "reason": "Prompt stale per fingerprint"}

    with patch.object(ci_drift_heal, "_discover_prompt_files", return_value=[fake_prompt]), \
         patch.object(ci_drift_heal, "_infer_module_identity", side_effect=fake_identify), \
         patch.object(ci_drift_heal, "_get_pdd_file_paths_safe", side_effect=fake_paths), \
         patch.object(ci_drift_heal, "_sync_determine_operation", side_effect=fake_decision):
        prompt_drifts, example_drifts = ci_drift_heal.detect_drift(
            modules=None, diff_base=None
        )

    print(f"  prompt_drifts: {[(d.basename, d.operation, d.reason) for d in prompt_drifts]}")
    print(f"  example_drifts: {example_drifts}")
    assert len(prompt_drifts) == 1 and prompt_drifts[0].operation == "update"


def demonstrate_heal_module_update():
    """heal_module dispatches `update` drifts to `pdd update` plus example refresh."""
    print()
    print("--- heal_module (update operation, mocked subprocess) ---")

    drift = DriftInfo(
        basename="widget",
        language="python",
        operation="update",
        reason="Code changed without prompt",
        prompt_path="/tmp/fake/prompts/widget_python.prompt",
        code_path="/tmp/fake/pdd/widget.py",
    )

    # Mock the subprocess runner so neither pdd nor git is actually invoked.
    # Return True (success) for every command.
    def fake_run(cmd, env, label):
        return True

    # Patch the gates and the metadata-sync helper to report success.
    # `_resolve_prompt_after_update` returns the prompt path after the
    # `pdd update` subprocess completes — return it directly.
    with patch.object(ci_drift_heal, "_run_pdd_command", side_effect=fake_run), \
         patch.object(ci_drift_heal, "_resolve_prompt_after_update", return_value=drift.prompt_path), \
         patch.object(ci_drift_heal, "_enforce_prompt_churn_gate", return_value=True), \
         patch.object(ci_drift_heal, "_enforce_structural_invariants", return_value=True), \
         patch.object(ci_drift_heal, "_run_metadata_sync_safe", return_value=True), \
         patch.object(ci_drift_heal, "_snapshot_metadata_state_for", return_value={}), \
         patch.object(Path, "exists", return_value=True):
        result = ci_drift_heal.heal_module(
            drift, env={"PDD_OUTPUT_COST_PATH": "/tmp/x.csv"}
        )

    print(f"  heal result: {result}  (True = success)")
    assert result is True


def demonstrate_heal_module_example_missing_paths():
    """`example` heal fails closed without both prompt_path and code_path."""
    print()
    print("--- heal_module (example op, missing paths) ---")
    drift = DriftInfo(
        basename="widget",
        language="python",
        operation="example",
        reason="example out of date",
        prompt_path=None,
        code_path=None,
    )
    result = ci_drift_heal.heal_module(drift, env={})
    print(f"  heal result: {result}  (False = fail closed)")
    assert result is False


def demonstrate_heal_module_bypass():
    """PDD_HEAL_SYNC_SKIP_MODULES skips non-update heals for the named module."""
    print()
    print("--- heal_module (operational bypass via env) ---")
    drift = DriftInfo(
        basename="widget",
        language="python",
        operation="example",
        reason="skip me",
        prompt_path="/tmp/p",
        code_path="/tmp/c",
    )
    with patch.dict(os.environ, {"PDD_HEAL_SYNC_SKIP_MODULES": "widget"}):
        result = ci_drift_heal.heal_module(drift, env={})
    print(f"  heal result: {result}  (None = skipped)")
    assert result is None


def demonstrate_commit_and_push_empty():
    """commit_and_push short-circuits to True when no modules were healed."""
    print()
    print("--- commit_and_push (no healed modules) ---")
    ok = ci_drift_heal.commit_and_push(
        healed_modules=[], skip_ci=False, checkpoint=False
    )
    print(f"  commit_and_push([]) returned: {ok}")
    assert ok is True


def demonstrate_main_no_drift():
    """main() returns 0 when there is no drift."""
    print()
    print("--- main (no drift, expect exit 0) ---")
    with patch.object(ci_drift_heal, "detect_drift", return_value=([], [])):
        exit_code = ci_drift_heal.main(
            modules=None,
            budget_cap=None,
            skip_ci=False,
            diff_base=None,
        )
    print(f"  exit code: {exit_code}")
    assert exit_code == 0


def demonstrate_prompt_revert_error():
    """PromptRevertError signals an unsafe-to-commit run."""
    print()
    print("--- PromptRevertError is exposed ---")
    err = PromptRevertError("git checkout failed")
    print(f"  type: {type(err).__name__}, message: {err}")
    assert isinstance(err, RuntimeError)


if __name__ == "__main__":
    print("PDD CI Drift Heal Example")
    print("=========================")

    demonstrate_drift_info()
    demonstrate_heal_result()
    demonstrate_detect_drift_no_drift()
    demonstrate_detect_drift_with_decision()
    demonstrate_heal_module_update()
    demonstrate_heal_module_example_missing_paths()
    demonstrate_heal_module_bypass()
    demonstrate_commit_and_push_empty()
    demonstrate_main_no_drift()
    demonstrate_prompt_revert_error()

    print()
    print("Example completed successfully.")
