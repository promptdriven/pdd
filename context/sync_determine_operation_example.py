"""
Example demonstrating PDD state analysis and deterministic operation selection
using the `pdd.sync_determine_operation` module.

This script simulates different lifecycle stages of a PDD unit (from fresh
creation to stale tests and coverage gaps) to show how the decision-making
engine operates.
"""

import json
import os
import sys
import shutil
from pathlib import Path

# Import the core decision-making utilities from the PDD module
from pdd.sync_determine_operation import (
    get_pdd_file_paths,
    sync_determine_operation,
    Fingerprint,
    RunReport,
    SyncDecision
)


def setup_mock_project() -> tuple[Path, Path]:
    """
    Sets up a temporary local PDD project structure in the ./output folder.
    
    Returns:
        A tuple of (prompts_dir, meta_dir) paths.
    """
    # Define and create output directories
    output_root = Path("./output")
    prompts_dir = output_root / "prompts"
    pdd_dir = Path.cwd() / ".pdd"
    meta_dir = pdd_dir / "meta"

    prompts_dir.mkdir(parents=True, exist_ok=True)
    meta_dir.mkdir(parents=True, exist_ok=True)

    # 1. Create a mock prompt file
    prompt_file = prompts_dir / "calculator_Python.prompt"
    prompt_file.write_text(
        "Generate a simple Calculator class with add and subtract methods.\n"
        "Ensure all inputs are validated.",
        encoding="utf-8"
    )

    # 2. Create a basic .pddrc configuration to help with path routing
    pddrc_file = Path.cwd() / ".pddrc"
    pddrc_config = {
        "contexts": {
            "default": {
                "defaults": {
                    "prompts_dir": "output/prompts",
                    "generate_output_path": "output/src/",
                    "test_output_path": "output/tests/"
                }
            }
        }
    }
    pddrc_file.write_text(json.dumps(pddrc_config, indent=2), encoding="utf-8")

    return prompts_dir, meta_dir


def cleanup_mock_project(prompts_dir: Path, meta_dir: Path) -> None:
    """Cleans up the mocked configuration files and directories."""
    # Clean up generated output folder
    if Path("./output").exists():
        shutil.rmtree("./output")
        
    # Clean up local .pdd metadata
    pdd_dir = Path.cwd() / ".pdd"
    if pdd_dir.exists():
        shutil.rmtree(pdd_dir)

    # Clean up local .pddrc configuration
    pddrc_file = Path.cwd() / ".pddrc"
    if pddrc_file.exists():
        pddrc_file.unlink()


def print_decision(scenario: str, decision: SyncDecision) -> None:
    """Pretty prints the SyncDecision output."""
    print(f"\n=== Scenario: {scenario} ===")
    print(f"Recommended Operation : {decision.operation.upper()}")
    print(f"Reason                : {decision.reason}")
    print(f"Confidence (0.0-1.0)  : {decision.confidence:.2f}")
    print(f"Estimated Cost (USD)  : ${decision.estimated_cost:.4f}")
    if decision.details:
        print(f"Details               : {json.dumps(decision.details, indent=2)}")


def main() -> None:
    # Ensure standard PDD_PATH setup is respected. 
    # (The environment is pre-configured, but we derive the mock directories relative to CWD)
    prompts_dir, meta_dir = setup_mock_project()

    basename = "calculator"
    language = "Python"
    target_coverage = 80.0  # target coverage percentage

    print(f"Starting sync decision example for module '{basename}' [{language}]")
    print(f"Target Test Coverage: {target_coverage}%")

    # =================Scenario 1: New Module (Untracked)=================
    # In this scenario, a prompt file exists, but there are no code, tests, 
    # examples, or metadata fingerprints yet.
    decision_new = sync_determine_operation(
        basename=basename,
        language=language,
        target_coverage=target_coverage,
        prompts_dir=str(prompts_dir),
        log_mode=True  # Bypasses system-level file-locking for read-only analysis
    )
    print_decision("New Module (Untracked Prompt)", decision_new)


    # =================Scenario 2: Code Exists but Stale Run Report=================
    # Resolve the expected file paths for our unit so we can mock its outputs
    paths = get_pdd_file_paths(basename, language, prompts_dir=str(prompts_dir))
    
    # Ensure parent folders exist before writing files
    paths["code"].parent.mkdir(parents=True, exist_ok=True)
    paths["example"].parent.mkdir(parents=True, exist_ok=True)
    paths["test"].parent.mkdir(parents=True, exist_ok=True)

    # Write dummy implementations representing a completed cycle
    paths["code"].write_text("class Calculator:\n    def add(self, a, b): return a + b", encoding="utf-8")
    paths["example"].write_text("from output.src.calculator import Calculator\nprint(Calculator().add(1, 2))", encoding="utf-8")
    paths["test"].write_text("from output.src.calculator import Calculator\ndef test_add(): assert Calculator().add(1, 2) == 3", encoding="utf-8")

    # Create a Fingerprint detailing successful code generation
    fingerprint_data = {
        "pdd_version": "1.0.0",
        "timestamp": "2023-10-27T10:00:00Z",
        "command": "generate",
        "prompt_hash": "mock_prompt_sha256_hash",
        "code_hash": "mock_code_sha256_hash",
        "example_hash": "mock_example_sha256_hash",
        "test_hash": "mock_test_sha256_hash"
    }
    
    fp_file = meta_dir / f"calculator_python.json"
    fp_file.write_text(json.dumps(fingerprint_data, indent=2), encoding="utf-8")

    # Create a RunReport indicating low test coverage (e.g. 50% vs target 80%)
    run_report_data = {
        "timestamp": "2023-10-27T10:05:00Z",
        "exit_code": 0,
        "tests_passed": 1,
        "tests_failed": 0,
        "coverage": 50.0,  # Coverage gap
        "test_hash": "mock_test_sha256_hash"
    }
    
    rr_file = meta_dir / f"calculator_python_run.json"
    rr_file.write_text(json.dumps(run_report_data, indent=2), encoding="utf-8")

    # Re-evaluate. Because tests pass but coverage (50%) is below the target (80%),
    # the decision engine should request test extension.
    decision_low_coverage = sync_determine_operation(
        basename=basename,
        language=language,
        target_coverage=target_coverage,
        prompts_dir=str(prompts_dir),
        log_mode=True
    )
    print_decision("Low Coverage (Targeting Test Extension)", decision_low_coverage)


    # =================Scenario 3: Runtime Crashes in Example=================
    # Simulating a failing runtime execution context (non-zero exit code)
    run_report_failed = {
        "timestamp": "2023-10-27T10:10:00Z",
        "exit_code": 1,  # Non-zero exit code (Crash)
        "tests_passed": 0,
        "tests_failed": 0,
        "coverage": 0.0,
        "test_hash": "mock_test_sha256_hash"
    }
    rr_file.write_text(json.dumps(run_report_failed, indent=2), encoding="utf-8")

    decision_crash = sync_determine_operation(
        basename=basename,
        language=language,
        target_coverage=target_coverage,
        prompts_dir=str(prompts_dir),
        log_mode=True
    )
    print_decision("Runtime Crash Recovery Mode", decision_crash)


    # Clean up mock directories to leave workspace pristine
    cleanup_mock_project(prompts_dir, meta_dir)
    print("\nWorkspace cleaned successfully. Example completed.")


if __name__ == "__main__":
    main()