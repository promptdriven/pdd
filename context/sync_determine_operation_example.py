import os
import json
import hashlib
from pathlib import Path
from datetime import datetime

# The example is structured to be run from a directory that has the 'pdd'
# module as a subdirectory or in the Python path.
from pdd.sync_determine_operation import (
    sync_determine_operation,
    Fingerprint,
    RunReport
)

def create_file(path: Path, content: str) -> str:
    """Creates a file with given content and returns its SHA256 hash."""
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(content, encoding="utf-8")
    return hashlib.sha256(content.encode("utf-8")).hexdigest()

def main():
    """
    Demonstrates using sync_determine_operation in various scenarios.
    
    This script simulates a project environment by creating necessary files
    and directories inside './output'. It changes the current working
    directory to './output' because sync_determine_operation relies on
    Path.cwd() to locate the .pdd metadata directory.
    """
    basename = "calculator"
    language = "python"
    target_coverage = 10.0

    # --- Setup Simulated Project Environment ---
    output_dir = Path("./output").resolve()
    output_dir.mkdir(exist_ok=True)
    original_cwd = Path.cwd()
    os.chdir(output_dir)
    
    # Define paths relative to the new CWD
    pdd_dir = Path(".pdd")
    meta_dir = pdd_dir / "meta"
    
    print(f"--- Running PDD Sync Analysis for '{basename}' ---")
    print(f"Simulated project root: {output_dir}\n")

    # --- Scenario 1: New PDD Unit ---
    print("SCENARIO 1: New Unit")
    print("  - State: A new prompt file exists. No other files or history.")
    # Cleanup and setup
    for f in (list(output_dir.glob("*.prompt")) + list(output_dir.glob("prompts/*.prompt")) + 
              list(meta_dir.glob("*"))):
        if f.is_file(): f.unlink(missing_ok=True)
    # Create prompts directory and prompt file
    Path("prompts").mkdir(exist_ok=True)
    create_file(Path(f"prompts/{basename}_{language}.prompt"), "Create a function to add two numbers.")
    
    # Determine the operation
    decision = sync_determine_operation(basename, language, target_coverage, log_mode=True)
    print(f"  - Decision: '{decision.operation}'")
    print(f"  - Reason: {decision.reason}\n")


    # --- Scenario 2: Test Failures Detected ---
    print("SCENARIO 2: Test Failure")
    print("  - State: A run report exists indicating test failures.")
    # Setup files
    Path("prompts").mkdir(exist_ok=True)
    prompt_hash = create_file(Path(f"prompts/{basename}_{language}.prompt"), "...")
    code_hash = create_file(Path(f"{basename}.py"), "def add(a, b): return a + b")
    test_hash = create_file(Path(f"test_{basename}.py"), "assert add(2, 2) == 5")
    
    # Create a run report indicating failure (exit_code=1, tests_failed=1)
    # RunReport now includes test_hash to distinguish real test runs from synthetic reports
    run_report = RunReport(datetime.now().isoformat(), 1, 0, 1, 50.0, test_hash=test_hash)
    create_file(meta_dir / f"{basename}_{language}_run.json", json.dumps(run_report.__dict__))
    
    # Determine the operation
    decision = sync_determine_operation(basename, language, target_coverage, log_mode=True)
    print(f"  - Decision: '{decision.operation}'")
    print(f"  - Reason: {decision.reason}\n")


    # --- Scenario 3: Manual Code Change ---
    print("SCENARIO 3: Manual Code Change")
    print("  - State: Code file was modified; its hash no longer matches the fingerprint.")
    # Cleanup and setup
    if (meta_dir / f"{basename}_{language}_run.json").exists():
        (meta_dir / f"{basename}_{language}_run.json").unlink()
    
    Path("prompts").mkdir(exist_ok=True)
    prompt_hash = create_file(Path(f"prompts/{basename}_{language}.prompt"), "...")
    # The hash of the code file as it was last saved by PDD
    original_code_hash = "abc123def456" 
    
    # Create a fingerprint for the original state
    fingerprint = Fingerprint("0.1.0", datetime.now().isoformat(), "generate", prompt_hash, original_code_hash, None, None)
    create_file(meta_dir / f"{basename}_{language}.json", json.dumps(fingerprint.__dict__))
    
    # Now, simulate a user modifying the code file, which changes its hash
    create_file(Path(f"{basename}.py"), "# User added a comment\ndef add(a, b): return a + b")
    
    # Determine the operation
    decision = sync_determine_operation(basename, language, target_coverage, log_mode=True)
    print(f"  - Decision: '{decision.operation}'")
    print(f"  - Reason: {decision.reason}\n")


    # --- Scenario 4: Unit is Synchronized ---
    print("SCENARIO 4: Unit Synchronized")
    print("  - State: All file hashes match the fingerprint and tests passed.")
    # Setup files with matching hashes
    Path("prompts").mkdir(exist_ok=True)
    prompt_hash = create_file(Path(f"prompts/{basename}_{language}.prompt"), "...")
    code_hash = create_file(Path(f"{basename}.py"), "def add(a, b): return a + b")
    example_hash = create_file(Path(f"{basename}_example.py"), "print(add(1,1))")
    test_hash = create_file(Path(f"test_{basename}.py"), "assert add(2, 2) == 4")
    
    # Create a fingerprint that matches the current file hashes
    fingerprint = Fingerprint("0.1.0", datetime.now().isoformat(), "fix", prompt_hash, code_hash, example_hash, test_hash)
    create_file(meta_dir / f"{basename}_{language}.json", json.dumps(fingerprint.__dict__))
    
    # Create a successful run report with test_hash to indicate real test execution
    run_report = RunReport(datetime.now().isoformat(), 0, 1, 0, 100.0, test_hash=test_hash)
    create_file(meta_dir / f"{basename}_{language}_run.json", json.dumps(run_report.__dict__))
    
    # Determine the operation
    decision = sync_determine_operation(basename, language, target_coverage, log_mode=True)
    print(f"  - Decision: '{decision.operation}'")
    print(f"  - Reason: {decision.reason}\n")

    # --- Cleanup ---
    os.chdir(original_cwd)

if __name__ == "__main__":
    main()