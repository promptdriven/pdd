import json
import os
import sys
from pathlib import Path

from pdd.checkup_gates import (
    discover_gates,
    run_gates,
    gate_results_to_findings
)

def main():
    """
    Example demonstrating how to use the checkup_gates module to discover,
    execute, and convert deterministic gates into actionable review findings.
    """
    # Setup a dummy worktree in the output directory
    worktree = Path("./output/mock_repo")
    worktree.mkdir(parents=True, exist_ok=True)
    
    # 1. Create a dummy Python file with a syntax error to trigger a failure
    # The py-compile gate will catch this syntax error without writing .pyc files.
    py_file = worktree / "bad_syntax.py"
    py_file.write_text("def missing_colon()\n    pass\n", encoding="utf-8")
    
    # 2. Create a dummy package.json with a valid deterministic gate
    pkg_json = worktree / "package.json"
    pkg_json.write_text(json.dumps({
        "scripts": {
            "prettier:check": "npx --no-install prettier --check ."
        }
    }), encoding="utf-8")
    
    # Simulate a PR diff that touched these files
    changed_files = ["bad_syntax.py", "package.json"]
    
    print(f"Discovering gates in {worktree}...")
    # discover_gates scans the worktree and changed_files to find applicable local checks
    gates = discover_gates(worktree, changed_files=changed_files)
    
    print(f"Discovered {len(gates)} gates:")
    for g in gates:
        print(f" - {g.name}: {' '.join(g.cmd)}")
        
    artifacts_dir = Path("./output/artifacts")
    artifacts_dir.mkdir(parents=True, exist_ok=True)
    
    print("\nRunning gates...")
    # run_gates executes the subprocesses in the worktree securely
    results = run_gates(
        worktree=worktree,
        gates=gates,
        artifacts_dir=artifacts_dir,
        round_number=1,
        mode="example"
    )
    
    print("\nGate Results:")
    for res in results:
        status = "PASSED" if res.passed else "FAILED"
        print(f" - {res.gate.name}: {status} (Exit Code: {res.exit_code})")
        
    print("\nConverting failures to findings...")
    # gate_results_to_findings converts failures into ReviewFinding objects
    # that match the LLM reviewer output format.
    findings = gate_results_to_findings(results, round_number=1)
    
    if not findings:
        print("No findings (all gates passed).")
    else:
        for f in findings:
            print(f"[{f.severity.upper()}] {f.reviewer} at {f.location}")
            print(f"  Finding: {f.finding}")
            print(f"  Fix: {f.required_fix}")

if __name__ == "__main__":
    main()