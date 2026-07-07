"""
Example showcasing how to use the agentic_sync_runner module to coordinate
parallel sync operations with dependency-aware scheduling.
"""

from __future__ import annotations

import json
import os
import sys
from pathlib import Path

# Ensure the module can be discovered
sys.path.insert(0, os.path.abspath(os.path.join(os.path.dirname(__file__), "..")))

from pdd.agentic_sync_runner import (
    AsyncSyncRunner,
    build_dep_graph_from_architecture_data,
)


def main() -> None:
    # 1. Initialize output directory relative to this script
    output_dir = Path("./output")
    output_dir.mkdir(parents=True, exist_ok=True)
    
    # Define file paths within the output directory
    architecture_path = output_dir / "architecture.json"
    
    print(f"Initializing example workspace in: {output_dir.resolve()}")

    # 2. Define a mock architecture data structure
    # This architecture defines two modules:
    # - 'auth' (no dependencies)
    # - 'users' (depends on 'auth')
    architecture_data = {
        "modules": [
            {
                "filename": "auth_python.prompt",
                "filepath": "src/auth.py",
                "reason": "Handles secure user authentication",
                "dependencies": [],
                "priority": 1,
                "interface": {
                    "type": "module",
                    "module": {
                        "functions": [
                            {"name": "login", "signature": "def login(u: str, p: str) -> str"}
                        ]
                    }
                }
            },
            {
                "filename": "users_python.prompt",
                "filepath": "src/users.py",
                "reason": "Manages user profiles and depends on auth",
                "dependencies": ["auth_python.prompt"],
                "priority": 2,
                "interface": {
                    "type": "module",
                    "module": {
                        "functions": [
                            {"name": "get_profile", "signature": "def get_profile(token: str) -> dict"}
                        ]
                    }
                }
            }
        ]
    }

    # Write the mock architecture.json file to disk
    with open(architecture_path, "w", encoding="utf-8") as f:
        json.dump(architecture_data, f, indent=2)

    # 3. Build the dependency graph from the architecture data
    # Target basenames are normalized identifiers matching architecture prompt names
    target_basenames = ["auth", "users"]
    
    print("\n--- Step 1: Building Dependency Graph ---")
    dep_result = build_dep_graph_from_architecture_data(
        architecture=architecture_data,
        target_basenames=target_basenames,
        source_name=str(architecture_path)
    )

    print("Resolved Dependency Graph:")
    for module, dependencies in dep_result.graph.items():
        print(f"  - Module '{module}' depends on: {dependencies}")
    
    if dep_result.warnings:
        print(f"Warnings encountered: {dep_result.warnings}")

    # 4. Configure sync options
    # These parameters steer the LLM and the test/conformance verification gates
    sync_options = {
        "local": True,               # Run using local LLM models
        "agentic": True,             # Run in agentic self-repair mode
        "target_coverage": 80.0,     # Enforce 80% unit test coverage
        "max_attempts": 3,           # Retry generation up to 3 times on compiler/conformance failures
        "skip_verify": True          # Skip functional verification for this offline demonstration
    }

    # 5. Initialize the AsyncSyncRunner
    # We pass None for github_info to run in clean offline mode.
    # We specify module_cwds to ensure subprocesses execute within our isolated ./output folder.
    print("\n--- Step 2: Instantiating AsyncSyncRunner ---")
    runner = AsyncSyncRunner(
        basenames=target_basenames,
        dep_graph=dep_result.graph,
        sync_options=sync_options,
        github_info=None,            # Disable live GitHub comment posting
        quiet=False,
        verbose=True,
        issue_url=None,              # Disable resumable state comments
        module_cwds={
            "auth": str(output_dir),
            "users": str(output_dir)
        },
        initial_cost=0.0             # Track baseline cost in USD
    )

    # 6. Run the parallel sync pipeline
    # Since we are running in a mock environment without real underlying prompt contents,
    # the subprocesses will gracefully report that the modules are not fully implemented.
    print("\n--- Step 3: Executing AsyncSyncRunner.run() ---")
    print("Executing dependency-aware scheduling (auth will run first, followed by users)...")
    
    success, message, total_cost = runner.run()

    print("\n--- Execution Summary ---")
    print(f"Overall Success : {success}")
    print(f"Summary Message : {message}")
    print(f"Total Cost (USD): ${total_cost:.4f}")


if __name__ == "__main__":
    main()