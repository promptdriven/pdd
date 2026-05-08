"""Example showing how to use AsyncSyncRunner for parallel module sync."""

import sys
from pathlib import Path
from unittest.mock import patch

# Prepend the project root to sys.path so the local checkout always wins
# over an older installed `pdd` package (e.g. one missing recently-added
# helpers like `_is_nonfatal_warning`).
project_root = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(project_root))

from pdd.agentic_sync_runner import (
    AsyncSyncRunner,
    ModuleState,
    build_dep_graph_from_architecture,
    _format_duration,
    _is_nonfatal_warning,
    _parse_cost_from_csv,
)


def main():
    """Demonstrate the AsyncSyncRunner with mocked subprocess calls."""

    # --- Dependency Graph Building ---
    # build_dep_graph_from_architecture reads architecture.json and filters
    # to only include dependencies within the target basenames.
    print("--- Dependency Graph Example ---")
    # With a real architecture.json:
    # result = build_dep_graph_from_architecture(Path("architecture.json"), ["auth", "user_service", "api"])
    # result.graph    -> {"auth": [], "user_service": ["auth"], "api": ["auth", "user_service"]}
    # result.warnings -> ["architecture.json: module 'api' depends on 'logger' which is outside the target sync set ..."]
    print("(would load architecture.json and produce a DepGraphFromArchitectureResult)")

    # --- Module State Tracking ---
    state = ModuleState()
    print(f"Initial state: {state.status}")  # "pending"

    # --- Duration Formatting (per spec: 'Xs' or 'Xm Ys') ---
    print(f"45 seconds: {_format_duration(100.0, 145.0)}")   # "45s"
    print(f"2 minutes: {_format_duration(0.0, 125.0)}")      # "2m 5s"


    # --- Runner Execution (mocked) ---
    print("\n--- AsyncSyncRunner Example ---")

    # Define modules and their dependencies
    basenames = ["db_schema", "models", "api_orders", "api_users"]
    dep_graph = {
        "db_schema": [],
        "models": ["db_schema"],
        "api_orders": ["models"],
        "api_users": ["models"],
    }

    # Sync options passed through to each subprocess
    sync_options = {
        "budget": 5.0,
        "skip_verify": False,
        "skip_tests": False,
        "agentic": True,
        "no_steer": True,
    }

    # GitHub info for live comment updates (set to None to disable)
    # github_info = {
    #     "owner": "example",
    #     "repo": "myproject",
    #     "issue_number": 42,
    #     "cwd": Path.cwd(),
    # }

    runner = AsyncSyncRunner(
        basenames=basenames,
        dep_graph=dep_graph,
        sync_options=sync_options,
        github_info=None,        # Disable GitHub comments for demo
        quiet=True,
        verbose=False,
        issue_url=None,          # None disables resumability/state file
        module_cwds=None,        # Defaults all modules to project_root
        initial_cost=0.0,
    )

    # Mock the per-module sync. `_sync_one_module` returns
    # (success, cost, error_message). Returning success keeps the
    # runner on the happy path.
    fake_costs = {
        "db_schema": 0.12, "models": 0.08, "api_orders": 0.15, "api_users": 0.10,
    }

    def fake_sync(basename):
        return (True, fake_costs.get(basename, 0.0), "")

    with patch.object(runner, "_sync_one_module", side_effect=fake_sync), \
         patch.object(runner, "_update_github_comment"), \
         patch.object(runner, "_update_github_comment_throttled"):
        # --- EXECUTE THE RUNNER ---
        success, message, total_cost = runner.run()

    print(f"Success    : {success}")
    print(f"Total Cost : ${total_cost:.2f}")
    print(f"Message    : {message}")

    # Show final module states
    print("\n--- Module States ---")
    for name, state in runner.module_states.items():
        print(f"  {name}: {state.status} (cost: ${state.cost:.2f})")
    print(
        "A failed module blocks only modules that depend on it; unrelated "
        "modules continue when their own dependencies are satisfied. The "
        "blocked set is transitive, and total-budget exhaustion still stops "
        "all new scheduling."
    )

    # --- Comment Body Preview ---
    # `_build_comment_body(issue_number)` renders the markdown table that
    # is posted/patched to the GitHub issue comment.
    print("\n--- GitHub Comment Preview ---")
    body = runner._build_comment_body(42)
    print(body)

    # --- Failure-summary contract (issue #1399) ---
    # The error string for a failed module always leads with a deterministic
    # failure reason (`Overall status: Failed` line if present, else
    # `Exit code N`). High-signal lines (containing
    # error/failed/traceback/exception/abort) follow, with known nonfatal
    # preprocessing warnings filtered out:
    print("\n--- Nonfatal-warning filter ---")
    print(_is_nonfatal_warning('Warning: ContentSelector failed for select="class:Foo"'))  # True
    print(_is_nonfatal_warning("RuntimeError: real failure"))                              # False

    # --- Cost CSV parsing ---
    # `_parse_cost_from_csv` reads the file pointed to by PDD_OUTPUT_COST_PATH
    # and sums the `cost` column. Returns 0.0 when the path is missing.
    print(f"Cost from missing file: ${_parse_cost_from_csv('/tmp/nonexistent.csv'):.2f}")


if __name__ == "__main__":
    main()
