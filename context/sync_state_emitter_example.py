"""
Example of how to use the sync_state_emitter module.

This script demonstrates:
1. Creating a SyncStateEmitter with a module basename and budget.
2. Emitting a sync_start event with file paths.
3. Emitting state_update events as operations progress.
4. Emitting a sync_complete event when done.
5. Cleaning up the state file.

The emitter writes JSON state to a temp file which the server reads
on each poll and includes in the job status response. The frontend
then renders the SyncVisualization component from this state.

Cross-process flow:
  sync subprocess → writes temp file → server reads on poll → includes in response → frontend renders
"""

import os
import time

from pdd.sync_state_emitter import SyncStateEmitter


def main():
    """Simulate a sync workflow with state emissions."""

    # --- 1. Create emitter with module name and budget ---
    # In production, the job manager sets PDD_SYNC_STATE_FILE env var.
    # For this example, we'll let it use the default PID-based path.
    emitter = SyncStateEmitter(basename="calculator", budget=5.0)

    # --- 2. Define file paths ---
    paths = {
        "prompt": "prompts/calculator.prompt",
        "code": "src/calculator.py",
        "example": "examples/calculator_example.py",
        "tests": "tests/test_calculator.py",
    }

    # --- 3. Emit sync_start at the beginning ---
    # Writes: {"operation":"initializing","cost":0,"budget":5.0,"basename":"calculator",...,"status":"running"}
    emitter.emit_sync_start(paths=paths)

    # --- 4. Simulate operations with state updates ---

    # Operation: generate
    emitter.emit_state_update(
        operation="generate",
        cost=0.0,
        paths=paths,
        colors={"prompt": "purple", "code": "cyan", "example": "blue", "tests": "blue"},
    )
    time.sleep(0.5)  # Simulate work

    # Cost updated after generate completes
    emitter.emit_state_update(
        operation="generate",
        cost=0.45,
        paths=paths,
        colors={"prompt": "green", "code": "green", "example": "blue", "tests": "blue"},
    )

    # Operation: example
    emitter.emit_state_update(
        operation="example",
        cost=0.45,
        paths=paths,
        colors={"prompt": "green", "code": "green", "example": "cyan", "tests": "blue"},
    )
    time.sleep(0.3)  # Simulate work

    # Cost updated after example
    emitter.emit_state_update(
        operation="example",
        cost=0.72,
        paths=paths,
        colors={"prompt": "green", "code": "green", "example": "green", "tests": "blue"},
    )

    # Operation: test
    emitter.emit_state_update(
        operation="test",
        cost=0.72,
        paths=paths,
        colors={"prompt": "green", "code": "green", "example": "green", "tests": "magenta"},
    )
    time.sleep(0.3)  # Simulate work

    # Cost updated after test
    emitter.emit_state_update(
        operation="test",
        cost=1.15,
        paths=paths,
        colors={"prompt": "green", "code": "green", "example": "green", "tests": "green"},
    )

    # --- 5. Emit sync_complete when done ---
    # Writes: {"operation":"test","cost":1.15,"budget":5.0,...,"status":"completed"}
    emitter.emit_sync_complete(cost=1.15, success=True)

    # --- 6. Cleanup the state file ---
    # In production, the server or job manager handles cleanup.
    emitter.cleanup()


if __name__ == "__main__":
    main()
