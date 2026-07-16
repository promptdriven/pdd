"""Execute an allowlisted shell step from the verified source unit workflow."""

from __future__ import annotations

import os
import subprocess
import sys
from pathlib import Path

import yaml


ALLOWED_STEPS = {
    "Provision identity-bound Vitest toolchain",
    "Provision identity-bound Playwright Chromium toolchain",
    "Configure git identity",
    "Install dependencies",
    "Provision and verify protected Linux sandbox",
    "Verify protected cgroup-v2 containment smoke",
    "Verify protected pytest smoke",
    "Verify protected signer containment smoke",
}


def main() -> int:
    """Execute one allowlisted source-workflow shell body."""
    if len(sys.argv) != 2 or sys.argv[1] not in ALLOWED_STEPS:
        print("expected one allowlisted source-workflow step name", file=sys.stderr)
        return 2
    workflow_path = Path(".github/workflows/unit-tests.yml")
    workflow = yaml.safe_load(workflow_path.read_text(encoding="utf-8"))
    steps = workflow["jobs"]["unit-tests"]["steps"]
    matches = [step for step in steps if step.get("name") == sys.argv[1]]
    if len(matches) != 1 or "run" not in matches[0] or "uses" in matches[0]:
        print("source workflow step is not one executable shell step", file=sys.stderr)
        return 3
    step = matches[0]
    if step.get("shell", "bash") != "bash":
        print("source workflow step is not bash", file=sys.stderr)
        return 4
    environment = os.environ.copy()
    environment.update(step.get("env", {}))
    completed = subprocess.run(
        ("bash", "-euo", "pipefail", "-c", step["run"]),
        env=environment,
        check=False,
    )
    return completed.returncode


if __name__ == "__main__":
    raise SystemExit(main())
