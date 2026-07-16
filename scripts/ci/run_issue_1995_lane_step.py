"""Execute an allowlisted shell step from the verified source unit workflow."""

from __future__ import annotations

import os
import subprocess
import sys
from pathlib import Path


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
    try:
        command = extract_unit_job_command(
            workflow_path.read_text(encoding="utf-8"), sys.argv[1]
        )
    except ValueError as error:
        print(str(error), file=sys.stderr)
        return 3
    completed = subprocess.run(
        ("bash", "-euo", "pipefail", "-c", command),
        env=os.environ.copy(),
        check=False,
    )
    return completed.returncode


def extract_unit_job_command(document: str, step_name: str) -> str:
    """Extract one literal or simply-folded run body from the unit-test job."""
    lines = document.splitlines()
    try:
        job_start = lines.index("  unit-tests:") + 1
    except ValueError as error:
        raise ValueError("unit-tests job is absent") from error
    job_end = next(
        (
            index
            for index in range(job_start, len(lines))
            if lines[index].startswith("  ")
            and not lines[index].startswith("    ")
            and lines[index].rstrip().endswith(":")
        ),
        len(lines),
    )
    marker = f"      - name: {step_name}"
    matches = [index for index in range(job_start, job_end) if lines[index] == marker]
    if len(matches) != 1:
        raise ValueError("expected one allowlisted step in unit-tests job")
    step_end = next(
        (
            index
            for index in range(matches[0] + 1, job_end)
            if lines[index].startswith("      - name:")
        ),
        job_end,
    )
    block = lines[matches[0] : step_end]
    if any(line.startswith("        uses:") for line in block):
        raise ValueError("allowlisted step unexpectedly uses an action")
    run_markers = [
        (index, line.removeprefix("        run: "))
        for index, line in enumerate(block)
        if line.startswith("        run: ")
    ]
    if len(run_markers) != 1:
        raise ValueError("allowlisted step has an unsupported run body")
    run_index, style = run_markers[0]
    if style not in {"|", ">"}:
        if run_index != len(block) - 1 and any(block[run_index + 1 :]):
            raise ValueError("inline allowlisted run body has trailing fields")
        return style
    body_lines = block[run_index + 1 :]
    while body_lines and not body_lines[-1]:
        body_lines.pop()
    if not body_lines or any(
        line and not line.startswith("          ") for line in body_lines
    ):
        raise ValueError("allowlisted run body has unexpected indentation")
    body = [line[10:] if line else "" for line in body_lines]
    if style == "|":
        return "\n".join(body) + "\n"
    if any(not line for line in body):
        raise ValueError("folded allowlisted body unexpectedly contains a paragraph")
    return " ".join(line.strip() for line in body) + "\n"


if __name__ == "__main__":
    raise SystemExit(main())
