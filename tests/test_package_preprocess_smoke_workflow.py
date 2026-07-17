"""Policy contracts for the Package Preprocess Smoke workflow job."""

from __future__ import annotations

from pathlib import Path

import yaml


WORKFLOW_PATH = (
    Path(__file__).resolve().parents[1] / ".github" / "workflows" / "unit-tests.yml"
)
JOB_ID = "package-preprocess-smoke"
PROVISION_STEP_NAME = "Provision identity-bound Playwright Chromium toolchain"


def test_package_preprocess_resolves_playwright_native_runtime_paths() -> None:
    """The package smoke manifest must bind resolved native library identities."""
    workflow = yaml.safe_load(WORKFLOW_PATH.read_text(encoding="utf-8"))
    job = workflow["jobs"][JOB_ID]
    steps = [step for step in job["steps"] if step.get("name") == PROVISION_STEP_NAME]

    assert len(steps) == 1
    source = steps[0]["run"]
    assert "resolved = Path(match.group(1)).resolve(strict=True)" in source
    assert "if match and resolved.is_file():" in source
    assert "native.add(str(resolved))" in source
