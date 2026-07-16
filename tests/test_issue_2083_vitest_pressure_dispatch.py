"""Contracts for the temporary trusted issue-2083 dispatcher."""

from __future__ import annotations

import hashlib
import json
import os
import re
import subprocess
from pathlib import Path

import yaml


ROOT = Path(__file__).resolve().parents[1]
WORKFLOW = ROOT / ".github/workflows/2083-vitest-pressure-dispatch.yml"
SUBJECT = "bd4a250420c3b7aaa50bab6fd73aded271115c71"
SOURCE = "829fb7e2818bb326d31a06cb16bdcb698576b7e6"
SOURCE_FILES = {
    "scripts/ci/run_issue_2083_vitest_pressure.py":
        "1103102193911a8b28588d4efb44eb6a83520c945e94ab7e65c2dfea0d99c469",
    "scripts/ci/issue_2083_vitest_barrier.py":
        "b63e3ce1f2d427ca8588d300b7c85144d23350d46d2cbda6bc1dec8c4b442d02",
    "tests/test_issue_2083_vitest_pressure_diagnostic.py":
        "fb146ad1edbaf3f7fb1267dc7fb0ceee93a94610a9ae1cccfb0f4f2cccfe9e75",
}


def _workflow() -> tuple[dict, str]:
    text = WORKFLOW.read_text(encoding="utf-8")
    return yaml.safe_load(text), text


def _step(name: str) -> dict:
    workflow, _ = _workflow()
    return next(
        step
        for step in workflow["jobs"]["vitest-pressure-diagnostic"]["steps"]
        if step["name"] == name
    )


def test_dispatcher_is_manual_read_only_and_bounded() -> None:
    """Only a manual unprivileged job may execute this temporary dispatcher."""
    workflow, text = _workflow()
    job = workflow["jobs"]["vitest-pressure-diagnostic"]

    assert workflow["on"] == {"workflow_dispatch": None}
    assert workflow["permissions"] == {"contents": "read"}
    assert job["timeout-minutes"] <= 20
    assert "pull_request" not in workflow["on"]
    assert "push" not in workflow["on"]
    assert "secrets." not in text
    assert "id-token" not in text
    assert "gcloud" not in text
    assert re.search(r"\b(?:contents|actions|checks|pull-requests):\s*write\b", text) is None


def test_dispatcher_pins_source_actions_and_failing_node_patch() -> None:
    """All executable inputs must be immutable and reproduce the failing host."""
    workflow, text = _workflow()
    job = workflow["jobs"]["vitest-pressure-diagnostic"]

    assert job["env"]["PDD_ISSUE_2083_SUBJECT_SHA"] == SUBJECT
    assert job["env"]["PDD_ISSUE_2083_SOURCE_SHA"] == SOURCE
    assert job["env"]["PDD_ISSUE_2083_NODE_VERSION"] == "22.23.1"
    assert "10.9.8" in text
    assert "4.1.10" in text
    for path, digest in SOURCE_FILES.items():
        assert path in text
        assert digest in text

    checkout = next(
        step for step in job["steps"] if step["name"] == "Check out immutable source"
    )
    assert checkout["with"]["ref"] == SOURCE
    assert checkout["with"]["persist-credentials"] is False
    assert checkout["with"]["fetch-depth"] == 0
    assert re.fullmatch(r"actions/checkout@[0-9a-f]{40}", checkout["uses"])
    assert "ref: main" not in text
    assert "github.head_ref" not in text
    assert "github.event.pull_request" not in text
    for step in job["steps"]:
        if uses := step.get("uses"):
            assert re.fullmatch(r"actions/[a-z-]+@[0-9a-f]{40}", uses)


def test_dispatcher_gates_bytes_and_constructs_bound_toolchain() -> None:
    """The immutable checkout and runtime roles must be verified before use."""
    workflow, text = _workflow()
    steps = workflow["jobs"]["vitest-pressure-diagnostic"]["steps"]
    names = [step["name"] for step in steps]

    assert "Verify immutable source bytes" in names
    assert "git merge-base --is-ancestor" in text
    assert "git diff --name-only" in text
    assert "git diff --check" in text
    assert "sha256sum --check" in text
    assert text.index("Verify immutable source bytes") < text.index(
        "Install diagnostic dependencies"
    )
    assert '"version": 1' in text
    for role in (
        "launcher", "entrypoint", "dependencies", "native_runtime", "lockfile",
    ):
        assert f'"{role}"' in text
    assert "separators=(\",\", \":\")" in text
    assert "sort_keys=True" in text
    assert "PDD_REAL_VITEST_TOOLCHAIN_MANIFEST" in text
    assert "attest-toolchain" in text
    assert "--toolchain-identity" in text


def test_dispatcher_seals_uploads_then_propagates_exact_run_status() -> None:
    """Evidence upload must precede the final exact-status propagation."""
    workflow, text = _workflow()
    steps = workflow["jobs"]["vitest-pressure-diagnostic"]["steps"]
    names = [step["name"] for step in steps]
    fallback_index = names.index("Always ensure canonical uploadable evidence")
    upload_index = names.index("Always upload sealed diagnostic evidence")
    final_index = names.index("Propagate exact diagnostic status")

    assert "900s" in text
    assert "--expected-source-sha" in text
    assert "--expected-run-id" in text
    assert "--expected-attempt" in text
    assert fallback_index < upload_index < final_index
    assert steps[fallback_index]["if"] == "always()"
    assert steps[upload_index]["if"] == "always()"
    assert steps[final_index]["if"] == "always()"
    assert SOURCE in steps[upload_index]["with"]["name"]
    assert "${{ github.run_id }}" in steps[upload_index]["with"]["name"]
    assert "${{ github.run_attempt }}" in steps[upload_index]["with"]["name"]
    assert steps[upload_index]["with"]["if-no-files-found"] == "error"


def test_early_failure_creates_canonical_redacted_fallback_artifact(
    tmp_path: Path,
) -> None:
    """An early failure must still produce a hashed status-only artifact."""
    fallback = _step("Always ensure canonical uploadable evidence")
    assert "/usr/bin/python3 -I" in fallback["run"]
    sealed = tmp_path / "sealed"
    environment = os.environ.copy()
    environment.update({
        "SEALED_EVIDENCE_DIR": str(sealed),
        "PDD_ISSUE_2083_SUBJECT_SHA": SUBJECT,
        "PDD_ISSUE_2083_SOURCE_SHA": SOURCE,
        "GITHUB_RUN_ID": "12345",
        "GITHUB_RUN_ATTEMPT": "1",
        "NORMAL_SEAL_OUTCOME": "skipped",
        "INITIALIZE_OUTCOME": "success",
        "CHECKOUT_OUTCOME": "failure",
        "SOURCE_OUTCOME": "skipped",
        "PYTHON_OUTCOME": "skipped",
        "NODE_OUTCOME": "skipped",
        "TOOLCHAIN_OUTCOME": "skipped",
        "DEPENDENCIES_OUTCOME": "skipped",
        "SANDBOX_OUTCOME": "skipped",
        "ATTEST_OUTCOME": "skipped",
        "DIAGNOSTIC_OUTCOME": "skipped",
        "UNRELATED_SECRET": "must-not-appear",
    })

    result = subprocess.run(
        ["bash"],
        input=fallback["run"],
        text=True,
        capture_output=True,
        check=False,
        env=environment,
        cwd=ROOT,
    )
    assert result.returncode == 0, result.stderr
    assert {path.name for path in sealed.iterdir()} == {
        "fallback-status.json",
        "manifest.json",
    }

    status_path = sealed / "fallback-status.json"
    manifest_path = sealed / "manifest.json"
    status_raw = status_path.read_text(encoding="utf-8")
    manifest_raw = manifest_path.read_text(encoding="utf-8")
    status = json.loads(status_raw)
    manifest = json.loads(manifest_raw)
    assert status_raw == json.dumps(status, separators=(",", ":"), sort_keys=True)
    assert manifest_raw == json.dumps(manifest, separators=(",", ":"), sort_keys=True)
    assert status["subject_sha"] == SUBJECT
    assert status["source_sha"] == SOURCE
    assert status["run_id"] == "12345"
    assert status["run_attempt"] == 1
    assert status["fallback"] is True
    assert set(status["stages"]) == {
        "attest", "checkout", "dependencies", "diagnostic", "initialize",
        "node", "python", "sandbox", "seal", "source", "toolchain",
    }
    assert all(
        record == {"outcome": record["outcome"]}
        and record["outcome"] in {"success", "failure", "cancelled", "skipped"}
        for record in status["stages"].values()
    )
    assert "must-not-appear" not in status_raw + manifest_raw
    assert str(tmp_path) not in status_raw + manifest_raw
    assert manifest["files"] == {
        "fallback-status.json": {
            "sha256": hashlib.sha256(status_path.read_bytes()).hexdigest(),
            "size": status_path.stat().st_size,
        }
    }


def test_dispatcher_tracks_one_shot_removal_contract() -> None:
    """The temporary dispatcher must explicitly require immediate retirement."""
    workflow, text = _workflow()

    assert "TEMPORARY ONE-SHOT" in workflow["name"]
    assert "ONE-SHOT REMOVAL CONTRACT" in text
    assert "immediately after the first terminal run" in text
    assert "tests/test_issue_2083_vitest_pressure_dispatch.py" in text
    assert "remove both exact preauthorization rules" in text
    assert "must not remain available" in text


def test_every_shell_block_parses_as_bash() -> None:
    """Static validation must cover every shell block in the workflow."""
    workflow, _ = _workflow()
    blocks = [
        step["run"]
        for step in workflow["jobs"]["vitest-pressure-diagnostic"]["steps"]
        if "run" in step
    ]

    assert blocks
    for block in blocks:
        result = subprocess.run(
            ["bash", "-n"], input=block, text=True, capture_output=True, check=False,
        )
        assert result.returncode == 0, result.stderr
