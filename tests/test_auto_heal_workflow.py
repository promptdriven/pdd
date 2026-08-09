import os
import subprocess
from pathlib import Path

import yaml


WORKFLOW_PATH = Path(".github/workflows/auto-heal.yml")
GENERATED_BOT = "prompt-driven-github[bot]"


def _load_workflow():
    return yaml.safe_load(WORKFLOW_PATH.read_text())


def _steps():
    return _load_workflow()["jobs"]["heal"]["steps"]


def _step(name):
    for step in _steps():
        if step.get("name") == name:
            return step
    raise AssertionError(f"Missing workflow step: {name}")


def _run_preflight(tmp_path, *, event_name, requester, fork=False, body="/heal"):
    output_path = tmp_path / "github_output"
    env = os.environ.copy()
    env.update(
        {
            "GITHUB_OUTPUT": str(output_path),
            "GH_TOKEN": "unused",
            "EVENT_NAME": event_name,
            "BODY": body,
            "PR_NUMBER_FROM_PR": "123",
            "PR_HEAD_SHA_FROM_PR": "abc123",
            "PR_HEAD_REPO_FROM_PR": "someone/other" if fork else "promptdriven/pdd",
            "REQUESTER_FROM_PR": requester,
            "ISSUE_NUMBER": "123",
            "REQUESTER_FROM_COMMENT": requester,
            "REPO": "promptdriven/pdd",
        }
    )
    result = subprocess.run(
        ["bash", "-c", _step("Pre-flight (validate trigger + resolve PR)")["run"]],
        env=env,
        text=True,
        capture_output=True,
        check=False,
    )
    outputs = {}
    if output_path.exists():
        for line in output_path.read_text().splitlines():
            key, value = line.split("=", 1)
            outputs[key] = value
    return result, outputs


def test_generated_bot_pull_request_is_trusted_app_requester(tmp_path):
    result, outputs = _run_preflight(
        tmp_path,
        event_name="pull_request_target",
        requester=GENERATED_BOT,
    )

    assert result.returncode == 0, result.stderr
    assert outputs["trusted_app_requester"] == "true"
    assert outputs["fork"] == "false"
    assert outputs["requester"] == GENERATED_BOT


def test_trusted_app_requester_is_exact_to_internal_generated_prs(tmp_path):
    human_result, human_outputs = _run_preflight(
        tmp_path,
        event_name="pull_request_target",
        requester="trusted-human",
    )
    fork_result, fork_outputs = _run_preflight(
        tmp_path,
        event_name="pull_request_target",
        requester=GENERATED_BOT,
        fork=True,
    )

    assert human_result.returncode == 0, human_result.stderr
    assert fork_result.returncode == 0, fork_result.stderr
    assert human_outputs["trusted_app_requester"] == "false"
    assert fork_outputs["trusted_app_requester"] == "false"
    assert fork_outputs["fork"] == "true"


def test_authorize_step_allows_only_preflight_trusted_app_requester():
    auth_step = _step("Authorize requester (must be pdd_cloud collaborator)")
    auth_script = auth_step["run"]

    assert "TRUSTED_APP_REQUESTER" in auth_step["env"]
    assert '[ "$TRUSTED_APP_REQUESTER" = "true" ]' in auth_script
    assert "trusted generated-PR App identity" in auth_script
    assert "collaborators/$REQUESTER" in auth_script


def test_privileged_heal_steps_run_for_internal_generated_prs():
    privileged_steps = [
        "Mint pdd_cloud App token",
        "Authorize requester (must be pdd_cloud collaborator)",
        "Authenticate to GCP via Workload Identity Federation",
        "Set up gcloud",
        "Submit Cloud Build (async)",
        "Wait for Cloud Build to complete",
        "Finalize check_run",
    ]

    for name in privileged_steps:
        condition = _step(name)["if"]
        assert "manual_heal_required" not in condition, name
        assert "trusted_app_requester" not in condition, name


def test_workflow_does_not_allowlist_arbitrary_bot_identities():
    auth_script = _step("Authorize requester (must be pdd_cloud collaborator)")["run"]
    workflow_text = WORKFLOW_PATH.read_text()

    assert "*\"[bot]\"" not in auth_script
    assert '"$REQUESTER" == *"[bot]"' not in auth_script
    assert "manual_heal_required" not in workflow_text
    assert "auto-heal waiting for /heal" not in workflow_text
    assert "-f conclusion='action_required'" not in workflow_text
