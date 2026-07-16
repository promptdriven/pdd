"""Security contracts for Cloud Batch runtime credential handling."""

from __future__ import annotations

import importlib.util
import json
import subprocess
import urllib.error
import urllib.request
from pathlib import Path
from types import ModuleType

import pytest


REPO_ROOT = Path(__file__).resolve().parents[1]
CLOUD_BATCH = REPO_ROOT / "ci" / "cloud-batch"
TEMPLATES = sorted(CLOUD_BATCH.glob("job-template*.json"))


def _load_script(name: str, filename: str) -> ModuleType:
    spec = importlib.util.spec_from_file_location(name, CLOUD_BATCH / filename)
    assert spec and spec.loader
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def test_job_templates_pass_resource_names_not_secret_variables() -> None:
    assert TEMPLATES
    for template in TEMPLATES:
        document = json.loads(template.read_text(encoding="utf-8"))
        serialized = json.dumps(document)
        assert "secretVariables" not in serialized

        variables = document["taskGroups"][0]["taskSpec"]["runnables"][0][
            "environment"
        ]["variables"]
        container = document["taskGroups"][0]["taskSpec"]["runnables"][0][
            "container"
        ]
        assert container["entrypoint"] == "/runtime-secrets.py"
        resources = {
            key: value
            for key, value in variables.items()
            if key.endswith("_SECRET_RESOURCE")
        }
        assert resources
        assert all(value == "{{" + key + "}}" for key, value in resources.items())


def test_runtime_loader_fetches_only_task_required_credentials() -> None:
    loader = _load_script("cloud_batch_runtime_secrets", "runtime-secrets.py")
    marker = "payload-" + "never-render"
    environment = {
        "BATCH_TASK_INDEX": "0",
        "GCS_HMAC_ACCESS_KEY_ID_SECRET_RESOURCE": (
            "projects/example/secrets/GCS_HMAC_ACCESS_KEY_ID/versions/1"
        ),
        "GCS_HMAC_SECRET_ACCESS_KEY_SECRET_RESOURCE": (
            "projects/example/secrets/GCS_HMAC_SECRET_ACCESS_KEY/versions/1"
        ),
        "OPENAI_API_KEY_SECRET_RESOURCE": (
            "projects/example/secrets/OPENAI_API_KEY/versions/1"
        ),
        "GITHUB_CLIENT_ID_SECRET_RESOURCE": (
            "projects/example/secrets/github-client-id/versions/1"
        ),
        "CLAUDE_CODE_OAUTH_TOKEN_SECRET_RESOURCE": (
            "projects/example/secrets/CLAUDE_CODE_OAUTH_TOKEN/versions/1"
        ),
        "PDD_REFRESH_TOKEN_SECRET_RESOURCE": (
            "projects/example/secrets/pdd-refresh-token/versions/1"
        ),
    }
    fetched: list[str] = []

    def fetch(resource: str) -> str:
        fetched.append(resource)
        return marker

    loaded = loader.load_required_secrets(
        environment,
        trusted_project="example",
        secret_fetcher=fetch,
    )

    assert set(loaded) == {
        "GCS_HMAC_ACCESS_KEY_ID",
        "GCS_HMAC_SECRET_ACCESS_KEY",
        "OPENAI_API_KEY",
        "GITHUB_CLIENT_ID",
        "CLAUDE_CODE_OAUTH_TOKEN",
    }
    assert environment["PDD_REFRESH_TOKEN_SECRET_RESOURCE"] not in fetched


@pytest.mark.parametrize("failure", [PermissionError("denied"), ValueError("bad")])
def test_runtime_loader_fails_closed_without_echoing_payload(
    failure: Exception, capsys: pytest.CaptureFixture[str]
) -> None:
    loader = _load_script("cloud_batch_runtime_failure", "runtime-secrets.py")
    marker = "payload-" + "never-render"
    environment = {
        "BATCH_TASK_INDEX": "68",
        "FIREBASE_API_KEY_SECRET_RESOURCE": (
            "projects/example/secrets/staging-firebase-api-key/versions/1"
        ),
        "GITHUB_CLIENT_ID_SECRET_RESOURCE": (
            "projects/example/secrets/github-client-id/versions/1"
        ),
        "PDD_REFRESH_TOKEN_SECRET_RESOURCE": (
            "projects/example/secrets/pdd-refresh-token/versions/1"
        ),
    }

    def fetch(_resource: str) -> str:
        raise failure

    with pytest.raises(loader.SecretLoadError, match="required runtime credential") as exc:
        loader.load_required_secrets(
            environment,
            trusted_project="example",
            secret_fetcher=fetch,
        )

    captured = capsys.readouterr()
    output = captured.out + captured.err + str(exc.value)
    assert marker not in output
    assert "denied" not in output
    assert "bad" not in output


def test_runtime_loader_rejects_malformed_secret_payload(monkeypatch: pytest.MonkeyPatch) -> None:
    loader = _load_script("cloud_batch_runtime_malformed", "runtime-secrets.py")
    documents = iter(
        [
            {"access_token": "workload-token"},
            {"payload": {"data": "not valid base64"}},
        ]
    )
    monkeypatch.setattr(
        loader,
        "_read_json",
        lambda _request, **_kwargs: next(documents),
    )

    with pytest.raises(loader.SecretLoadError, match="required runtime credential") as exc:
        loader.fetch_secret(
            "projects/example/secrets/provider-key/versions/1"
        )

    assert "base64" not in str(exc.value)


def test_runtime_loader_exec_boundary_keeps_payload_out_of_output_and_files(
    tmp_path: Path, capsys: pytest.CaptureFixture[str]
) -> None:
    loader = _load_script("cloud_batch_runtime_exec", "runtime-secrets.py")
    marker = "payload-" + "never-render"
    environment = {
        "BATCH_TASK_INDEX": "76",
        "OPENAI_API_KEY_SECRET_RESOURCE": (
            "projects/example/secrets/provider-key/versions/1"
        ),
        "RESULTS_DIR": str(tmp_path),
    }
    called: list[tuple[list[str], dict[str, str]]] = []

    def exec_process(command: list[str], child_env: dict[str, str]) -> None:
        called.append((command, child_env))

    loader.exec_with_runtime_secrets(
        ["/entrypoint.sh"],
        environment,
        secret_fetcher=lambda _resource: marker,
        exec_process=exec_process,
    )

    assert called == [(["/entrypoint.sh"], environment)]
    assert marker not in capsys.readouterr().out
    assert all(
        marker not in path.read_text(errors="replace")
        for path in tmp_path.glob("**/*")
        if path.is_file()
    )


def test_firebase_exchange_keeps_credentials_out_of_command_arguments() -> None:
    """The post-load JWT exchange must consume inherited environment only."""
    entrypoint = (CLOUD_BATCH / "entrypoint.sh").read_text(encoding="utf-8")
    dockerfile = (CLOUD_BATCH / "Dockerfile").read_text(encoding="utf-8")

    assert "python3 /firebase-token-exchange.py" in entrypoint
    assert "securetoken.googleapis.com/v1/token?key=${FIREBASE_API_KEY}" not in entrypoint
    assert "refresh_token=${PDD_REFRESH_TOKEN}" not in entrypoint
    assert "COPY ci/cloud-batch/firebase-token-exchange.py" in dockerfile


def test_firebase_exchange_rejects_redirects_without_rendering_credentials() -> None:
    """The in-process refresh exchange must stay on the exact provider URL."""
    exchange = _load_script(
        "cloud_batch_firebase_exchange_redirect", "firebase-token-exchange.py"
    )
    marker = "payload-" + "never-render"

    class RedirectedResponse:
        status = 200

        def __enter__(self):
            return self

        def __exit__(self, *_args):
            return None

        @staticmethod
        def geturl() -> str:
            return "https://redirect.invalid/token"

        @staticmethod
        def read() -> bytes:
            return b"{}"

    with pytest.raises(RuntimeError, match="token exchange transport failed") as exc:
        exchange.exchange_token(
            marker,
            marker,
            opener=lambda *_args, **_kwargs: RedirectedResponse(),
        )
    assert marker not in str(exc.value)

    request = urllib.request.Request("https://securetoken.googleapis.com/v1/token")
    with pytest.raises(urllib.error.HTTPError, match="redirects disabled"):
        exchange._NoRedirectHandler().redirect_request(
            request,
            None,
            307,
            "redirect",
            {},
            "https://redirect.invalid/token",
        )


def test_log_verifier_reports_only_fingerprint_on_match(tmp_path: Path) -> None:
    verifier = _load_script("cloud_batch_secret_verifier", "verify-secret-logs.py")
    marker = "payload-" + "never-render"
    log_file = tmp_path / "batch.log"
    log_file.write_text(f"prefix {marker} suffix", encoding="utf-8")

    findings = verifier.find_matches(
        {"projects/example/secrets/provider-key/versions/latest": marker},
        [log_file.read_text(encoding="utf-8")],
    )

    assert len(findings) == 1
    finding = findings[0]
    assert finding.startswith("sha256:")
    assert marker not in finding


def test_log_verifier_fails_closed_when_attributable_logs_are_absent() -> None:
    verifier = _load_script("cloud_batch_secret_verifier_empty", "verify-secret-logs.py")

    with pytest.raises(RuntimeError, match="attributable Batch logs unavailable"):
        verifier._job_logs(
            {"job-name": ("job-uid", 1)},
            "example",
            "us-central1",
            command_runner=lambda _command: "[]",
        )


@pytest.mark.parametrize(
    "resource_key,resource",
    [
        (
            "FIREBASE_API_KEY_SECRET_RESOURCE",
            "projects/other-project/secrets/staging-firebase-api-key/versions/7",
        ),
        (
            "FIREBASE_API_KEY_SECRET_RESOURCE",
            "projects/trusted-project/secrets/wrong-name/versions/7",
        ),
        (
            "FIREBASE_API_KEY_SECRET_RESOURCE",
            "projects/trusted-project/secrets/staging-firebase-api-key/versions/latest",
        ),
    ],
)
def test_runtime_loader_rejects_wrong_identity_or_mutable_version(
    resource_key: str, resource: str
) -> None:
    loader = _load_script("cloud_batch_runtime_identity", "runtime-secrets.py")
    environment = {
        "BATCH_TASK_INDEX": "68",
        "FIREBASE_API_KEY_SECRET_RESOURCE": (
            "projects/trusted-project/secrets/staging-firebase-api-key/versions/7"
        ),
        "GITHUB_CLIENT_ID_SECRET_RESOURCE": (
            "projects/trusted-project/secrets/github-client-id/versions/4"
        ),
        "PDD_REFRESH_TOKEN_SECRET_RESOURCE": (
            "projects/trusted-project/secrets/pdd-refresh-token/versions/11"
        ),
    }
    environment[resource_key] = resource

    with pytest.raises(loader.SecretLoadError, match="configuration invalid"):
        loader.load_required_secrets(
            environment,
            trusted_project="trusted-project",
            secret_fetcher=lambda _resource: "synthetic-value",
        )


def test_secret_manager_reader_rejects_redirected_response() -> None:
    loader = _load_script("cloud_batch_runtime_redirect", "runtime-secrets.py")
    request = urllib.request.Request(
        "https://secretmanager.googleapis.com/v1/projects/trusted-project/"
        "secrets/provider-key/versions/3:access",
        headers={"Authorization": "Bearer synthetic"},
    )

    class RedirectedResponse:
        status = 200

        def __enter__(self):
            return self

        def __exit__(self, *_args):
            return None

        @staticmethod
        def geturl() -> str:
            return "https://redirect.invalid/credential"

        @staticmethod
        def read() -> bytes:
            return b"{}"

    with pytest.raises(loader.SecretLoadError, match="unavailable"):
        loader._read_json(
            request,
            expected_scheme="https",
            expected_host="secretmanager.googleapis.com",
            opener=lambda *_args, **_kwargs: RedirectedResponse(),
        )

    with pytest.raises(urllib.error.HTTPError, match="redirects disabled"):
        loader._NoRedirectHandler().redirect_request(
            request,
            None,
            302,
            "redirect",
            {},
            "https://redirect.invalid/credential",
        )


def _complete_log_entries(project: str, uid: str, task_count: int) -> list[dict]:
    group_name = (
        f"projects/{project}/locations/us-central1/jobs/job-name/"
        "taskGroups/group0"
    )
    resource = {
        "type": "batch.googleapis.com/Job",
        "labels": {
            "job_id": uid,
            "location": "us-central1-b",
            "resource_container": project,
        },
    }
    entries = []
    for task_index in range(task_count):
        task_id = f"{uid}-group0-{task_index}"
        entries.append(
            {
                "labels": {
                    "job_uid": uid,
                    "task_group_name": group_name,
                    "task_id": task_id,
                },
                "logName": f"projects/{project}/logs/batch_task_logs",
                "resource": resource,
            }
        )
    entries.append(
        {
            "labels": {
                "job_uid": uid,
                "task_group_name": group_name,
                "task_id": "action/STARTUP/0/0/group0",
            },
            "logName": f"projects/{project}/logs/batch_agent_logs",
            "resource": resource,
        }
    )
    return entries


def test_log_verifier_requires_every_task_and_unbounded_pagination() -> None:
    verifier = _load_script("cloud_batch_secret_verifier_complete", "verify-secret-logs.py")
    commands: list[list[str]] = []
    entries = _complete_log_entries("trusted-project", "job-uid", 2)
    entries = [
        entry
        for entry in entries
        if entry["labels"]["task_id"] != "job-uid-group0-1"
    ]

    def run(command: list[str]) -> str:
        commands.append(command)
        return json.dumps(entries)

    with pytest.raises(RuntimeError, match="attributable Batch logs incomplete"):
        verifier._job_logs(
            {"job-name": ("job-uid", 2)},
            "trusted-project",
            "us-central1",
            command_runner=run,
        )

    assert all(not argument.startswith("--limit") for command in commands for argument in command)


def test_log_verifier_accepts_complete_exact_job_accounting() -> None:
    verifier = _load_script("cloud_batch_secret_verifier_exact", "verify-secret-logs.py")
    entries = _complete_log_entries("trusted-project", "job-uid", 2)

    logs = verifier._job_logs(
        {"job-name": ("job-uid", 2)},
        "trusted-project",
        "us-central1",
        command_runner=lambda _command: json.dumps(entries),
    )

    assert len(logs) == 1


def test_log_verifier_requires_exact_batch_task_resources() -> None:
    verifier = _load_script("cloud_batch_task_resources", "verify-secret-logs.py")
    tasks = [
        {
            "name": (
                "projects/trusted-project/locations/us-central1/jobs/job-name/"
                f"taskGroups/group0/tasks/{index}"
            )
        }
        for index in range(2)
    ]
    tasks[1]["name"] = tasks[1]["name"].replace("tasks/1", "tasks/99")

    with pytest.raises(RuntimeError, match="Batch task identity mismatch"):
        verifier._job_tasks(
            {"job-name": ("job-uid", 2)},
            "trusted-project",
            "us-central1",
            command_runner=lambda _command: json.dumps(tasks),
        )


def test_log_verifier_accepts_authoritative_numeric_project_task_resources() -> None:
    """Batch returns canonical task names with the project's numeric identity."""
    verifier = _load_script(
        "cloud_batch_numeric_task_resources", "verify-secret-logs.py"
    )
    tasks = [
        {
            "name": (
                "projects/590888610376/locations/us-central1/jobs/job-name/"
                f"taskGroups/group0/tasks/{index}"
            )
        }
        for index in range(2)
    ]

    def run(command: list[str]) -> str:
        if command[1:3] == ["projects", "describe"]:
            return "590888610376\n"
        return json.dumps(tasks)

    verifier._job_tasks(
        {"job-name": ("job-uid", 2)},
        "trusted-project",
        "us-central1",
        command_runner=run,
    )


@pytest.mark.parametrize(
    "original,replacement",
    [
        ("projects/590888610376", "projects/590888610377"),
        ("locations/us-central1", "locations/europe-west1"),
        ("jobs/job-name", "jobs/other-job"),
    ],
)
def test_log_verifier_rejects_wrong_numeric_task_resource_identity(
    original: str, replacement: str
) -> None:
    verifier = _load_script(
        "cloud_batch_wrong_numeric_task_resource", "verify-secret-logs.py"
    )
    task_name = (
        "projects/590888610376/locations/us-central1/jobs/job-name/"
        "taskGroups/group0/tasks/0"
    ).replace(original, replacement)

    def run(command: list[str]) -> str:
        if command[1:3] == ["projects", "describe"]:
            return "590888610376\n"
        return json.dumps([{"name": task_name}])

    with pytest.raises(RuntimeError, match="Batch task identity mismatch"):
        verifier._job_tasks(
            {"job-name": ("job-uid", 1)},
            "trusted-project",
            "us-central1",
            command_runner=run,
        )


def test_log_verifier_accepts_agent_action_identity_with_exact_task_coverage() -> None:
    """Agent logs identify startup actions, while task logs identify every task."""
    verifier = _load_script(
        "cloud_batch_agent_action_identity", "verify-secret-logs.py"
    )
    group_name = (
        "projects/590888610376/locations/us-central1/jobs/job-name/"
        "taskGroups/group0"
    )
    resource = {
        "type": "batch.googleapis.com/Job",
        "labels": {
            "job_id": "job-uid",
            "location": "us-central1-b",
            "resource_container": "trusted-project",
        }
    }
    entries = [
        {
            "labels": {
                "job_uid": "job-uid",
                "task_group_name": group_name,
                "task_id": f"job-uid-group0-{index}",
            },
            "logName": "projects/trusted-project/logs/batch_task_logs",
            "resource": resource,
        }
        for index in range(2)
    ]
    entries.append(
        {
            "labels": {
                "job_uid": "job-uid",
                "task_group_name": group_name,
                "task_id": "action/STARTUP/0/0/group0",
            },
            "logName": "projects/trusted-project/logs/batch_agent_logs",
            "resource": resource,
        }
    )

    def run(command: list[str]) -> str:
        if command[1:3] == ["projects", "describe"]:
            return "590888610376\n"
        return json.dumps(entries)

    logs = verifier._job_logs(
        {"job-name": ("job-uid", 2)},
        "trusted-project",
        "us-central1",
        command_runner=run,
    )

    assert len(logs) == 1


@pytest.mark.parametrize(
    "mutation",
    [
        "wrong-group-project",
        "missing-group-project",
        "wrong-group-location",
        "wrong-group-job",
        "wrong-group-name",
        "wrong-resource-type",
        "missing-resource-type",
        "wrong-resource-uid",
        "missing-resource-uid",
        "wrong-resource-container",
        "missing-resource-container",
        "wrong-resource-location",
        "missing-resource-location",
        "wrong-action-structure",
        "unrelated-agent",
    ],
)
def test_log_verifier_rejects_unrelated_or_malformed_agent_identity(
    mutation: str,
) -> None:
    """Only the evidence-bound Batch job's startup agent can satisfy the gate."""
    verifier = _load_script(
        f"cloud_batch_agent_identity_{mutation}", "verify-secret-logs.py"
    )
    entries = _complete_log_entries("trusted-project", "job-uid", 1)
    agent = entries[-1]
    group_name = agent["labels"]["task_group_name"]
    resource = agent["resource"]
    resource_labels = resource["labels"]
    if mutation == "wrong-group-project":
        agent["labels"]["task_group_name"] = group_name.replace(
            "projects/trusted-project", "projects/590888610377"
        )
    elif mutation == "missing-group-project":
        agent["labels"]["task_group_name"] = group_name.removeprefix(
            "projects/trusted-project/"
        )
    elif mutation == "wrong-group-location":
        agent["labels"]["task_group_name"] = group_name.replace(
            "locations/us-central1", "locations/europe-west1"
        )
    elif mutation == "wrong-group-job":
        agent["labels"]["task_group_name"] = group_name.replace(
            "jobs/job-name", "jobs/unrelated-job"
        )
    elif mutation == "wrong-group-name":
        agent["labels"]["task_group_name"] = group_name.replace(
            "taskGroups/group0", "taskGroups/group1"
        )
    elif mutation == "wrong-resource-type":
        resource["type"] = "batch.googleapis.com/Task"
    elif mutation == "missing-resource-type":
        resource.pop("type")
    elif mutation == "wrong-resource-uid":
        resource_labels["job_id"] = "unrelated-job-uid"
    elif mutation == "missing-resource-uid":
        resource_labels.pop("job_id")
    elif mutation == "wrong-resource-container":
        resource_labels["resource_container"] = "unrelated-project"
    elif mutation == "missing-resource-container":
        resource_labels.pop("resource_container")
    elif mutation == "wrong-resource-location":
        resource_labels["location"] = "europe-west1-b"
    elif mutation == "missing-resource-location":
        resource_labels.pop("location")
    elif mutation == "wrong-action-structure":
        agent["labels"]["task_id"] = "action/SHUTDOWN/0/0/group0"
    elif mutation == "unrelated-agent":
        agent["labels"]["task_group_name"] = (
            "projects/590888610377/locations/europe-west1/"
            "jobs/unrelated-job/taskGroups/group1"
        )
        resource["type"] = "batch.googleapis.com/Task"
        resource_labels.update(
            {
                "job_id": "unrelated-job-uid",
                "location": "europe-west1-b",
                "resource_container": "unrelated-project",
            }
        )

    def run(command: list[str]) -> str:
        if command[1:3] == ["projects", "describe"]:
            return "590888610376\n"
        return json.dumps(entries)

    with pytest.raises(RuntimeError, match="attributable Batch logs invalid"):
        verifier._job_logs(
            {"job-name": ("job-uid", 1)},
            "trusted-project",
            "us-central1",
            command_runner=run,
        )


def test_log_verifier_rejects_agent_action_with_wrong_job_uid() -> None:
    verifier = _load_script(
        "cloud_batch_agent_wrong_job_uid", "verify-secret-logs.py"
    )
    entries = _complete_log_entries("trusted-project", "job-uid", 1)
    entries[-1]["labels"]["job_uid"] = "other-job-uid"

    with pytest.raises(RuntimeError, match="attributable Batch logs invalid"):
        verifier._job_logs(
            {"job-name": ("job-uid", 1)},
            "trusted-project",
            "us-central1",
            command_runner=lambda _command: json.dumps(entries),
        )


def test_log_verifier_rejects_unexpected_log_name() -> None:
    verifier = _load_script("cloud_batch_secret_verifier_log_name", "verify-secret-logs.py")
    entries = _complete_log_entries("trusted-project", "job-uid", 1)
    entries[0]["logName"] = "projects/trusted-project/logs/unexpected"

    with pytest.raises(RuntimeError, match="attributable Batch logs invalid"):
        verifier._job_logs(
            {"job-name": ("job-uid", 1)},
            "trusted-project",
            "us-central1",
            command_runner=lambda _command: json.dumps(entries),
        )


def test_verifier_rejects_mutable_secret_version() -> None:
    verifier = _load_script("cloud_batch_secret_verifier_version", "verify-secret-logs.py")

    with pytest.raises(RuntimeError, match="configuration invalid"):
        verifier._secret_values(
            ["projects/trusted-project/secrets/provider-key/versions/latest"],
            "trusted-project",
        )

    with pytest.raises(RuntimeError, match="configuration invalid"):
        verifier._parse_job_specs(["only-job=job-uid=32"])


def test_verifier_binds_job_uid_and_count_to_evidence(tmp_path: Path) -> None:
    verifier = _load_script("cloud_batch_job_evidence", "verify-secret-logs.py")
    evidence = tmp_path / "evidence.json"
    evidence.write_text(
        json.dumps(
            {
                "job_uids": {
                    "job-name": {"uid": "different-uid", "task_indexes": [0, 1]}
                }
            }
        ),
        encoding="utf-8",
    )

    with pytest.raises(RuntimeError, match="job identity evidence mismatch"):
        verifier._verify_job_evidence(evidence, {"job-name": ("job-uid", 2)})


def test_worker_image_inputs_and_templates_are_immutable() -> None:
    makefile = (REPO_ROOT / "Makefile").read_text(encoding="utf-8")
    cloudbuild = (CLOUD_BATCH / "cloudbuild.yaml").read_text(encoding="utf-8")
    submit = (CLOUD_BATCH / "submit.sh").read_text(encoding="utf-8")

    assert "$(CLOUD_BATCH_DIR)/runtime-secrets.py" in makefile
    assert "$(CLOUD_BATCH_DIR)/firebase-token-exchange.py" in makefile
    assert "$(CLOUD_BATCH_DIR)/cloud-regression-runner.py" in makefile
    assert "$(CLOUD_BATCH_DIR)/source-identity.py" in makefile
    assert "_IMAGE_TAG" in cloudbuild
    assert "{{IMAGE_URI}}" in "".join(
        template.read_text(encoding="utf-8") for template in TEMPLATES
    )
    assert "pdd-test:latest" not in "".join(
        template.read_text(encoding="utf-8") for template in TEMPLATES
    )
    for evidence_key in (
        "candidate_sha",
        "candidate_tree",
        "source_sha256",
        "source_generation",
        "image_digest",
        "job_uids",
    ):
        assert evidence_key in submit


def test_source_archive_rejects_dirty_or_untracked_candidate(tmp_path: Path) -> None:
    source_identity = _load_script("cloud_batch_source_identity_dirty", "source-identity.py")
    repo = tmp_path / "repo"
    repo.mkdir()
    subprocess.run(["git", "init", "-q"], cwd=repo, check=True)
    subprocess.run(["git", "config", "user.email", "ci@example.invalid"], cwd=repo, check=True)
    subprocess.run(["git", "config", "user.name", "CI"], cwd=repo, check=True)
    (repo / "tracked.txt").write_text("committed\n", encoding="utf-8")
    (repo / "must-also-ship.txt").write_text("all tracked bytes\n", encoding="utf-8")
    (repo / ".gitattributes").write_text(
        "must-also-ship.txt export-ignore\n", encoding="utf-8"
    )
    subprocess.run(
        ["git", "add", "tracked.txt", "must-also-ship.txt", ".gitattributes"],
        cwd=repo,
        check=True,
    )
    subprocess.run(["git", "commit", "-qm", "initial"], cwd=repo, check=True)
    (repo / "untracked.txt").write_text("must not upload\n", encoding="utf-8")

    with pytest.raises(source_identity.SourceIdentityError, match="not clean"):
        source_identity.create_archive(repo, tmp_path / "source.tar.gz")

    (repo / "untracked.txt").unlink()
    first = tmp_path / "first.tar.gz"
    second = tmp_path / "second.tar.gz"
    first_identity = source_identity.create_archive(repo, first)
    second_identity = source_identity.create_archive(repo, second)
    assert first.read_bytes() == second.read_bytes()
    assert first_identity == second_identity
    checkout = tmp_path / "checkout"
    source_identity.extract_verified_candidate(
        first,
        checkout,
        expected_candidate_sha=first_identity["candidate_sha"],
        expected_candidate_tree=first_identity["candidate_tree"],
    )
    assert (checkout / "tracked.txt").read_text(encoding="utf-8") == "committed\n"
    assert (checkout / "must-also-ship.txt").read_text(encoding="utf-8") == (
        "all tracked bytes\n"
    )
    assert not (checkout / "untracked.txt").exists()
    assert subprocess.run(
        ["git", "status", "--porcelain=v1", "--untracked-files=all"],
        cwd=checkout,
        check=True,
        text=True,
        capture_output=True,
    ).stdout == ""


def test_worker_rejects_extracted_tree_not_matching_candidate(tmp_path: Path) -> None:
    source_identity = _load_script("cloud_batch_source_identity_tree", "source-identity.py")
    repo = tmp_path / "repo"
    repo.mkdir()
    subprocess.run(["git", "init", "-q"], cwd=repo, check=True)
    subprocess.run(["git", "config", "user.email", "ci@example.invalid"], cwd=repo, check=True)
    subprocess.run(["git", "config", "user.name", "CI"], cwd=repo, check=True)
    (repo / "tracked.txt").write_text("candidate\n", encoding="utf-8")
    subprocess.run(["git", "add", "tracked.txt"], cwd=repo, check=True)
    subprocess.run(["git", "commit", "-qm", "candidate"], cwd=repo, check=True)
    archive = tmp_path / "candidate.tar.gz"
    identity = source_identity.create_archive(repo, archive)
    checkout = tmp_path / "checkout"
    source_identity.extract_verified_candidate(
        archive,
        checkout,
        expected_candidate_sha=identity["candidate_sha"],
        expected_candidate_tree=identity["candidate_tree"],
    )
    (checkout / "tracked.txt").write_text("different\n", encoding="utf-8")

    with pytest.raises(source_identity.SourceIdentityError, match="identity mismatch"):
        source_identity.verify_candidate_checkout(
            checkout,
            expected_candidate_sha=identity["candidate_sha"],
            expected_candidate_tree=identity["candidate_tree"],
        )


def test_worker_source_verification_rejects_mismatched_bytes(tmp_path: Path) -> None:
    source_identity = _load_script("cloud_batch_source_identity_hash", "source-identity.py")
    archive = tmp_path / "source.tar.gz"
    archive.write_bytes(b"candidate bytes")

    with pytest.raises(source_identity.SourceIdentityError, match="identity mismatch"):
        source_identity.verify_local_source(
            archive,
            expected_sha256="0" * 64,
            expected_size=len(b"candidate bytes"),
        )

    with pytest.raises(source_identity.SourceIdentityError, match="identity mismatch"):
        source_identity.validate_gcs_metadata(
            {
                "bucket": "bucket-name",
                "name": "run/source/pdd-source.tar.gz",
                "generation": "124",
                "size": "15",
            },
            expected_bucket="bucket-name",
            expected_object="run/source/pdd-source.tar.gz",
            expected_generation="123",
            expected_size=15,
        )


def test_log_verifier_requires_exact_task_ids() -> None:
    verifier = _load_script("cloud_batch_secret_verifier_task_ids", "verify-secret-logs.py")
    entries = _complete_log_entries("trusted-project", "job-uid", 2)
    for entry in entries:
        if entry["labels"]["task_id"] == "job-uid-group0-1":
            entry["labels"]["task_id"] = "job-uid-group0-unexpected"

    with pytest.raises(RuntimeError, match="attributable Batch logs incomplete"):
        verifier._job_logs(
            {"job-name": ("job-uid", 2)},
            "trusted-project",
            "us-central1",
            command_runner=lambda _command: json.dumps(entries),
        )


@pytest.mark.parametrize("encoding", ["percent", "form", "percent-lower", "form-mixed"])
def test_log_verifier_detects_encoded_payload_without_rendering_it(encoding: str) -> None:
    verifier = _load_script("cloud_batch_secret_verifier_encoded", "verify-secret-logs.py")
    marker = "payload value/+?&"
    rendered = {
        "percent": "payload%20value%2F%2B%3F%26",
        "form": "payload+value%2F%2B%3F%26",
        "percent-lower": "payload%20value%2f%2b%3f%26",
        "form-mixed": "payload+value%2f%2B%3f%26",
    }[encoding]

    findings = verifier.find_matches({"resource": marker}, [rendered])

    assert len(findings) == 1
    assert marker not in findings[0]


def test_result_identity_validator_rejects_mismatched_task(tmp_path: Path) -> None:
    validator = _load_script(
        "cloud_batch_result_identity", "verify-result-identities.py"
    )
    expected = {
        "candidate_sha": "a" * 40,
        "candidate_tree": "b" * 40,
        "source_sha256": "c" * 64,
        "source_generation": "123",
        "image_digest": "sha256:" + "d" * 64,
    }
    results = [
        {
            "task_index": 0,
            "identity": expected
            | {
                "job_name": "job",
                "task_group": "group0",
                "raw_task_index": 0,
                "task_resource": (
                    "projects/trusted-project/locations/us-central1/jobs/job/"
                    "taskGroups/group0/tasks/0"
                ),
            },
        },
        {
            "task_index": 1,
            "identity": expected
            | {
                "source_sha256": "e" * 64,
                "job_name": "job",
                "task_group": "group0",
                "raw_task_index": 1,
                "task_resource": (
                    "projects/trusted-project/locations/us-central1/jobs/job/"
                    "taskGroups/group0/tasks/1"
                ),
            },
        },
    ]

    with pytest.raises(validator.ResultIdentityError, match="identity mismatch"):
        validator.validate_results(
            results,
            expected_identity=expected,
            expected_tasks={
                0: {
                    "job_name": "job",
                    "task_group": "group0",
                    "raw_task_index": 0,
                    "task_resource": (
                        "projects/trusted-project/locations/us-central1/jobs/job/"
                        "taskGroups/group0/tasks/0"
                    ),
                },
                1: {
                    "job_name": "job",
                    "task_group": "group0",
                    "raw_task_index": 1,
                    "task_resource": (
                        "projects/trusted-project/locations/us-central1/jobs/job/"
                        "taskGroups/group0/tasks/1"
                    ),
                },
            },
        )


def test_result_artifacts_require_exact_json_and_log_set(tmp_path: Path) -> None:
    validator = _load_script(
        "cloud_batch_result_artifacts", "verify-result-identities.py"
    )
    evidence = {
        "project": "trusted-project",
        "location": "us-central1",
        "candidate_sha": "a" * 40,
        "candidate_tree": "b" * 40,
        "source_sha256": "c" * 64,
        "source_generation": "123",
        "image_digest": "sha256:" + "d" * 64,
        "job_uids": {"job": {"uid": "job-uid", "task_indexes": [54]}},
    }
    evidence_path = tmp_path / "evidence.json"
    evidence_path.write_text(json.dumps(evidence), encoding="utf-8")
    result = {
        "task_index": 54,
        "identity": {
            **{key: evidence[key] for key in validator.IDENTITY_FIELDS},
            "job_name": "job",
            "task_group": "group0",
            "raw_task_index": 0,
            "task_resource": (
                "projects/trusted-project/locations/us-central1/jobs/job/"
                "taskGroups/group0/tasks/0"
            ),
        },
    }
    (tmp_path / "task_54.json").write_text(json.dumps(result), encoding="utf-8")

    with pytest.raises(validator.ResultIdentityError, match="artifact set incomplete"):
        validator.validate_result_directory(evidence_path, tmp_path)

    (tmp_path / "task_54.log").write_text("safe output", encoding="utf-8")
    (tmp_path / "task_99.log").write_text("unexpected", encoding="utf-8")
    with pytest.raises(validator.ResultIdentityError, match="artifact set invalid"):
        validator.validate_result_directory(evidence_path, tmp_path)

    (tmp_path / "task_99.log").unlink()
    validator.validate_result_directory(evidence_path, tmp_path)


def test_result_identity_rejects_wrong_raw_task_resource() -> None:
    validator = _load_script(
        "cloud_batch_result_task_resource", "verify-result-identities.py"
    )
    expected = {
        "candidate_sha": "a" * 40,
        "candidate_tree": "b" * 40,
        "source_sha256": "c" * 64,
        "source_generation": "123",
        "image_digest": "sha256:" + "d" * 64,
    }
    expected_task = {
        "job_name": "job",
        "task_group": "group0",
        "raw_task_index": 0,
        "task_resource": (
            "projects/trusted-project/locations/us-central1/jobs/job/"
            "taskGroups/group0/tasks/0"
        ),
    }
    result = {
        "task_index": 54,
        "identity": expected
        | expected_task
        | {
            "raw_task_index": 1,
            "task_resource": expected_task["task_resource"].replace("tasks/0", "tasks/1"),
        },
    }

    with pytest.raises(validator.ResultIdentityError, match="task identity mismatch"):
        validator.validate_results(
            [result], expected_identity=expected, expected_tasks={54: expected_task}
        )


def test_result_identity_allows_many_logical_results_from_one_physical_task(tmp_path: Path):
    validator = _load_script(
        "cloud_batch_result_shared_task", "verify-result-identities.py"
    )
    evidence = {
        "project": "trusted-project",
        "location": "us-central1",
        "candidate_sha": "a" * 40,
        "candidate_tree": "b" * 40,
        "source_sha256": "c" * 64,
        "source_generation": "123",
        "image_digest": "sha256:" + "d" * 64,
        "job_uids": {
            "cloud-job": {
                "uid": "cloud-uid",
                "task_indexes": list(range(68, 76)),
                "physical_task_indexes": [0] * 8,
            }
        },
    }
    identity, tasks = validator._expected_from_evidence(evidence)

    assert set(tasks) == set(range(68, 76))
    assert {task["raw_task_index"] for task in tasks.values()} == {0}
    assert len({task["task_resource"] for task in tasks.values()}) == 1
    assert identity["candidate_sha"] == "a" * 40


def test_job_evidence_compares_physical_counts_not_logical_result_counts(tmp_path: Path):
    verifier = _load_script("cloud_batch_physical_evidence", "verify-secret-logs.py")
    evidence = tmp_path / "evidence.json"
    evidence.write_text(
        json.dumps(
            {
                "job_uids": {
                    "cloud-job": {
                        "uid": "cloud-uid",
                        "task_indexes": list(range(68, 76)),
                        "physical_task_indexes": [0] * 8,
                    }
                }
            }
        ),
        encoding="utf-8",
    )

    verifier._verify_job_evidence(evidence, {"cloud-job": ("cloud-uid", 1)})

    document = json.loads(evidence.read_text(encoding="utf-8"))
    document["job_uids"]["cloud-job"]["physical_task_indexes"] = [1] * 8
    evidence.write_text(json.dumps(document), encoding="utf-8")
    with pytest.raises(RuntimeError, match="job identity evidence invalid"):
        verifier._verify_job_evidence(evidence, {"cloud-job": ("cloud-uid", 1)})


def test_worker_result_binds_canonical_batch_task_identity() -> None:
    entrypoint = (CLOUD_BATCH / "entrypoint.sh").read_text(encoding="utf-8")

    for variable in (
        "BATCH_TASK_INDEX",
        "PDD_BATCH_PROJECT",
        "PDD_BATCH_LOCATION",
        "PDD_BATCH_JOB_NAME",
        "raw_task_index",
        "task_group",
        "task_resource",
    ):
        assert variable in entrypoint
    assert "BATCH_TASK_UID" not in entrypoint
    assert "BATCH_TASK_GROUP_UID" not in entrypoint


def test_submit_scans_complete_artifacts_before_reporting() -> None:
    submit = (CLOUD_BATCH / "submit.sh").read_text(encoding="utf-8")

    assert 'results/task_*.log" "${STREAMING_DIR}/"' in submit
    assert 'verifier_args+=(--log-file "${artifact_log}")' in submit
    assert "gcloud storage cat" not in submit
