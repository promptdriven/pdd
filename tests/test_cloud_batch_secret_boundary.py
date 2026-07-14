"""Security contracts for Cloud Batch runtime credential handling."""

from __future__ import annotations

import importlib.util
import json
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
        assert all(
            value.startswith("projects/{{PROJECT_ID}}/secrets/")
            and value.endswith("/versions/latest")
            for value in resources.values()
        )


def test_runtime_loader_fetches_only_task_required_credentials() -> None:
    loader = _load_script("cloud_batch_runtime_secrets", "runtime-secrets.py")
    marker = "payload-" + "never-render"
    environment = {
        "BATCH_TASK_INDEX": "0",
        "GCS_HMAC_ACCESS_KEY_ID_SECRET_RESOURCE": (
            "projects/example/secrets/cache-id/versions/latest"
        ),
        "GCS_HMAC_SECRET_ACCESS_KEY_SECRET_RESOURCE": (
            "projects/example/secrets/cache-key/versions/latest"
        ),
        "OPENAI_API_KEY_SECRET_RESOURCE": (
            "projects/example/secrets/provider-key/versions/latest"
        ),
        "GITHUB_CLIENT_ID_SECRET_RESOURCE": (
            "projects/example/secrets/client-id/versions/latest"
        ),
        "CLAUDE_CODE_OAUTH_TOKEN_SECRET_RESOURCE": (
            "projects/example/secrets/agent-oauth/versions/latest"
        ),
        "PDD_REFRESH_TOKEN_SECRET_RESOURCE": (
            "projects/example/secrets/cloud-refresh/versions/latest"
        ),
    }
    fetched: list[str] = []

    def fetch(resource: str) -> str:
        fetched.append(resource)
        return marker

    loaded = loader.load_required_secrets(environment, secret_fetcher=fetch)

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
            "projects/example/secrets/cloud-api-key/versions/latest"
        ),
        "GITHUB_CLIENT_ID_SECRET_RESOURCE": (
            "projects/example/secrets/client-id/versions/latest"
        ),
        "PDD_REFRESH_TOKEN_SECRET_RESOURCE": (
            "projects/example/secrets/cloud-refresh/versions/latest"
        ),
    }

    def fetch(_resource: str) -> str:
        raise failure

    with pytest.raises(loader.SecretLoadError, match="required runtime credential") as exc:
        loader.load_required_secrets(environment, secret_fetcher=fetch)

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
    monkeypatch.setattr(loader, "_read_json", lambda _request: next(documents))

    with pytest.raises(loader.SecretLoadError, match="required runtime credential") as exc:
        loader.fetch_secret(
            "projects/example/secrets/provider-key/versions/latest"
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
            "projects/example/secrets/provider-key/versions/latest"
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


def test_log_verifier_fails_closed_when_attributable_logs_are_absent(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    verifier = _load_script("cloud_batch_secret_verifier_empty", "verify-secret-logs.py")
    responses = iter(["job-uid\n", "[]"])
    monkeypatch.setattr(verifier, "_run", lambda _command: next(responses))

    with pytest.raises(RuntimeError, match="attributable Batch logs unavailable"):
        verifier._job_logs(["job-name"], "example", "us-central1")


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


def _complete_log_entries(project: str, uid: str, task_count: int) -> list[dict]:
    entries = []
    for task_index in range(task_count):
        task_id = f"job-group0-{task_index}"
        for log_id in ("batch_agent_logs", "batch_task_logs"):
            entries.append(
                {
                    "labels": {"job_uid": uid, "task_id": task_id},
                    "logName": f"projects/{project}/logs/{log_id}",
                }
            )
    return entries


def test_log_verifier_requires_every_task_and_unbounded_pagination() -> None:
    verifier = _load_script("cloud_batch_secret_verifier_complete", "verify-secret-logs.py")
    commands: list[list[str]] = []
    entries = _complete_log_entries("trusted-project", "job-uid", 2)
    entries = [entry for entry in entries if entry["labels"]["task_id"] != "job-group0-1"]

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


def test_worker_image_inputs_and_templates_are_immutable() -> None:
    makefile = (REPO_ROOT / "Makefile").read_text(encoding="utf-8")
    cloudbuild = (CLOUD_BATCH / "cloudbuild.yaml").read_text(encoding="utf-8")
    submit = (CLOUD_BATCH / "submit.sh").read_text(encoding="utf-8")

    assert "$(CLOUD_BATCH_DIR)/runtime-secrets.py" in makefile
    assert "$(CLOUD_BATCH_DIR)/firebase-token-exchange.py" in makefile
    assert "_IMAGE_TAG" in cloudbuild
    assert "{{IMAGE_URI}}" in "".join(
        template.read_text(encoding="utf-8") for template in TEMPLATES
    )
    assert "pdd-test:latest" not in "".join(
        template.read_text(encoding="utf-8") for template in TEMPLATES
    )
    for evidence_key in (
        "candidate_sha",
        "source_sha256",
        "image_digest",
        "job_uids",
    ):
        assert evidence_key in submit
