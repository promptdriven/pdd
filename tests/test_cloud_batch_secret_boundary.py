"""Security contracts for Cloud Batch runtime credential handling."""

from __future__ import annotations

import importlib.util
import json
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
        "OPENAI_API_KEY_SECRET_RESOURCE": (
            "projects/example/secrets/provider-key/versions/latest"
        ),
        "PDD_REFRESH_TOKEN_SECRET_RESOURCE": (
            "projects/example/secrets/cloud-refresh/versions/latest"
        ),
    }
    fetched: list[str] = []

    def fetch(resource: str) -> str:
        fetched.append(resource)
        return marker

    loaded = loader.load_required_secrets(environment, fetch_secret=fetch)

    assert loaded == {"OPENAI_API_KEY": marker}
    assert fetched == [environment["OPENAI_API_KEY_SECRET_RESOURCE"]]


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
        loader.load_required_secrets(environment, fetch_secret=fetch)

    output = capsys.readouterr().out + capsys.readouterr().err + str(exc.value)
    assert marker not in output
    assert "denied" not in output
    assert "bad" not in output


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
        fetch_secret=lambda _resource: marker,
        exec_process=exec_process,
    )

    assert called == [(["/entrypoint.sh"], environment)]
    assert marker not in capsys.readouterr().out
    assert all(marker not in path.read_text(errors="replace") for path in tmp_path.glob("**/*") if path.is_file())


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

