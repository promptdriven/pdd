"""Preflight checks and the Connect-facing facade."""

from __future__ import annotations

from pathlib import Path

import pytest

from pdd_k8s import api, doctor, runtime
from pdd_k8s.config import DeploymentConfig, load_config

from .conftest import FakeRuntime, pod, pod_list_json


@pytest.fixture
def all_tools(monkeypatch: pytest.MonkeyPatch) -> None:
    """Pretend docker, kind and kubectl are installed and healthy."""
    monkeypatch.setattr(runtime, "tool_path", lambda tool: f"/usr/local/bin/{tool}")
    monkeypatch.setattr(runtime, "docker_available", lambda: (True, "Docker daemon 27.0 is running."))
    monkeypatch.setattr(runtime, "kind_clusters", lambda: ["demo-local"])
    monkeypatch.setattr(runtime, "kubectl_context_exists", lambda _context: True)


def status_of(checks: list[doctor.Check], name_fragment: str) -> str:
    return next(check.status for check in checks if name_fragment in check.name)


def test_doctor_passes_when_everything_is_present(
    project: Path, config: DeploymentConfig, all_tools: None, fake_runtime: FakeRuntime
) -> None:
    checks = doctor.run_doctor(project, config)

    assert doctor.blocking(checks) == []
    assert status_of(checks, "dockerfile") == doctor.OK
    assert status_of(checks, "dev units") == doctor.OK


def test_doctor_blocks_when_docker_daemon_is_down(
    project: Path,
    config: DeploymentConfig,
    all_tools: None,
    fake_runtime: FakeRuntime,
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    monkeypatch.setattr(runtime, "docker_available", lambda: (False, "daemon not running"))
    checks = doctor.run_doctor(project, config)

    blocking = doctor.blocking(checks)
    assert [check.name for check in blocking] == ["docker daemon"]
    assert "Docker Desktop" in (blocking[0].remedy or "")


def test_doctor_blocks_on_missing_dockerfile_and_says_pdd_wont_write_one(
    project: Path, config: DeploymentConfig, all_tools: None, fake_runtime: FakeRuntime
) -> None:
    (project / "deploy" / "Dockerfile").unlink()
    blocking = doctor.blocking(doctor.run_doctor(project, config))

    assert len(blocking) == 1
    assert "never writes Dockerfiles" in (blocking[0].remedy or "")


def test_absent_cluster_is_a_warning_not_a_blocker(
    project: Path, config: DeploymentConfig, all_tools: None, monkeypatch: pytest.MonkeyPatch
) -> None:
    monkeypatch.setattr(runtime, "kind_clusters", lambda: [])
    checks = doctor.run_doctor(project, config)

    assert status_of(checks, "cluster") == doctor.WARN
    assert doctor.blocking(checks) == []


def test_unmapped_dev_unit_is_a_warning(
    project: Path, all_tools: None, fake_runtime: FakeRuntime
) -> None:
    manifest = project / ".pdd" / "deployments.yaml"
    manifest.write_text(
        manifest.read_text(encoding="utf-8").replace("[router, analyzer]", "[router, ghost]"),
        encoding="utf-8",
    )
    checks = doctor.run_doctor(project, load_config(project))

    assert status_of(checks, "dev units") == doctor.WARN
    assert doctor.blocking(checks) == []


def test_doctor_without_a_manifest_still_checks_tools(tmp_path: Path, all_tools: None) -> None:
    checks = doctor.run_doctor(tmp_path, None)
    blocking = doctor.blocking(checks)

    assert [check.name for check in blocking] == ["deployment manifest"]
    assert "pdd-k8s init" in (blocking[0].remedy or "")


def test_discover_dev_units_reads_prompt_basenames(project: Path) -> None:
    assert doctor.discover_dev_units(project) == {"router", "analyzer"}


# --- Connect-facing facade -------------------------------------------------


def test_is_configured_is_the_opt_in_signal(project: Path, tmp_path: Path) -> None:
    assert api.is_configured(project) is True
    assert api.is_configured(tmp_path / "elsewhere") is False


def test_describe_on_an_unconfigured_project_explains_opt_in(tmp_path: Path) -> None:
    payload = api.describe(tmp_path)

    assert payload["configured"] is False
    assert payload["available"] is False
    assert payload["services"] == []
    assert "pdd-k8s init" in payload["message"]


def test_describe_reports_invalid_manifest_without_raising(tmp_path: Path) -> None:
    manifest = tmp_path / ".pdd" / "deployments.yaml"
    manifest.parent.mkdir(parents=True)
    manifest.write_text("version: 9\nservices: {}\n", encoding="utf-8")

    payload = api.describe(tmp_path)
    assert payload["configured"] is True
    assert payload["available"] is False
    assert "unsupported manifest version" in payload["message"]


def test_describe_returns_service_and_pod_state(project: Path, fake_runtime: FakeRuntime) -> None:
    fake_runtime.when("get pods", stdout=pod_list_json(pod("api-1")))
    payload = api.describe(project)

    assert payload["configured"] is True
    assert payload["available"] is True
    assert payload["manifest_path"].endswith(".pdd/deployments.yaml")
    assert payload["services"][0]["name"] == "api"
    assert payload["services"][0]["state"] == "running"


def test_service_logs_reports_unknown_service(project: Path, fake_runtime: FakeRuntime) -> None:
    result = api.service_logs(project, "nope")
    assert result["logs"] == ""
    assert "unknown service" in result["message"]


def test_deploy_and_stop_return_structured_results(project: Path, fake_runtime: FakeRuntime) -> None:
    deployed = api.deploy(project, ["api"])
    assert deployed["ok"] is True
    assert deployed["results"][0]["service"] == "api"

    stopped = api.stop(project, ["api"])
    assert stopped["ok"] is True


def test_deploy_failure_is_reported_not_raised(project: Path, fake_runtime: FakeRuntime) -> None:
    fake_runtime.when("docker build", returncode=1, stderr="build blew up")
    result = api.deploy(project, ["api"])

    assert result["ok"] is False
    assert "build blew up" in result["message"]


def test_doctor_report_is_safe_on_an_unconfigured_project(tmp_path: Path) -> None:
    report = api.doctor_report(tmp_path)
    assert report["ok"] is False
    assert any("manifest" in check["name"] for check in report["checks"])
