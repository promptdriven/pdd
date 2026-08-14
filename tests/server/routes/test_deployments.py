"""Tests for the optional local deployment API.

The pdd-k8s plugin is faked here: core PDD must not depend on it, so these
tests cover both the installed and not-installed paths.
"""

from __future__ import annotations

import sys
import types

import pytest
from fastapi import FastAPI
from fastapi.testclient import TestClient

from pdd.server.routes import deployments
from pdd.server.routes.deployments import create_deployments_router


def _client(project_root):
    app = FastAPI()
    app.include_router(create_deployments_router(project_root))
    return TestClient(app)


class FakePlugin(types.SimpleNamespace):
    """Stand-in for the pdd_k8s facade."""

    def __init__(self, **overrides):
        super().__init__()
        self.calls = []
        self.describe_payload = {
            "configured": True,
            "available": True,
            "cluster": "pdd-local",
            "namespace": "pdd-local",
            "message": None,
            "manifest_path": "/project/.pdd/deployments.yaml",
            "services": [
                {
                    "name": "api",
                    "dev_units": ["router", "analyzer"],
                    "state": "running",
                    "ready_replicas": 1,
                    "desired_replicas": 1,
                    "restarts": 0,
                    "pods": [],
                    "events": [],
                }
            ],
        }
        self.deploy_result = {"ok": True, "message": None, "results": [{"service": "api", "ok": True}]}
        self.__dict__.update(overrides)

    def describe(self, root):
        self.calls.append(("describe", root))
        return self.describe_payload

    def doctor_report(self, root):
        self.calls.append(("doctor_report", root))
        return {"ok": True, "checks": []}

    def service_logs(self, root, service, tail):
        self.calls.append(("service_logs", root, service, tail))
        return {"service": service, "logs": "line one\n", "message": None}

    def deploy(self, root, names):
        self.calls.append(("deploy", root, names))
        return self.deploy_result

    def stop(self, root, names):
        self.calls.append(("stop", root, names))
        return {"ok": True, "message": None, "results": [{"service": names[0], "ok": True}]}


@pytest.fixture
def plugin(monkeypatch):
    """Install a fake pdd_k8s module for the duration of a test."""
    fake = FakePlugin()
    monkeypatch.setitem(sys.modules, "pdd_k8s", fake)
    return fake


@pytest.fixture
def no_plugin(monkeypatch):
    """Simulate pdd-k8s not being installed."""
    monkeypatch.setattr(deployments, "_load_plugin", lambda: None)


def test_describe_without_the_plugin_explains_how_to_opt_in(tmp_path, no_plugin):
    response = _client(tmp_path).get("/api/v1/deployments")
    body = response.json()

    assert response.status_code == 200
    assert body["plugin_installed"] is False
    assert body["configured"] is False
    assert body["services"] == []
    assert "pip install pdd-k8s" in body["message"]


def test_describe_returns_service_and_dev_unit_mapping(tmp_path, plugin):
    body = _client(tmp_path).get("/api/v1/deployments").json()

    assert body["plugin_installed"] is True
    assert body["services"][0]["dev_units"] == ["router", "analyzer"]
    assert body["services"][0]["state"] == "running"


def test_describe_passes_the_resolved_project_root(tmp_path, plugin):
    _client(tmp_path).get("/api/v1/deployments")
    assert plugin.calls[0] == ("describe", tmp_path.resolve())


def test_unconfigured_project_is_reported_not_an_error(tmp_path, plugin):
    plugin.describe_payload = {
        "configured": False,
        "available": False,
        "message": "This project has no local deployment manifest.",
        "services": [],
    }
    response = _client(tmp_path).get("/api/v1/deployments")

    assert response.status_code == 200
    assert response.json()["configured"] is False


def test_action_endpoints_return_501_without_the_plugin(tmp_path, no_plugin):
    client = _client(tmp_path)
    for method, path in [
        ("get", "/api/v1/deployments/doctor"),
        ("get", "/api/v1/deployments/api/logs"),
        ("post", "/api/v1/deployments/api/deploy"),
        ("post", "/api/v1/deployments/api/stop"),
    ]:
        response = getattr(client, method)(path)
        assert response.status_code == 501, path
        assert "pip install pdd-k8s" in response.json()["detail"]


def test_logs_endpoint_forwards_the_tail_size(tmp_path, plugin):
    body = _client(tmp_path).get("/api/v1/deployments/api/logs?tail=25").json()

    assert body["logs"] == "line one\n"
    assert plugin.calls[0] == ("service_logs", tmp_path.resolve(), "api", 25)


@pytest.mark.parametrize("tail", [0, 5000])
def test_logs_endpoint_rejects_out_of_range_tail(tmp_path, plugin, tail):
    response = _client(tmp_path).get(f"/api/v1/deployments/api/logs?tail={tail}")
    assert response.status_code == 422


def test_deploy_returns_a_running_operation_then_records_success(tmp_path, plugin):
    client = _client(tmp_path)
    started = client.post("/api/v1/deployments/api/deploy").json()

    assert started["state"] == "running"
    assert started["action"] == "deploy"
    assert started["service"] == "api"

    # The background task completes before the next request is served.
    operations = client.get("/api/v1/deployments/operations").json()["operations"]
    recorded = next(op for op in operations if op["id"] == started["id"])
    assert recorded["state"] == "succeeded"
    assert ("deploy", tmp_path.resolve(), ["api"]) in plugin.calls


def test_failed_deploy_is_recorded_with_its_message(tmp_path, plugin):
    plugin.deploy_result = {"ok": False, "message": "build: no such file", "results": []}
    client = _client(tmp_path)
    started = client.post("/api/v1/deployments/api/deploy").json()

    operations = client.get("/api/v1/deployments/operations").json()["operations"]
    recorded = next(op for op in operations if op["id"] == started["id"])
    assert recorded["state"] == "failed"
    assert recorded["message"] == "build: no such file"


def test_plugin_exception_fails_the_operation_without_a_500(tmp_path, plugin):
    def explode(_root, _names):
        raise RuntimeError("kubectl vanished")

    plugin.deploy = explode
    client = _client(tmp_path)
    started = client.post("/api/v1/deployments/api/deploy").json()

    operations = client.get("/api/v1/deployments/operations").json()["operations"]
    recorded = next(op for op in operations if op["id"] == started["id"])
    assert recorded["state"] == "failed"
    assert "kubectl vanished" in recorded["message"]


def test_stop_records_a_separate_operation(tmp_path, plugin):
    client = _client(tmp_path)
    client.post("/api/v1/deployments/api/deploy")
    stopped = client.post("/api/v1/deployments/api/stop").json()

    operations = client.get("/api/v1/deployments/operations").json()["operations"]
    assert {op["action"] for op in operations} == {"deploy", "stop"}
    # Newest first.
    assert operations[0]["id"] == stopped["id"]


def test_operation_history_is_capped(tmp_path, plugin):
    client = _client(tmp_path)
    for _ in range(deployments.MAX_TRACKED_OPERATIONS + 5):
        client.post("/api/v1/deployments/api/deploy")

    operations = client.get("/api/v1/deployments/operations").json()["operations"]
    assert len(operations) <= deployments.MAX_TRACKED_OPERATIONS
