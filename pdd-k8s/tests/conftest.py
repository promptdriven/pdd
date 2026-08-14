"""Shared fixtures: a project on disk and a fake external-command runtime."""

from __future__ import annotations

import json
from collections.abc import Callable
from pathlib import Path

import pytest

from pdd_k8s import orchestrator, runtime
from pdd_k8s.config import DeploymentConfig, load_config

MANIFEST = """\
version: 1
cluster:
  name: demo-local
  namespace: demo
services:
  api:
    dev_units: [router, analyzer]
    dockerfile: deploy/Dockerfile
    port: 8000
"""


@pytest.fixture
def project(tmp_path: Path) -> Path:
    """A project directory with a valid manifest, Dockerfile and prompts."""
    manifest_path = tmp_path / ".pdd" / "deployments.yaml"
    manifest_path.parent.mkdir(parents=True, exist_ok=True)
    manifest_path.write_text(MANIFEST, encoding="utf-8")

    dockerfile = tmp_path / "deploy" / "Dockerfile"
    dockerfile.parent.mkdir(parents=True, exist_ok=True)
    dockerfile.write_text("FROM python:3.12-slim\n", encoding="utf-8")

    prompts = tmp_path / "prompts"
    prompts.mkdir(exist_ok=True)
    for unit in ("router", "analyzer"):
        (prompts / f"{unit}_python.prompt").write_text("x", encoding="utf-8")
    return tmp_path


@pytest.fixture
def config(project: Path) -> DeploymentConfig:
    return load_config(project)


class FakeRuntime:
    """Records commands and replays scripted results instead of running them."""

    def __init__(self) -> None:
        self.calls: list[list[str]] = []
        self._rules: list[tuple[Callable[[list[str]], bool], runtime.CommandResult]] = []
        self.default = runtime.CommandResult([], 0, "", "")

    def when(self, *fragments: str, returncode: int = 0, stdout: str = "", stderr: str = "") -> None:
        """Match a command containing every fragment, in order of registration."""
        def matches(command: list[str]) -> bool:
            joined = " ".join(command)
            return all(fragment in joined for fragment in fragments)

        self._rules.append((matches, runtime.CommandResult([], returncode, stdout, stderr)))

    def __call__(self, command: list[str], **_kwargs: object) -> runtime.CommandResult:
        self.calls.append(list(command))
        for matches, result in self._rules:
            if matches(command):
                return runtime.CommandResult(command, result.returncode, result.stdout, result.stderr)
        return runtime.CommandResult(command, 0, "", "")

    def commands(self) -> list[str]:
        return [" ".join(call) for call in self.calls]

    def ran(self, *fragments: str) -> bool:
        return any(all(fragment in line for fragment in fragments) for line in self.commands())


def pod(name: str, *, service: str = "api", ready: bool = True, restarts: int = 0,
        phase: str = "Running", waiting: str | None = None) -> dict:
    """Build a pod object shaped like `kubectl get pods -o json` output."""
    state: dict = {"running": {}} if ready else {"waiting": {"reason": waiting or "ContainerCreating"}}
    return {
        "metadata": {
            "name": name,
            "labels": {"app.kubernetes.io/name": service, "app.kubernetes.io/managed-by": "pdd"},
            "creationTimestamp": "2026-08-14T10:00:00Z",
        },
        # nodeName is set by the scheduler on spec, mirroring real API output.
        "spec": {"nodeName": "demo-local-control-plane"},
        "status": {
            "phase": phase,
            "containerStatuses": [{"ready": ready, "restartCount": restarts, "state": state}],
            "conditions": [
                {
                    "type": "Ready",
                    "status": "True" if ready else "False",
                    "lastTransitionTime": "2026-08-14T10:00:05Z",
                    "reason": None if ready else "ContainersNotReady",
                }
            ],
        },
    }


def pod_list_json(*pods: dict) -> str:
    return json.dumps({"items": list(pods)})


@pytest.fixture
def fake_runtime(monkeypatch: pytest.MonkeyPatch) -> FakeRuntime:
    """Replace every external command with a recorded fake."""
    fake = FakeRuntime()
    monkeypatch.setattr(runtime, "run", fake)
    monkeypatch.setattr(orchestrator.runtime, "run", fake)
    monkeypatch.setattr(orchestrator.runtime, "kind_clusters", lambda: ["demo-local"])
    monkeypatch.setattr(orchestrator.runtime, "kubectl_context_exists", lambda _context: True)
    return fake
