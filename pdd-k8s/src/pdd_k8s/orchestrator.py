"""Local service lifecycle: build, load, apply, observe, tear down.

The orchestrator only ever addresses the named cluster from the manifest and
only ever manages objects carrying the PDD ``managed-by`` label, so an
unrelated Kubernetes context cannot be modified by these operations.
"""

from __future__ import annotations

import json
from collections.abc import Callable, Iterable
from dataclasses import dataclass, field
from typing import Any

from . import manifests, runtime
from .config import DeploymentConfig, ServiceSpec

Reporter = Callable[[str], None]

BUILD_TIMEOUT = 600.0
ROLLOUT_TIMEOUT = 180.0


def _noop(_message: str) -> None:
    """Default reporter used when a caller does not want progress output."""


@dataclass
class StepResult:
    """One named step of a multi-stage operation."""

    step: str
    ok: bool
    detail: str = ""

    def as_dict(self) -> dict[str, Any]:
        return {"step": self.step, "ok": self.ok, "detail": self.detail}


@dataclass
class ServiceOutcome:
    """Aggregated result of deploying or removing a single service."""

    service: str
    ok: bool
    steps: list[StepResult] = field(default_factory=list)

    def as_dict(self) -> dict[str, Any]:
        return {
            "service": self.service,
            "ok": self.ok,
            "steps": [step.as_dict() for step in self.steps],
        }

    def failure(self) -> str | None:
        for step in self.steps:
            if not step.ok:
                return f"{step.step}: {step.detail}"
        return None


def ensure_cluster(config: DeploymentConfig, report: Reporter = _noop) -> StepResult:
    """Create the named kind cluster when it does not already exist."""
    name = config.cluster.name
    if name in runtime.kind_clusters() and runtime.kubectl_context_exists(config.cluster.context):
        return StepResult("cluster", True, f"Using existing cluster '{name}'.")

    report(f"Creating local cluster '{name}' (first run downloads a node image)…")
    result = runtime.run(["kind", "create", "cluster", "--name", name, "--wait", "90s"], timeout=600)
    if not result.ok:
        return StepResult("cluster", False, result.error_text())
    return StepResult("cluster", True, f"Created cluster '{name}'.")


def _build_image(config: DeploymentConfig, service: ServiceSpec, report: Reporter) -> StepResult:
    dockerfile = service.dockerfile_path(config.project_root)
    if not dockerfile.is_file():
        return StepResult("build", False, f"Dockerfile not found: {service.dockerfile}")

    report(f"Building image {service.image}…")
    result = runtime.run(
        [
            "docker", "build",
            "--file", str(dockerfile),
            "--tag", service.image,
            str(service.context_path(config.project_root)),
        ],
        timeout=BUILD_TIMEOUT,
    )
    if not result.ok:
        return StepResult("build", False, result.error_text())
    return StepResult("build", True, service.image)


def _load_image(config: DeploymentConfig, service: ServiceSpec, report: Reporter) -> StepResult:
    report(f"Loading {service.image} into cluster '{config.cluster.name}'…")
    result = runtime.run(
        ["kind", "load", "docker-image", service.image, "--name", config.cluster.name],
        timeout=BUILD_TIMEOUT,
    )
    if not result.ok:
        return StepResult("load", False, result.error_text())
    return StepResult("load", True, f"Side-loaded into '{config.cluster.name}'.")


def _apply(config: DeploymentConfig, service: ServiceSpec, report: Reporter) -> StepResult:
    report(f"Applying manifests for '{service.name}'…")
    bundle = manifests.render([service], config.cluster)
    result = runtime.kubectl(
        ["apply", "--filename", "-"], context=config.cluster.context, stdin=bundle
    )
    if not result.ok:
        return StepResult("apply", False, result.error_text())
    return StepResult("apply", True, result.stdout.strip())


def _wait_ready(config: DeploymentConfig, service: ServiceSpec, report: Reporter) -> StepResult:
    if service.replicas == 0:
        return StepResult("ready", True, "Scaled to zero; nothing to wait for.")
    report(f"Waiting for '{service.name}' to become ready…")
    result = runtime.kubectl(
        [
            "rollout", "status", f"deployment/{service.name}",
            "--namespace", config.cluster.namespace,
            "--timeout", f"{int(ROLLOUT_TIMEOUT)}s",
        ],
        context=config.cluster.context,
        timeout=ROLLOUT_TIMEOUT + 30,
    )
    if not result.ok:
        events = recent_events(config, service, limit=5)
        detail = result.error_text()
        if events:
            detail = f"{detail}\nRecent events:\n" + "\n".join(f"  {line}" for line in events)
        return StepResult("ready", False, detail)
    return StepResult("ready", True, result.stdout.strip())


def up(
    config: DeploymentConfig,
    services: Iterable[ServiceSpec],
    report: Reporter = _noop,
) -> list[ServiceOutcome]:
    """Build, load, apply and await readiness for the selected services."""
    outcomes: list[ServiceOutcome] = []
    cluster_step = ensure_cluster(config, report)

    for service in services:
        outcome = ServiceOutcome(service.name, ok=cluster_step.ok, steps=[cluster_step])
        if cluster_step.ok:
            for stage in (_build_image, _load_image, _apply, _wait_ready):
                step = stage(config, service, report)
                outcome.steps.append(step)
                if not step.ok:
                    outcome.ok = False
                    break
            else:
                outcome.ok = True
        outcomes.append(outcome)
    return outcomes


def down(
    config: DeploymentConfig,
    services: Iterable[ServiceSpec],
    report: Reporter = _noop,
) -> list[ServiceOutcome]:
    """Delete the Kubernetes objects for the selected services.

    The cluster itself is left in place; ``delete_cluster`` removes it.
    """
    outcomes: list[ServiceOutcome] = []
    for service in services:
        report(f"Removing '{service.name}'…")
        result = runtime.kubectl(
            [
                "delete", "deployment,service",
                "--namespace", config.cluster.namespace,
                "--selector", manifests.service_selector(service),
                "--ignore-not-found",
            ],
            context=config.cluster.context,
        )
        detail = result.stdout.strip() or "Nothing to remove." if result.ok else result.error_text()
        outcomes.append(
            ServiceOutcome(service.name, result.ok, [StepResult("delete", result.ok, detail)])
        )
    return outcomes


def delete_cluster(config: DeploymentConfig, report: Reporter = _noop) -> StepResult:
    """Delete the entire named local cluster."""
    name = config.cluster.name
    if name not in runtime.kind_clusters():
        return StepResult("cluster", True, f"Cluster '{name}' does not exist.")
    report(f"Deleting cluster '{name}'…")
    result = runtime.run(["kind", "delete", "cluster", "--name", name], timeout=180)
    if not result.ok:
        return StepResult("cluster", False, result.error_text())
    return StepResult("cluster", True, f"Deleted cluster '{name}'.")


def _pod_health(pod: dict[str, Any]) -> tuple[str, str | None, str | None]:
    """Derive (phase, health, last transition) from one pod's status."""
    status = pod.get("status", {})
    containers = status.get("containerStatuses") or []
    conditions = {item.get("type"): item for item in status.get("conditions") or []}
    ready_condition = conditions.get("Ready", {})
    last_transition = ready_condition.get("lastTransitionTime")

    if status.get("phase") == "Failed":
        return "failed", "failing", last_transition
    if containers and all(item.get("ready") for item in containers):
        return "ready", "passing", last_transition

    waiting = next(
        (
            item.get("state", {}).get("waiting", {}).get("reason")
            for item in containers
            if item.get("state", {}).get("waiting", {}).get("reason")
        ),
        None,
    )
    phase = str(status.get("phase", "unknown")).lower()
    health = waiting or ready_condition.get("reason") or "not ready"
    return phase, health, last_transition


def _pods_for(config: DeploymentConfig, selector: str) -> tuple[list[dict[str, Any]], str | None]:
    result = runtime.kubectl(
        [
            "get", "pods",
            "--namespace", config.cluster.namespace,
            "--selector", selector,
            "--output", "json",
        ],
        context=config.cluster.context,
        timeout=20,
    )
    if not result.ok:
        return [], result.error_text()
    try:
        items = json.loads(result.stdout).get("items", [])
    except (json.JSONDecodeError, AttributeError):
        return [], "Kubernetes returned an unreadable pod list."

    pods: list[dict[str, Any]] = []
    for pod in items:
        metadata = pod.get("metadata", {})
        status = pod.get("status", {})
        containers = status.get("containerStatuses") or []
        phase, health, last_transition = _pod_health(pod)
        pods.append(
            {
                "name": str(metadata.get("name", "unknown")),
                "service": str(metadata.get("labels", {}).get("app.kubernetes.io/name", "unknown")),
                "phase": phase,
                "health": health,
                "health_checked_at": last_transition,
                "restarts": sum(int(item.get("restartCount", 0)) for item in containers),
                # nodeName is assigned by the scheduler and lives on spec, not status.
                "node": str(pod.get("spec", {}).get("nodeName") or "unscheduled"),
                "created_at": str(metadata.get("creationTimestamp", "unknown")),
            }
        )
    return sorted(pods, key=lambda pod: pod["name"]), None


def recent_events(
    config: DeploymentConfig, service: ServiceSpec, limit: int = 10
) -> list[str]:
    """Recent Kubernetes events mentioning a service, newest last."""
    result = runtime.kubectl(
        [
            "get", "events",
            "--namespace", config.cluster.namespace,
            "--sort-by", ".lastTimestamp",
            "--output", "json",
        ],
        context=config.cluster.context,
        timeout=20,
    )
    if not result.ok:
        return []
    try:
        items = json.loads(result.stdout).get("items", [])
    except (json.JSONDecodeError, AttributeError):
        return []

    lines = [
        f"{item.get('type', '?')} {item.get('reason', '?')}: {item.get('message', '').strip()}"
        for item in items
        if service.name in str(item.get("involvedObject", {}).get("name", ""))
    ]
    return lines[-limit:]


def status(config: DeploymentConfig, services: Iterable[ServiceSpec]) -> dict[str, Any]:
    """Full deployment picture: service definitions plus live pod state."""
    selected = list(services)
    cluster_exists = config.cluster.name in runtime.kind_clusters()
    if not cluster_exists:
        return {
            "available": False,
            "cluster": config.cluster.name,
            "namespace": config.cluster.namespace,
            "message": f"Local cluster '{config.cluster.name}' is not running. Run 'pdd-k8s up'.",
            "services": [_service_summary(service, [], None) for service in selected],
        }

    all_pods, error = _pods_for(config, manifests.MANAGED_SELECTOR)
    if error:
        return {
            "available": False,
            "cluster": config.cluster.name,
            "namespace": config.cluster.namespace,
            "message": error,
            "services": [_service_summary(service, [], None) for service in selected],
        }

    by_service: dict[str, list[dict[str, Any]]] = {}
    for pod in all_pods:
        by_service.setdefault(pod["service"], []).append(pod)

    return {
        "available": True,
        "cluster": config.cluster.name,
        "namespace": config.cluster.namespace,
        "message": None,
        "services": [
            _service_summary(service, by_service.get(service.name, []), config)
            for service in selected
        ],
    }


def _service_summary(
    service: ServiceSpec,
    pods: list[dict[str, Any]],
    config: DeploymentConfig | None,
) -> dict[str, Any]:
    ready = sum(1 for pod in pods if pod["phase"] == "ready")
    if not pods:
        state = "not deployed"
    elif ready == len(pods):
        state = "running"
    elif any(pod["phase"] == "failed" for pod in pods):
        state = "failed"
    else:
        state = "pending"

    summary: dict[str, Any] = {
        "name": service.name,
        "dev_units": list(service.dev_units),
        "image": service.image,
        "port": service.port,
        "health_path": service.health.path,
        "desired_replicas": service.replicas,
        "ready_replicas": ready,
        "state": state,
        "restarts": sum(pod["restarts"] for pod in pods),
        "pods": pods,
        "events": [],
    }
    # Events are only useful, and only worth an extra API call, when unhealthy.
    if config is not None and state in {"failed", "pending"}:
        summary["events"] = recent_events(config, service, limit=5)
    return summary


def logs(
    config: DeploymentConfig, service: ServiceSpec, tail: int = 200
) -> tuple[str, str | None]:
    """Tail aggregated logs for a service. Returns (text, error)."""
    result = runtime.kubectl(
        [
            "logs",
            "--namespace", config.cluster.namespace,
            "--selector", manifests.service_selector(service),
            "--tail", str(tail),
            "--all-containers",
            "--prefix",
        ],
        context=config.cluster.context,
        timeout=30,
    )
    if not result.ok:
        return "", result.error_text()
    return result.stdout, None
