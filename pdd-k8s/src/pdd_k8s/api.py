"""Stable facade consumed by PDD Connect.

Every function takes a project root, returns plain JSON-serialisable data and
never raises: callers render whatever ``message`` comes back. This is the only
module Connect is expected to import, so the CLI can evolve independently.
"""

from __future__ import annotations

from pathlib import Path
from typing import Any

from . import doctor, orchestrator
from .config import ConfigError, DeploymentConfig, config_exists, config_path, load_config


def is_configured(project_root: Path) -> bool:
    """True when the project opted in by adding ``.pdd/deployments.yaml``."""
    return config_exists(Path(project_root))


def _unconfigured(project_root: Path, message: str) -> dict[str, Any]:
    return {
        "configured": False,
        "available": False,
        "cluster": None,
        "namespace": None,
        "manifest_path": str(config_path(Path(project_root))),
        "message": message,
        "services": [],
    }


def _load(project_root: Path) -> tuple[DeploymentConfig | None, dict[str, Any] | None]:
    """Load config, returning an error payload instead of raising."""
    root = Path(project_root)
    if not config_exists(root):
        return None, _unconfigured(
            root,
            "This project has no local deployment manifest. "
            "Run 'pdd-k8s init' to map Dev Units onto runnable services.",
        )
    try:
        return load_config(root), None
    except ConfigError as error:
        payload = _unconfigured(root, str(error))
        payload["configured"] = True
        return None, payload


def describe(project_root: Path) -> dict[str, Any]:
    """Full panel payload: service/Dev Unit mapping plus live pod health."""
    config, error = _load(project_root)
    if config is None:
        return error or _unconfigured(project_root, "Deployment manifest could not be read.")

    payload = orchestrator.status(config, config.select([]))
    payload["configured"] = True
    payload["manifest_path"] = str(config_path(config.project_root))
    return payload


def doctor_report(project_root: Path) -> dict[str, Any]:
    """Environment readiness, safe to call when nothing is installed."""
    root = Path(project_root)
    config, _ = _load(root)
    checks = doctor.run_doctor(root, config)
    return {
        "ok": not doctor.blocking(checks),
        "checks": [check.as_dict() for check in checks],
    }


def service_logs(project_root: Path, service_name: str, tail: int = 200) -> dict[str, Any]:
    """Tail logs for one service."""
    config, error = _load(project_root)
    if config is None:
        return {"service": service_name, "logs": "", "message": (error or {}).get("message")}
    try:
        service = config.select([service_name])[0]
    except ConfigError as config_error:
        return {"service": service_name, "logs": "", "message": str(config_error)}

    text, failure = orchestrator.logs(config, service, tail=tail)
    return {"service": service_name, "logs": text, "message": failure}


def deploy(project_root: Path, service_names: list[str] | None = None) -> dict[str, Any]:
    """Build and deploy the named services (all services when None)."""
    return _lifecycle(project_root, service_names, orchestrator.up)


def stop(project_root: Path, service_names: list[str] | None = None) -> dict[str, Any]:
    """Remove the named services from the local cluster."""
    return _lifecycle(project_root, service_names, orchestrator.down)


def _lifecycle(project_root: Path, service_names: list[str] | None, action: Any) -> dict[str, Any]:
    config, error = _load(project_root)
    if config is None:
        return {"ok": False, "message": (error or {}).get("message"), "results": []}
    try:
        services = config.select(service_names or [])
    except ConfigError as config_error:
        return {"ok": False, "message": str(config_error), "results": []}

    outcomes = action(config, services)
    failures = [outcome for outcome in outcomes if not outcome.ok]
    return {
        "ok": not failures,
        "message": failures[0].failure() if failures else None,
        "results": [outcome.as_dict() for outcome in outcomes],
    }
