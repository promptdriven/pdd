"""Local service deployment endpoints, backed by the optional pdd-k8s plugin.

Core PDD does not depend on Kubernetes. These endpoints degrade to a single
"not installed" / "not configured" response so the Connect panel can stay
hidden for the many projects — scripts, CLIs, libraries — that never need
containers at all.
"""

from __future__ import annotations

import asyncio
import time
import uuid
from pathlib import Path
from typing import Any, Callable

from fastapi import APIRouter, HTTPException, Query

PLUGIN_NAME = "pdd-k8s"
PLUGIN_HINT = "Install the optional companion package to run services locally: pip install pdd-k8s"
MAX_TRACKED_OPERATIONS = 20


def _load_plugin() -> Any | None:
    """Import pdd_k8s on demand, returning None when it is not installed."""
    try:
        import pdd_k8s
    except ImportError:
        return None
    return pdd_k8s


def _unavailable_payload(project_root: Path) -> dict[str, Any]:
    return {
        "plugin_installed": False,
        "configured": False,
        "available": False,
        "cluster": None,
        "namespace": None,
        "manifest_path": str(project_root / ".pdd" / "deployments.yaml"),
        "message": PLUGIN_HINT,
        "services": [],
    }


class OperationTracker:
    """In-memory record of deploy/stop actions started from Connect.

    Builds take minutes, so mutating endpoints return immediately with an
    operation id and the panel polls for the outcome.
    """

    def __init__(self, limit: int = MAX_TRACKED_OPERATIONS) -> None:
        self._operations: dict[str, dict[str, Any]] = {}
        self._limit = limit
        self._lock = asyncio.Lock()

    async def start(self, action: str, service: str | None) -> dict[str, Any]:
        operation = {
            "id": uuid.uuid4().hex[:12],
            "action": action,
            "service": service,
            "state": "running",
            "message": None,
            "results": [],
            "started_at": time.time(),
            "finished_at": None,
        }
        async with self._lock:
            self._operations[operation["id"]] = operation
            self._evict_locked()
        return operation

    async def finish(self, operation_id: str, result: dict[str, Any]) -> None:
        async with self._lock:
            operation = self._operations.get(operation_id)
            if operation is None:
                return
            operation["state"] = "succeeded" if result.get("ok") else "failed"
            operation["message"] = result.get("message")
            operation["results"] = result.get("results", [])
            operation["finished_at"] = time.time()

    async def fail(self, operation_id: str, message: str) -> None:
        await self.finish(operation_id, {"ok": False, "message": message, "results": []})

    async def snapshot(self) -> list[dict[str, Any]]:
        async with self._lock:
            return sorted(
                (dict(operation) for operation in self._operations.values()),
                key=lambda operation: operation["started_at"],
                reverse=True,
            )

    def _evict_locked(self) -> None:
        """Drop the oldest finished operations once the cap is exceeded."""
        if len(self._operations) <= self._limit:
            return
        finished = sorted(
            (op for op in self._operations.values() if op["finished_at"] is not None),
            key=lambda operation: operation["finished_at"],
        )
        for operation in finished[: len(self._operations) - self._limit]:
            self._operations.pop(operation["id"], None)


def create_deployments_router(project_root: Path) -> APIRouter:
    """Create project-scoped endpoints for optional local service deployment."""
    root = project_root.resolve()
    router = APIRouter(prefix="/api/v1/deployments", tags=["deployments"])
    tracker = OperationTracker()

    def _require_plugin() -> Any:
        plugin = _load_plugin()
        if plugin is None:
            raise HTTPException(status_code=501, detail=PLUGIN_HINT)
        return plugin

    async def _run_action(
        operation_id: str, action: Callable[..., dict[str, Any]], service: str | None
    ) -> None:
        """Run a blocking plugin call off the event loop and record its result."""
        names = [service] if service else None
        try:
            result = await asyncio.to_thread(action, root, names)
        except Exception as error:  # plugin must never take the server down
            await tracker.fail(operation_id, f"{type(error).__name__}: {error}")
            return
        await tracker.finish(operation_id, result)

    @router.get("")
    async def describe_deployments() -> dict[str, Any]:
        """Service definitions, Dev Unit mapping and live pod health."""
        plugin = _load_plugin()
        if plugin is None:
            return _unavailable_payload(root)
        payload = await asyncio.to_thread(plugin.describe, root)
        payload["plugin_installed"] = True
        return payload

    @router.get("/doctor")
    async def deployment_doctor() -> dict[str, Any]:
        """Environment readiness for local deployment."""
        plugin = _require_plugin()
        return await asyncio.to_thread(plugin.doctor_report, root)

    @router.get("/operations")
    async def list_operations() -> dict[str, Any]:
        """Recent deploy/stop actions started from Connect."""
        return {"operations": await tracker.snapshot()}

    @router.get("/{service_name}/logs")
    async def service_logs(
        service_name: str, tail: int = Query(default=200, ge=1, le=2000)
    ) -> dict[str, Any]:
        """Tail recent logs for one service."""
        plugin = _require_plugin()
        return await asyncio.to_thread(plugin.service_logs, root, service_name, tail)

    @router.post("/{service_name}/deploy")
    async def deploy_service(service_name: str) -> dict[str, Any]:
        """Build and (re)deploy one service. Returns an operation to poll."""
        plugin = _require_plugin()
        operation = await tracker.start("deploy", service_name)
        asyncio.create_task(_run_action(operation["id"], plugin.deploy, service_name))
        return operation

    @router.post("/{service_name}/stop")
    async def stop_service(service_name: str) -> dict[str, Any]:
        """Remove one service from the local cluster."""
        plugin = _require_plugin()
        operation = await tracker.start("stop", service_name)
        asyncio.create_task(_run_action(operation["id"], plugin.stop, service_name))
        return operation

    return router
