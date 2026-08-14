"""Read-only observability endpoints for a local PDD Connect project."""

from __future__ import annotations

import json
import re
from pathlib import Path
from typing import Any

from fastapi import APIRouter, HTTPException


_SENSITIVE_KEY = re.compile(r"(?:token|secret|password|api[_-]?key|credential)", re.IGNORECASE)
_SENSITIVE_VALUE = re.compile(
    r"((?:token|secret|password|api[_-]?key|credential)\s*[=:]\s*)[^\s,;]+",
    re.IGNORECASE,
)


def _read_json(file_path: Path) -> dict[str, Any] | None:
    """Return a JSON object from ``file_path`` or ``None`` for invalid reports."""
    try:
        with file_path.open(encoding="utf-8") as report_file:
            data = json.load(report_file)
    except (OSError, json.JSONDecodeError):
        return None
    return data if isinstance(data, dict) else None


def _run_status(report: dict[str, Any]) -> str:
    """Derive a stable dashboard status from a core-dump report."""
    terminal_output = str(report.get("terminal_output", "")).lower()
    if report.get("errors") or "status: failed" in terminal_output or "failed:" in terminal_output:
        return "failed"
    return "success"


def _primary_model(report: dict[str, Any]) -> str:
    """Return the first named model from a report's execution steps."""
    steps = report.get("steps", [])
    if not isinstance(steps, list):
        return "unknown"
    for step in steps:
        if isinstance(step, dict) and step.get("model") not in (None, "", "unknown"):
            return str(step["model"])
    return "unknown"


def _run_summary(file_path: Path, report: dict[str, Any]) -> dict[str, Any]:
    """Create the small, list-safe representation of a run report."""
    errors = report.get("errors", [])
    first_error = errors[0] if isinstance(errors, list) and errors else {}
    if not isinstance(first_error, dict):
        first_error = {}
    argv = report.get("argv", [])
    return {
        "filename": file_path.name,
        "timestamp": str(report.get("timestamp_utc", "unknown")),
        "argv": [str(value) for value in argv] if isinstance(argv, list) else [],
        "status": _run_status(report),
        "total_cost": float(report.get("total_cost", 0.0) or 0.0),
        "model": _primary_model(report),
        "error_message": str(first_error.get("message", "")) or None,
    }


def _safe_run_detail(report: dict[str, Any]) -> dict[str, Any]:
    """Return dashboard details without environment values or secret-bearing fields."""
    errors = report.get("errors", [])
    safe_errors = []
    if isinstance(errors, list):
        for error in errors:
            if not isinstance(error, dict):
                continue
            safe_errors.append({
                key: _redact_value(value)
                for key, value in error.items()
                if not _SENSITIVE_KEY.search(key)
            })

    return {
        "timestamp_utc": str(report.get("timestamp_utc", "unknown")),
        "argv": report.get("argv", []) if isinstance(report.get("argv"), list) else [],
        "total_cost": float(report.get("total_cost", 0.0) or 0.0),
        "steps": _redact_value(report.get("steps", [])) if isinstance(report.get("steps"), list) else [],
        "errors": safe_errors,
        "terminal_output": _redact_value(str(report.get("terminal_output", ""))),
        "platform": _redact_value(report.get("platform", {})) if isinstance(report.get("platform"), dict) else {},
    }


def _redact_value(value: Any) -> Any:
    """Remove values whose keys or inline labels indicate credential material."""
    if isinstance(value, dict):
        return {
            key: "[redacted]" if _SENSITIVE_KEY.search(str(key)) else _redact_value(item)
            for key, item in value.items()
        }
    if isinstance(value, list):
        return [_redact_value(item) for item in value]
    if isinstance(value, str):
        return _SENSITIVE_VALUE.sub(r"\1[redacted]", value)
    return value


def create_observability_router(project_root: Path) -> APIRouter:
    """Create project-scoped, read-only observability endpoints."""
    root = project_root.resolve()
    core_dumps_dir = root / ".pdd" / "core_dumps"
    metadata_dir = root / ".pdd" / "meta"
    router = APIRouter(prefix="/api/v1/observability", tags=["observability"])

    @router.get("/runs")
    async def list_runs() -> list[dict[str, Any]]:
        """List valid core dumps, newest first."""
        if not core_dumps_dir.is_dir():
            return []
        runs = []
        for file_path in core_dumps_dir.glob("*.json"):
            report = _read_json(file_path)
            if report is not None:
                runs.append(_run_summary(file_path, report))
        return sorted(runs, key=lambda run: run["timestamp"], reverse=True)

    @router.get("/runs/{filename}")
    async def get_run(filename: str) -> dict[str, Any]:
        """Return safe details for one core dump identified by its basename."""
        if Path(filename).name != filename or not filename.endswith(".json"):
            raise HTTPException(status_code=404, detail="Run not found")
        report = _read_json(core_dumps_dir / filename)
        if report is None:
            raise HTTPException(status_code=404, detail="Run not found")
        return _safe_run_detail(report)

    @router.get("/modules")
    async def list_modules() -> list[dict[str, Any]]:
        """List module metadata and optional latest test-run reports."""
        if not metadata_dir.is_dir():
            return []
        modules = []
        for file_path in metadata_dir.glob("*.json"):
            if file_path.name.endswith("_run.json") or "_" not in file_path.stem:
                continue
            fingerprint = _read_json(file_path)
            if fingerprint is None:
                continue
            module_name, language = file_path.stem.rsplit("_", maxsplit=1)
            run_report = _read_json(metadata_dir / f"{file_path.stem}_run.json")
            modules.append({
                "module_name": module_name,
                "language": language,
                "fingerprint": fingerprint,
                "run_report": run_report,
            })
        return sorted(modules, key=lambda module: module["module_name"])

    return router
