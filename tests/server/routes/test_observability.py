"""Tests for the read-only PDD Connect observability API."""

from __future__ import annotations

import json

from fastapi import FastAPI
from fastapi.testclient import TestClient

from pdd.server.routes.observability import create_observability_router


def _client(project_root):
    app = FastAPI()
    app.include_router(create_observability_router(project_root))
    return TestClient(app)


def test_runs_are_sorted_and_invalid_reports_are_ignored(tmp_path):
    core_dumps = tmp_path / ".pdd" / "core_dumps"
    core_dumps.mkdir(parents=True)
    (core_dumps / "older.json").write_text(json.dumps({"timestamp_utc": "2026-01-01", "argv": ["sync"]}))
    (core_dumps / "newer.json").write_text(json.dumps({"timestamp_utc": "2026-01-02", "argv": ["checkup"], "steps": [{"model": "local/test"}]}))
    (core_dumps / "broken.json").write_text("not json")

    response = _client(tmp_path).get("/api/v1/observability/runs")

    assert response.status_code == 200
    assert [run["filename"] for run in response.json()] == ["newer.json", "older.json"]
    assert response.json()[0]["model"] == "local/test"


def test_run_details_exclude_environment_and_redact_secrets(tmp_path):
    core_dumps = tmp_path / ".pdd" / "core_dumps"
    core_dumps.mkdir(parents=True)
    (core_dumps / "run.json").write_text(json.dumps({
        "environment": {"API_KEY": "must-not-leak"},
        "terminal_output": "API_KEY=must-not-leak",
        "steps": [{"model": "model", "access_token": "must-not-leak"}],
        "errors": [{"message": "token=must-not-leak", "api_key": "must-not-leak"}],
    }))

    response = _client(tmp_path).get("/api/v1/observability/runs/run.json")

    assert response.status_code == 200
    assert "environment" not in response.json()
    assert "must-not-leak" not in response.text
    assert response.json()["steps"][0]["access_token"] == "[redacted]"


def test_run_details_reject_paths_outside_core_dumps(tmp_path):
    response = _client(tmp_path).get("/api/v1/observability/runs/%2E%2E%2Fother.json")

    assert response.status_code == 404


def test_modules_return_metadata_with_optional_run_report(tmp_path):
    meta = tmp_path / ".pdd" / "meta"
    meta.mkdir(parents=True)
    (meta / "parser_python.json").write_text(json.dumps({"timestamp": "2026-01-01"}))
    (meta / "parser_python_run.json").write_text(json.dumps({"tests_passed": 3, "tests_failed": 0}))

    response = _client(tmp_path).get("/api/v1/observability/modules")

    assert response.status_code == 200
    assert response.json() == [{
        "module_name": "parser",
        "language": "python",
        "fingerprint": {"timestamp": "2026-01-01"},
        "run_report": {"tests_passed": 3, "tests_failed": 0},
    }]
