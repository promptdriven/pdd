"""Deterministic tests for the single-task cloud-regression runner."""

from __future__ import annotations

import base64
import importlib.util
import json
from pathlib import Path


REPO_ROOT = Path(__file__).resolve().parents[1]
RUNNER_PATH = REPO_ROOT / "ci" / "cloud-batch" / "cloud-regression-runner.py"


def _load_runner():
    spec = importlib.util.spec_from_file_location("cloud_regression_runner", RUNNER_PATH)
    assert spec and spec.loader
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def _jwt(expiry: int) -> bytes:
    payload = base64.urlsafe_b64encode(json.dumps({"exp": expiry}).encode()).rstrip(b"=")
    token = b"header." + payload + b".signature"
    return json.dumps({"id_token": token.decode()}).encode()


def _environment() -> dict[str, str]:
    return {
        "BATCH_TASK_INDEX": "0",
        "BATCH_TASK_RETRY_ATTEMPT": "2",
        "PDD_BATCH_PROJECT": "trusted-project",
        "PDD_BATCH_LOCATION": "us-central1",
        "PDD_BATCH_JOB_NAME": "job-name",
        "PDD_CANDIDATE_SHA": "a" * 40,
        "PDD_CANDIDATE_TREE": "b" * 40,
        "PDD_SOURCE_SHA256": "c" * 64,
        "PDD_SOURCE_GCS_GENERATION": "123",
        "PDD_IMAGE_DIGEST": "sha256:" + "d" * 64,
        "FIREBASE_API_KEY": "fake-api-key",
        "PDD_REFRESH_TOKEN": "fake-refresh-token",
    }


class _Clock:
    def __init__(self, value: float = 1_000.0) -> None:
        self.value = value

    def monotonic(self) -> float:
        return self.value

    def time(self) -> float:
        return self.value

    def sleep(self, seconds: float) -> None:
        self.value += seconds


def test_single_exchange_runs_eight_cases_and_emits_logical_artifacts(tmp_path: Path):
    runner = _load_runner()
    clock = _Clock()
    exchanges: list[int] = []
    cases: list[int] = []

    def fake_endpoint(_api_key: str, _refresh_token: str) -> bytes:
        exchanges.append(1)
        return _jwt(10_000)

    def invoke(case: int, log_path: Path, environment: dict[str, str]) -> int:
        cases.append(case)
        assert environment["PDD_JWT_TOKEN"].count(".") == 2
        log_path.write_text(f"case {case} safe output\n", encoding="utf-8")
        return 0

    outcome = runner.run_cloud_regression(
        _environment(),
        tmp_path,
        exchange=fake_endpoint,
        invoke_case=invoke,
        monotonic=clock.monotonic,
        wall_time=clock.time,
        sleep=clock.sleep,
    )

    assert outcome == 0
    assert len(exchanges) == 1
    assert cases == list(range(1, 9))
    assert {path.name for path in tmp_path.glob("task_*.json")} == {
        f"task_{index}.json" for index in range(68, 76)
    }
    assert {path.name for path in tmp_path.glob("task_*.log")} == {
        f"task_{index}.log" for index in range(68, 76)
    }
    for index in range(68, 76):
        result = json.loads((tmp_path / f"task_{index}.json").read_text())
        assert result["identity"]["raw_task_index"] == 0
        assert result["execution"] == {
            "auth_elapsed_seconds": 0.0,
            "auth_attempt_count": 1,
            "batch_task_retry_attempt": 2,
            "logical_case": index - 67,
        }
    attempt_files = list(tmp_path.glob("cloud_regression_attempt_2_*.jsonl"))
    assert len(attempt_files) == 1
    events = [json.loads(line) for line in attempt_files[0].read_text().splitlines()]
    assert events[0]["event"] == "attempt_started"
    assert events[-1]["event"] == "attempt_finished"
    assert all("fake-api-key" not in event and "fake-refresh-token" not in event for event in attempt_files[0].read_text().splitlines())


def test_quota_failure_records_true_elapsed_attempt_evidence_and_invokes_no_case(tmp_path: Path):
    runner = _load_runner()
    clock = _Clock()
    calls = 0

    def quota_endpoint(_api_key: str, _refresh_token: str) -> bytes:
        nonlocal calls
        calls += 1
        return b'{"error":{"message":"QUOTA_EXCEEDED"}}'

    outcome = runner.run_cloud_regression(
        _environment(),
        tmp_path,
        exchange=quota_endpoint,
        invoke_case=lambda *_args: (_ for _ in ()).throw(AssertionError("case invoked")),
        monotonic=clock.monotonic,
        wall_time=clock.time,
        sleep=clock.sleep,
        jitter=lambda _upper: 0,
    )

    assert outcome == 1
    assert calls == 6
    assert clock.monotonic() == 1_150.0
    for index in range(68, 76):
        result = json.loads((tmp_path / f"task_{index}.json").read_text())
        assert result["status"] == "error"
        assert result["detail"] == f"jwt_exchange_failed_case_{index - 67}: quota_exceeded"
        assert result["execution"]["auth_elapsed_seconds"] == 150.0
        assert result["execution"]["auth_attempt_count"] == 6
        assert (tmp_path / f"task_{index}.log").exists()


def test_expired_token_is_refreshed_only_before_the_next_case(tmp_path: Path):
    runner = _load_runner()
    clock = _Clock()
    expiries = iter((1_001, 10_000))
    exchanges = 0

    def endpoint(_api_key: str, _refresh_token: str) -> bytes:
        nonlocal exchanges
        exchanges += 1
        return _jwt(next(expiries))

    outcome = runner.run_cloud_regression(
        _environment(),
        tmp_path,
        exchange=endpoint,
        invoke_case=lambda _case, log, _env: (log.write_text("safe\n"), 0)[1],
        monotonic=clock.monotonic,
        wall_time=clock.time,
        sleep=clock.sleep,
    )

    assert outcome == 0
    assert exchanges == 2


def test_invalid_token_response_fails_closed_without_response_body_in_evidence(tmp_path: Path):
    runner = _load_runner()
    sensitive_body = b'{"id_token":"credential-response-body"}'

    outcome = runner.run_cloud_regression(
        _environment(),
        tmp_path,
        exchange=lambda *_args: sensitive_body,
        invoke_case=lambda *_args: (_ for _ in ()).throw(AssertionError("case invoked")),
        sleep=lambda _seconds: None,
        jitter=lambda _upper: 0,
    )

    assert outcome == 1
    rendered = "\n".join(path.read_text() for path in tmp_path.iterdir())
    assert "credential-response-body" not in rendered

