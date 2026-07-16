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
        assert "FIREBASE_API_KEY" not in environment
        assert "PDD_REFRESH_TOKEN" not in environment
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
        assert len(result["attempt_id"]) == 32
        assert result["identity"]["raw_task_index"] == 0
        assert result["execution"] == {
            "auth_elapsed_seconds": 0.0,
            "auth_attempt_count": 1,
            "batch_task_retry_attempt": 2,
            "logical_case": index - 67,
            "jwt_fingerprint": runner._jwt_fingerprint(
                json.loads(_jwt(10_000))["id_token"]
            ),
        }
    attempt_files = list(tmp_path.glob("cloud_regression_attempt_2_*.jsonl"))
    assert len(attempt_files) == 1
    events = [json.loads(line) for line in attempt_files[0].read_text().splitlines()]
    assert events[0]["event"] == "attempt_started"
    assert events[-1]["event"] == "attempt_finished"
    assert {event["candidate_sha"] for event in events} == {"a" * 40}
    assert len({event["attempt_id"] for event in events}) == 1
    attempt_id = events[0]["attempt_id"]
    assert {
        json.loads((tmp_path / f"task_{index}.json").read_text())["attempt_id"]
        for index in range(68, 76)
    } == {attempt_id}
    assert {event["task_resource"] for event in events} == {
        "projects/trusted-project/locations/us-central1/jobs/job-name/"
        "taskGroups/group0/tasks/0"
    }
    assert all(
        "fake-api-key" not in event and "fake-refresh-token" not in event
        for event in attempt_files[0].read_text().splitlines()
    )

    validator_spec = importlib.util.spec_from_file_location(
        "cloud_result_validator",
        REPO_ROOT / "ci" / "cloud-batch" / "verify-result-identities.py",
    )
    assert validator_spec and validator_spec.loader
    validator = importlib.util.module_from_spec(validator_spec)
    validator_spec.loader.exec_module(validator)
    evidence = {
        "project": "trusted-project",
        "location": "us-central1",
        "candidate_sha": "a" * 40,
        "candidate_tree": "b" * 40,
        "source_sha256": "c" * 64,
        "source_generation": "123",
        "image_digest": "sha256:" + "d" * 64,
        "job_uids": {
            "job-name": {
                "uid": "job-uid",
                "task_indexes": list(range(68, 76)),
                "physical_task_indexes": [0] * 8,
            }
        },
    }
    evidence_path = tmp_path / "identity.json"
    evidence_path.write_text(json.dumps(evidence), encoding="utf-8")
    validator.validate_result_directory(evidence_path, tmp_path)

    complete_stream = attempt_files[0].read_text()
    attempt_files[0].write_text(complete_stream.splitlines()[0] + "\n")
    try:
        validator.validate_result_directory(evidence_path, tmp_path)
    except validator.ResultIdentityError as error:
        assert "cloud attempt evidence incomplete" in str(error)
    else:
        raise AssertionError("truncated final attempt stream was accepted")
    attempt_files[0].write_text(complete_stream)

    late_auth = next(event.copy() for event in events if event["event"] == "auth_succeeded")
    late_auth.update(
        auth_attempt_count=999,
        auth_elapsed_seconds=-1,
        jwt_fingerprint="sha256:invalid",
    )
    contradictory_stream = [*events[:-1], late_auth, events[-1]]
    attempt_files[0].write_text(
        "".join(json.dumps(event) + "\n" for event in contradictory_stream)
    )
    try:
        validator.validate_result_directory(evidence_path, tmp_path)
    except validator.ResultIdentityError as error:
        assert "cloud attempt evidence invalid" in str(error)
    else:
        raise AssertionError("contradictory late auth event was accepted")
    attempt_files[0].write_text(complete_stream)

    tampered_path = tmp_path / "task_75.json"
    tampered = json.loads(tampered_path.read_text())
    tampered["execution"]["auth_attempt_count"] = 0
    tampered_path.write_text(json.dumps(tampered), encoding="utf-8")
    try:
        validator.validate_result_directory(evidence_path, tmp_path)
    except validator.ResultIdentityError as error:
        assert "cloud execution evidence invalid" in str(error)
    else:
        raise AssertionError("tampered auth evidence was accepted")


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


def test_printed_jwt_is_redacted_and_fails_case_without_persisting_token(tmp_path: Path):
    runner = _load_runner()
    token_document = _jwt(4_000_000_000)
    token = json.loads(token_document)["id_token"]

    def invoke(_case: int, log_path: Path, environment: dict[str, str]) -> int:
        log_path.write_text(f"unsafe {environment['PDD_JWT_TOKEN']}\n", encoding="utf-8")
        return 0

    outcome = runner.run_cloud_regression(
        _environment(), tmp_path, exchange=lambda *_args: token_document,
        invoke_case=invoke,
    )

    assert outcome == 1
    rendered = "\n".join(path.read_text() for path in tmp_path.iterdir())
    assert token not in rendered
    assert "jwt_log_boundary_failed" in rendered
    fingerprints = {
        json.loads((tmp_path / f"task_{index}.json").read_text())["execution"][
            "jwt_fingerprint"
        ]
        for index in range(68, 76)
    }
    assert len(fingerprints) == 1
    assert next(iter(fingerprints)).startswith("sha256:")


def test_base64_encoded_jwt_is_redacted_without_persisting_reversible_credential(
    tmp_path: Path,
):
    runner = _load_runner()
    token_document = _jwt(4_000_000_000)
    token = json.loads(token_document)["id_token"]
    encoded = {
        representation
        for representation in (
            base64.b64encode(token.encode("utf-8")).decode("ascii"),
            base64.urlsafe_b64encode(token.encode("utf-8")).decode("ascii"),
        )
        for representation in (representation, representation.rstrip("="))
    }

    def invoke(_case: int, log_path: Path, _environment: dict[str, str]) -> int:
        log_path.write_text("unsafe " + " ".join(sorted(encoded)) + "\n", encoding="utf-8")
        return 0

    outcome = runner.run_cloud_regression(
        _environment(),
        tmp_path,
        exchange=lambda *_args: token_document,
        invoke_case=invoke,
    )

    if outcome != 1:
        raise AssertionError("encoded runtime JWT did not fail closed")
    rendered = "\n".join(path.read_text() for path in tmp_path.iterdir())
    if token in rendered or any(representation in rendered for representation in encoded):
        raise AssertionError("reversible runtime JWT representation remained in artifacts")
