#!/usr/bin/env python3
"""Verify every Cloud Batch result against immutable run identity evidence."""
# pylint: disable=invalid-name,duplicate-code

from __future__ import annotations

import argparse
import json
import math
import re
import sys
from collections.abc import Mapping, Sequence
from pathlib import Path


IDENTITY_FIELDS = (
    "candidate_sha",
    "candidate_tree",
    "source_sha256",
    "source_generation",
    "image_digest",
)
TASK_IDENTITY_FIELDS = (
    "job_name",
    "task_group",
    "raw_task_index",
    "task_resource",
)
ATTEMPT_FILE = re.compile(
    r"^cloud_regression_attempt_(?P<retry>0|[1-9][0-9]*)_(?P<id>[0-9a-f]{32})\.jsonl$"
)


class ResultIdentityError(RuntimeError):
    """A result set is missing or disagrees with immutable run evidence."""


def validate_results(
    results: Sequence[object],
    *,
    expected_identity: Mapping[str, str],
    expected_tasks: Mapping[int, Mapping[str, object]],
) -> None:
    """Require one exact, identity-bound result for every expected task."""
    if set(expected_identity) != set(IDENTITY_FIELDS) or not expected_tasks:
        raise ResultIdentityError("result identity configuration invalid")
    observed: dict[int, object] = {}
    for result in results:
        if not isinstance(result, dict) or not isinstance(result.get("task_index"), int):
            raise ResultIdentityError("result identity invalid")
        task_index = result["task_index"]
        if task_index in observed or task_index not in expected_tasks:
            raise ResultIdentityError("result task identity invalid")
        identity = result.get("identity")
        if not isinstance(identity, dict):
            raise ResultIdentityError("result identity missing")
        if any(identity.get(field) != expected_identity[field] for field in IDENTITY_FIELDS):
            raise ResultIdentityError("result identity mismatch")
        if any(
            identity.get(field) != expected_tasks[task_index][field]
            for field in TASK_IDENTITY_FIELDS
        ):
            raise ResultIdentityError("result task identity mismatch")
        observed[task_index] = result
    if set(observed) != set(expected_tasks):
        raise ResultIdentityError("result identity set incomplete")
    _validate_cloud_execution(results)


def _validate_cloud_execution(results: Sequence[object]) -> tuple[int, str] | None:
    """Validate sanitized auth/attempt evidence on the eight logical results."""
    cloud_results = {
        result["task_index"]: result
        for result in results
        if isinstance(result, dict) and result.get("task_index") in range(68, 76)
    }
    if not cloud_results:
        return None
    if set(cloud_results) != set(range(68, 76)):
        raise ResultIdentityError("cloud execution evidence incomplete")
    retries: set[int] = set()
    attempt_ids: set[str] = set()
    prior_attempt_count = 0
    prior_elapsed = 0.0
    for task_index in range(68, 76):
        execution = cloud_results[task_index].get("execution")
        if not isinstance(execution, dict) or set(execution) != {
            "auth_elapsed_seconds",
            "auth_attempt_count",
            "batch_task_retry_attempt",
            "logical_case",
            "jwt_fingerprint",
        }:
            raise ResultIdentityError("cloud execution evidence invalid")
        elapsed = execution["auth_elapsed_seconds"]
        attempts = execution["auth_attempt_count"]
        retry = execution["batch_task_retry_attempt"]
        attempt_id = cloud_results[task_index].get("attempt_id")
        if not (
            isinstance(elapsed, (int, float))
            and not isinstance(elapsed, bool)
            and math.isfinite(elapsed)
            and elapsed >= prior_elapsed
            and isinstance(attempts, int)
            and not isinstance(attempts, bool)
            and attempts >= max(1, prior_attempt_count)
            and isinstance(retry, int)
            and not isinstance(retry, bool)
            and retry >= 0
            and execution["logical_case"] == task_index - 67
            and isinstance(attempt_id, str)
            and re.fullmatch(r"[0-9a-f]{32}", attempt_id)
            and (
                execution["jwt_fingerprint"] is None
                or isinstance(execution["jwt_fingerprint"], str)
                and re.fullmatch(
                    r"sha256:[0-9a-f]{64}", execution["jwt_fingerprint"]
                )
            )
        ):
            raise ResultIdentityError("cloud execution evidence invalid")
        prior_elapsed = float(elapsed)
        prior_attempt_count = attempts
        retries.add(retry)
        attempt_ids.add(attempt_id)
    if len(retries) != 1 or len(attempt_ids) != 1:
        raise ResultIdentityError("cloud execution evidence invalid")
    return next(iter(retries)), next(iter(attempt_ids))


def _validate_attempt_events(
    events: Sequence[object],
    *,
    attempt_id: str,
    retry: int,
    candidate_sha: str,
    task_resource: object,
) -> None:
    """Validate event boundaries, names, and immutable attempt identity."""
    if not events or not isinstance(events[0], dict):
        raise ResultIdentityError("cloud attempt evidence invalid")
    if events[0].get("event") != "attempt_started":
        raise ResultIdentityError("cloud attempt evidence invalid")
    if (
        not isinstance(events[-1], dict)
        or events[-1].get("event") != "attempt_finished"
    ):
        raise ResultIdentityError("cloud attempt evidence incomplete")
    allowed = {
        "attempt_started",
        "auth_succeeded",
        "auth_failed",
        "case_finished",
        "attempt_finished",
    }
    for event in events:
        if not isinstance(event, dict):
            raise ResultIdentityError("cloud attempt evidence invalid")
        if (
            event.get("event") not in allowed
            or event.get("attempt_id") != attempt_id
            or event.get("batch_task_retry_attempt") != retry
            or event.get("candidate_sha") != candidate_sha
            or event.get("task_resource") != task_resource
        ):
            raise ResultIdentityError("cloud attempt evidence invalid")
    if (
        sum(event["event"] == "attempt_started" for event in events) != 1
        or sum(event["event"] == "attempt_finished" for event in events) != 1
    ):
        raise ResultIdentityError("cloud attempt evidence invalid")


def _valid_auth_elapsed(value: object, minimum: float) -> bool:
    return (
        isinstance(value, (int, float))
        and not isinstance(value, bool)
        and math.isfinite(value)
        and value >= minimum
    )


def _validate_auth_metrics(
    event: Mapping[str, object], prior_count: int, prior_elapsed: float
) -> tuple[int, float]:
    count = event.get("auth_attempt_count")
    elapsed = event.get("auth_elapsed_seconds")
    if (
        not isinstance(count, int)
        or isinstance(count, bool)
        or count != prior_count + 1
        or not _valid_auth_elapsed(elapsed, prior_elapsed)
    ):
        raise ResultIdentityError("cloud attempt evidence invalid")
    return count, float(elapsed)


def _validate_auth_event_shape(
    event: Mapping[str, object], envelope: set[str]
) -> tuple[bool, str | None]:
    """Return whether an exact auth event succeeded and its fingerprint."""
    if event["event"] == "auth_failed":
        if set(event) != envelope | {
            "auth_attempt_count",
            "auth_elapsed_seconds",
            "category",
        } or event.get("category") not in {
            "expired_token",
            "invalid_response",
            "invalid_token",
            "parse_failed",
            "provider_rejected",
            "quota_exceeded",
            "transport_failed",
        }:
            raise ResultIdentityError("cloud attempt evidence invalid")
        return False, None
    fingerprint = event.get("jwt_fingerprint")
    if (
        set(event)
        != envelope
        | {
            "auth_attempt_count",
            "auth_elapsed_seconds",
            "jwt_fingerprint",
        }
        or not isinstance(fingerprint, str)
        or not re.fullmatch(r"sha256:[0-9a-f]{64}", fingerprint)
    ):
        raise ResultIdentityError("cloud attempt evidence invalid")
    return True, fingerprint


def _validate_case_event(
    event: Mapping[str, object],
    envelope: set[str],
    expected_case: int,
    auth_state: tuple[int, float, object],
) -> None:
    """Require one exact case event bound to the current auth state."""
    auth_count, auth_elapsed, active_fingerprint = auth_state
    if event["event"] != "case_finished" or set(event) != envelope | {
        "logical_case",
        "status",
        "auth_attempt_count",
        "auth_elapsed_seconds",
        "jwt_fingerprint",
    }:
        raise ResultIdentityError("cloud attempt evidence invalid")
    if (
        event.get("logical_case") != expected_case
        or event.get("status") not in {"passed", "failed", "error"}
    ):
        raise ResultIdentityError("cloud attempt evidence invalid")
    if (
        event.get("auth_attempt_count") != auth_count
        or event.get("auth_elapsed_seconds") != auth_elapsed
    ):
        raise ResultIdentityError("cloud attempt evidence invalid")
    if event.get("jwt_fingerprint") != active_fingerprint:
        raise ResultIdentityError("cloud attempt evidence invalid")
    if active_fingerprint is None and event.get("status") != "error":
        raise ResultIdentityError("cloud attempt evidence invalid")


def _validate_attempt_grammar(
    events: Sequence[Mapping[str, object]],
) -> list[Mapping[str, object]]:
    """Validate strict auth transitions and their binding to each logical case."""
    envelope = {
        "event",
        "attempt_id",
        "batch_task_retry_attempt",
        "candidate_sha",
        "task_resource",
    }
    if set(events[0]) != envelope:
        raise ResultIdentityError("cloud attempt evidence invalid")
    auth_count = 0
    auth_elapsed = 0.0
    active_fingerprint: object = None
    consecutive_failures = 0
    auth_succeeded_since_case = False
    auth_exhausted = False
    expected_case = 1
    cases: list[Mapping[str, object]] = []
    for event in events[1:-1]:
        name = event["event"]
        if name in {"auth_failed", "auth_succeeded"}:
            if (
                expected_case > 8
                or auth_exhausted
                or auth_succeeded_since_case
                or consecutive_failures >= 6
            ):
                raise ResultIdentityError("cloud attempt evidence invalid")
            auth_count, auth_elapsed = _validate_auth_metrics(
                event, auth_count, auth_elapsed
            )
            succeeded, fingerprint = _validate_auth_event_shape(event, envelope)
            if succeeded:
                active_fingerprint = fingerprint
                consecutive_failures = 0
                auth_succeeded_since_case = True
            else:
                consecutive_failures += 1
            continue
        if consecutive_failures:
            if consecutive_failures != 6:
                raise ResultIdentityError("cloud attempt evidence invalid")
            active_fingerprint = None
            auth_exhausted = True
            consecutive_failures = 0
        _validate_case_event(
            event,
            envelope,
            expected_case,
            (auth_count, auth_elapsed, active_fingerprint),
        )
        cases.append(event)
        expected_case += 1
        auth_succeeded_since_case = False
    if expected_case != 9:
        raise ResultIdentityError("cloud attempt evidence incomplete")
    final = events[-1]
    if (
        set(final)
        != envelope
        | {
            "status",
            "cases_completed",
            "auth_attempt_count",
            "auth_elapsed_seconds",
        }
        or final.get("status") not in {"passed", "failed"}
        or final.get("cases_completed") != 8
        or final.get("auth_attempt_count") != auth_count
        or final.get("auth_elapsed_seconds") != auth_elapsed
    ):
        raise ResultIdentityError("cloud attempt evidence invalid")
    return cases


def _expected_from_evidence(
    evidence: object,
) -> tuple[dict[str, str], dict[int, dict[str, object]]]:
    if not isinstance(evidence, dict) or not isinstance(evidence.get("job_uids"), dict):
        raise ResultIdentityError("result identity configuration invalid")
    identity = {field: evidence.get(field) for field in IDENTITY_FIELDS}
    if not all(isinstance(value, str) and value for value in identity.values()):
        raise ResultIdentityError("result identity configuration invalid")
    project = evidence.get("project")
    location = evidence.get("location")
    if not isinstance(project, str) or not isinstance(location, str):
        raise ResultIdentityError("result identity configuration invalid")
    tasks: dict[int, dict[str, object]] = {}
    for job_name, job in evidence["job_uids"].items():
        if not isinstance(job, dict) or not isinstance(job.get("task_indexes"), list):
            raise ResultIdentityError("result identity configuration invalid")
        uid = job.get("uid")
        if (
            not isinstance(job_name, str)
            or not job_name
            or not isinstance(uid, str)
            or not uid
        ):
            raise ResultIdentityError("result identity configuration invalid")
        logical_indexes = job["task_indexes"]
        physical_indexes = job.get("physical_task_indexes")
        if physical_indexes is None:
            physical_indexes = list(range(len(logical_indexes)))
        if (
            not isinstance(physical_indexes, list)
            or len(physical_indexes) != len(logical_indexes)
            or any(
                not isinstance(index, int) or isinstance(index, bool) or index < 0
                for index in physical_indexes
            )
        ):
            raise ResultIdentityError("result identity configuration invalid")
        physical_count = len(set(physical_indexes))
        if set(physical_indexes) != set(range(physical_count)):
            raise ResultIdentityError("result identity configuration invalid")
        for task_index, raw_task_index in zip(logical_indexes, physical_indexes):
            if not isinstance(task_index, int) or task_index in tasks:
                raise ResultIdentityError("result identity configuration invalid")
            tasks[task_index] = {
                "job_name": job_name,
                "task_group": "group0",
                "raw_task_index": raw_task_index,
                "task_resource": (
                    f"projects/{project}/locations/{location}/jobs/{job_name}/"
                    f"taskGroups/group0/tasks/{raw_task_index}"
                ),
            }
    return identity, tasks


def validate_result_directory(evidence_path: Path, results_dir: Path) -> None:
    """Require exact JSON/log artifacts and validate every result identity."""
    evidence = json.loads(evidence_path.read_text(encoding="utf-8"))
    identity, tasks = _expected_from_evidence(evidence)
    expected_json = {f"task_{task_index}.json" for task_index in tasks}
    expected_logs = {f"task_{task_index}.log" for task_index in tasks}
    observed_json = {path.name for path in results_dir.glob("task_*.json")}
    observed_logs = {path.name for path in results_dir.glob("task_*.log")}
    if observed_json - expected_json or observed_logs - expected_logs:
        raise ResultIdentityError("result artifact set invalid")
    if observed_json != expected_json or observed_logs != expected_logs:
        raise ResultIdentityError("result artifact set incomplete")
    results = []
    for task_index in sorted(tasks):
        path = results_dir / f"task_{task_index}.json"
        results.append(json.loads(path.read_text(encoding="utf-8")))
    validate_results(results, expected_identity=identity, expected_tasks=tasks)
    result_attempt = _validate_cloud_execution(results)
    _validate_attempt_evidence(results_dir, identity, tasks, results, result_attempt)


def _validate_attempt_evidence(
    results_dir: Path,
    identity: Mapping[str, str],
    tasks: Mapping[int, Mapping[str, object]],
    results: Sequence[object],
    result_attempt: tuple[int, str] | None,
) -> None:
    """Bind append-only cloud auth attempts to the candidate and physical task."""
    cloud_indexes = set(range(68, 76))
    if not cloud_indexes <= set(tasks):
        return
    resources = {tasks[index]["task_resource"] for index in cloud_indexes}
    raw_indexes = {tasks[index]["raw_task_index"] for index in cloud_indexes}
    if len(resources) != 1 or len(raw_indexes) != 1:
        raise ResultIdentityError("cloud attempt identity configuration invalid")
    if result_attempt is None:
        raise ResultIdentityError("cloud attempt evidence incomplete")
    expected_resource = next(iter(resources))
    retry, attempt_id = result_attempt
    path = results_dir / f"cloud_regression_attempt_{retry}_{attempt_id}.jsonl"
    if not path.is_file():
        raise ResultIdentityError("cloud attempt evidence incomplete")
    cloud_results = {
        result["execution"]["logical_case"]: result
        for result in results
        if isinstance(result, dict) and result.get("task_index") in cloud_indexes
    }
    _validate_attempt_file(
        path, identity["candidate_sha"], expected_resource, cloud_results
    )


def _validate_attempt_file(
    path: Path,
    candidate_sha: str,
    task_resource: object,
    cloud_results: Mapping[int, Mapping[str, object]],
) -> None:
    """Validate one uniquely named, append-only physical-attempt event stream."""
    match = ATTEMPT_FILE.fullmatch(path.name)
    if not match:
        raise ResultIdentityError("cloud attempt evidence invalid")
    retry = int(match.group("retry"))
    attempt_id = match.group("id")
    try:
        events = [
            json.loads(line) for line in path.read_text(encoding="utf-8").splitlines()
        ]
    except ValueError as error:
        raise ResultIdentityError("cloud attempt evidence invalid") from error
    _validate_attempt_events(
        events,
        attempt_id=attempt_id,
        retry=retry,
        candidate_sha=candidate_sha,
        task_resource=task_resource,
    )
    cases = _validate_attempt_grammar(events)
    if [event.get("logical_case") for event in cases] != list(range(1, 9)):
        raise ResultIdentityError("cloud attempt evidence incomplete")
    for event in cases:
        result = cloud_results[event["logical_case"]]
        execution = result["execution"]
        if (
            event.get("status") != result.get("status")
            or event.get("auth_attempt_count") != execution["auth_attempt_count"]
            or event.get("auth_elapsed_seconds") != execution["auth_elapsed_seconds"]
            or event.get("jwt_fingerprint") != execution["jwt_fingerprint"]
        ):
            raise ResultIdentityError("cloud attempt evidence invalid")
    final = events[-1]
    expected_status = "failed" if any(
        result.get("status") != "passed" for result in cloud_results.values()
    ) else "passed"
    if (
        final.get("status") != expected_status
        or final.get("cases_completed") != 8
        or final.get("auth_attempt_count") != cases[-1]["auth_attempt_count"]
        or final.get("auth_elapsed_seconds") != cases[-1]["auth_elapsed_seconds"]
    ):
        raise ResultIdentityError("cloud attempt evidence incomplete")


def parse_args() -> argparse.Namespace:
    """Parse evidence and result-directory arguments."""
    parser = argparse.ArgumentParser()
    parser.add_argument("--evidence", type=Path, required=True)
    parser.add_argument("--results", type=Path, required=True)
    return parser.parse_args()


def main() -> int:
    """Verify result identities and emit only non-sensitive status."""
    args = parse_args()
    try:
        validate_result_directory(args.evidence, args.results)
    except (OSError, ValueError, ResultIdentityError):
        print("FATAL: Cloud Batch result identity verification failed", file=sys.stderr)
        return 2
    print("Cloud Batch result identities verified.")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
