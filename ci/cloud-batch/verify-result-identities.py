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


def _validate_cloud_execution(results: Sequence[object]) -> int | None:
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
    prior_attempt_count = 0
    prior_elapsed = 0.0
    for task_index in range(68, 76):
        execution = cloud_results[task_index].get("execution")
        if not isinstance(execution, dict) or set(execution) != {
            "auth_elapsed_seconds",
            "auth_attempt_count",
            "batch_task_retry_attempt",
            "logical_case",
        }:
            raise ResultIdentityError("cloud execution evidence invalid")
        elapsed = execution["auth_elapsed_seconds"]
        attempts = execution["auth_attempt_count"]
        retry = execution["batch_task_retry_attempt"]
        valid_elapsed = (
            isinstance(elapsed, (int, float))
            and not isinstance(elapsed, bool)
            and math.isfinite(elapsed)
            and elapsed >= prior_elapsed
        )
        valid_attempts = (
            isinstance(attempts, int)
            and not isinstance(attempts, bool)
            and attempts >= max(1, prior_attempt_count)
        )
        valid_retry = (
            isinstance(retry, int) and not isinstance(retry, bool) and retry >= 0
        )
        if not (
            valid_elapsed
            and valid_attempts
            and valid_retry
            and execution["logical_case"] == task_index - 67
        ):
            raise ResultIdentityError("cloud execution evidence invalid")
        prior_elapsed = float(elapsed)
        prior_attempt_count = attempts
        retries.add(retry)
    if len(retries) != 1:
        raise ResultIdentityError("cloud execution evidence invalid")
    return next(iter(retries))


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
    result_retry = _validate_cloud_execution(results)
    attempt_retries = _validate_attempt_evidence(results_dir, identity, tasks)
    if result_retry is not None and result_retry not in attempt_retries:
        raise ResultIdentityError("cloud attempt evidence incomplete")


def _validate_attempt_evidence(
    results_dir: Path,
    identity: Mapping[str, str],
    tasks: Mapping[int, Mapping[str, object]],
) -> set[int]:
    """Bind append-only cloud auth attempts to the candidate and physical task."""
    cloud_indexes = set(range(68, 76))
    if not cloud_indexes <= set(tasks):
        return set()
    resources = {tasks[index]["task_resource"] for index in cloud_indexes}
    raw_indexes = {tasks[index]["raw_task_index"] for index in cloud_indexes}
    if len(resources) != 1 or len(raw_indexes) != 1:
        raise ResultIdentityError("cloud attempt identity configuration invalid")
    paths = sorted(results_dir.glob("cloud_regression_attempt_*.jsonl"))
    if not paths:
        raise ResultIdentityError("cloud attempt evidence incomplete")
    expected_resource = next(iter(resources))
    retries: set[int] = set()
    for path in paths:
        retries.add(
            _validate_attempt_file(path, identity["candidate_sha"], expected_resource)
        )
    return retries


def _validate_attempt_file(path: Path, candidate_sha: str, task_resource: object) -> int:
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
    if (
        not events
        or not isinstance(events[0], dict)
        or events[0].get("event") != "attempt_started"
    ):
        raise ResultIdentityError("cloud attempt evidence invalid")
    for event in events:
        if (
            not isinstance(event, dict)
            or event.get("attempt_id") != attempt_id
            or event.get("batch_task_retry_attempt") != retry
            or event.get("candidate_sha") != candidate_sha
            or event.get("task_resource") != task_resource
        ):
            raise ResultIdentityError("cloud attempt evidence invalid")
    return retry


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
