#!/usr/bin/env python3
"""Verify every Cloud Batch result against immutable run identity evidence."""
# pylint: disable=invalid-name,duplicate-code

from __future__ import annotations

import argparse
import json
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
        for raw_task_index, task_index in enumerate(job["task_indexes"]):
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
