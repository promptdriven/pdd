#!/usr/bin/env python3
"""Fail when attributable Cloud Batch logs contain a configured credential."""
# pylint: disable=invalid-name

from __future__ import annotations

import argparse
import hashlib
import json
import re
import subprocess
import sys
import urllib.parse
from collections.abc import Callable, Mapping, Sequence
from pathlib import Path


RESOURCE_PATTERN = re.compile(
    r"^projects/(?P<project>[^/]+)/secrets/(?P<secret>[^/]+)/versions/"
    r"(?P<version>[1-9][0-9]*)$"
)
JOB_SPEC_PATTERN = re.compile(
    r"^(?P<name>[a-z][a-z0-9-]{0,62})=(?P<uid>[A-Za-z0-9-]+)="
    r"(?P<count>[1-9][0-9]*)$"
)
EXPECTED_LOG_IDS = ("batch_agent_logs", "batch_task_logs")
EXPECTED_SECRET_IDS = {
    "GCS_HMAC_ACCESS_KEY_ID",
    "GCS_HMAC_SECRET_ACCESS_KEY",
    "OPENAI_API_KEY",
    "staging-firebase-api-key",
    "github-client-id",
    "pdd-refresh-token",
    "CLAUDE_CODE_OAUTH_TOKEN",
}
PERCENT_ESCAPE = re.compile(r"%[0-9A-Fa-f]{2}")


def fingerprint(value: str) -> str:
    """Return a non-reversible identifier suitable for gate diagnostics."""
    return "sha256:" + hashlib.sha256(value.encode("utf-8")).hexdigest()[:16]


def find_matches(secrets: Mapping[str, str], logs: Sequence[str]) -> list[str]:
    """Find exact payload occurrences while returning fingerprints only."""
    findings: set[str] = set()
    normalized_logs = [
        PERCENT_ESCAPE.sub(lambda match: match.group(0).upper(), log) for log in logs
    ]
    for value in secrets.values():
        representations = {
            value,
            json.dumps(value)[1:-1],
            urllib.parse.quote(value, safe=""),
            urllib.parse.quote_plus(value, safe=""),
        }
        normalized_representations = {
            PERCENT_ESCAPE.sub(lambda match: match.group(0).upper(), representation)
            for representation in representations
        }
        if value and any(
            representation in log
            for representation in normalized_representations
            for log in normalized_logs
        ):
            findings.add(fingerprint(value))
    return sorted(findings)


def _run(command: list[str]) -> str:
    result = subprocess.run(command, check=False, capture_output=True, text=True)
    if result.returncode != 0:
        raise RuntimeError("credential-log verification dependency failed")
    return result.stdout


def _verify_result_identities(evidence: Path, results: Path) -> None:
    verifier = Path(__file__).with_name("verify-result-identities.py")
    result = subprocess.run(
        [
            sys.executable,
            str(verifier),
            "--evidence",
            str(evidence),
            "--results",
            str(results),
        ],
        check=False,
        capture_output=True,
        text=True,
    )
    if result.returncode != 0:
        raise RuntimeError("result identity verification failed")


def _verify_job_evidence(
    evidence: Path, job_specs: Mapping[str, tuple[str, int]]
) -> None:
    """Bind submitted job names, server UIDs, and counts to result evidence."""
    try:
        document = json.loads(evidence.read_text(encoding="utf-8"))
    except (OSError, ValueError) as error:
        raise RuntimeError("Batch job identity evidence invalid") from error
    jobs = document.get("job_uids") if isinstance(document, dict) else None
    if not isinstance(jobs, dict):
        raise RuntimeError("Batch job identity evidence invalid")
    observed: dict[str, tuple[str, int]] = {}
    for job_name, job in jobs.items():
        if (
            not isinstance(job_name, str)
            or not isinstance(job, dict)
            or not isinstance(job.get("uid"), str)
            or not isinstance(job.get("task_indexes"), list)
        ):
            raise RuntimeError("Batch job identity evidence invalid")
        observed[job_name] = (job["uid"], len(job["task_indexes"]))
    if observed != dict(job_specs):
        raise RuntimeError("Batch job identity evidence mismatch")


def _secret_values(
    resources: Sequence[str],
    project: str,
    *,
    command_runner: Callable[[list[str]], str] = _run,
) -> dict[str, str]:
    values: dict[str, str] = {}
    seen_secret_ids: set[str] = set()
    for resource in resources:
        match = RESOURCE_PATTERN.fullmatch(resource)
        if (
            not match
            or match.group("project") != project
            or match.group("secret") not in EXPECTED_SECRET_IDS
            or match.group("secret") in seen_secret_ids
        ):
            raise RuntimeError("credential-log verification configuration invalid")
        seen_secret_ids.add(match.group("secret"))
        value = command_runner(
            [
                "gcloud",
                "secrets",
                "versions",
                "access",
                match.group("version"),
                f"--secret={match.group('secret')}",
                f"--project={project}",
            ]
        )
        if not value:
            raise RuntimeError("credential-log verification dependency failed")
        values[resource] = value
    if seen_secret_ids != EXPECTED_SECRET_IDS:
        raise RuntimeError("credential-log verification configuration invalid")
    return values


def _job_logs(
    job_specs: Mapping[str, tuple[str, int]],
    project: str,
    _region: str,
    *,
    command_runner: Callable[[list[str]], str] = _run,
) -> list[str]:
    logs: list[str] = []
    if not job_specs:
        raise RuntimeError("credential-log verification configuration invalid")
    for job_name, (uid, task_count) in job_specs.items():
        if (
            not re.fullmatch(r"[a-z][a-z0-9-]{0,62}", job_name)
            or not re.fullmatch(r"[A-Za-z0-9-]+", uid)
            or task_count < 1
        ):
            raise RuntimeError("credential-log verification configuration invalid")
        log_document = command_runner(
            [
                "gcloud",
                "logging",
                "read",
                (
                    'resource.type="batch.googleapis.com/Job" '
                    f'AND labels.job_uid="{uid}" '
                    'AND (log_id("batch_task_logs") OR log_id("batch_agent_logs"))'
                ),
                f"--project={project}",
                "--format=json",
                "--order=asc",
            ]
        )
        try:
            parsed_logs = json.loads(log_document)
        except json.JSONDecodeError as error:
            raise RuntimeError("credential-log verification dependency failed") from error
        if not isinstance(parsed_logs, list) or not parsed_logs:
            raise RuntimeError("attributable Batch logs unavailable")
        _validate_log_entries(parsed_logs, project, uid, task_count)
        logs.append(log_document)
    return logs


def _job_tasks(
    job_specs: Mapping[str, tuple[str, int]],
    project: str,
    region: str,
    *,
    command_runner: Callable[[list[str]], str] = _run,
) -> None:
    """Require the Batch API's exact canonical task-resource set per job."""
    for job_name, (_uid, task_count) in job_specs.items():
        document = command_runner(
            [
                "gcloud",
                "batch",
                "tasks",
                "list",
                f"--job={job_name}",
                f"--location={region}",
                f"--project={project}",
                "--format=json(name)",
            ]
        )
        try:
            parsed = json.loads(document)
        except json.JSONDecodeError as error:
            raise RuntimeError("Batch task identity unavailable") from error
        if not isinstance(parsed, list) or any(
            not isinstance(task, dict) or not isinstance(task.get("name"), str)
            for task in parsed
        ):
            raise RuntimeError("Batch task identity unavailable")
        observed = [task["name"] for task in parsed]
        expected = {
            f"projects/{project}/locations/{region}/jobs/{job_name}/"
            f"taskGroups/group0/tasks/{index}"
            for index in range(task_count)
        }
        if len(observed) != len(set(observed)) or set(observed) != expected:
            raise RuntimeError("Batch task identity mismatch")


def _validate_log_entries(
    entries: list[object], project: str, uid: str, task_count: int
) -> None:
    """Require every expected task in both attributable Batch log streams."""
    observed_tasks = {log_id: set() for log_id in EXPECTED_LOG_IDS}
    allowed_log_names = {
        f"projects/{project}/logs/{log_id}": log_id for log_id in EXPECTED_LOG_IDS
    }
    for entry in entries:
        if not isinstance(entry, dict):
            raise RuntimeError("attributable Batch logs invalid")
        labels = entry.get("labels")
        log_name = entry.get("logName")
        if (
            not isinstance(labels, dict)
            or labels.get("job_uid") != uid
            or log_name not in allowed_log_names
            or not isinstance(labels.get("task_id"), str)
            or not labels["task_id"]
        ):
            raise RuntimeError("attributable Batch logs invalid")
        observed_tasks[allowed_log_names[log_name]].add(labels["task_id"])
    expected_tasks = {f"{uid}-group0-{index}" for index in range(task_count)}
    if any(tasks != expected_tasks for tasks in observed_tasks.values()):
        raise RuntimeError("attributable Batch logs incomplete")


def _parse_job_specs(specs: Sequence[str]) -> dict[str, tuple[str, int]]:
    parsed: dict[str, tuple[str, int]] = {}
    for spec in specs:
        match = JOB_SPEC_PATTERN.fullmatch(spec)
        if not match or match.group("name") in parsed:
            raise RuntimeError("credential-log verification configuration invalid")
        parsed[match.group("name")] = (
            match.group("uid"),
            int(match.group("count")),
        )
    if len(parsed) != 4 or sorted(count for _, count in parsed.values()) != [1, 8, 32, 36]:
        raise RuntimeError("credential-log verification configuration invalid")
    return parsed


def parse_args() -> argparse.Namespace:
    """Parse the release-gate verifier arguments."""
    parser = argparse.ArgumentParser()
    parser.add_argument("--project", required=True)
    parser.add_argument("--region", required=True)
    parser.add_argument("--job-spec", action="append", default=[])
    parser.add_argument("--secret-resource", action="append", default=[])
    parser.add_argument("--log-file", action="append", type=Path, default=[])
    parser.add_argument("--evidence", type=Path, required=True)
    parser.add_argument("--results", type=Path, required=True)
    return parser.parse_args()


def main() -> int:
    """Fetch configured credentials and inspect only attributable job logs."""
    args = parse_args()
    try:
        _verify_result_identities(args.evidence, args.results)
        job_specs = _parse_job_specs(args.job_spec)
        _verify_job_evidence(args.evidence, job_specs)
        _job_tasks(job_specs, args.project, args.region)
        values = _secret_values(args.secret_resource, args.project)
        logs = _job_logs(
            job_specs,
            args.project,
            args.region,
        )
        logs.extend(path.read_text(encoding="utf-8", errors="replace") for path in args.log_file)
        findings = find_matches(values, logs)
    except (OSError, RuntimeError):
        print("FATAL: credential-log verification could not complete", file=sys.stderr)
        return 2
    if findings:
        print(
            "FATAL: credential fingerprint found in attributable Batch logs: "
            + ", ".join(findings),
            file=sys.stderr,
        )
        return 1
    print("Credential-log boundary verified (no matching fingerprints).")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
