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
from typing import NamedTuple


RESOURCE_PATTERN = re.compile(
    r"^projects/(?P<project>[^/]+)/secrets/(?P<secret>[^/]+)/versions/"
    r"(?P<version>[1-9][0-9]*)$"
)
JOB_SPEC_PATTERN = re.compile(
    r"^(?P<name>[a-z][a-z0-9-]{0,62})=(?P<uid>[A-Za-z0-9-]+)="
    r"(?P<count>[1-9][0-9]*)$"
)
EXPECTED_LOG_IDS = ("batch_agent_logs", "batch_task_logs")
PROJECT_ID_PATTERN = re.compile(r"^[a-z][a-z0-9-]{4,28}[a-z0-9]$")
PROJECT_NUMBER_PATTERN = re.compile(r"^[1-9][0-9]*$")
TASK_RESOURCE_PATTERN = re.compile(
    r"^projects/(?P<project>[^/]+)/locations/(?P<location>[^/]+)/jobs/"
    r"(?P<job>[^/]+)/taskGroups/(?P<group>[^/]+)/tasks/(?P<index>[^/]+)$"
)
TASK_GROUP_RESOURCE_PATTERN = re.compile(
    r"^projects/(?P<project>[^/]+)/locations/(?P<location>[^/]+)/jobs/"
    r"(?P<job>[^/]+)/taskGroups/(?P<group>[^/]+)$"
)
AGENT_ACTION_PATTERN = re.compile(
    r"^action/STARTUP/(?:0|[1-9][0-9]*)/"
    r"(?:0|[1-9][0-9]*)/group0$"
)
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


class _ExpectedLogIdentity(NamedTuple):
    """Evidence-bound identity expected from one job's log streams."""

    project: str
    job_name: str
    uid: str
    task_count: int
    region: str
    command_runner: Callable[[list[str]], str]


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
    region: str,
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
        _validate_log_entries(
            parsed_logs,
            _ExpectedLogIdentity(
                project=project,
                job_name=job_name,
                uid=uid,
                task_count=task_count,
                region=region,
                command_runner=command_runner,
            ),
        )
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
    if not PROJECT_ID_PATTERN.fullmatch(project):
        raise RuntimeError("credential-log verification configuration invalid")
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
        observed = _canonical_task_identities(parsed, project, command_runner)
        expected = {
            (region, job_name, "group0", index) for index in range(task_count)
        }
        if observed != expected:
            raise RuntimeError("Batch task identity mismatch")


def _canonical_task_identities(
    tasks: list[dict[str, object]],
    project: str,
    command_runner: Callable[[list[str]], str],
) -> set[tuple[str, str, str, int]]:
    """Canonicalize task resources while preserving explicit project binding."""
    identities: list[tuple[str, str, str, int]] = []
    resource_projects: set[str] = set()
    for task in tasks:
        task_name = task["name"]
        if not isinstance(task_name, str):
            raise RuntimeError("Batch task identity unavailable")
        match = TASK_RESOURCE_PATTERN.fullmatch(task_name)
        if not match or not re.fullmatch(r"0|[1-9][0-9]*", match.group("index")):
            raise RuntimeError("Batch task identity mismatch")
        resource_projects.add(match.group("project"))
        identities.append(
            (
                match.group("location"),
                match.group("job"),
                match.group("group"),
                int(match.group("index")),
            )
        )
    allowed_projects = {project}
    if resource_projects - allowed_projects:
        allowed_projects.add(_project_number(project, command_runner))
    if not resource_projects <= allowed_projects or len(identities) != len(set(identities)):
        raise RuntimeError("Batch task identity mismatch")
    return set(identities)


def _project_number(
    project: str, command_runner: Callable[[list[str]], str]
) -> str:
    """Resolve the configured project ID to its authoritative numeric identity."""
    project_number = command_runner(
        [
            "gcloud",
            "projects",
            "describe",
            project,
            "--format=value(projectNumber)",
        ]
    ).strip()
    if not PROJECT_NUMBER_PATTERN.fullmatch(project_number):
        raise RuntimeError("Batch task identity unavailable")
    return project_number


def _agent_identity_valid(
    entry: Mapping[str, object],
    labels: Mapping[str, object],
    task_id: str,
    expected: _ExpectedLogIdentity,
    expected_project: Callable[[str], bool],
) -> bool:
    """Return whether one startup action proves its canonical Batch job."""
    task_group_name = labels.get("task_group_name")
    resource = entry.get("resource")
    if (
        not isinstance(task_group_name, str)
        or not isinstance(resource, dict)
        or resource.get("type") != "batch.googleapis.com/Job"
        or not isinstance(resource.get("labels"), dict)
    ):
        return False
    task_group = TASK_GROUP_RESOURCE_PATTERN.fullmatch(task_group_name)
    resource_labels = resource["labels"]
    resource_location = resource_labels.get("location")
    resource_container = resource_labels.get("resource_container")
    if not task_group:
        return False
    canonical_identity = (
        (
            task_group.group("location"),
            task_group.group("job"),
            task_group.group("group"),
        ) == (expected.region, expected.job_name, "group0")
        and expected_project(task_group.group("project"))
        and resource_labels.get("job_id") == expected.uid
    )
    if not canonical_identity:
        return False
    if not isinstance(resource_container, str) or not expected_project(
        resource_container
    ):
        return False
    if not isinstance(resource_location, str):
        return False
    exact_region_or_zone = re.fullmatch(
        rf"{re.escape(expected.region)}(?:-[a-z])?", resource_location
    )
    return bool(exact_region_or_zone and AGENT_ACTION_PATTERN.fullmatch(task_id))


def _validate_log_entries(
    entries: list[object],
    expected: _ExpectedLogIdentity,
) -> None:
    """Validate the distinct task-log and agent-action identity contracts."""
    observed_tasks: set[str] = set()
    observed_actions: set[str] = set()
    authoritative_project_number: str | None = None

    def expected_project(value: str) -> bool:
        nonlocal authoritative_project_number
        if value == expected.project:
            return True
        if not PROJECT_NUMBER_PATTERN.fullmatch(value):
            return False
        if authoritative_project_number is None:
            authoritative_project_number = _project_number(
                expected.project, expected.command_runner
            )
        return value == authoritative_project_number

    allowed_log_names = {
        f"projects/{expected.project}/logs/{log_id}": log_id
        for log_id in EXPECTED_LOG_IDS
    }
    for entry in entries:
        if not isinstance(entry, dict):
            raise RuntimeError("attributable Batch logs invalid")
        labels = entry.get("labels")
        log_name = entry.get("logName")
        if (
            not isinstance(labels, dict)
            or labels.get("job_uid") != expected.uid
            or log_name not in allowed_log_names
            or not isinstance(labels.get("task_id"), str)
            or not labels["task_id"]
        ):
            raise RuntimeError("attributable Batch logs invalid")
        task_id = labels["task_id"]
        if allowed_log_names[log_name] == "batch_task_logs":
            observed_tasks.add(task_id)
        elif not _agent_identity_valid(
            entry,
            labels,
            task_id,
            expected,
            expected_project,
        ):
            raise RuntimeError("attributable Batch logs invalid")
        else:
            observed_actions.add(task_id)
    expected_tasks = {
        f"{expected.uid}-group0-{index}" for index in range(expected.task_count)
    }
    if observed_tasks != expected_tasks or not observed_actions:
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
