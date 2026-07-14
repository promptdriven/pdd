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
from collections.abc import Mapping, Sequence
from pathlib import Path


RESOURCE_PATTERN = re.compile(
    r"^projects/(?P<project>[^/]+)/secrets/(?P<secret>[^/]+)/versions/"
    r"(?P<version>latest|[1-9][0-9]*)$"
)


def fingerprint(value: str) -> str:
    """Return a non-reversible identifier suitable for gate diagnostics."""
    return "sha256:" + hashlib.sha256(value.encode("utf-8")).hexdigest()[:16]


def find_matches(secrets: Mapping[str, str], logs: Sequence[str]) -> list[str]:
    """Find exact payload occurrences while returning fingerprints only."""
    findings: set[str] = set()
    for value in secrets.values():
        encoded_value = json.dumps(value)[1:-1]
        if value and any(value in log or encoded_value in log for log in logs):
            findings.add(fingerprint(value))
    return sorted(findings)


def _run(command: list[str]) -> str:
    result = subprocess.run(command, check=False, capture_output=True, text=True)
    if result.returncode != 0:
        raise RuntimeError("credential-log verification dependency failed")
    return result.stdout


def _secret_values(resources: Sequence[str], project: str) -> dict[str, str]:
    values: dict[str, str] = {}
    for resource in resources:
        match = RESOURCE_PATTERN.fullmatch(resource)
        if not match or match.group("project") != project:
            raise RuntimeError("credential-log verification configuration invalid")
        value = _run(
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
    return values


def _job_logs(job_names: Sequence[str], project: str, region: str) -> list[str]:
    logs: list[str] = []
    for job_name in job_names:
        uid = _run(
            [
                "gcloud",
                "batch",
                "jobs",
                "describe",
                job_name,
                f"--project={project}",
                f"--location={region}",
                "--format=value(uid)",
            ]
        ).strip()
        if not uid:
            raise RuntimeError("credential-log verification dependency failed")
        log_document = _run(
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
                "--limit=100000",
            ]
        )
        try:
            parsed_logs = json.loads(log_document)
        except json.JSONDecodeError as error:
            raise RuntimeError("credential-log verification dependency failed") from error
        if not isinstance(parsed_logs, list) or not parsed_logs:
            raise RuntimeError("attributable Batch logs unavailable")
        logs.append(log_document)
    return logs


def parse_args() -> argparse.Namespace:
    """Parse the release-gate verifier arguments."""
    parser = argparse.ArgumentParser()
    parser.add_argument("--project", required=True)
    parser.add_argument("--region", required=True)
    parser.add_argument("--job-name", action="append", default=[])
    parser.add_argument("--secret-resource", action="append", default=[])
    parser.add_argument("--log-file", action="append", type=Path, default=[])
    return parser.parse_args()


def main() -> int:
    """Fetch configured credentials and inspect only attributable job logs."""
    args = parse_args()
    try:
        values = _secret_values(args.secret_resource, args.project)
        logs = _job_logs(args.job_name, args.project, args.region)
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
