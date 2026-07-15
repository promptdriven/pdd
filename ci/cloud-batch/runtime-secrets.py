#!/usr/bin/env python3
"""Load Cloud Batch credentials in-process, then replace this process.

Batch receives only Secret Manager resource names. Credential payloads are
resolved with the task service account and exist only in this process'
environment and the process that replaces it.
"""
# pylint: disable=invalid-name

from __future__ import annotations

import base64
import binascii
import json
import os
import re
import sys
import urllib.error
import urllib.parse
import urllib.request
from collections.abc import Callable, Mapping, MutableMapping, Sequence


METADATA_TOKEN_URL = (
    "http://metadata.google.internal/computeMetadata/v1/instance/"
    "service-accounts/default/token"
)
METADATA_PROJECT_URL = (
    "http://metadata.google.internal/computeMetadata/v1/project/project-id"
)
SECRET_API_ROOT = "https://secretmanager.googleapis.com/v1/"
RESOURCE_PATTERN = re.compile(
    r"^projects/[a-z][a-z0-9-]{4,28}[a-z0-9]/secrets/"
    r"[A-Za-z0-9_-]{1,255}/versions/[1-9][0-9]*$"
)

EXPECTED_SECRET_IDS = {
    "GCS_HMAC_ACCESS_KEY_ID": "GCS_HMAC_ACCESS_KEY_ID",
    "GCS_HMAC_SECRET_ACCESS_KEY": "GCS_HMAC_SECRET_ACCESS_KEY",
    "OPENAI_API_KEY": "OPENAI_API_KEY",
    "FIREBASE_API_KEY": "staging-firebase-api-key",
    "GITHUB_CLIENT_ID": "github-client-id",
    "PDD_REFRESH_TOKEN": "pdd-refresh-token",
    "CLAUDE_CODE_OAUTH_TOKEN": "CLAUDE_CODE_OAUTH_TOKEN",
}

COMMON_TASK_SECRETS = (
    "GCS_HMAC_ACCESS_KEY_ID",
    "GCS_HMAC_SECRET_ACCESS_KEY",
    "OPENAI_API_KEY",
    "GITHUB_CLIENT_ID",
    "CLAUDE_CODE_OAUTH_TOKEN",
)
CLOUD_TASK_SECRETS = (
    "FIREBASE_API_KEY",
    "GITHUB_CLIENT_ID",
    "PDD_REFRESH_TOKEN",
)


class SecretLoadError(RuntimeError):
    """A sanitized, fail-closed runtime credential error."""


class _NoRedirectHandler(urllib.request.HTTPRedirectHandler):
    """Reject redirects before urllib can forward sensitive headers."""

    # Signature is defined by urllib's redirect-handler protocol.
    # pylint: disable=too-many-arguments,too-many-positional-arguments
    def redirect_request(self, req, fp, code, msg, headers, newurl):
        del req, fp, code, msg, headers, newurl
        raise urllib.error.HTTPError(
            "redirects-disabled", 400, "redirects disabled", {}, None
        )


_NO_REDIRECT_OPENER = urllib.request.build_opener(_NoRedirectHandler()).open


def effective_task_index(environment: Mapping[str, str]) -> int:
    """Mirror the shell entrypoint's global task-index mapping."""
    fixed = environment.get("FIXED_TASK_INDEX")
    if fixed:
        return int(fixed)

    raw = int(environment["BATCH_TASK_INDEX"])
    task_index = raw + int(environment.get("TASK_INDEX_OFFSET", "0"))
    skip_indexes = environment.get("SKIP_INDEXES", "")
    if skip_indexes:
        for item in skip_indexes.split(","):
            if item and int(item) <= task_index:
                task_index += 1
    else:
        skip_index = environment.get("SKIP_INDEX")
        if skip_index and int(skip_index) <= task_index:
            task_index += 1
    return task_index


def required_secret_names(environment: Mapping[str, str]) -> tuple[str, ...]:
    """Return the smallest stable credential set for a task group."""
    try:
        task_index = effective_task_index(environment)
    except (KeyError, ValueError) as error:
        raise SecretLoadError("required runtime credential configuration invalid") from error
    if 68 <= task_index <= 75:
        return CLOUD_TASK_SECRETS
    if 0 <= task_index <= 67:
        if (
            0 <= task_index <= 31
            and environment.get("PDD_BATCH_ENABLE_PYTEST_CLOUD_E2E") == "1"
        ):
            return tuple(dict.fromkeys(COMMON_TASK_SECRETS + CLOUD_TASK_SECRETS))
        return COMMON_TASK_SECRETS
    if task_index == 76:
        return ()
    raise SecretLoadError("required runtime credential selection failed")


def _read_bytes(
    request: urllib.request.Request,
    *,
    expected_scheme: str,
    expected_host: str,
    opener: Callable[..., object] = _NO_REDIRECT_OPENER,
) -> bytes:
    parsed_request = urllib.parse.urlsplit(request.full_url)
    if (
        parsed_request.scheme != expected_scheme
        or parsed_request.hostname != expected_host
    ):
        raise SecretLoadError("required runtime credential unavailable")
    try:
        with opener(request, timeout=15) as response:
            final_url = urllib.parse.urlsplit(response.geturl())
            if (
                getattr(response, "status", None) != 200
                or final_url.scheme != expected_scheme
                or final_url.hostname != expected_host
                or response.geturl() != request.full_url
            ):
                raise SecretLoadError("required runtime credential unavailable")
            return response.read()
    except (OSError, urllib.error.URLError) as error:
        raise SecretLoadError("required runtime credential unavailable") from error


def _read_json(
    request: urllib.request.Request,
    *,
    expected_scheme: str,
    expected_host: str,
    opener: Callable[..., object] = _NO_REDIRECT_OPENER,
) -> object:
    try:
        return json.loads(
            _read_bytes(
                request,
                expected_scheme=expected_scheme,
                expected_host=expected_host,
                opener=opener,
            )
        )
    except ValueError as error:
        raise SecretLoadError("required runtime credential unavailable") from error


def trusted_metadata_project() -> str:
    """Read the workload's project identity from the trusted metadata server."""
    request = urllib.request.Request(
        METADATA_PROJECT_URL,
        headers={"Metadata-Flavor": "Google"},
    )
    try:
        project = _read_bytes(
            request,
            expected_scheme="http",
            expected_host="metadata.google.internal",
        ).decode("ascii")
    except UnicodeDecodeError as error:
        raise SecretLoadError("required runtime credential unavailable") from error
    if not re.fullmatch(r"[a-z][a-z0-9-]{4,28}[a-z0-9]", project):
        raise SecretLoadError("required runtime credential unavailable")
    return project


def fetch_secret(resource: str) -> str:
    """Access one Secret Manager version with the workload identity."""
    if not RESOURCE_PATTERN.fullmatch(resource):
        raise SecretLoadError("required runtime credential configuration invalid")

    token_request = urllib.request.Request(
        METADATA_TOKEN_URL,
        headers={"Metadata-Flavor": "Google"},
    )
    token_document = _read_json(
        token_request,
        expected_scheme="http",
        expected_host="metadata.google.internal",
    )
    if not isinstance(token_document, dict):
        raise SecretLoadError("required runtime credential unavailable")
    access_token = token_document.get("access_token")
    if not isinstance(access_token, str) or not access_token:
        raise SecretLoadError("required runtime credential unavailable")

    access_request = urllib.request.Request(
        SECRET_API_ROOT + urllib.parse.quote(resource, safe="/") + ":access",
        headers={"Authorization": f"Bearer {access_token}"},
    )
    secret_document = _read_json(
        access_request,
        expected_scheme="https",
        expected_host="secretmanager.googleapis.com",
    )
    if not isinstance(secret_document, dict):
        raise SecretLoadError("required runtime credential unavailable")
    payload = secret_document.get("payload")
    encoded = payload.get("data") if isinstance(payload, dict) else None
    if not isinstance(encoded, str) or not encoded:
        raise SecretLoadError("required runtime credential unavailable")
    try:
        value = base64.b64decode(encoded, validate=True).decode("utf-8")
    except (binascii.Error, UnicodeDecodeError) as error:
        raise SecretLoadError("required runtime credential unavailable") from error
    if not value or "\x00" in value:
        raise SecretLoadError("required runtime credential unavailable")
    return value


def load_required_secrets(
    environment: Mapping[str, str],
    *,
    trusted_project: str,
    secret_fetcher: Callable[[str], str] = fetch_secret,
) -> dict[str, str]:
    """Resolve required payloads without logging values or provider errors."""
    loaded: dict[str, str] = {}
    for name in required_secret_names(environment):
        resource_key = f"{name}_SECRET_RESOURCE"
        resource = environment.get(resource_key)
        if not resource:
            raise SecretLoadError("required runtime credential configuration missing")
        expected_resource = re.compile(
            rf"^projects/{re.escape(trusted_project)}/secrets/"
            rf"{re.escape(EXPECTED_SECRET_IDS[name])}/versions/[1-9][0-9]*$"
        )
        if not expected_resource.fullmatch(resource):
            raise SecretLoadError("required runtime credential configuration invalid")
        try:
            value = secret_fetcher(resource)
        except SecretLoadError:
            raise
        except Exception as error:
            raise SecretLoadError("required runtime credential unavailable") from error
        if not isinstance(value, str) or not value or "\x00" in value:
            raise SecretLoadError("required runtime credential unavailable")
        loaded[name] = value
    return loaded


def _exec_process(command: list[str], environment: dict[str, str]) -> None:
    os.execvpe(command[0], command, environment)


def exec_with_runtime_secrets(
    command: Sequence[str],
    environment: MutableMapping[str, str],
    *,
    secret_fetcher: Callable[[str], str] = fetch_secret,
    project_reader: Callable[[], str] = trusted_metadata_project,
    exec_process: Callable[[list[str], dict[str, str]], None] = _exec_process,
) -> None:
    """Load credentials into a private child environment and exec command."""
    if not command:
        raise SecretLoadError("runtime command missing")
    child_environment = dict(environment)
    if required_secret_names(child_environment):
        trusted_project = project_reader()
        child_environment.update(
            load_required_secrets(
                child_environment,
                trusted_project=trusted_project,
                secret_fetcher=secret_fetcher,
            )
        )
    exec_process(list(command), child_environment)


def main() -> int:
    """Run the real Batch entrypoint with sanitized failure reporting."""
    command = sys.argv[1:] or ["/entrypoint.sh"]
    try:
        exec_with_runtime_secrets(command, os.environ)
    except SecretLoadError as error:
        print(f"FATAL: {error}", file=sys.stderr)
        return 78
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
