#!/usr/bin/env python3
"""Run all cloud-regression cases in one identity-bound Batch task."""
# pylint: disable=invalid-name,too-many-arguments,too-many-locals,too-many-statements

from __future__ import annotations

import base64
import hashlib
import importlib.util
import json
import os
import random
import re
import subprocess
import sys
import time
import uuid
import urllib.parse
from collections.abc import Callable, Mapping, MutableMapping
from datetime import datetime, timezone
from pathlib import Path


LOGICAL_CASES = tuple(range(1, 9))
LOGICAL_START = 68
JWT_MAX_ATTEMPTS = 6
JWT_QUOTA_BACKOFF_SECONDS = 30
JWT_REFRESH_MARGIN_SECONDS = 30


class CloudRegressionError(RuntimeError):
    """A sanitized, fail-closed cloud-regression runner error."""

    def __init__(self, category: str, *, quota: bool = False) -> None:
        super().__init__(category)
        self.category = category
        self.quota = quota


def _firebase_exchange(api_key: str, refresh_token: str) -> bytes:
    """Call the no-redirect exchange helper without exposing credentials in argv."""
    helper = Path(__file__).with_name("firebase-token-exchange.py")
    spec = importlib.util.spec_from_file_location("firebase_token_exchange", helper)
    if not spec or not spec.loader:
        raise CloudRegressionError("transport_failed")
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    try:
        return module.exchange_token(api_key, refresh_token)
    except RuntimeError as error:
        raise CloudRegressionError("transport_failed") from error


def _parse_token(response: bytes) -> tuple[str, int]:
    """Return an ID token and expiry while never rendering the provider body."""
    try:
        document = json.loads(response)
    except (TypeError, ValueError) as error:
        raise CloudRegressionError("parse_failed") from error
    if not isinstance(document, dict):
        raise CloudRegressionError("invalid_response")
    provider_error = document.get("error")
    if provider_error:
        message = provider_error.get("message", "") if isinstance(provider_error, dict) else ""
        quota = "QUOTA_EXCEEDED" in str(message)
        raise CloudRegressionError("quota_exceeded" if quota else "provider_rejected", quota=quota)
    token = document.get("id_token")
    if not isinstance(token, str) or token.count(".") != 2 or any(char.isspace() for char in token):
        raise CloudRegressionError("invalid_token")
    try:
        payload = token.split(".")[1]
        payload += "=" * (-len(payload) % 4)
        claims = json.loads(base64.urlsafe_b64decode(payload.encode("ascii")))
        expiry = claims.get("exp") if isinstance(claims, dict) else None
    except (UnicodeError, ValueError) as error:
        raise CloudRegressionError("invalid_token") from error
    if not isinstance(expiry, int) or isinstance(expiry, bool) or expiry <= 0:
        raise CloudRegressionError("invalid_token")
    return token, expiry


def _default_invoke(case: int, log_path: Path, environment: dict[str, str]) -> int:
    """Invoke one real logical case, writing its dedicated sanitized artifact log."""
    with log_path.open("wb") as output:
        result = subprocess.run(
            ["bash", "tests/cloud_regression.sh", str(case)],
            check=False,
            stdout=output,
            stderr=subprocess.STDOUT,
            env=environment,
        )
    return result.returncode


def _required(environment: Mapping[str, str], name: str, pattern: str) -> str:
    value = environment.get(name, "")
    if not re.fullmatch(pattern, value):
        raise CloudRegressionError("configuration_invalid")
    return value


def _identity(environment: Mapping[str, str]) -> dict[str, object]:
    project = _required(environment, "PDD_BATCH_PROJECT", r"[a-z][a-z0-9-]{4,28}[a-z0-9]")
    location = _required(environment, "PDD_BATCH_LOCATION", r"[a-z0-9-]+")
    job_name = _required(environment, "PDD_BATCH_JOB_NAME", r"[a-z][a-z0-9-]{0,62}")
    raw_index = int(_required(environment, "BATCH_TASK_INDEX", r"0|[1-9][0-9]*"))
    return {
        "candidate_sha": _required(environment, "PDD_CANDIDATE_SHA", r"[0-9a-f]{40}"),
        "candidate_tree": _required(environment, "PDD_CANDIDATE_TREE", r"[0-9a-f]{40}"),
        "source_sha256": _required(environment, "PDD_SOURCE_SHA256", r"[0-9a-f]{64}"),
        "source_generation": _required(environment, "PDD_SOURCE_GCS_GENERATION", r"[1-9][0-9]*"),
        "image_digest": _required(environment, "PDD_IMAGE_DIGEST", r"sha256:[0-9a-f]{64}"),
        "job_name": job_name,
        "task_group": "group0",
        "raw_task_index": raw_index,
        "task_resource": (
            f"projects/{project}/locations/{location}/jobs/{job_name}/"
            f"taskGroups/group0/tasks/{raw_index}"
        ),
    }


def _timestamp(wall_time: Callable[[], float]) -> str:
    return datetime.fromtimestamp(wall_time(), timezone.utc).strftime("%Y-%m-%dT%H:%M:%SZ")


def _write_json(path: Path, document: object) -> None:
    temporary = path.with_name(f".{path.name}.{os.getpid()}.{uuid.uuid4().hex}.tmp")
    with temporary.open("x", encoding="utf-8") as handle:
        json.dump(document, handle, sort_keys=True, indent=2)
        handle.write("\n")
    os.replace(temporary, path)


def _jwt_fingerprint(token: str) -> str:
    return "sha256:" + hashlib.sha256(token.encode("utf-8")).hexdigest()


def _sanitize_jwt_log(path: Path, token: str) -> bool:
    """Remove every common token rendering and report whether one was present."""
    token_bytes = token.encode("utf-8")
    standard_base64 = base64.b64encode(token_bytes).decode("ascii")
    urlsafe_base64 = base64.urlsafe_b64encode(token_bytes).decode("ascii")
    text = path.read_text(encoding="utf-8", errors="replace")
    representations = {
        token,
        json.dumps(token)[1:-1],
        urllib.parse.quote(token, safe=""),
        urllib.parse.quote_plus(token, safe=""),
        standard_base64,
        standard_base64.rstrip("="),
        urlsafe_base64,
        urlsafe_base64.rstrip("="),
    }
    leaked = any(value and value in text for value in representations)
    if leaked:
        for value in sorted(representations, key=len, reverse=True):
            if value:
                text = text.replace(value, "[REDACTED JWT]")
        temporary = path.with_name(f".{path.name}.{os.getpid()}.redacted")
        temporary.write_text(text, encoding="utf-8")
        os.replace(temporary, path)
    return leaked


def run_cloud_regression(
    environment: Mapping[str, str],
    results_dir: Path,
    *,
    exchange: Callable[[str, str], bytes] = _firebase_exchange,
    invoke_case: Callable[[int, Path, dict[str, str]], int] = _default_invoke,
    monotonic: Callable[[], float] = time.monotonic,
    wall_time: Callable[[], float] = time.time,
    sleep: Callable[[float], None] = time.sleep,
    jitter: Callable[[int], int] = random.randrange,
) -> int:
    """Run eight logical cases sequentially with the smallest required auth load."""
    identity = _identity(environment)
    retry_attempt = int(environment.get("BATCH_TASK_RETRY_ATTEMPT", "0"))
    if retry_attempt < 0:
        raise CloudRegressionError("configuration_invalid")
    api_key = environment.get("FIREBASE_API_KEY", "")
    refresh_token = environment.get("PDD_REFRESH_TOKEN", "")
    if not api_key or not refresh_token:
        raise CloudRegressionError("configuration_invalid")
    results_dir.mkdir(parents=True, exist_ok=True)
    nonce = uuid.uuid4().hex
    attempt_path = results_dir / f"cloud_regression_attempt_{retry_attempt}_{nonce}.jsonl"
    attempt_log = attempt_path.open("x", encoding="utf-8", buffering=1)

    def event(name: str, **fields: object) -> None:
        json.dump(
            {
                "event": name,
                "attempt_id": nonce,
                "batch_task_retry_attempt": retry_attempt,
                "candidate_sha": identity["candidate_sha"],
                "task_resource": identity["task_resource"],
                **fields,
            },
            attempt_log,
            sort_keys=True,
        )
        attempt_log.write("\n")
        attempt_log.flush()

    event("attempt_started")
    child_environment: MutableMapping[str, str] = dict(environment)
    child_environment.pop("FIREBASE_API_KEY", None)
    child_environment.pop("PDD_REFRESH_TOKEN", None)
    token = ""
    token_expiry = 0
    auth_attempt_count = 0
    auth_elapsed = 0.0
    auth_failure: CloudRegressionError | None = None
    auth_exhausted = False

    def authenticate() -> None:
        nonlocal token, token_expiry, auth_attempt_count, auth_elapsed, auth_failure, auth_exhausted
        auth_failure = None
        for local_attempt in range(1, JWT_MAX_ATTEMPTS + 1):
            started = monotonic()
            auth_attempt_count += 1
            try:
                candidate, candidate_expiry = _parse_token(
                    exchange(api_key, refresh_token)
                )
                if candidate_expiry <= int(wall_time()) + JWT_REFRESH_MARGIN_SECONDS:
                    raise CloudRegressionError("expired_token")
                token, token_expiry = candidate, candidate_expiry
                auth_elapsed += monotonic() - started
                child_environment["PDD_JWT_TOKEN"] = token
                token_fingerprint = _jwt_fingerprint(token)
                auth_exhausted = False
                event(
                    "auth_succeeded",
                    auth_attempt_count=auth_attempt_count,
                    auth_elapsed_seconds=round(auth_elapsed, 3),
                    jwt_fingerprint=token_fingerprint,
                )
                return
            except CloudRegressionError as error:
                auth_elapsed += monotonic() - started
                auth_failure = error
                event(
                    "auth_failed",
                    auth_attempt_count=auth_attempt_count,
                    auth_elapsed_seconds=round(auth_elapsed, 3),
                    category=error.category,
                )
                if local_attempt < JWT_MAX_ATTEMPTS:
                    delay = (
                        JWT_QUOTA_BACKOFF_SECONDS + jitter(6)
                        if error.quota
                        else 2**local_attempt + jitter(3)
                    )
                    sleep_started = monotonic()
                    sleep(delay)
                    auth_elapsed += monotonic() - sleep_started
        token = ""
        token_expiry = 0
        auth_exhausted = True

    overall_failed = False
    for case in LOGICAL_CASES:
        if not auth_exhausted and (
            not token or token_expiry <= int(wall_time()) + JWT_REFRESH_MARGIN_SECONDS
        ):
            authenticate()
        logical_index = LOGICAL_START + case - 1
        log_path = results_dir / f"task_{logical_index}.log"
        started = monotonic()
        if not token:
            overall_failed = True
            category = auth_failure.category if auth_failure else "unavailable"
            status = "error"
            detail = f"jwt_exchange_failed_case_{case}: {category}"
            log_path.write_text(
                "Cloud authentication unavailable; case not invoked.\n",
                encoding="utf-8",
            )
        else:
            return_code = invoke_case(case, log_path, dict(child_environment))
            leaked = _sanitize_jwt_log(log_path, token)
            status = "error" if leaked else ("passed" if return_code == 0 else "failed")
            detail = f"jwt_log_boundary_failed_case_{case}" if leaked else f"case_{case}"
            overall_failed = overall_failed or return_code != 0 or leaked
        duration = auth_elapsed if not token else max(0.0, monotonic() - started)
        result = {
            "attempt_id": nonce,
            "task_index": logical_index,
            "suite": "cloud_regression",
            "detail": detail,
            "status": status,
            "duration_seconds": round(duration, 3),
            "setup_seconds": int(environment.get("PDD_SETUP_SECONDS", "0")),
            "identity": identity,
            "execution": {
                "auth_elapsed_seconds": round(auth_elapsed, 3),
                "auth_attempt_count": auth_attempt_count,
                "batch_task_retry_attempt": retry_attempt,
                "logical_case": case,
                "jwt_fingerprint": _jwt_fingerprint(token) if token else None,
            },
            "timestamp": _timestamp(wall_time),
        }
        _write_json(results_dir / f"task_{logical_index}.json", result)
        event(
            "case_finished", logical_case=case, status=status,
            auth_attempt_count=auth_attempt_count,
            auth_elapsed_seconds=round(auth_elapsed, 3),
            jwt_fingerprint=_jwt_fingerprint(token) if token else None,
        )
    event(
        "attempt_finished", status="failed" if overall_failed else "passed",
        cases_completed=len(LOGICAL_CASES), auth_attempt_count=auth_attempt_count,
        auth_elapsed_seconds=round(auth_elapsed, 3),
    )
    attempt_log.close()
    return 1 if overall_failed else 0


def main() -> int:
    """Execute from the Batch entrypoint with sanitized terminal output."""
    try:
        return run_cloud_regression(os.environ, Path("/mnt/disks/results"))
    except (CloudRegressionError, OSError, ValueError):
        print("FATAL: cloud-regression runner failed closed", file=sys.stderr)
        return 2


if __name__ == "__main__":
    raise SystemExit(main())
