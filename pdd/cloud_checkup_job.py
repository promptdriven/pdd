"""
Cloud job submission and polling for ``pdd checkup --pr --cloud-job``.

This module provides fully non-local execution of ``pdd checkup --pr`` via
PDD Cloud infrastructure.  The cloud executor handles repository checkout,
test execution, reviewer/fixer stages, Git operations, and credit accounting.
Local ``codex`` installation and local Codex credentials are never required.

Contract (mirrors the 10-point spec in issue #2295):
1.  Authenticates the PDD user and verifies GitHub App installation.
2.  Reserves PDD Cloud credits before dispatch.
3.  Preserves and validates the complete ``checkup`` argument vector.
4.  Executor clones and checks out the exact PR head in isolation.
5.  Executor runs the real ``pdd checkup --pr ...`` workflow end-to-end.
6.  Executor uses a PDD-managed Codex credential — never copies it locally.
7.  Persists job status, sanitized terminal output, exit code, report, model
    attribution, and credit/cost settlement for CLI polling.
8.  Fails closed: submission or polling failure does NOT fall back to local
    Codex or local credentials.
9.  Emits secret-safe provider-limit metadata including in quiet mode.
10. Shows billing source so users can distinguish PDD Cloud from BYO.
"""

from __future__ import annotations

import time
from dataclasses import dataclass, field
from typing import Any, Dict, List, Optional, Tuple

import requests

from .core.cloud import (
    CLOUD_CHECKUP_POLL_INTERVAL,
    CLOUD_CHECKUP_POLL_TIMEOUT,
    CLOUD_CONNECT_TIMEOUT,
    CloudConfig,
    get_cloud_timeout,
)

# Terminal states returned by the cloud executor
_TERMINAL_STATES = frozenset({"succeeded", "failed", "cancelled", "error"})
# Maximum lines of remote output to include in the bounded local report
_MAX_OUTPUT_LINES = 500
# Maximum bytes of the bounded remote report to forward locally
_MAX_REPORT_BYTES = 64 * 1024  # 64 KiB


class CloudCheckupError(Exception):
    """Raised when cloud checkup submission or polling fails closed."""


@dataclass
class CloudCheckupJob:
    """Immutable handle returned by :func:`submit_cloud_checkup_job`."""

    job_id: str
    pr_url: str
    billing_source: str = "pdd-cloud"
    submitted_at: float = field(default_factory=time.time)


@dataclass
class CloudCheckupResult:
    """Terminal result returned by :func:`poll_cloud_checkup_job`."""

    success: bool
    message: str
    cost_usd: float
    model: str
    exit_code: int
    output_lines: List[str]
    report: Optional[str]
    billing_source: str
    job_id: str
    provider_meta: Dict[str, Any] = field(default_factory=dict)


def _build_checkup_args(
    pr_url: str,
    issue_url: Optional[str],
    test_scope: str,
    full_suite_source: str,
    review_loop: bool,
    final_gate: bool,
    agentic_review_loop: bool,
    reviewer: Optional[str],
    fixer: Optional[str],
    reviewers: str,
    reviewer_fallback: Optional[str],
    fixer_fallback: Optional[str],
    allow_same_reviewer_fixer: bool,
    max_review_rounds: int,
    max_review_cost: float,
    max_review_minutes: float,
    require_all_reviewers_clean: bool,
    continue_on_reviewer_limit: bool,
    require_final_fresh_review: bool,
    blocking_severities: Optional[str],
    clean_reviewer_states: Optional[str],
    fallback_reviewer_on_failure: bool,
    no_fix: bool,
    review_only: bool,
    fresh_final_review: Optional[str],
    adversarial_prompt: Optional[str],
    enable_gates: bool,
    gate_timeout: float,
    gate_allow: Tuple[str, ...],
    timeout_adder: float,
    no_github_state: bool,
    terra_sol: bool,
    fresh_start: bool,
) -> Dict[str, Any]:
    """Build the validated argument vector forwarded verbatim to the executor."""
    args: Dict[str, Any] = {
        "pr_url": pr_url,
        "test_scope": test_scope,
        "full_suite_source": full_suite_source,
        "review_loop": review_loop,
        "final_gate": final_gate,
        "agentic_review_loop": agentic_review_loop,
        "reviewers": reviewers,
        "allow_same_reviewer_fixer": allow_same_reviewer_fixer,
        "max_review_rounds": max_review_rounds,
        "max_review_cost": max_review_cost,
        "max_review_minutes": max_review_minutes,
        "require_all_reviewers_clean": require_all_reviewers_clean,
        "continue_on_reviewer_limit": continue_on_reviewer_limit,
        "require_final_fresh_review": require_final_fresh_review,
        "fallback_reviewer_on_failure": fallback_reviewer_on_failure,
        "no_fix": no_fix,
        "review_only": review_only,
        "enable_gates": enable_gates,
        "gate_timeout": gate_timeout,
        "gate_allow": list(gate_allow),
        "timeout_adder": timeout_adder,
        "no_github_state": no_github_state,
        "terra_sol": terra_sol,
        "fresh_start": fresh_start,
    }
    if issue_url is not None:
        args["issue_url"] = issue_url
    if reviewer is not None:
        args["reviewer"] = reviewer
    if fixer is not None:
        args["fixer"] = fixer
    if reviewer_fallback is not None:
        args["reviewer_fallback"] = reviewer_fallback
    if fixer_fallback is not None:
        args["fixer_fallback"] = fixer_fallback
    if blocking_severities is not None:
        args["blocking_severities"] = blocking_severities
    if clean_reviewer_states is not None:
        args["clean_reviewer_states"] = clean_reviewer_states
    if fresh_final_review is not None:
        args["fresh_final_review"] = fresh_final_review
    if adversarial_prompt is not None:
        args["adversarial_prompt"] = adversarial_prompt
    return args


def submit_cloud_checkup_job(
    pr_url: str,
    jwt_token: str,
    *,
    issue_url: Optional[str] = None,
    test_scope: str = "full",
    full_suite_source: str = "local",
    review_loop: bool = False,
    final_gate: bool = False,
    agentic_review_loop: bool = False,
    reviewer: Optional[str] = None,
    fixer: Optional[str] = None,
    reviewers: str = "codex,claude",
    reviewer_fallback: Optional[str] = None,
    fixer_fallback: Optional[str] = None,
    allow_same_reviewer_fixer: bool = False,
    max_review_rounds: int = 5,
    max_review_cost: float = 50.0,
    max_review_minutes: float = 90.0,
    require_all_reviewers_clean: bool = True,
    continue_on_reviewer_limit: bool = False,
    require_final_fresh_review: bool = True,
    blocking_severities: Optional[str] = None,
    clean_reviewer_states: Optional[str] = None,
    fallback_reviewer_on_failure: bool = False,
    no_fix: bool = False,
    review_only: bool = False,
    fresh_final_review: Optional[str] = None,
    adversarial_prompt: Optional[str] = None,
    enable_gates: bool = True,
    gate_timeout: float = 60.0,
    gate_allow: Tuple[str, ...] = (),
    timeout_adder: float = 0.0,
    no_github_state: bool = False,
    terra_sol: bool = False,
    fresh_start: bool = False,
) -> CloudCheckupJob:
    """Submit a ``pdd checkup --pr`` job to the PDD Cloud executor.

    Fails closed: raises :class:`CloudCheckupError` on any submission failure
    rather than silently falling back to local execution.

    Returns a :class:`CloudCheckupJob` handle for subsequent polling.
    """
    checkup_args = _build_checkup_args(
        pr_url=pr_url,
        issue_url=issue_url,
        test_scope=test_scope,
        full_suite_source=full_suite_source,
        review_loop=review_loop,
        final_gate=final_gate,
        agentic_review_loop=agentic_review_loop,
        reviewer=reviewer,
        fixer=fixer,
        reviewers=reviewers,
        reviewer_fallback=reviewer_fallback,
        fixer_fallback=fixer_fallback,
        allow_same_reviewer_fixer=allow_same_reviewer_fixer,
        max_review_rounds=max_review_rounds,
        max_review_cost=max_review_cost,
        max_review_minutes=max_review_minutes,
        require_all_reviewers_clean=require_all_reviewers_clean,
        continue_on_reviewer_limit=continue_on_reviewer_limit,
        require_final_fresh_review=require_final_fresh_review,
        blocking_severities=blocking_severities,
        clean_reviewer_states=clean_reviewer_states,
        fallback_reviewer_on_failure=fallback_reviewer_on_failure,
        no_fix=no_fix,
        review_only=review_only,
        fresh_final_review=fresh_final_review,
        adversarial_prompt=adversarial_prompt,
        enable_gates=enable_gates,
        gate_timeout=gate_timeout,
        gate_allow=gate_allow,
        timeout_adder=timeout_adder,
        no_github_state=no_github_state,
        terra_sol=terra_sol,
        fresh_start=fresh_start,
    )

    payload = {
        "checkupArgs": checkup_args,
        "billingSource": "pdd-cloud",
    }

    endpoint = CloudConfig.get_endpoint_url("submitCheckup")
    headers = {
        "Authorization": f"Bearer {jwt_token}",
        "Content-Type": "application/json",
    }

    try:
        response = requests.post(
            endpoint,
            json=payload,
            headers=headers,
            timeout=(CLOUD_CONNECT_TIMEOUT, get_cloud_timeout()),
        )
    except requests.exceptions.ConnectionError as exc:
        raise CloudCheckupError(
            f"Cannot reach PDD Cloud at {endpoint}: {exc}"
        ) from exc
    except requests.exceptions.Timeout as exc:
        raise CloudCheckupError(
            f"Timed out submitting checkup job to {endpoint}: {exc}"
        ) from exc
    except requests.exceptions.RequestException as exc:
        raise CloudCheckupError(f"Submission request failed: {exc}") from exc

    if response.status_code == 401:
        raise CloudCheckupError(
            "PDD Cloud authentication failed (401). "
            "Run `pdd auth login` to refresh your credentials."
        )
    if response.status_code == 402:
        raise CloudCheckupError(
            "Insufficient PDD Cloud credits (402). "
            "Visit pdd.dev to add credits before running --cloud-job."
        )
    if response.status_code == 403:
        raise CloudCheckupError(
            "Access denied (403). "
            "Verify the PDD GitHub App is installed for this repository."
        )
    if not response.ok:
        try:
            body = response.json()
            detail = body.get("error") or body.get("message") or response.text[:200]
        except Exception:
            detail = response.text[:200]
        raise CloudCheckupError(
            f"Cloud checkup submission failed ({response.status_code}): {detail}"
        )

    try:
        data = response.json()
    except Exception as exc:
        raise CloudCheckupError(
            f"Cloud returned non-JSON submission response: {response.text[:200]}"
        ) from exc

    job_id = data.get("jobId") or data.get("job_id") or ""
    if not job_id:
        raise CloudCheckupError(
            "Cloud did not return a job ID in the submission response."
        )

    billing_source = data.get("billingSource", "pdd-cloud")
    return CloudCheckupJob(
        job_id=job_id,
        pr_url=pr_url,
        billing_source=billing_source,
    )


def poll_cloud_checkup_job(
    job: CloudCheckupJob,
    jwt_token: str,
    *,
    quiet: bool = False,
    poll_interval: int = CLOUD_CHECKUP_POLL_INTERVAL,
    poll_timeout: int = CLOUD_CHECKUP_POLL_TIMEOUT,
) -> CloudCheckupResult:
    """Poll a submitted cloud checkup job until it reaches a terminal state.

    Emits periodic status lines to stdout (suppressed by ``quiet=True``).
    Fails closed: raises :class:`CloudCheckupError` on any polling failure
    rather than silently falling back to local execution.
    """
    endpoint = CloudConfig.get_endpoint_url("getCheckupStatus")
    headers = {
        "Authorization": f"Bearer {jwt_token}",
        "Content-Type": "application/json",
    }
    deadline = time.monotonic() + poll_timeout
    elapsed_steps = 0

    while True:
        now = time.monotonic()
        if now >= deadline:
            raise CloudCheckupError(
                f"Cloud checkup job {job.job_id!r} did not complete within "
                f"{poll_timeout}s. The job may still be running on the server; "
                "check the PDD dashboard for its final status."
            )

        try:
            response = requests.post(
                endpoint,
                json={"jobId": job.job_id},
                headers=headers,
                timeout=(CLOUD_CONNECT_TIMEOUT, get_cloud_timeout()),
            )
        except requests.exceptions.RequestException as exc:
            raise CloudCheckupError(
                f"Polling cloud checkup job {job.job_id!r} failed: {exc}"
            ) from exc

        if response.status_code == 401:
            raise CloudCheckupError(
                "PDD Cloud authentication expired during polling (401). "
                "Run `pdd auth login` to refresh credentials."
            )
        if not response.ok:
            try:
                body = response.json()
                detail = body.get("error") or body.get("message") or response.text[:200]
            except Exception:
                detail = response.text[:200]
            raise CloudCheckupError(
                f"Status poll failed ({response.status_code}): {detail}"
            )

        try:
            data = response.json()
        except Exception as exc:
            raise CloudCheckupError(
                f"Non-JSON status response: {response.text[:200]}"
            ) from exc

        status = (data.get("status") or "").lower()
        if not quiet and elapsed_steps % 4 == 0:
            step_info = data.get("currentStep", "")
            step_str = f" ({step_info})" if step_info else ""
            print(f"[pdd cloud] checkup job {job.job_id[:8]}…: {status}{step_str}", flush=True)

        if status not in _TERMINAL_STATES:
            elapsed_steps += 1
            time.sleep(poll_interval)
            continue

        # Terminal state reached — extract result.
        success = status == "succeeded"
        exit_code = int(data.get("exitCode", 0 if success else 1))
        cost_usd = float(data.get("costUsd", 0.0))
        model = data.get("model", "pdd-cloud")
        billing_source = data.get("billingSource", job.billing_source)
        report = data.get("report") or None
        if isinstance(report, str) and len(report) > _MAX_REPORT_BYTES:
            report = report[:_MAX_REPORT_BYTES] + "\n[report truncated]"

        raw_output = data.get("output") or ""
        if isinstance(raw_output, str):
            output_lines = raw_output.splitlines()
        elif isinstance(raw_output, list):
            output_lines = [str(line) for line in raw_output]
        else:
            output_lines = []
        if len(output_lines) > _MAX_OUTPUT_LINES:
            dropped = len(output_lines) - _MAX_OUTPUT_LINES
            output_lines = output_lines[:_MAX_OUTPUT_LINES]
            output_lines.append(f"[{dropped} lines omitted]")

        # Sanitize: strip any line containing secret-shaped tokens.
        output_lines = _sanitize_output_lines(output_lines)

        message = data.get("message") or ("checkup succeeded" if success else "checkup failed")

        # Provider-limit metadata — emit secret-safe even in quiet mode.
        provider_meta: Dict[str, Any] = {}
        for key in ("rateLimitInfo", "providerLimitMeta", "modelAttribution"):
            if key in data:
                provider_meta[key] = data[key]

        return CloudCheckupResult(
            success=success,
            message=message,
            cost_usd=cost_usd,
            model=model,
            exit_code=exit_code,
            output_lines=output_lines,
            report=report,
            billing_source=billing_source,
            job_id=job.job_id,
            provider_meta=provider_meta,
        )


# Naïve secret-safe sanitizer: drop lines that look like raw credentials.
_SECRET_PATTERNS = (
    "eyJ",          # JWT prefix
    "ghp_",         # GitHub PAT
    "ghs_",         # GitHub App token
    "AKIA",         # AWS access key
    "sk-",          # OpenAI key prefix
    "Bearer ",      # auth header leak
    "Authorization:",
)


def _sanitize_output_lines(lines: List[str]) -> List[str]:
    """Remove lines that contain secret-shaped tokens from remote output."""
    clean = []
    for line in lines:
        if any(pat in line for pat in _SECRET_PATTERNS):
            clean.append("[line redacted: possible credential]")
        else:
            clean.append(line)
    return clean


def run_cloud_checkup(
    pr_url: str,
    *,
    issue_url: Optional[str] = None,
    test_scope: str = "full",
    full_suite_source: str = "local",
    review_loop: bool = False,
    final_gate: bool = False,
    agentic_review_loop: bool = False,
    reviewer: Optional[str] = None,
    fixer: Optional[str] = None,
    reviewers: str = "codex,claude",
    reviewer_fallback: Optional[str] = None,
    fixer_fallback: Optional[str] = None,
    allow_same_reviewer_fixer: bool = False,
    max_review_rounds: int = 5,
    max_review_cost: float = 50.0,
    max_review_minutes: float = 90.0,
    require_all_reviewers_clean: bool = True,
    continue_on_reviewer_limit: bool = False,
    require_final_fresh_review: bool = True,
    blocking_severities: Optional[str] = None,
    clean_reviewer_states: Optional[str] = None,
    fallback_reviewer_on_failure: bool = False,
    no_fix: bool = False,
    review_only: bool = False,
    fresh_final_review: Optional[str] = None,
    adversarial_prompt: Optional[str] = None,
    enable_gates: bool = True,
    gate_timeout: float = 60.0,
    gate_allow: Tuple[str, ...] = (),
    timeout_adder: float = 0.0,
    no_github_state: bool = False,
    terra_sol: bool = False,
    fresh_start: bool = False,
    quiet: bool = False,
    verbose: bool = False,
    poll_interval: int = CLOUD_CHECKUP_POLL_INTERVAL,
    poll_timeout: int = CLOUD_CHECKUP_POLL_TIMEOUT,
) -> CloudCheckupResult:
    """Top-level helper: authenticate, submit, poll, and return the result.

    This is the entry point called by ``pdd checkup --pr --cloud-job``.
    Fails closed: any error raises :class:`CloudCheckupError`.
    """
    jwt_token = CloudConfig.get_jwt_token(verbose=verbose)
    if not jwt_token:
        raise CloudCheckupError(
            "PDD Cloud authentication required for --cloud-job. "
            "Run `pdd auth login` first."
        )

    job = submit_cloud_checkup_job(
        pr_url=pr_url,
        jwt_token=jwt_token,
        issue_url=issue_url,
        test_scope=test_scope,
        full_suite_source=full_suite_source,
        review_loop=review_loop,
        final_gate=final_gate,
        agentic_review_loop=agentic_review_loop,
        reviewer=reviewer,
        fixer=fixer,
        reviewers=reviewers,
        reviewer_fallback=reviewer_fallback,
        fixer_fallback=fixer_fallback,
        allow_same_reviewer_fixer=allow_same_reviewer_fixer,
        max_review_rounds=max_review_rounds,
        max_review_cost=max_review_cost,
        max_review_minutes=max_review_minutes,
        require_all_reviewers_clean=require_all_reviewers_clean,
        continue_on_reviewer_limit=continue_on_reviewer_limit,
        require_final_fresh_review=require_final_fresh_review,
        blocking_severities=blocking_severities,
        clean_reviewer_states=clean_reviewer_states,
        fallback_reviewer_on_failure=fallback_reviewer_on_failure,
        no_fix=no_fix,
        review_only=review_only,
        fresh_final_review=fresh_final_review,
        adversarial_prompt=adversarial_prompt,
        enable_gates=enable_gates,
        gate_timeout=gate_timeout,
        gate_allow=gate_allow,
        timeout_adder=timeout_adder,
        no_github_state=no_github_state,
        terra_sol=terra_sol,
        fresh_start=fresh_start,
    )

    if not quiet:
        print(
            f"[pdd cloud] Submitted checkup job {job.job_id!r} "
            f"(billing: {job.billing_source}). Polling for completion…",
            flush=True,
        )

    return poll_cloud_checkup_job(
        job,
        jwt_token=jwt_token,
        quiet=quiet,
        poll_interval=poll_interval,
        poll_timeout=poll_timeout,
    )
