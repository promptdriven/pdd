from __future__ import annotations

import dataclasses
import hashlib
import json
import os
import subprocess
import time
from dataclasses import dataclass
from datetime import datetime, timezone
from pathlib import Path
from typing import Any, Callable, List, Optional

# Use rich.console.Console for all printing
from rich.console import Console

from .agentic_common import AgenticTaskResult, run_agentic_task
from .failure_classification import classify_failure

console = Console()


@dataclass
class MultishotCandidateRecord:
    shot_id: int
    task_id: str
    multishot_run_id: str
    cli_version: str
    config_id: str
    verdict: str  # "pass" or "fail"
    failure_class: Optional[str]
    cost_usd: float
    latency_ms: float
    started_at: str  # UTC ISO-8601
    finished_at: str  # UTC ISO-8601
    stop_reason: Optional[str]


@dataclass
class MultishotResult:
    winner: Optional[MultishotCandidateRecord]
    candidates: List[MultishotCandidateRecord]
    total_cost_usd: float
    total_latency_ms: float


def run_multishot_candidates(
    instruction: str,
    cwd: Path,
    *,
    n_shots: int = 1,
    per_shot_budget: float,
    total_budget: float,
    per_shot_timeout_s: float,
    total_timeout_s: float,
    stop_on_first_pass: bool = True,
    verifier_fn: Callable[[AgenticTaskResult], bool],
    config_id: str,
    task_id: str,
    jsonl_path: Optional[str | Path] = None,
    **kwargs: Any,
) -> MultishotResult:
    """
    Sequential multi-shot repeat-run controller for agentic CLI harnesses.
    Wraps run_agentic_task with per-shot budget/timeout limits, hidden-verifier selection,
    and append-only JSONL telemetry.

    Candidate Isolation Contract:
    Before shot 1, the task input state is snapshotted: a SHA256 hash is computed from the
    sorted relative file paths and sizes in `cwd`, combined with the sorted environment
    variable keys. This fingerprint is captured as `multishot_run_id` across all shots.
    The caller is responsible for filesystem restoration between shots; each shot is
    invoked with identical parameters.
    """
    start_time = time.time()
    accumulated_cost = 0.0
    candidates: list[MultishotCandidateRecord] = []

    # 1. Capture CLI Version
    cli_version = ""
    try:
        res = subprocess.run(
            ["pdd", "--version"], capture_output=True, text=True, timeout=5
        )
        if res.returncode == 0:
            cli_version = res.stdout.strip()
    except Exception:
        pass

    # 2. Candidate Isolation Contract: Snapshot task input state
    files_state: list[tuple[str, int]] = []
    for root, _, files in os.walk(cwd):
        for file in files:
            full_path = os.path.join(root, file)
            try:
                rel_path = os.path.relpath(full_path, cwd)
                size = os.path.getsize(full_path)
                files_state.append((rel_path, size))
            except Exception:
                pass
    files_state.sort()

    hasher = hashlib.sha256()
    for rel_path, size in files_state:
        hasher.update(f"{rel_path}:{size}\n".encode("utf-8"))

    env_keys = sorted(os.environ.keys())
    hasher.update(",".join(env_keys).encode("utf-8"))
    multishot_run_id = hasher.hexdigest()

    # Sequential Loop over Shots
    for shot_idx in range(1, n_shots + 1):
        # Pre-shot budget pre-check
        remaining_budget = total_budget - accumulated_cost
        if remaining_budget < per_shot_budget:
            now_iso = datetime.now(timezone.utc).isoformat()
            record = MultishotCandidateRecord(
                shot_id=shot_idx,
                task_id=task_id,
                multishot_run_id=multishot_run_id,
                cli_version=cli_version,
                config_id=config_id,
                verdict="fail",
                failure_class="budget_truncated",
                cost_usd=0.0,
                latency_ms=0.0,
                started_at=now_iso,
                finished_at=now_iso,
                stop_reason="budget_exhausted",
            )
            candidates.append(record)
            _persist_record(record, jsonl_path)
            break

        # Total timeout enforcement
        elapsed = time.time() - start_time
        if elapsed >= total_timeout_s:
            now_iso = datetime.now(timezone.utc).isoformat()
            record = MultishotCandidateRecord(
                shot_id=shot_idx,
                task_id=task_id,
                multishot_run_id=multishot_run_id,
                cli_version=cli_version,
                config_id=config_id,
                verdict="fail",
                failure_class="timeout_flaky",
                cost_usd=0.0,
                latency_ms=0.0,
                started_at=now_iso,
                finished_at=now_iso,
                stop_reason="timeout",
            )
            candidates.append(record)
            _persist_record(record, jsonl_path)
            break

        # Execute Per-shot Invocation
        shot_start_time = time.time()
        started_at_iso = datetime.now(timezone.utc).isoformat()
        task_result: Optional[AgenticTaskResult] = None
        failure_class: Optional[str] = None
        stop_reason: Optional[str] = None

        try:
            task_result = run_agentic_task(
                instruction, cwd, timeout=per_shot_timeout_s, **kwargs
            )
            cost = task_result.cost_usd
            accumulated_cost += cost
        except Exception:
            # Infrastructure error during run_agentic_task execution
            finished_at_iso = datetime.now(timezone.utc).isoformat()
            latency_ms = (time.time() - shot_start_time) * 1000.0
            record = MultishotCandidateRecord(
                shot_id=shot_idx,
                task_id=task_id,
                multishot_run_id=multishot_run_id,
                cli_version=cli_version,
                config_id=config_id,
                verdict="fail",
                failure_class="infrastructure_error",
                cost_usd=0.0,
                latency_ms=latency_ms,
                started_at=started_at_iso,
                finished_at=finished_at_iso,
                stop_reason="infrastructure_error",
            )
            candidates.append(record)
            _persist_record(record, jsonl_path)
            break

        # Hidden Verifier Invocation
        is_passed = False
        try:
            is_passed = verifier_fn(task_result)
        except Exception:
            failure_class = "infrastructure_error"

        if failure_class != "infrastructure_error":
            if is_passed:
                verdict = "pass"
            else:
                verdict = "fail"
                if not task_result.success:
                    failure_class = classify_failure(task_result.output_text or "")
                else:
                    failure_class = "assertion_logic"
        else:
            verdict = "fail"

        finished_at_iso = datetime.now(timezone.utc).isoformat()
        latency_ms = (time.time() - shot_start_time) * 1000.0

        # Determine stop reason
        if verdict == "pass" and stop_on_first_pass:
            stop_reason = "verifier_pass"
        elif shot_idx == n_shots:
            stop_reason = "max_shots_reached"

        record = MultishotCandidateRecord(
            shot_id=shot_idx,
            task_id=task_id,
            multishot_run_id=multishot_run_id,
            cli_version=cli_version,
            config_id=config_id,
            verdict=verdict,
            failure_class=failure_class,
            cost_usd=task_result.cost_usd,
            latency_ms=latency_ms,
            started_at=started_at_iso,
            finished_at=finished_at_iso,
            stop_reason=stop_reason,
        )
        candidates.append(record)
        _persist_record(record, jsonl_path)

        # Early exit on success
        if verdict == "pass" and stop_on_first_pass:
            break

    # Winner Selection: first passing shot by shot_id ascending
    winner: Optional[MultishotCandidateRecord] = None
    for candidate in candidates:
        if candidate.verdict == "pass":
            winner = candidate
            break

    total_latency_ms = (time.time() - start_time) * 1000.0

    return MultishotResult(
        winner=winner,
        candidates=candidates,
        total_cost_usd=accumulated_cost,
        total_latency_ms=total_latency_ms,
    )


def _persist_record(
    record: MultishotCandidateRecord, jsonl_path: Optional[str | Path]
) -> None:
    if jsonl_path is None:
        return
    try:
        path = Path(jsonl_path)
        path.parent.mkdir(parents=True, exist_ok=True)
        with open(path, "a", encoding="utf-8") as f:
            f.write(json.dumps(dataclasses.asdict(record)) + "\n")
            f.flush()
    except Exception as e:
        console.print(f"[bold red]Failed to write telemetry to {jsonl_path}: {e}[/bold red]")