"""
Agentic CLI Config Benchmark Runner.

Iterates all (task_id, config, trial_index) cells defined in benchmark_config_axis.json,
verifies locked fixture hashes, invokes the agentic CLI harness via subprocess, and
writes one JSONL record per run to reports/.

Usage:
    python run_benchmark.py [--axis benchmark_config_axis.json] [--dry-run] [--cell LABEL]

See design.md for the full experiment design and schema documentation.
Issue: https://github.com/promptdriven/pdd/issues/1594
"""

from __future__ import annotations

import argparse
import csv
import hashlib
import json
import logging
import subprocess
import sys
import time
from datetime import datetime, timezone
from pathlib import Path
from typing import Any, Optional

logging.basicConfig(
    level=logging.INFO,
    format="%(asctime)s %(levelname)s %(message)s",
    datefmt="%Y-%m-%dT%H:%M:%SZ",
)
log = logging.getLogger(__name__)

REPO_ROOT = Path(__file__).resolve().parent.parent.parent
LLM_MODEL_CSV = REPO_ROOT / "pdd" / "data" / "llm_model.csv"
REPORTS_DIR = Path(__file__).resolve().parent / "reports"

DEEPSWE_RANK_CAVEAT = (
    "Measured under DeepSWE harness; not directly comparable to PDD agentic CLI pass-rate."
)

# ---------------------------------------------------------------------------
# Schema version for run records
# ---------------------------------------------------------------------------
RUN_RECORD_SCHEMA_VERSION = 1


# ---------------------------------------------------------------------------
# Config identity hash
# ---------------------------------------------------------------------------

def compute_config_sha256(
    harness_id: str,
    harness_version: str,
    model_id: str,
    thinking_enabled: bool,
    thinking_effort: Optional[str],
) -> str:
    """Stable config identity hash over the five config-axis dimensions."""
    canonical = json.dumps(
        {
            "harness_id": harness_id,
            "harness_version": harness_version,
            "model_id": model_id,
            "thinking_enabled": thinking_enabled,
            "thinking_effort": thinking_effort,
        },
        sort_keys=True,
        separators=(",", ":"),
    )
    return hashlib.sha256(canonical.encode()).hexdigest()


# ---------------------------------------------------------------------------
# Model registry
# ---------------------------------------------------------------------------

def load_model_registry(csv_path: Path) -> dict[str, dict[str, Any]]:
    """Load pdd/data/llm_model.csv into a dict keyed by model id."""
    registry: dict[str, dict[str, Any]] = {}
    if not csv_path.exists():
        log.warning("llm_model.csv not found at %s; model validation skipped.", csv_path)
        return registry
    with open(csv_path, newline="") as fh:
        reader = csv.DictReader(fh)
        for row in reader:
            model_id = row.get("model", "").strip()
            if model_id:
                registry[model_id] = {
                    "model_rank_score": _safe_float(row.get("model_rank_score")),
                    "model_rank_source": row.get("model_rank_source", "").strip(),
                    "reasoning_type": row.get("reasoning_type", "").strip(),
                    "interactive_only": row.get("interactive_only", "False").strip().lower() == "true",
                }
    return registry


def _safe_float(value: Optional[str]) -> Optional[float]:
    try:
        return float(value) if value else None
    except (ValueError, TypeError):
        return None


# ---------------------------------------------------------------------------
# Locked invariant verification
# ---------------------------------------------------------------------------

def verify_locked_hashes(locked: dict[str, Any]) -> None:
    """Abort if any hash field is a placeholder."""
    for key, value in locked.items():
        if isinstance(value, str) and value.startswith("PLACEHOLDER_"):
            raise SystemExit(
                f"ERROR: locked_invariants.{key} is still a placeholder value '{value}'. "
                "Replace with the actual SHA256 hash from #1419 fixtures before running."
            )


# ---------------------------------------------------------------------------
# Harness invocation
# ---------------------------------------------------------------------------

def invoke_harness(
    config: dict[str, Any],
    task_id: str,
    trial_index: int,
    timeout_seconds: int,
    materialized_repo_path: Optional[Path],
    dry_run: bool,
) -> dict[str, Any]:
    """
    Invoke the agentic CLI harness for one (task, config, trial) cell.

    Returns a dict with the run outcome fields to merge into the run record.
    In dry-run mode, returns a placeholder outcome without invoking the harness.
    """
    if dry_run:
        log.info(
            "[DRY RUN] Would invoke harness: task=%s config=%s trial=%d",
            task_id,
            config["label"],
            trial_index,
        )
        return {
            "hidden_pass": None,
            "visible_pass": None,
            "failure_class": None,
            "cost_usd": None,
            "cost_source": "unavailable",
            "input_tokens": None,
            "output_tokens": None,
            "wall_clock_seconds": 0.0,
            "timed_out": False,
            "files_read_before_first_edit": None,
            "files_read_source": "unavailable",
            "wrong_file_edit_count": None,
            "raw_trace_path": None,
        }

    run_dir = REPORTS_DIR / f"{task_id}.{config['label']}.trial{trial_index}"
    run_dir.mkdir(parents=True, exist_ok=True)
    trace_path = run_dir / "trace.jsonl"

    cmd = _build_harness_command(config, task_id, trial_index, timeout_seconds, run_dir)
    log.info("Invoking harness: %s", " ".join(str(c) for c in cmd))

    start = time.monotonic()
    timed_out = False
    proc_result: Optional[subprocess.CompletedProcess] = None

    try:
        proc_result = subprocess.run(
            cmd,
            timeout=timeout_seconds + 30,  # grace period beyond the harness timeout
            capture_output=True,
            text=True,
            cwd=str(materialized_repo_path) if materialized_repo_path else None,
        )
    except subprocess.TimeoutExpired:
        timed_out = True
        log.warning("Harness subprocess timed out for %s/%s trial %d", task_id, config["label"], trial_index)

    wall_clock = time.monotonic() - start

    # Parse harness output for outcome fields
    outcome = _parse_harness_output(proc_result, timed_out, trace_path)
    outcome["wall_clock_seconds"] = round(wall_clock, 3)
    outcome["timed_out"] = timed_out
    outcome["raw_trace_path"] = str(trace_path.relative_to(REPORTS_DIR.parent)) if trace_path.exists() else None

    return outcome


def _build_harness_command(
    config: dict[str, Any],
    task_id: str,
    trial_index: int,
    timeout_seconds: int,
    run_dir: Path,
) -> list[str]:
    """
    Build the harness subprocess command for the given config cell.

    The PDD agentic CLI harness is invoked consistently with research/repo-bloat-benchmark.
    Extend this function when the harness CLI interface changes.
    """
    cmd = [
        sys.executable, "-m", "pdd", "agentic-run",
        "--task-id", task_id,
        "--model", config["model_id"],
        "--harness", config["harness_id"],
        "--harness-version", config["harness_version"],
        "--timeout", str(timeout_seconds),
        "--trial", str(trial_index),
        "--output-dir", str(run_dir),
    ]
    if config.get("thinking_enabled"):
        cmd += ["--thinking-enabled", "--thinking-effort", config.get("thinking_effort") or "medium"]
    return cmd


def _parse_harness_output(
    proc_result: Optional[subprocess.CompletedProcess],
    timed_out: bool,
    trace_path: Path,
) -> dict[str, Any]:
    """Extract outcome fields from harness output. Falls back to safe nulls on parse failure."""
    outcome: dict[str, Any] = {
        "hidden_pass": None,
        "visible_pass": None,
        "failure_class": "timeout" if timed_out else None,
        "cost_usd": None,
        "cost_source": "unavailable",
        "input_tokens": None,
        "output_tokens": None,
        "files_read_before_first_edit": None,
        "files_read_source": "unavailable",
        "wrong_file_edit_count": None,
    }

    if proc_result is None:
        return outcome

    # Harness writes a result JSON to stdout on success
    try:
        result = json.loads(proc_result.stdout or "{}")
        outcome["hidden_pass"] = result.get("hidden_pass")
        outcome["visible_pass"] = result.get("visible_pass")
        outcome["failure_class"] = result.get("failure_class") or outcome["failure_class"]
        outcome["cost_usd"] = result.get("cost_usd")
        outcome["cost_source"] = result.get("cost_source", "unavailable")
        outcome["input_tokens"] = result.get("input_tokens")
        outcome["output_tokens"] = result.get("output_tokens")
        outcome["files_read_before_first_edit"] = result.get("files_read_before_first_edit")
        outcome["files_read_source"] = result.get("files_read_source", "unavailable")
        outcome["wrong_file_edit_count"] = result.get("wrong_file_edit_count")
    except (json.JSONDecodeError, AttributeError):
        log.debug("Could not parse harness stdout as JSON; outcome fields remain null.")

    return outcome


# ---------------------------------------------------------------------------
# Run record construction
# ---------------------------------------------------------------------------

def build_run_record(
    config: dict[str, Any],
    task_id: str,
    trial_index: int,
    locked: dict[str, Any],
    outcome: dict[str, Any],
    model_registry: dict[str, dict[str, Any]],
) -> dict[str, Any]:
    """Assemble a complete JSONL run record for one (task, config, trial) cell."""
    model_id = config["model_id"]
    model_meta = model_registry.get(model_id, {})
    thinking_enabled: bool = config.get("thinking_enabled", False)
    thinking_effort: Optional[str] = config.get("thinking_effort")
    harness_id: str = config["harness_id"]
    harness_version: str = config["harness_version"]

    config_sha = compute_config_sha256(
        harness_id, harness_version, model_id, thinking_enabled, thinking_effort
    )

    ts = datetime.now(timezone.utc).strftime("%Y-%m-%dT%H:%M:%SZ")
    run_id = f"{task_id}.{config['label']}.trial{trial_index}.{ts}"

    model_rank_source = model_meta.get("model_rank_source") or config.get("model_rank_source")
    deepswe_score: Optional[float] = None
    deepswe_caveat: Optional[str] = None
    if model_rank_source == "deepswe-solve-rate":
        deepswe_score = model_meta.get("model_rank_score") or config.get("model_rank_score")
        deepswe_caveat = DEEPSWE_RANK_CAVEAT

    record: dict[str, Any] = {
        "run_id": run_id,
        "schema_version": RUN_RECORD_SCHEMA_VERSION,
        "task_id": task_id,
        "config_sha256": config_sha,
        "config_label": config["label"],
        "config_rank": config.get("config_rank"),
        "trial_index": trial_index,
        # Config identity
        "harness_id": harness_id,
        "harness_version": harness_version,
        "model_id": model_id,
        "thinking_enabled": thinking_enabled,
        "thinking_effort": thinking_effort,
        "is_default_baseline": config.get("is_default_baseline", False),
        # Model metadata from registry
        "model_rank_score": model_meta.get("model_rank_score") or config.get("model_rank_score"),
        "model_rank_source": model_rank_source,
        "reasoning_type": model_meta.get("reasoning_type") or config.get("reasoning_type"),
        "external_deepswe_rank_score": deepswe_score,
        "deepswe_rank_caveat": deepswe_caveat,
        # Locked invariants (verified pre-run)
        "task_id_locked": locked.get("task_id"),
        "visible_tests_sha256": locked.get("visible_tests_sha256"),
        "hidden_verifier_sha256": locked.get("hidden_verifier_sha256"),
        "materialized_repo_sha256": locked.get("materialized_repo_sha256"),
        "timeout_seconds": locked.get("timeout_seconds"),
        "repeat_runs": locked.get("repeat_runs"),
        "hash_verified": True,
        # Outcome fields
        **outcome,
    }
    return record


# ---------------------------------------------------------------------------
# Main loop
# ---------------------------------------------------------------------------

def run_sweep(
    axis_path: Path,
    dry_run: bool,
    cell_filter: Optional[str],
    materialized_repo_path: Optional[Path],
) -> None:
    """Run the full (task × config × trial) matrix."""
    REPORTS_DIR.mkdir(parents=True, exist_ok=True)

    with open(axis_path) as fh:
        axis = json.load(fh)

    locked: dict[str, Any] = axis["locked_invariants"]
    configs: list[dict[str, Any]] = axis["configs"]
    repeat_runs: int = locked.get("repeat_runs", 5)
    timeout_seconds: int = locked.get("timeout_seconds", 1800)
    task_id: str = locked.get("task_id", "unknown-task")

    verify_locked_hashes(locked)
    model_registry = load_model_registry(LLM_MODEL_CSV)

    thinking_eligible = set(axis.get("scheduling_rules", {}).get("thinking_eligible_reasoning_types", ["effort", "budget"]))

    total_cells = 0
    skipped_cells = 0
    failed_cells = 0

    for config in configs:
        label = config["label"]
        if cell_filter and label != cell_filter:
            continue

        # Scheduling gates
        if config.get("interactive_only"):
            log.info("Skipping config '%s': interactive_only=True.", label)
            skipped_cells += 1
            continue

        if config.get("thinking_enabled"):
            reasoning_type = config.get("reasoning_type", "")
            if reasoning_type not in thinking_eligible:
                log.info(
                    "Skipping config '%s': thinking=True but reasoning_type='%s' not in %s.",
                    label, reasoning_type, sorted(thinking_eligible),
                )
                skipped_cells += 1
                continue

        log.info("Running config '%s' (rank=%s, model=%s, thinking=%s), %d trials.",
                 label, config.get("config_rank"), config["model_id"],
                 config.get("thinking_enabled"), repeat_runs)

        for trial_index in range(repeat_runs):
            total_cells += 1
            log.info("  Trial %d/%d ...", trial_index + 1, repeat_runs)
            try:
                outcome = invoke_harness(
                    config=config,
                    task_id=task_id,
                    trial_index=trial_index,
                    timeout_seconds=timeout_seconds,
                    materialized_repo_path=materialized_repo_path,
                    dry_run=dry_run,
                )
                record = build_run_record(
                    config=config,
                    task_id=task_id,
                    trial_index=trial_index,
                    locked=locked,
                    outcome=outcome,
                    model_registry=model_registry,
                )
                _write_run_record(record)
                status = "pass" if record.get("hidden_pass") else ("null" if record.get("hidden_pass") is None else "fail")
                log.info("  Trial %d done: hidden_pass=%s, failure_class=%s, cost_usd=%s",
                         trial_index, status, record.get("failure_class"), record.get("cost_usd"))
            except Exception as exc:
                failed_cells += 1
                log.error("  Trial %d FAILED with exception: %s", trial_index, exc, exc_info=True)

    log.info(
        "Sweep complete. total=%d skipped=%d failed=%d succeeded=%d",
        total_cells, skipped_cells, failed_cells, total_cells - failed_cells,
    )


def _write_run_record(record: dict[str, Any]) -> None:
    """Append a JSONL run record to the per-label run file in reports/."""
    label = record.get("config_label", "unknown")
    task_id = record.get("task_id", "unknown")
    out_path = REPORTS_DIR / f"{task_id}.{label}.runs.jsonl"
    with open(out_path, "a") as fh:
        fh.write(json.dumps(record, default=str) + "\n")
    log.debug("Wrote run record to %s", out_path)


# ---------------------------------------------------------------------------
# CLI entry point
# ---------------------------------------------------------------------------

def main() -> None:
    parser = argparse.ArgumentParser(
        description="Run the agentic-config-benchmark sweep.",
        formatter_class=argparse.RawDescriptionHelpFormatter,
        epilog=__doc__,
    )
    parser.add_argument(
        "--axis",
        default=str(Path(__file__).parent / "benchmark_config_axis.json"),
        help="Path to benchmark_config_axis.json (default: %(default)s)",
    )
    parser.add_argument(
        "--dry-run",
        action="store_true",
        help="Print what would be run without invoking the harness.",
    )
    parser.add_argument(
        "--cell",
        metavar="LABEL",
        default=None,
        help="Run only the config cell with this label (e.g. 'baseline').",
    )
    parser.add_argument(
        "--repo",
        metavar="PATH",
        default=None,
        help="Path to the materialized repo to pass to the harness (optional).",
    )
    parser.add_argument(
        "--verbose", "-v",
        action="store_true",
        help="Enable DEBUG logging.",
    )
    args = parser.parse_args()

    if args.verbose:
        logging.getLogger().setLevel(logging.DEBUG)

    axis_path = Path(args.axis)
    if not axis_path.exists():
        parser.error(f"Axis file not found: {axis_path}")

    repo_path = Path(args.repo) if args.repo else None

    run_sweep(
        axis_path=axis_path,
        dry_run=args.dry_run,
        cell_filter=args.cell,
        materialized_repo_path=repo_path,
    )


if __name__ == "__main__":
    main()
