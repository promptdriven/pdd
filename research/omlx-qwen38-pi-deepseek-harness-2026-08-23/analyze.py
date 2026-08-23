#!/usr/bin/env python3
"""Validate, summarize, and sanitize paired Pi/DSH benchmark JSONL."""

from __future__ import annotations

import argparse
import json
import statistics
from collections import defaultdict
from pathlib import Path
from typing import Any


EXPECTED_HARNESSES = {"pi", "dsh"}
EXPECTED_REQUEST_FIELDS = {
    "max_tokens": [32000],
    "temperature": [None],
    "top_p": [None],
    "reasoning_effort": [None],
    "chat_template_kwargs": [
        {"enable_thinking": True, "preserve_thinking": True}
    ],
}
EXPECTED_TOOL_COUNTS = {"pi": [4], "dsh": [19]}


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser()
    parser.add_argument("results", type=Path)
    parser.add_argument("--manifest", type=Path, required=True)
    parser.add_argument("--checker-revalidation", type=Path, required=True)
    parser.add_argument("--clean-output", type=Path)
    return parser.parse_args()


def load_jsonl(path: Path) -> list[dict[str, Any]]:
    return [json.loads(line) for line in path.read_text().splitlines() if line.strip()]


def validate_checker_revalidation(
    rows: list[dict[str, Any]], evidence: dict[str, Any]
) -> None:
    """Bind hardened checker evidence to every measured result row."""
    evidence_rows = evidence.get("results")
    if (
        evidence.get("rows") != len(rows)
        or evidence.get("all_scores_passes_and_exits_match_original") is not True
        or evidence.get("interpreter_policy")
        != "benchmark_orchestrator_sys.executable"
        or not isinstance(evidence_rows, list)
        or len(evidence_rows) != len(rows)
    ):
        raise RuntimeError("Missing or invalid hardened checker revalidation")
    indexed = {item.get("run_id"): item for item in evidence_rows}
    if len(indexed) != len(rows):
        raise RuntimeError("Duplicate or missing checker revalidation run IDs")
    for row in rows:
        item = indexed.get(row["run_id"])
        grade = row["grade"]
        if not item or item.get("matched_original") is not True:
            raise RuntimeError(f"Checker revalidation missing for {row['run_id']}")
        if (
            item.get("checker_exit") != grade["checker_exit"]
            or item.get("passed") != grade["passed"]
            or item.get("score") != grade["score"]
        ):
            raise RuntimeError(f"Checker revalidation mismatch for {row['run_id']}")


def validate_rows(rows: list[dict[str, Any]], manifest: dict[str, Any]) -> None:
    post_run = manifest.get("post_run_verification") or {}
    if (
        post_run.get("memory_guard_final_tier") != "balanced"
        or post_run.get("two_consecutive_idle_samples") is not True
        or post_run.get("active_requests") != 0
        or post_run.get("waiting_requests") != 0
    ):
        raise RuntimeError("Missing or invalid post-run oMLX restoration evidence")
    tasks = list(manifest["tasks"])
    trials = int(manifest["trials"])
    expected_ids = {
        f"{trial:02d}-{task}-{harness}"
        for trial in range(1, trials + 1)
        for task in tasks
        for harness in EXPECTED_HARNESSES
    }
    run_ids = [str(row["run_id"]) for row in rows]
    if len(run_ids) != len(set(run_ids)):
        raise RuntimeError("Duplicate benchmark run IDs")
    if set(run_ids) != expected_ids:
        missing = sorted(expected_ids - set(run_ids))
        extra = sorted(set(run_ids) - expected_ids)
        raise RuntimeError(f"Incomplete benchmark matrix: missing={missing}, extra={extra}")
    for row in rows:
        task = row["task"]
        expected_run_id = f"{int(row['trial']):02d}-{task}-{row['harness']}"
        if row["run_id"] != expected_run_id:
            raise RuntimeError(
                f"Run ID metadata mismatch: {row['run_id']} != {expected_run_id}"
            )
        if row.get("phase") != "benchmark":
            raise RuntimeError(f"Non-benchmark row in matrix: {row['run_id']}")
        if row["harness"] not in EXPECTED_HARNESSES:
            raise RuntimeError(f"Unknown harness: {row['harness']}")
        if row["model"] != manifest["model"]:
            raise RuntimeError(f"Model drift in {row['run_id']}")
        if row["task_sha256"] != manifest["task_hashes"][task]:
            raise RuntimeError(f"Task hash drift in {row['run_id']}")
        identity = row["proxy_identity"]
        if not identity.get("verified") or not identity.get("serial_requests"):
            raise RuntimeError(f"Unverified proxy identity in {row['run_id']}")
        if identity.get("model") != manifest["model"]:
            raise RuntimeError(f"Proxy model drift in {row['run_id']}")
        if identity.get("base_url") != "http://127.0.0.1:8000":
            raise RuntimeError(f"Proxy endpoint drift in {row['run_id']}")
        if identity.get("path") != "/v1/chat/completions":
            raise RuntimeError(f"Proxy path drift in {row['run_id']}")
        for field, expected in EXPECTED_REQUEST_FIELDS.items():
            if identity.get(field) != expected:
                raise RuntimeError(
                    f"Proxy request-setting drift in {row['run_id']}: {field}"
                )
        harness = str(row["harness"])
        if identity.get("tool_counts") != EXPECTED_TOOL_COUNTS[harness]:
            raise RuntimeError(f"Proxy tool-policy drift in {row['run_id']}")
        if identity.get("completion_requests") != row["proxy_totals"].get("requests"):
            raise RuntimeError(f"Proxy request-count drift in {row['run_id']}")


def aggregate(items: list[dict[str, Any]]) -> dict[str, Any]:
    scores = [float(item["grade"]["score"]) for item in items]
    walls = [float(item["harness_result"]["wall_seconds"]) for item in items]
    totals = [item["proxy_totals"] for item in items]
    input_tokens = sum(int(item["input_tokens"]) for item in totals)
    output_tokens = sum(int(item["output_tokens"]) for item in totals)
    generation_seconds = sum(float(item["generation_duration_seconds"]) for item in totals)
    prompt_eval_seconds = sum(float(item["prompt_eval_duration_seconds"]) for item in totals)
    completed_responses = sum(int(item["completed_responses"]) for item in totals)
    ttft_seconds = sum(float(item["time_to_first_token_seconds"]) for item in totals)
    return {
        "runs": len(items),
        "passes": sum(bool(item["grade"]["passed"]) for item in items),
        "timeouts": sum(bool(item["harness_result"]["timed_out"]) for item in items),
        "mean_score": statistics.fmean(scores),
        "median_wall_seconds": statistics.median(walls),
        "total_wall_seconds": sum(walls),
        "total_requests": sum(int(item["requests"]) for item in totals),
        "failed_requests": sum(int(item["failures"]) for item in totals),
        "completed_responses": completed_responses,
        "total_input_tokens": input_tokens,
        "total_output_tokens": output_tokens,
        "median_output_tokens": statistics.median(
            int(item["output_tokens"]) for item in totals
        ),
        "aggregate_prompt_tokens_per_second": (
            input_tokens / prompt_eval_seconds if prompt_eval_seconds else None
        ),
        "aggregate_generation_tokens_per_second": (
            output_tokens / generation_seconds if generation_seconds else None
        ),
        "mean_time_to_first_token_seconds": (
            ttft_seconds / completed_responses if completed_responses else None
        ),
    }


def summarize(rows: list[dict[str, Any]]) -> dict[str, Any]:
    by_harness: dict[str, list[dict[str, Any]]] = defaultdict(list)
    by_pair: dict[tuple[str, int], dict[str, dict[str, Any]]] = defaultdict(dict)
    by_task: dict[str, dict[str, list[dict[str, Any]]]] = defaultdict(
        lambda: defaultdict(list)
    )
    for row in rows:
        harness = str(row["harness"])
        task = str(row["task"])
        trial = int(row["trial"])
        by_harness[harness].append(row)
        by_pair[(task, trial)][harness] = row
        by_task[task][harness].append(row)
    summary: dict[str, Any] = {
        "runs": len(rows),
        "harnesses": {
            harness: aggregate(items) for harness, items in sorted(by_harness.items())
        },
        "pairs": [],
        "tasks": {},
    }
    deltas: list[float] = []
    for (task, trial), pair in sorted(by_pair.items()):
        if set(pair) != EXPECTED_HARNESSES:
            raise RuntimeError(f"Incomplete pair: {task} trial {trial}")
        pi_score = float(pair["pi"]["grade"]["score"])
        dsh_score = float(pair["dsh"]["grade"]["score"])
        delta = dsh_score - pi_score
        deltas.append(delta)
        summary["pairs"].append(
            {
                "task": task,
                "trial": trial,
                "pi_score": pi_score,
                "dsh_score": dsh_score,
                "score_delta_dsh_minus_pi": delta,
                "pi_passed": bool(pair["pi"]["grade"]["passed"]),
                "dsh_passed": bool(pair["dsh"]["grade"]["passed"]),
                "wall_delta_seconds_dsh_minus_pi": (
                    float(pair["dsh"]["harness_result"]["wall_seconds"])
                    - float(pair["pi"]["harness_result"]["wall_seconds"])
                ),
                "output_token_delta_dsh_minus_pi": (
                    int(pair["dsh"]["proxy_totals"]["output_tokens"])
                    - int(pair["pi"]["proxy_totals"]["output_tokens"])
                ),
            }
        )
    summary["mean_paired_delta_dsh_minus_pi"] = statistics.fmean(deltas)
    summary["dsh_pair_wins"] = sum(delta > 0 for delta in deltas)
    summary["pi_pair_wins"] = sum(delta < 0 for delta in deltas)
    summary["pair_ties"] = sum(delta == 0 for delta in deltas)
    for task, harnesses in sorted(by_task.items()):
        summary["tasks"][task] = {
            harness: aggregate(items) for harness, items in sorted(harnesses.items())
        }
    return summary


def sanitize_row(row: dict[str, Any]) -> dict[str, Any]:
    harness_result = row["harness_result"]
    grade = row["grade"]
    return {
        "schema_version": row["schema_version"],
        "run_id": row["run_id"],
        "phase": row["phase"],
        "task": row["task"],
        "task_sha256": row["task_sha256"],
        "harness": row["harness"],
        "trial": row["trial"],
        "model": row["model"],
        "thinking": row["thinking"],
        "timeout_seconds": row["timeout_seconds"],
        "harness_result": {
            "returncode": harness_result["returncode"],
            "timed_out": harness_result["timed_out"],
            "wall_seconds": harness_result["wall_seconds"],
            "stdout_bytes": harness_result["stdout_bytes"],
            "stderr_bytes": harness_result["stderr_bytes"],
            "forced_residual_pids": harness_result["forced_residual_pids"],
        },
        "proxy_totals": row["proxy_totals"],
        "proxy_identity": row["proxy_identity"],
        "grade": {
            "checker_exit": grade["checker_exit"],
            "score": grade["score"],
            "passed": grade["passed"],
        },
        "changes": row["changes"],
        "finished_at": row["finished_at"],
    }


def sanitized_artifact(
    manifest: dict[str, Any],
    rows: list[dict[str, Any]],
    summary: dict[str, Any],
    checker_revalidation: dict[str, Any],
) -> dict[str, Any]:
    safe_manifest_keys = (
        "schema_version",
        "started_at",
        "access_date",
        "endpoint",
        "model",
        "runtime",
        "memory_guard_during_trials",
        "memory_guard_required_final_tier",
        "post_run_verification",
        "tasks",
        "task_hashes",
        "task_source",
        "trials",
        "timeout_seconds",
        "smoke_timeout_seconds",
        "pi_version",
        "dsh",
        "tool_policy",
        "operational_notes_not_measurements",
    )
    artifact = {
        "study": "Pi versus official DeepSeek Harness on local oMLX",
        "manifest": {key: manifest[key] for key in safe_manifest_keys},
        "consistency": {
            "passed": True,
            "unique_run_ids": True,
            "complete_balanced_matrix": True,
            "task_hashes_match": True,
            "exact_endpoint_and_model_verified": True,
            "exact_request_settings_verified": True,
            "serial_request_telemetry_verified": True,
        },
        "checker_revalidation": checker_revalidation,
        "analysis": summary,
        "results": [sanitize_row(row) for row in rows],
    }
    serialized = json.dumps(artifact, sort_keys=True).lower()
    forbidden = (
        "authorization",
        "api_key",
        "apikey",
        "bearer ",
        "sk-",
        "loopback-proxy",
        "omlx_benchmark_api_key",
        "/private/tmp",
        "/users/",
    )
    found = [token for token in forbidden if token in serialized]
    if found:
        raise RuntimeError(f"Sanitized artifact contains forbidden material: {found}")
    return artifact


def main() -> None:
    args = parse_args()
    rows = load_jsonl(args.results)
    manifest = json.loads(args.manifest.read_text(encoding="utf-8"))
    checker_revalidation = json.loads(
        args.checker_revalidation.read_text(encoding="utf-8")
    )
    validate_checker_revalidation(rows, checker_revalidation)
    validate_rows(rows, manifest)
    summary = summarize(rows)
    if args.clean_output:
        artifact = sanitized_artifact(
            manifest, rows, summary, checker_revalidation
        )
        args.clean_output.parent.mkdir(parents=True, exist_ok=True)
        args.clean_output.write_text(
            json.dumps(artifact, indent=2, sort_keys=True) + "\n", encoding="utf-8"
        )
    print(json.dumps(summary, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
