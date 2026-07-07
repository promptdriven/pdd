"""Turn raw run artifacts into the design §6.3 run record.

Sources (all v2 tier-1 — no FS tap required):

- the proxy's snapshot series (tokens, tool calls, first-edit boundary),
- per-request attribution against the materialized tree + manifest
  (penetration family), reconciled against provider usage,
- the iteration analyzer (H2 trajectory family),
- ``git diff`` name lists against the pre-run baseline (edit classification),
- visible-test / hidden-verifier outcomes.
"""

from __future__ import annotations

from fnmatch import fnmatch
from pathlib import Path
from typing import Sequence

from harness.context_snapshots.attribution import (
    Attribution,
    TreeIndex,
    default_token_estimator,
    reconcile_with_usage,
)
from harness.context_snapshots.iteration_analyzer import RunTrajectory
from harness.context_snapshots.schema import SnapshotRecord

FAILURE_CLASSES = (
    "wrong_file_edit",
    "localization_miss",
    "context_overflow",
    "timeout",
    "hidden_contract_miss",
    "forbidden_access",
    "other",
)


def classify_edits(
    changed_paths: Sequence[str],
    target_files: set[str],
    allowed_edit_globs: Sequence[str],
    distractor_paths: set[str],
    core_files: set[str],
    forbidden_paths: Sequence[str] = ("hidden/**",),
) -> dict[str, list[str]]:
    """Design §6.2 post-hoc precedence: forbidden ⇒ distractor(wrong) ⇒
    target ⇒ allowed-glob-within-core ⇒ wrong."""
    result: dict[str, list[str]] = {
        "forbidden": [],
        "wrong_file": [],
        "target": [],
        "in_scope": [],
    }
    for path in changed_paths:
        path = path.replace("\\", "/")
        if any(fnmatch(path, glob) for glob in forbidden_paths):
            result["forbidden"].append(path)
        elif path in distractor_paths:
            result["wrong_file"].append(path)
        elif path in target_files:
            result["target"].append(path)
        elif path in core_files and any(
            fnmatch(path, glob) for glob in allowed_edit_globs
        ):
            result["in_scope"].append(path)
        else:
            result["wrong_file"].append(path)
    return result


def classify_failure(
    hidden_pass: bool,
    visible_pass: bool,
    timed_out: bool,
    edit_classes: dict[str, list[str]],
    target_read_into_context: bool,
    context_overflow: bool,
) -> str | None:
    """One primary failure class per non-pass run (design §6.4)."""
    if hidden_pass:
        return None
    if edit_classes["forbidden"]:
        return "forbidden_access"
    if timed_out:
        return "timeout"
    if context_overflow:
        return "context_overflow"
    if edit_classes["wrong_file"] and not edit_classes["target"]:
        return "wrong_file_edit"
    if not target_read_into_context and not edit_classes["target"]:
        return "localization_miss"
    if visible_pass:
        return "hidden_contract_miss"
    return "other"


def build_run_record(
    *,
    run_id: str,
    scenario_id: str,
    size: str,
    size_multiplier: int,
    trial_index: int,
    arm: str,
    manifest: dict,
    manifest_sha256: str,
    records: Sequence[SnapshotRecord],
    attributions: Sequence[Attribution],
    trajectory: RunTrajectory,
    tree_index: TreeIndex,
    request_texts: Sequence[str],
    changed_paths: Sequence[str],
    target_files: Sequence[str],
    allowed_edit_globs: Sequence[str],
    core_files: Sequence[str],
    visible_pass: bool,
    hidden_pass: bool,
    timed_out: bool,
    wall_clock_seconds: float,
    timeout_seconds: float,
    context_overflow: bool = False,
    env_fingerprint_sha256: str | None = None,
    cli_version: str | None = None,
) -> dict:
    """Assemble one design-§6.3 run record (JSONL-ready dict)."""
    records = sorted(records, key=lambda r: r.ordinal)
    if not (len(records) == len(attributions) == len(request_texts)):
        raise ValueError("records, attributions, request_texts must be parallel")

    first_edit = trajectory.first_edit_ordinal
    before_edit = [
        r for r in records if first_edit is None or r.ordinal < first_edit
    ]

    input_tokens = [r.input_tokens for r in records if r.input_tokens is not None]
    input_tokens_per_run = sum(input_tokens)
    input_tokens_before_first_edit = sum(
        r.input_tokens for r in before_edit if r.input_tokens is not None
    )
    tool_calls_total = sum(len(r.tool_call_names) for r in records)
    tool_calls_before_first_edit = sum(len(r.tool_call_names) for r in before_edit)

    # Penetration family (repeat-counted, usage-reconciled per request).
    distractor_context_tokens_total = 0.0
    distractor_context_tokens_before_first_edit = 0.0
    distractor_files_entered: set[str] = set()
    unique_lines: set[str] = set()
    any_unreconciled = False
    for record, attribution, text in zip(records, attributions, request_texts):
        reconciled = reconcile_with_usage(attribution, record.input_tokens)
        tokens = reconciled["distractor_context_tokens"]
        distractor_context_tokens_total += tokens
        if first_edit is None or record.ordinal < first_edit:
            distractor_context_tokens_before_first_edit += tokens
        distractor_files_entered |= attribution.distractor_files
        unique_lines |= tree_index.matched_distractor_lines(text)
        if not reconciled["reconciled_against_usage"]:
            any_unreconciled = True
    distractor_unique_tokens = sum(
        default_token_estimator(line) for line in unique_lines
    )
    distractor_tokens_on_disk = manifest.get("distractor_tokens_on_disk", 0)
    pool_coverage = (
        min(1.0, distractor_unique_tokens / distractor_tokens_on_disk)
        if distractor_tokens_on_disk
        else 0.0
    )
    distractor_context_share = (
        distractor_context_tokens_total / input_tokens_per_run
        if input_tokens_per_run
        else 0.0
    )

    # Targeting quality (edits) — snapshot-tap era: reads are context-based.
    distractor_paths = {f["upstream_path"] for f in manifest.get("files", [])}
    edit_classes = classify_edits(
        changed_paths,
        target_files={t.replace("\\", "/") for t in target_files},
        allowed_edit_globs=allowed_edit_globs,
        distractor_paths=distractor_paths,
        core_files={c.replace("\\", "/") for c in core_files},
    )
    edits_total = sum(len(v) for v in edit_classes.values())
    wrong_file_edit_rate = (
        len(edit_classes["wrong_file"]) / edits_total if edits_total else 0.0
    )

    target_read_into_context = any(
        attribution.core_files & set(target_files) for attribution in attributions
    )

    failure_class = classify_failure(
        hidden_pass=hidden_pass,
        visible_pass=visible_pass,
        timed_out=timed_out,
        edit_classes=edit_classes,
        target_read_into_context=target_read_into_context,
        context_overflow=context_overflow,
    )

    # Evidence gating (design §6.2/§9): token-level penetration metrics and
    # the H2 trajectory family are SUPPORTED only when the recording proxy
    # captured snapshots for the run and provider usage was present on every
    # request. A command-arm run without an env fingerprint is
    # development-only and must never enter pilot tables.
    token_metrics_supported = bool(records) and all(
        r.input_tokens is not None for r in records
    )
    development_only = arm == "command" and env_fingerprint_sha256 is None

    return {
        "schema_version": 4,
        "run_id": run_id,
        "scenario_id": scenario_id,
        "size": size,
        "size_multiplier": size_multiplier,
        "arm": arm,
        "trial_index": trial_index,
        "timeout_seconds": timeout_seconds,
        "manifest_sha256": manifest_sha256,
        "fs_tap_enabled": False,
        # §8.1.1: null means the run was NOT environment-frozen (mock arm or
        # harness development); real pilot records must carry both values.
        "env_fingerprint_sha256": env_fingerprint_sha256,
        "cli_version": cli_version,
        # Evidence gates consumed by the report (see comment above).
        "token_metrics_supported": token_metrics_supported,
        "development_only": development_only,
        # Cost.
        "iterations_total": trajectory.iterations_total,
        "iterations_before_first_edit": trajectory.iterations_before_first_edit,
        "search_or_tool_calls_before_first_edit": tool_calls_before_first_edit,
        "tool_calls_total": tool_calls_total,
        "input_tokens_before_first_edit": input_tokens_before_first_edit,
        "input_tokens_per_run": input_tokens_per_run,
        "max_request_input_tokens": max(input_tokens, default=0),
        "wall_clock_seconds": wall_clock_seconds,
        # Penetration.
        "distractor_tokens_on_disk": distractor_tokens_on_disk,
        "distractor_context_tokens_total": round(distractor_context_tokens_total, 1),
        "distractor_context_tokens_total_before_first_edit": round(
            distractor_context_tokens_before_first_edit, 1
        ),
        "distractor_context_share": round(distractor_context_share, 4),
        "distractor_unique_tokens_entered_context": round(distractor_unique_tokens, 1),
        "distractor_pool_coverage": round(pool_coverage, 4),
        "distractor_files_entered_context": len(distractor_files_entered),
        "attribution_unreconciled": any_unreconciled,
        # Trajectory (H2).
        "growth_shape": trajectory.growth_shape,
        "largest_single_jump_share": trajectory.largest_single_jump_share,
        "distractor_context_share_early": trajectory.distractor_share_early,
        "distractor_context_share_late": trajectory.distractor_share_late,
        "distractor_context_share_delta": trajectory.share_delta_late_minus_early,
        # Edits.
        "edit_classes": edit_classes,
        "wrong_file_edit_rate": round(wrong_file_edit_rate, 4),
        "forbidden_file_edits": len(edit_classes["forbidden"]),
        # Outcome.
        "visible_pass": visible_pass,
        "hidden_pass": hidden_pass,
        "failure_class": failure_class,
    }


# Runtime droppings that are not agent edits (created by running the tests).
_EDIT_NOISE = ("__pycache__/", ".pytest_cache/", ".pyc")


def read_changed_paths(workdir: str | Path) -> list[str]:
    """Changed paths vs. the pre-run baseline commit (git diff tap).

    Interpreter/test-runner cache artifacts are filtered: they are produced
    by the harness's own verification runs, not by the agent.
    """
    import subprocess

    result = subprocess.run(
        ["git", "diff", "--name-only", "HEAD"],
        cwd=str(workdir),
        capture_output=True,
        text=True,
        check=True,
    )
    untracked = subprocess.run(
        ["git", "ls-files", "--others", "--exclude-standard"],
        cwd=str(workdir),
        capture_output=True,
        text=True,
        check=True,
    )
    paths = [p for p in result.stdout.splitlines() if p.strip()]
    paths += [p for p in untracked.stdout.splitlines() if p.strip()]
    return sorted(
        {
            p
            for p in paths
            if not any(noise in p for noise in _EDIT_NOISE)
        }
    )
