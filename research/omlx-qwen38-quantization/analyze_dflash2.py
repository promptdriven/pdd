#!/usr/bin/env python3
"""Reproduce the local baseline and keep DFlash2 projections distinct from data.

The default output contains planning projections only. Pass a future oMLX result
with ``--dflash-results`` to add a measured arm. The adapter requires an explicit
``dflash_enabled: true`` marker so a projection cannot be mislabeled as a
measurement by accident.
"""

from __future__ import annotations

import argparse
import csv
import json
import math
import statistics
import sys
from pathlib import Path
from typing import Any, TextIO

from analyze_results import load_arm, rows_for, throughput_summary


ROOT = Path(__file__).resolve().parent
INPUTS_PATH = ROOT / "dflash2_projection_inputs.json"
PROMPT_LENGTHS = (1024, 4096, 16384)
GENERATION_LENGTH = 128


def positive_float(value: Any, name: str) -> float:
    """Return a positive finite float or raise a useful input error."""
    number = float(value)
    if number <= 0 or not math.isfinite(number):
        raise ValueError(f"{name} must be a positive finite number")
    return number


def decode_speed_ratio(scenario: dict[str, Any]) -> float:
    """Compute accepted tokens per cycle divided by cycle latency."""
    tokens = positive_float(
        scenario["tokens_per_cycle_ratio"], "tokens_per_cycle_ratio"
    )
    latency = positive_float(scenario["cycle_latency_ratio"], "cycle_latency_ratio")
    return tokens / latency


def project_e2e(
    e2e_seconds: float,
    ttft_seconds: float,
    decode_ratio: float,
    ttft_ratio: float = 1.0,
) -> dict[str, float]:
    """Apply a decode-only speed ratio to a measured request decomposition."""
    e2e = positive_float(e2e_seconds, "e2e_seconds")
    ttft = positive_float(ttft_seconds, "ttft_seconds")
    speed = positive_float(decode_ratio, "decode_ratio")
    prefill_multiplier = positive_float(ttft_ratio, "ttft_ratio")
    if ttft > e2e:
        raise ValueError("ttft_seconds cannot exceed e2e_seconds")
    decode_seconds = e2e - ttft
    projected = ttft * prefill_multiplier + decode_seconds / speed
    return {
        "baseline_decode_phase_seconds": decode_seconds,
        "baseline_decode_share": decode_seconds / e2e,
        "projected_e2e_seconds": projected,
        "e2e_speed_ratio": e2e / projected,
    }


def local_summary() -> dict[str, Any]:
    """Recompute the checked-in BF16 and oQ8e medians from raw JSON."""
    bf16_pre = load_arm("bf16_mtp_pre.json")
    bf16_post = load_arm("bf16_mtp_post.json")
    oq8e = load_arm("oq8e_mtp.json")
    return throughput_summary(bf16_pre, bf16_post, oq8e)


def external_h200_ratios(inputs: dict[str, Any]) -> dict[str, Any]:
    """Compute author-reported DFlash2/MTP ratios without transferring them."""
    evidence = inputs["external_evidence"]["qwen_dflash2_h200"]
    ratios: dict[str, Any] = {}
    for task, row in evidence["concurrency_1"].items():
        throughput = positive_float(row["dflash2_tps"], "dflash2_tps") / positive_float(
            row["mtp_tps"], "mtp_tps"
        )
        acceptance = positive_float(
            row["dflash2_acceptance_length"], "dflash2_acceptance_length"
        ) / positive_float(row["mtp_acceptance_length"], "mtp_acceptance_length")
        ratios[task] = {
            "dflash2_over_mtp_throughput": throughput,
            "dflash2_over_mtp_acceptance": acceptance,
        }
    values = [row["dflash2_over_mtp_throughput"] for row in ratios.values()]
    return {
        "kind": "external_measurement",
        "transfer_warning": (
            "H200/SGLang/FA3 evidence is not an Apple Metal or oMLX measurement."
        ),
        "source": evidence["source"],
        "task_ratios": ratios,
        "throughput_ratio_range": [min(values), max(values)],
    }


def projections(inputs: dict[str, Any], baseline: dict[str, Any]) -> list[dict[str, Any]]:
    """Build explicitly labeled Apple planning projections."""
    output = []
    for scenario in inputs["apple_planning_scenarios"]:
        speed = decode_speed_ratio(scenario)
        prompts: dict[str, Any] = {}
        for prompt in PROMPT_LENGTHS:
            row = baseline[str(prompt)]
            estimate = project_e2e(
                row["oq8e_e2e_seconds_median"],
                row["oq8e_ttft_seconds_median"],
                speed,
                scenario["ttft_ratio"],
            )
            ttft_penalty = project_e2e(
                row["oq8e_e2e_seconds_median"],
                row["oq8e_ttft_seconds_median"],
                speed,
                1.05,
            )
            prompts[str(prompt)] = {
                "baseline_oq8e_mtp_decode_tps": row["oq8e_decode_tps_median"],
                "projected_decode_tps": row["oq8e_decode_tps_median"] * speed,
                **estimate,
                "e2e_speed_ratio_with_5pct_ttft_penalty": ttft_penalty[
                    "e2e_speed_ratio"
                ],
            }
        output.append(
            {
                "kind": "projection",
                "warning": "Assumption-driven; no local DFlash2 measurement.",
                "name": scenario["name"],
                "assumptions": scenario,
                "decode_speed_ratio": speed,
                "prompts": prompts,
            }
        )
    return output


def _dflash_marker(document: dict[str, Any], arm: dict[str, Any]) -> bool:
    metadata = document.get("metadata", {})
    markers = [
        container["dflash_enabled"]
        for container in (metadata, arm)
        if "dflash_enabled" in container
    ]
    return bool(markers) and all(marker is True for marker in markers)


def measured_dflash(path: Path, baseline: dict[str, Any]) -> dict[str, Any]:
    """Normalize a future explicitly marked DFlash2 oMLX result artifact."""
    document = json.loads(path.read_text(encoding="utf-8"))
    metadata = document.get("metadata", {})
    arms = document.get("arms") or []
    if len(arms) != 1:
        raise ValueError("DFlash2 result must contain exactly one arm")
    arm = arms[0]
    if not _dflash_marker(document, arm):
        raise ValueError("DFlash2 result must record dflash_enabled: true")
    if int(metadata.get("generation_length", -1)) != GENERATION_LENGTH:
        raise ValueError(f"generation_length must equal {GENERATION_LENGTH}")
    prompts = tuple(int(value) for value in metadata.get("prompt_lengths", []))
    if prompts != PROMPT_LENGTHS:
        raise ValueError(f"prompt_lengths must equal {PROMPT_LENGTHS}")

    normalized: dict[str, Any] = {}
    for prompt in PROMPT_LENGTHS:
        rows = rows_for(arm, prompt)
        if not rows:
            raise ValueError(f"missing DFlash2 rows for prompt length {prompt}")
        decode = float(statistics.median(float(row["gen_tps"]) for row in rows))
        ttft = float(statistics.median(float(row["ttft_ms"]) for row in rows)) / 1000
        e2e = float(
            statistics.median(float(row["e2e_latency_s"]) for row in rows)
        )
        base = baseline[str(prompt)]
        normalized[str(prompt)] = {
            "dflash2_decode_tps_median": decode,
            "dflash2_ttft_seconds_median": ttft,
            "dflash2_e2e_seconds_median": e2e,
            "decode_ratio_over_checked_in_oq8e_mtp": (
                decode / base["oq8e_decode_tps_median"]
            ),
            "e2e_ratio_over_checked_in_oq8e_mtp": (
                base["oq8e_e2e_seconds_median"] / e2e
            ),
        }
    return {
        "kind": "measurement",
        "source_path": str(path),
        "comparison_warning": (
            "Ratios are apples-to-apples only if hardware, runtime build, target "
            "weights, prompts, order, and settings match the checked-in baseline."
        ),
        "metadata": metadata,
        "prompts": normalized,
    }


def build_report(dflash_path: Path | None = None) -> dict[str, Any]:
    """Return all reproducible local calculations and optional measurements."""
    inputs = json.loads(INPUTS_PATH.read_text(encoding="utf-8"))
    baseline = local_summary()
    report: dict[str, Any] = {
        "schema_version": 1,
        "accessed_date": inputs["accessed_date"],
        "local_baseline": baseline,
        "external_h200_evidence": external_h200_ratios(inputs),
        "apple_planning_projections": projections(inputs, baseline),
    }
    if dflash_path is not None:
        report["local_dflash2_measurement"] = measured_dflash(dflash_path, baseline)
    else:
        report["local_dflash2_measurement"] = None
        report["measurement_warning"] = "No local DFlash2 measurement was supplied."
    return report


def write_csv(report: dict[str, Any], stream: TextIO) -> None:
    """Write the compact projection table to a stream."""
    fields = [
        "kind",
        "scenario",
        "prompt_tokens",
        "decode_speed_ratio",
        "projected_decode_tps",
        "baseline_decode_share",
        "e2e_speed_ratio",
        "e2e_speed_ratio_with_5pct_ttft_penalty",
    ]
    writer = csv.DictWriter(stream, fieldnames=fields)
    writer.writeheader()
    for scenario in report["apple_planning_projections"]:
        for prompt, row in scenario["prompts"].items():
            writer.writerow(
                {
                    "kind": scenario["kind"],
                    "scenario": scenario["name"],
                    "prompt_tokens": prompt,
                    "decode_speed_ratio": scenario["decode_speed_ratio"],
                    "projected_decode_tps": row["projected_decode_tps"],
                    "baseline_decode_share": row["baseline_decode_share"],
                    "e2e_speed_ratio": row["e2e_speed_ratio"],
                    "e2e_speed_ratio_with_5pct_ttft_penalty": row[
                        "e2e_speed_ratio_with_5pct_ttft_penalty"
                    ],
                }
            )


def parse_args() -> argparse.Namespace:
    """Parse command-line options for projections and future raw results."""
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--dflash-results",
        type=Path,
        help="future oMLX JSON with an explicit dflash_enabled=true marker",
    )
    parser.add_argument("--format", choices=("json", "csv"), default="json")
    return parser.parse_args()


def main() -> None:
    """Render the comparison as deterministic JSON or CSV."""
    args = parse_args()
    report = build_report(args.dflash_results)
    if args.format == "csv":
        write_csv(report, sys.stdout)
    else:
        print(json.dumps(report, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
