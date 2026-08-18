#!/usr/bin/env python3
"""Recompute the published descriptive statistics from committed raw results."""

from __future__ import annotations

import json
import statistics
from pathlib import Path
from typing import Any


ROOT = Path(__file__).resolve().parent
RESULTS = ROOT / "results"
PROMPT_LENGTHS = (1024, 4096, 16384)


def load_arm(name: str, index: int = 0) -> dict[str, Any]:
    document = json.loads((RESULTS / name).read_text(encoding="utf-8"))
    return document["arms"][index]


def rows_for(arm: dict[str, Any], prompt_length: int) -> list[dict[str, Any]]:
    return [
        row
        for run in arm["throughput"]
        for row in run["results"]
        if int(row["requested_pp"]) == prompt_length
    ]


def median(rows: list[dict[str, Any]], field: str) -> float:
    return float(statistics.median(float(row[field]) for row in rows))


def throughput_summary(
    bf16_pre: dict[str, Any],
    bf16_post: dict[str, Any],
    oq8e: dict[str, Any],
) -> dict[str, Any]:
    summary: dict[str, Any] = {}
    for prompt_length in PROMPT_LENGTHS:
        pre = rows_for(bf16_pre, prompt_length)
        post = rows_for(bf16_post, prompt_length)
        bf16 = pre + post
        oq = rows_for(oq8e, prompt_length)
        bf16_decode = median(bf16, "gen_tps")
        oq_decode = median(oq, "gen_tps")
        bf16_e2e = median(bf16, "e2e_latency_s")
        oq_e2e = median(oq, "e2e_latency_s")
        summary[str(prompt_length)] = {
            "bf16_decode_tps_values": [float(row["gen_tps"]) for row in bf16],
            "oq8e_decode_tps_values": [float(row["gen_tps"]) for row in oq],
            "bf16_decode_tps_median": bf16_decode,
            "oq8e_decode_tps_median": oq_decode,
            "decode_ratio_oq8e_over_bf16": oq_decode / bf16_decode,
            "bf16_processing_tps_median": median(bf16, "processing_tps"),
            "oq8e_processing_tps_median": median(oq, "processing_tps"),
            "bf16_ttft_seconds_median": median(bf16, "ttft_ms") / 1000,
            "oq8e_ttft_seconds_median": median(oq, "ttft_ms") / 1000,
            "bf16_e2e_seconds_median": bf16_e2e,
            "oq8e_e2e_seconds_median": oq_e2e,
            "e2e_ratio_oq8e_over_bf16": oq_e2e / bf16_e2e,
        }
    return summary


def accuracy_summary(bf16: dict[str, Any], oq8e: dict[str, Any]) -> dict[str, Any]:
    left = {
        (row["suite"], str(row["id"])): row
        for row in bf16["accuracy"]["results"]
    }
    right = {
        (row["suite"], str(row["id"])): row
        for row in oq8e["accuracy"]["results"]
    }
    if left.keys() != right.keys():
        raise RuntimeError("BF16 and oQ8e task identities differ")
    pass_changes = []
    raw_exact = 0
    code_exact = 0
    for key, bf16_row in left.items():
        oq8e_row = right[key]
        raw_exact += bf16_row["response_sha256"] == oq8e_row["response_sha256"]
        code_exact += (
            bf16_row["extracted_code_sha256"]
            == oq8e_row["extracted_code_sha256"]
        )
        if bool(bf16_row["passed"]) != bool(oq8e_row["passed"]):
            pass_changes.append(
                {
                    "suite": key[0],
                    "id": key[1],
                    "bf16_passed": bool(bf16_row["passed"]),
                    "oq8e_passed": bool(oq8e_row["passed"]),
                }
            )
    return {
        "bf16": bf16["accuracy"]["summary"],
        "oq8e": oq8e["accuracy"]["summary"],
        "raw_response_exact": raw_exact,
        "extracted_code_exact": code_exact,
        "total": len(left),
        "pass_changes": pass_changes,
        "warning": (
            "Regression sample, not a blind accuracy benchmark: MBPP prompts expose "
            "up to three tests that are also used by the scorer."
        ),
    }


def main() -> None:
    bf16_ab = load_arm("bf16_mtp_ab.json", index=1)
    bf16_pre = load_arm("bf16_mtp_pre.json")
    bf16_post = load_arm("bf16_mtp_post.json")
    oq8e = load_arm("oq8e_mtp.json")
    report = {
        "scope": (
            "Descriptive single-session observation; fixed BF16-oQ8e-BF16 order, "
            "three repeats per bracket/model run, no thermal or power telemetry."
        ),
        "throughput": throughput_summary(bf16_pre, bf16_post, oq8e),
        "accuracy_regression_sample": accuracy_summary(bf16_ab, oq8e),
        "peak_process_footprint_gib": {
            "bf16_pre": bf16_pre["footprint"]["max_bytes"] / 2**30,
            "bf16_post": bf16_post["footprint"]["max_bytes"] / 2**30,
            "oq8e": oq8e["footprint"]["max_bytes"] / 2**30,
        },
        "load_seconds": {
            "bf16_pre": bf16_pre["load_seconds"],
            "bf16_post": bf16_post["load_seconds"],
            "oq8e": oq8e["load_seconds"],
        },
    }
    print(json.dumps(report, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
