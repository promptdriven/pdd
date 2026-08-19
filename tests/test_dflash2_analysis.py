"""Tests for the non-destructive DFlash2 comparison adapter."""

from __future__ import annotations

import json
import math
import sys
from pathlib import Path

import pytest


RESEARCH_DIR = (
    Path(__file__).resolve().parents[1]
    / "research"
    / "omlx-qwen38-quantization"
)
sys.path.insert(0, str(RESEARCH_DIR))

import analyze_dflash2 as analysis  # noqa: E402  pylint: disable=wrong-import-position


def test_local_summary_reproduces_committed_medians() -> None:
    """Raw committed rows remain the source of the published medians."""
    summary = analysis.local_summary()

    assert summary["1024"]["oq8e_decode_tps_median"] == 15.3
    assert summary["4096"]["bf16_decode_tps_median"] == 10.15
    assert summary["16384"]["oq8e_e2e_seconds_median"] == 170.584


def test_projection_identity_and_invalid_inputs() -> None:
    """The projection is stable at identity and rejects invalid ratios."""
    identity = analysis.project_e2e(20.0, 5.0, 1.0)

    assert identity["projected_e2e_seconds"] == 20.0
    assert identity["e2e_speed_ratio"] == 1.0
    with pytest.raises(ValueError, match="decode_ratio"):
        analysis.project_e2e(20.0, 5.0, 0.0)
    with pytest.raises(ValueError, match="decode_ratio"):
        analysis.project_e2e(20.0, 5.0, float("nan"))
    with pytest.raises(ValueError, match="cannot exceed"):
        analysis.project_e2e(5.0, 6.0, 1.0)


def test_golden_apple_projection_values() -> None:
    """Planning scenarios remain reproducible and explicitly unmeasured."""
    report = analysis.build_report()
    by_name = {
        item["name"]: item for item in report["apple_planning_projections"]
    }

    assert report["local_dflash2_measurement"] is None
    assert math.isclose(by_name["worst"]["decode_speed_ratio"], 0.76)
    assert math.isclose(
        by_name["base"]["prompts"]["4096"]["e2e_speed_ratio"],
        1.0227262772,
        rel_tol=1e-9,
    )
    assert math.isclose(
        by_name["best"]["prompts"]["16384"]["e2e_speed_ratio"],
        1.0117183534,
        rel_tol=1e-9,
    )


def _measurement_document(marker: object = True) -> dict[str, object]:
    metadata: dict[str, object] = {
        "generation_length": 128,
        "prompt_lengths": [1024, 4096, 16384],
    }
    if marker is not None:
        metadata["dflash_enabled"] = marker
    rows = [
        {
            "requested_pp": prompt,
            "gen_tps": decode,
            "ttft_ms": ttft,
            "e2e_latency_s": e2e,
        }
        for prompt, decode, ttft, e2e in (
            (1024, 18.0, 12000.0, 20.0),
            (4096, 17.0, 38000.0, 46.0),
            (16384, 16.0, 163000.0, 171.0),
        )
    ]
    return {
        "metadata": metadata,
        "arms": [{"throughput": [{"results": rows}]}],
    }


def test_measurement_adapter_requires_marker_and_preserves_kind(
    tmp_path: Path,
) -> None:
    """Only explicitly marked raw data can be labeled as a measurement."""
    path = tmp_path / "dflash.json"
    path.write_text(json.dumps(_measurement_document()), encoding="utf-8")

    measured = analysis.measured_dflash(path, analysis.local_summary())

    assert measured["kind"] == "measurement"
    assert measured["prompts"]["1024"]["dflash2_decode_tps_median"] == 18.0
    assert measured["prompts"]["4096"][
        "decode_ratio_over_checked_in_oq8e_mtp"
    ] == pytest.approx(17.0 / 15.2)

    invalid_documents = [
        _measurement_document(marker=None),
        _measurement_document(marker=False),
        _measurement_document(marker="false"),
        {
            **_measurement_document(),
            "arms": [
                {
                    **_measurement_document()["arms"][0],
                    "dflash_enabled": False,
                }
            ],
        },
    ]
    for invalid in invalid_documents:
        path.write_text(json.dumps(invalid), encoding="utf-8")
        with pytest.raises(ValueError, match="dflash_enabled"):
            analysis.measured_dflash(path, analysis.local_summary())
