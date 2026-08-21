"""Tests for the local Qwen3.8 oMLX benchmark adapter."""

from __future__ import annotations

import importlib.util
from pathlib import Path
from unittest.mock import Mock


ROOT = Path(__file__).resolve().parents[1]
MODULE_PATH = ROOT / "research" / "omlx-qwen38-quantization" / "benchmark.py"
SPEC = importlib.util.spec_from_file_location("omlx_qwen38_benchmark", MODULE_PATH)
assert SPEC and SPEC.loader
benchmark = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(benchmark)


def test_set_arm_enables_mtp_without_an_unsupported_depth_field() -> None:
    session = Mock()
    response = Mock(ok=True)
    response.json.return_value = {}
    session.put.return_value = response

    benchmark.set_arm(session, True)

    body = session.put.call_args.kwargs["json"]
    assert body["mtp_enabled"] is True
    assert "mtp_num_draft_tokens" not in body


def test_apply_mtp_depth_profile_can_restore_default_depth(monkeypatch) -> None:
    monkeypatch.setattr(
        benchmark,
        "get_models",
        lambda _session: [{"id": benchmark.MODEL_ID, "settings": {}}],
    )
    session = Mock()
    created = Mock(ok=True)
    created.json.return_value = {}
    applied = Mock(ok=True)
    applied.json.return_value = {"settings": {"mtp_num_draft_tokens": None}}
    session.post.side_effect = [created, applied]

    profile_name = benchmark.apply_mtp_depth_profile(session, None)

    assert profile_name.endswith("-default")
    assert session.post.call_args_list[0].kwargs["json"]["settings"][
        "mtp_num_draft_tokens"
    ] is None


def test_summarize_depth_sweep_uses_first_arm_as_baseline(monkeypatch) -> None:
    monkeypatch.setattr(benchmark, "PROMPT_LENGTHS", [1024])
    arms = [
        {
            "label": "depth_3",
            "throughput": [{"results": [{"requested_pp": 1024, "gen_tps": 10}]}],
        },
        {
            "label": "depth_5",
            "throughput": [{"results": [{"requested_pp": 1024, "gen_tps": 12}]}],
        },
    ]

    result = benchmark.summarize_depth_sweep(arms)["throughput"]["1024"]

    assert result["depth_3"]["speedup_vs_first_arm"] == 1.0
    assert result["depth_5"]["speedup_vs_first_arm"] == 1.2
