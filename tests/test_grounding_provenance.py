"""Tests for grounding provenance helpers."""
from __future__ import annotations

import pytest

from pdd.grounding_provenance import (
    build_grounding_metadata,
    extract_grounding_overrides,
    grounding_from_llm_result,
    grounding_reviewed_for_manifest,
    normalize_grounding,
    review_pinned_examples_before_generation,
    reviewed_from_decisions,
    selected_examples_from_cloud,
)


def test_extract_grounding_overrides_from_prompt() -> None:
    prompt = "Use <pin>refund_payment</pin> and skip <exclude>legacy_refund</exclude>."
    overrides = extract_grounding_overrides(prompt)
    assert overrides == {"pinned": ["refund_payment"], "excluded": ["legacy_refund"]}


def test_selected_examples_from_cloud_preserves_id_title_shape() -> None:
    """Regression: cloud examplesUsed id/title must not become an empty selected_examples list."""
    selected = selected_examples_from_cloud(
        [{"id": "ex-123", "title": "Test Example Title"}]
    )
    assert selected == [
        {
            "module": "ex-123",
            "id": "ex-123",
            "title": "Test Example Title",
        }
    ]


def test_selected_examples_from_cloud_maps_slug_fields() -> None:
    examples = [
        {
            "slug": "refund_payment",
            "promptSha256": "abc",
            "codeSha256": "def",
            "similarity": 0.91,
            "source": "cloud-history",
        }
    ]
    selected = selected_examples_from_cloud(examples)
    assert selected == [
        {
            "module": "refund_payment",
            "prompt_sha256": "abc",
            "code_sha256": "def",
            "similarity": 0.91,
            "source": "cloud-history",
        }
    ]


def test_normalize_grounding_defaults_to_unavailable() -> None:
    grounding = normalize_grounding(None)
    assert grounding["mode"] == "unavailable"
    assert grounding["selected_examples"] == []
    assert grounding["reviewed"] is False


def test_grounding_from_llm_result_prefers_embedded_grounding() -> None:
    payload = {
        "grounding": {
            "mode": "cloud",
            "selected_examples": [{"module": "auth"}],
            "pinned": ["auth"],
            "excluded": [],
            "reviewed": False,
        }
    }
    grounding = grounding_from_llm_result(payload, reviewed=True)
    assert grounding["mode"] == "cloud"
    assert grounding["reviewed"] is True


def test_reviewed_from_decisions_requires_pre_accept_for_every_example() -> None:
    decisions = [{"module": "payments", "decision": "accept", "phase": "pre"}]
    assert reviewed_from_decisions(decisions, examples_used=[{"id": "payments"}]) is True
    assert reviewed_from_decisions(decisions, examples_used=[{"id": "other"}]) is False
    assert reviewed_from_decisions(decisions, examples_used=[]) is False
    assert reviewed_from_decisions([], examples_used=[{"id": "payments"}]) is False
    assert (
        reviewed_from_decisions(
            [{"module": "payments", "decision": "reject", "phase": "pre"}],
            examples_used=[{"id": "payments"}],
        )
        is False
    )


def test_reviewed_from_decisions_ignores_post_phase_accepts() -> None:
    decisions = [{"module": "auth", "decision": "accept", "phase": "post"}]
    assert reviewed_from_decisions(decisions, examples_used=[{"id": "auth"}]) is False


def test_grounding_reviewed_for_manifest_requires_review_examples_flag() -> None:
    cli = {
        "review_examples": True,
        "grounding_review_decisions": [
            {"module": "payments", "decision": "accept", "phase": "pre"}
        ],
    }
    assert grounding_reviewed_for_manifest(cli, [{"id": "payments"}]) is True
    assert grounding_reviewed_for_manifest(cli, [{"id": "other"}]) is False
    cli_no_flag = dict(cli)
    cli_no_flag["review_examples"] = False
    assert grounding_reviewed_for_manifest(cli_no_flag, [{"id": "payments"}]) is False


def test_review_pinned_examples_before_generation_records_pre_accept(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    ctx: dict = {"grounding_review_decisions": []}
    monkeypatch.setattr("pdd.grounding_provenance.click.confirm", lambda *_, **__: True)
    review_pinned_examples_before_generation(
        ctx,
        "Use <pin>payments</pin> for grounding.\n",
        quiet=True,
    )
    assert reviewed_from_decisions(
        ctx["grounding_review_decisions"],
        examples_used=[{"id": "payments"}],
    ) is True


def test_build_grounding_metadata_cloud_mode() -> None:
    grounding = build_grounding_metadata(
        mode="cloud",
        examples_used=[{"slug": "payments"}],
        grounding_overrides={"pinned": ["payments"], "excluded": []},
    )
    assert grounding["mode"] == "cloud"
    assert grounding["selected_examples"][0]["module"] == "payments"
    assert grounding["pinned"] == ["payments"]
