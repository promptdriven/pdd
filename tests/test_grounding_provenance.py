"""Tests for grounding provenance helpers."""
from __future__ import annotations

from pdd.grounding_provenance import (
    build_grounding_metadata,
    extract_grounding_overrides,
    grounding_from_llm_result,
    normalize_grounding,
    reviewed_from_decisions,
    review_grounding_examples_interactive,
    selected_examples_from_cloud,
)


def test_extract_grounding_overrides_from_prompt() -> None:
  prompt = "Use <pin>refund_payment</pin> and skip <exclude>legacy_refund</exclude>."
  overrides = extract_grounding_overrides(prompt)
  assert overrides == {"pinned": ["refund_payment"], "excluded": ["legacy_refund"]}


def test_selected_examples_from_cloud_ignores_title_only_records() -> None:
    assert selected_examples_from_cloud([{"title": "Refund Example", "id": "x1"}]) == []


def test_selected_examples_from_cloud_maps_fields() -> None:
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


def test_reviewed_from_decisions_requires_accept() -> None:
    assert reviewed_from_decisions([]) is False
    assert reviewed_from_decisions([{"module": "auth", "decision": "reject"}]) is False
    assert reviewed_from_decisions([{"module": "auth", "decision": "accept"}]) is True


def test_review_grounding_examples_interactive_records_accept(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    ctx: dict = {"grounding_review_decisions": []}
    monkeypatch.setattr("pdd.grounding_provenance.click.confirm", lambda *_, **__: True)
    review_grounding_examples_interactive(
        [{"slug": "payments", "title": "Payments"}],
        ctx,
        quiet=True,
    )
    assert reviewed_from_decisions(ctx["grounding_review_decisions"]) is True


def test_build_grounding_metadata_cloud_mode() -> None:
  grounding = build_grounding_metadata(
      mode="cloud",
      examples_used=[{"slug": "payments"}],
      grounding_overrides={"pinned": ["payments"], "excluded": []},
  )
  assert grounding["mode"] == "cloud"
  assert grounding["selected_examples"][0]["module"] == "payments"
  assert grounding["pinned"] == ["payments"]
