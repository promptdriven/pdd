"""Live E2E coverage for story failure diagnostics.

This test creates a real prompt file and a real user story file, then validates
them through ``run_user_story_tests`` with the real ``detect_change`` LLM path.
It is opt-in because it makes live model calls and costs money.

Run with:
    pytest -q -m e2e tests/test_e2e_story_failure_diagnostics.py
"""

import csv
import os
from pathlib import Path

import google.auth
import pytest

import pdd
from pdd.user_story_tests import run_user_story_tests

pytestmark = [pytest.mark.e2e, pytest.mark.real, pytest.mark.timeout(600)]

_STRENGTH = float(os.environ.get("PDD_DEMO_STRENGTH", "0.5"))


def _pick_keyed_model() -> str | None:
    """Return a non-interactive model whose required key env vars are set."""
    csv_path = Path(pdd.__file__).resolve().parent / "data" / "llm_model.csv"
    if not csv_path.exists():
        return None

    vertex_project = (
        os.environ.get("VERTEXAI_PROJECT")
        or os.environ.get("VERTEX_PROJECT")
        or os.environ.get("GOOGLE_CLOUD_PROJECT")
    )
    vertex_location = os.environ.get("VERTEXAI_LOCATION") or os.environ.get(
        "VERTEX_LOCATION"
    )

    preferred_tokens = ("flash", "mini", "haiku", "lite", "small", "2.5")
    fallback = None
    with open(csv_path, newline="", encoding="utf-8") as handle:
        rows = list(csv.DictReader(handle))

    if vertex_project:
        explicit_vertex_fallback = None
        vertex_fallback = None
        for row in rows:
            if str(row.get("interactive_only", "")).strip().lower() == "true":
                continue
            env_vars = [
                env.strip()
                for env in (row.get("api_key") or "").split("|")
                if env.strip()
            ]
            model = (row.get("model") or "").strip()
            row_location = (row.get("location") or "").strip()
            if not (
                model
                and "GOOGLE_APPLICATION_CREDENTIALS" in env_vars
                and (vertex_location or row_location)
            ):
                continue
            is_explicit_vertex = model.lower().startswith("vertex_ai/")
            if is_explicit_vertex and "gemini" in model.lower() and "flash" in model.lower():
                return model
            if is_explicit_vertex:
                explicit_vertex_fallback = explicit_vertex_fallback or model
            elif "gemini" in model.lower() and "flash" in model.lower():
                vertex_fallback = vertex_fallback or model
            else:
                vertex_fallback = vertex_fallback or model
        if explicit_vertex_fallback or vertex_fallback:
            return explicit_vertex_fallback or vertex_fallback

    for row in rows:
            if str(row.get("interactive_only", "")).strip().lower() == "true":
                continue
            env_vars = [
                env.strip()
                for env in (row.get("api_key") or "").split("|")
                if env.strip()
            ]
            model = (row.get("model") or "").strip()
            if not model:
                continue
            if not env_vars or not all(os.environ.get(env) for env in env_vars):
                continue
            if any(token in model.lower() for token in preferred_tokens):
                return model
            fallback = fallback or model
    return fallback


_KEYED_MODEL = _pick_keyed_model()
_ADC_PATH_SNAPSHOT = (
    Path(os.environ["GOOGLE_APPLICATION_CREDENTIALS"])
    if os.environ.get("GOOGLE_APPLICATION_CREDENTIALS")
    else Path.home() / ".config" / "gcloud" / "application_default_credentials.json"
)

# conftest clears provider keys before each test so ordinary unit tests cannot
# accidentally make live calls. Snapshot the keys at import and re-inject them in
# this explicitly marked real/e2e test.
_PROVIDER_ENV_SNAPSHOT = {
    key: value
    for key, value in os.environ.items()
    if key.endswith("_API_KEY")
    or key
    in (
        "AWS_ACCESS_KEY_ID",
        "AWS_SECRET_ACCESS_KEY",
        "AWS_REGION_NAME",
        "GOOGLE_APPLICATION_CREDENTIALS",
        "GOOGLE_CLOUD_PROJECT",
        "VERTEXAI_LOCATION",
        "VERTEXAI_PROJECT",
        "VERTEX_LOCATION",
        "VERTEX_PROJECT",
    )
}


@pytest.mark.skipif(
    _KEYED_MODEL is None,
    reason="no keyed local LLM model available - skipping live e2e",
)
def test_e2e_story_failure_diagnostics_with_real_llm(
    tmp_path, capsys, monkeypatch
):
    """A real story/prompt mismatch fails and prints actionable diagnostics."""
    monkeypatch.chdir(tmp_path)
    monkeypatch.setenv("PDD_FORCE_LOCAL", "1")
    monkeypatch.setenv("PDD_FORCE", "1")
    monkeypatch.setenv("PDD_MODEL_DEFAULT", _KEYED_MODEL)
    monkeypatch.delenv("PDD_ALLOW_INTERACTIVE", raising=False)
    for key, value in _PROVIDER_ENV_SNAPSHOT.items():
        monkeypatch.setenv(key, value)
    vertex_project = (
        os.environ.get("VERTEXAI_PROJECT")
        or os.environ.get("VERTEX_PROJECT")
        or os.environ.get("GOOGLE_CLOUD_PROJECT")
    )
    if vertex_project:
        monkeypatch.setenv("VERTEXAI_PROJECT", vertex_project)
    if not os.environ.get("VERTEXAI_LOCATION") and not os.environ.get("VERTEX_LOCATION"):
        monkeypatch.setenv("VERTEXAI_LOCATION", "global")
    adc_path = _ADC_PATH_SNAPSHOT
    if adc_path.exists():
        monkeypatch.setenv("GOOGLE_APPLICATION_CREDENTIALS", str(adc_path))
    try:
        google.auth.default(scopes=["https://www.googleapis.com/auth/cloud-platform"])
    except Exception as exc:  # pragma: no cover - environment-dependent e2e guard
        pytest.skip(f"Vertex ADC is not available for live e2e: {exc}")

    prompts_dir = tmp_path / "prompts"
    stories_dir = tmp_path / "user_stories"
    contracts_dir = stories_dir / "contracts"
    prompts_dir.mkdir()
    contracts_dir.mkdir(parents=True)

    prompt_file = prompts_dir / "refund_python.prompt"
    prompt_file.write_text(
        "% Module: customer email notifications\n"
        "Implement an email-notification helper for completed purchases.\n"
        "Requirements:\n"
        "- Send a purchase confirmation email after a successful checkout.\n"
        "- Include the order number and purchased item names.\n"
        "- Do not handle refunds, cancellations, or refund receipts.\n",
        encoding="utf-8",
    )

    story_file = stories_dir / "story__refund_receipts.md"
    story_file.write_text(
        "<!-- pdd-story-prompts: refund_python.prompt -->\n\n"
        "## Story\n\n"
        "As a support agent, I can issue a refund with a required reason code "
        "and automatically send the customer a refund receipt, so that the "
        "customer has a clear record of the refund.\n",
        encoding="utf-8",
    )
    (contracts_dir / "refund_receipts.contract.md").write_text(
        "# Contract: Refund receipts\n\n"
        "## Acceptance Criteria\n\n"
        "- Refunds require a reason code before completion.\n"
        "- Completing a refund sends the customer a refund receipt email.\n\n"
        "## Oracle\n\n"
        "- The linked prompt must explicitly cover refund receipt emails.\n"
        "- The linked prompt must explicitly cover required refund reason codes.\n\n"
        "## Non-Goals\n\n"
        "- This story does not require changing purchase confirmation behavior.\n",
        encoding="utf-8",
    )

    passed, results, cost, model = run_user_story_tests(
        prompts_dir="prompts",
        stories_dir="user_stories",
        strength=_STRENGTH,
        temperature=0.0,
        time=0.25,
        quiet=False,
    )

    captured = capsys.readouterr()
    output = captured.out
    flattened_output = " ".join(output.split()).lower()
    change_text = " ".join(
        str(change.get("change_instructions", ""))
        for result in results
        for change in result.get("changes", [])
        if isinstance(change, dict)
    ).lower()

    assert passed is False
    assert cost > 0
    assert model
    assert len(results) == 1
    assert results[0]["passed"] is False
    assert results[0]["changes"], "live detect_change should explain the mismatch"

    assert "FAIL" in output
    assert "story__refund_receipts.md" in output
    assert "Linked prompts:" in output
    assert "refund_python.prompt" in output
    assert "Missing or stale behavior:" in output
    assert "Next step:" in output
    assert "pdd fix user_stories/story__refund_receipts.md" in output

    combined_explanation = f"{flattened_output} {change_text}"
    assert "refund" in combined_explanation
    assert "receipt" in combined_explanation or "reason code" in combined_explanation
