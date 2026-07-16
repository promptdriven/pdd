"""Invariant tests for the public story-detection result contract."""

import json
from pathlib import Path
import jsonschema

from pdd.story_detection_result import (
    _normalize_changes,
    _redact_message,
    build_story_detection_document,
    failure_document,
    render_json,
)
from pdd.evidence_manifest import write_evidence_manifest


def _scope(tmp_path: Path, *, contract: bool = True):
    stories = tmp_path / "stories"
    prompts = tmp_path / "prompts"
    stories.mkdir()
    prompts.mkdir()
    story = stories / "story__payment.md"
    story.write_text(
        "<!-- pdd-story-prompts: prompts/payment.prompt -->\n## Story", encoding="utf-8"
    )
    (prompts / "payment.prompt").write_text("prompt", encoding="utf-8")
    if contract:
        (stories / "contracts").mkdir()
        (stories / "contracts" / "payment.contract.md").write_text(
            "## Oracle", encoding="utf-8"
        )
    return stories, prompts, story


def _document(
    tmp_path: Path, story: Path, stories: Path, prompts: Path, rows, passed=True
):
    return build_story_detection_document(
        story_files=[story],
        raw_results=rows,
        passed=passed,
        total_cost=0.0,
        model="model",
        project_root=tmp_path,
        stories_dir=stories,
        prompts_dir=prompts,
        include_llm=False,
        fail_fast=False,
        read_only=True,
    )


def test_missing_contract_must_not_be_reported_pass(tmp_path):
    stories, prompts, story = _scope(tmp_path, contract=False)
    payload = _document(
        tmp_path, story, stories, prompts, [{"story": str(story), "passed": True}]
    )
    assert payload["all_pass"] is False
    assert payload["results"][0]["verdict"] == "UNKNOWN"
    assert payload["results"][0]["errors"][0]["code"] == "story:MISSING_CONTRACT"
    assert payload["errors"][0]["code"] == "story:MISSING_CONTRACT"


def test_duplicate_verdict_must_be_unknown(tmp_path):
    stories, prompts, story = _scope(tmp_path)
    rows = [
        {"story": str(story), "passed": True},
        {"story": str(story), "passed": True},
    ]
    payload = _document(tmp_path, story, stories, prompts, rows)
    assert payload["outcome"] == "INCOMPLETE"
    assert payload["results"][0]["verdict"] == "UNKNOWN"
    assert payload["results"][0]["errors"][0]["code"] == "detector:CONFLICTING_VERDICT"


def test_missing_row_must_be_unknown_even_when_legacy_aggregate_passes(tmp_path):
    stories, prompts, story = _scope(tmp_path)
    payload = _document(tmp_path, story, stories, prompts, [], passed=True)
    assert payload["all_pass"] is False
    assert payload["results"][0]["verdict"] == "UNKNOWN"


def test_json_serializer_is_deterministic_and_has_no_ansi(tmp_path):
    stories, prompts, story = _scope(tmp_path)
    payload = _document(
        tmp_path,
        story,
        stories,
        prompts,
        [{"story": str(story), "passed": False, "changes": ["fix"]}],
        passed=False,
    )
    encoded = render_json(payload)
    assert json.loads(encoded)["results"][0]["changes"] == [{"instruction": "fix"}]
    assert "\x1b[" not in encoded


def test_llm_link_requires_explicit_include_flag(tmp_path: Path):
    stories, prompts, story = _scope(tmp_path)
    llm = prompts / "secret_llm.prompt"
    llm.write_text("llm", encoding="utf-8")
    story.write_text(
        "<!-- pdd-story-prompts: prompts/secret_llm.prompt -->\n## Story",
        encoding="utf-8",
    )
    without_include = _document(
        tmp_path,
        story,
        stories,
        prompts,
        [{"story": str(story), "passed": True}],
    )
    assert without_include["results"][0]["verdict"] == "UNKNOWN"
    assert without_include["errors"][0]["code"] == "prompt:LLM_EXCLUDED"

    with_include = build_story_detection_document(
        story_files=[story],
        raw_results=[{"story": str(story), "passed": True}],
        passed=True,
        total_cost=0.0,
        model="model",
        project_root=tmp_path,
        stories_dir=stories,
        prompts_dir=prompts,
        include_llm=True,
        fail_fast=True,
        read_only=True,
    )
    assert with_include["results"][0]["verdict"] == "PASS"


def test_provider_diagnostic_is_redacted_and_aggregated(tmp_path: Path):
    stories, prompts, story = _scope(tmp_path)
    payload = _document(
        tmp_path,
        story,
        stories,
        prompts,
        [
            {
                "story": str(story),
                "passed": False,
                "errors": [
                    {
                        "code": "provider:UNAVAILABLE",
                        "severity": "error",
                        "message": "api_key=sk-secret-value /Users/secret/project",
                    }
                ],
            }
        ],
        passed=False,
    )
    rendered = render_json(payload)
    assert payload["outcome"] == "INCOMPLETE"
    assert payload["errors"][0]["code"] == "provider:UNAVAILABLE"
    assert "sk-secret-value" not in rendered
    assert "/Users/secret/project" not in rendered


def test_quoted_json_credentials_are_redacted() -> None:
    """Quoted and nested provider payloads cannot leak credential values."""
    messages = (
        '{"api_key": "sk-json-secret"}',
        '{ "apiKey" : "sk-camel-secret", "nested": {"password": "pw-secret"} }',
        '{"Authorization": "Bearer bearer-secret", "token": "token-secret"}',
        "Authorization: Bearer header-secret",
    )
    for message in messages:
        redacted = _redact_message(message)
        assert all(
            secret not in redacted for secret in message.split() if "secret" in secret
        )
        assert "[REDACTED]" in redacted


def test_nested_structured_changes_redact_credential_keys() -> None:
    """Credential-shaped keys are redacted recursively in change payloads."""
    normalized = _normalize_changes(
        {
            "changes": [
                {
                    "api_key": "sk-structured-secret",
                    "apiKey": "sk-camel-secret",
                    "PASSWORD": "password-secret",
                    "token": "token-secret",
                    "secret": "secret-value",
                    "client_secret": "client-secret-value",
                    "Authorization": "Bearer auth-secret",
                    "nested": {
                        "access-token": "access-secret",
                        "items": [{"password": "nested-password-secret"}],
                    },
                }
            ]
        }
    )
    rendered = json.dumps(normalized)
    assert all(
        secret not in rendered
        for secret in (
            "sk-structured-secret",
            "sk-camel-secret",
            "password-secret",
            "token-secret",
            "secret-value",
            "client-secret-value",
            "auth-secret",
            "access-secret",
            "nested-password-secret",
        )
    )
    assert rendered.count("[REDACTED]") == 9


def test_failure_document_redacts_provider_payloads() -> None:
    """Top-level infrastructure documents must apply the same redaction boundary."""
    payload = failure_document(
        outcome="INFRASTRUCTURE_ERROR",
        code="provider:ERROR",
        message='provider response {"apiKey": "failure-secret", "password": "pw-secret"}',
        retryable=False,
    )
    rendered = render_json(payload)
    assert "failure-secret" not in rendered
    assert "pw-secret" not in rendered
    assert payload["errors"][0]["message"].count("[REDACTED]") == 2


def test_contract_symlink_escape_is_not_a_valid_contract(tmp_path: Path):
    stories, prompts, story = _scope(tmp_path)
    contract = stories / "contracts" / "payment.contract.md"
    outside = tmp_path / "outside.contract.md"
    outside.write_text("## Oracle", encoding="utf-8")
    contract.unlink()
    contract.symlink_to(outside)
    payload = _document(
        tmp_path, story, stories, prompts, [{"story": str(story), "passed": True}]
    )
    assert payload["all_pass"] is False
    assert payload["results"][0]["verdict"] == "UNKNOWN"
    assert payload["results"][0]["contract"] is None
    assert payload["errors"][0]["code"] == "story:INVALID_CONTRACT"


def test_link_metadata_and_changes_do_not_leak_external_paths_or_secrets(
    tmp_path: Path,
):
    stories, prompts, story = _scope(tmp_path)
    story.write_text(
        "<!-- pdd-story-prompts: /Users/private/secret.prompt, ../outside.prompt -->\n## Story",
        encoding="utf-8",
    )
    payload = _document(
        tmp_path,
        story,
        stories,
        prompts,
        [
            {
                "story": str(story),
                "passed": False,
                "changes": [
                    {
                        "prompt_name": "/Users/private/secret.prompt",
                        "change_instructions": "token=super-secret /tmp/private/file",
                    }
                ],
            }
        ],
        passed=False,
    )
    rendered = render_json(payload)
    assert all("/" not in value for value in payload["results"][0]["linked_prompts"])
    assert "super-secret" not in rendered
    assert "/Users/private" not in rendered
    assert "/tmp/private" not in rendered


def test_malformed_aggregate_provenance_is_schema_valid_and_fail_closed(
    tmp_path: Path,
):
    stories, prompts, story = _scope(tmp_path)
    payload = build_story_detection_document(
        story_files=[story],
        raw_results=["not-a-row"],  # type: ignore[list-item]
        passed="yes",  # type: ignore[arg-type]
        total_cost="not-a-cost",  # type: ignore[arg-type]
        model={"secret": "value"},  # type: ignore[arg-type]
        project_root=tmp_path,
        stories_dir=stories,
        prompts_dir=prompts,
        include_llm=False,
        fail_fast=False,
        read_only=True,
    )
    assert payload["all_pass"] is False
    assert payload["results"][0]["verdict"] == "UNKNOWN"
    assert payload["usage"]["cost_usd"] is None
    assert payload["usage"]["model"] == ""
    assert {item["code"] for item in payload["errors"]} >= {
        "detector:MALFORMED_RESULT",
        "billing:UNAVAILABLE",
        "provenance:INVALID_MODEL",
    }
    schema_path = (
        Path(__file__).parents[1]
        / "pdd"
        / "schemas"
        / "story_detection_result.schema.json"
    )
    jsonschema.Draft202012Validator(
        json.loads(schema_path.read_text(encoding="utf-8"))
    ).validate(payload)


def test_unreadable_story_is_schema_valid_unknown(tmp_path: Path):
    stories, prompts, story = _scope(tmp_path)
    story.write_bytes(b"## Story\n\xff\xfe")
    payload = _document(
        tmp_path,
        story,
        stories,
        prompts,
        [{"story": str(story), "passed": True}],
    )
    assert payload["all_pass"] is False
    assert payload["results"][0]["verdict"] == "UNKNOWN"
    assert payload["results"][0]["errors"][0]["code"] == "story:UNREADABLE"
    schema_path = (
        Path(__file__).parents[1]
        / "pdd"
        / "schemas"
        / "story_detection_result.schema.json"
    )
    jsonschema.Draft202012Validator(
        json.loads(schema_path.read_text(encoding="utf-8"))
    ).validate(payload)


def test_nonfinite_story_cost_is_unknown_and_redacted(tmp_path: Path):
    stories, prompts, story = _scope(tmp_path)
    payload = _document(
        tmp_path,
        story,
        stories,
        prompts,
        [{"story": str(story), "passed": True, "cost_usd": "NaN"}],
    )
    assert payload["all_pass"] is False
    assert payload["results"][0]["verdict"] == "UNKNOWN"
    assert payload["results"][0]["cost_usd"] is None
    assert payload["results"][0]["errors"][0]["code"] == "billing:INVALID_STORY_COST"


def test_empty_model_and_negative_cost_fail_closed(tmp_path: Path):
    stories, prompts, story = _scope(tmp_path)
    payload = build_story_detection_document(
        story_files=[story],
        raw_results=[
            {
                "story": str(story),
                "passed": True,
                "changes": [],
            }
        ],
        passed=True,
        total_cost=-0.1,
        model="   ",
        project_root=tmp_path,
        stories_dir=stories,
        prompts_dir=prompts,
        include_llm=False,
        fail_fast=False,
        read_only=True,
    )
    assert payload["all_pass"] is False
    assert payload["outcome"] == "INCOMPLETE"
    assert {item["code"] for item in payload["errors"]} >= {
        "provenance:INVALID_MODEL",
        "billing:UNAVAILABLE",
    }


def test_changes_are_json_safe_for_nested_non_json_values(tmp_path: Path):
    stories, prompts, story = _scope(tmp_path)
    payload = _document(
        tmp_path,
        story,
        stories,
        prompts,
        [
            {
                "story": str(story),
                "passed": False,
                "changes": [{"metadata": {"opaque": {"token=secret", 3}}}],
            }
        ],
        passed=False,
    )
    rendered = render_json(payload)
    assert "token=secret" not in rendered
    assert '"changes"' in rendered


def test_document_matches_published_v1_schema(tmp_path):
    stories, prompts, story = _scope(tmp_path)
    payload = _document(
        tmp_path,
        story,
        stories,
        prompts,
        [{"story": str(story), "passed": True, "changes": []}],
    )
    schema_path = (
        Path(__file__).parents[1]
        / "pdd"
        / "schemas"
        / "story_detection_result.schema.json"
    )
    jsonschema.Draft202012Validator(
        json.loads(schema_path.read_text(encoding="utf-8"))
    ).validate(payload)


def test_evidence_embeds_same_structured_result_without_recalculation(tmp_path):
    stories, prompts, story = _scope(tmp_path)
    payload = _document(
        tmp_path,
        story,
        stories,
        prompts,
        [{"story": str(story), "passed": False, "changes": [{"instruction": "fix"}]}],
        passed=False,
    )
    evidence_path = write_evidence_manifest(
        command="pdd detect --stories",
        basename="stories",
        project_root=tmp_path,
        validation={"detect_stories": "failed"},
        story_detection=payload,
    )
    evidence = json.loads(evidence_path.read_text(encoding="utf-8"))
    assert evidence["story_detection"] == payload
    schema_path = (
        Path(__file__).parents[1] / "pdd" / "schemas" / "evidence_manifest.schema.json"
    )
    jsonschema.Draft202012Validator(
        json.loads(schema_path.read_text(encoding="utf-8"))
    ).validate(evidence)
