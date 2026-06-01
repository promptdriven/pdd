"""Tests for routine evidence manifest emission."""
from __future__ import annotations

import hashlib
import json
import os
from pathlib import Path

import jsonschema
import pytest

from pdd.evidence_manifest import (
    SCHEMA_VERSION,
    _preprocessed_expanded_sha256,
    grounding_kwargs_from_ctx,
    validation_from_sync,
    write_evidence_manifest,
)
from pdd.preprocess import preprocess


def _hash(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def _schema() -> dict:
    schema_path = Path(__file__).parents[1] / "pdd" / "schemas" / "evidence_manifest.schema.json"
    return json.loads(schema_path.read_text(encoding="utf-8"))


def _expected_preprocessed_hash(prompt_text: str, project_root: Path) -> str:
    previous = os.getcwd()
    os.chdir(project_root)
    try:
        expanded = preprocess(prompt_text, recursive=True, double_curly_brackets=False)
    finally:
        os.chdir(previous)
    return hashlib.sha256(expanded.encode("utf-8")).hexdigest()


def test_writes_schema_valid_run_and_latest_manifest(tmp_path: Path) -> None:
    """Verify that a valid evidence manifest is written according to the schema."""
    prompt = tmp_path / "prompts" / "refund_python.prompt"
    output = tmp_path / "src" / "refund.py"
    include = tmp_path / "context" / "policy.prompt"
    prompt.parent.mkdir()
    output.parent.mkdir()
    include.parent.mkdir()
    include.write_text("Policy context.\n", encoding="utf-8")
    prompt_text = "Use ```<context/policy.prompt>```.\n"
    prompt.write_text(prompt_text, encoding="utf-8")
    output.write_text("def refund():\n    return True\n", encoding="utf-8")

    manifest_path = write_evidence_manifest(
        command="pdd generate",
        prompt_file=prompt,
        output_files=[output],
        model="local-model",
        cost_usd=0.25,
        temperature=0.0,
        project_root=tmp_path,
    )
    manifest = json.loads(manifest_path.read_text(encoding="utf-8"))

    jsonschema.validate(instance=manifest, schema=_schema())
    assert manifest["prompt"]["sha256"] == _hash(prompt)
    assert manifest["context"]["includes"] == [
        {"path": "context/policy.prompt", "sha256": _hash(include)}
    ]
    assert manifest["prompt"]["expanded_sha256"] == _expected_preprocessed_hash(
        prompt_text, tmp_path
    )
    assert manifest["outputs"] == [{"path": "src/refund.py", "sha256": _hash(output)}]
    assert manifest["contracts"]["status"] == "not_applicable"
    assert manifest["schema_version"] == SCHEMA_VERSION == 2
    grounding = manifest["generation"]["grounding"]
    assert grounding["mode"] == "unavailable"
    assert grounding["selected_examples"] == []
    assert grounding["reviewed"] is False
    assert manifest["generation"]["grounding_examples"] == []
    latest = tmp_path / ".pdd" / "evidence" / "devunits" / "refund.latest.json"
    assert json.loads(latest.read_text(encoding="utf-8")) == manifest


def test_write_evidence_manifest_serializes_cloud_grounding(tmp_path: Path) -> None:
    prompt = tmp_path / "prompts" / "payments_python.prompt"
    prompt.parent.mkdir()
    prompt.write_text("Generate payments.\n", encoding="utf-8")

    grounding = {
        "mode": "cloud",
        "selected_examples": [
            {
                "module": "payments",
                "prompt_sha256": "abc123",
                "similarity": 0.9,
                "source": "cloud-history",
            }
        ],
        "pinned": ["payments"],
        "excluded": ["legacy_payments"],
        "reviewed": True,
    }
    manifest_path = write_evidence_manifest(
        command="pdd generate",
        prompt_file=prompt,
        project_root=tmp_path,
        grounding=grounding,
        reviewed=True,
    )
    manifest = json.loads(manifest_path.read_text(encoding="utf-8"))
    jsonschema.validate(instance=manifest, schema=_schema())
    assert manifest["generation"]["grounding"] == grounding
    assert manifest["generation"]["grounding_examples"] == grounding["selected_examples"]


def test_grounding_kwargs_from_ctx_merges_review_decisions() -> None:
    kwargs = grounding_kwargs_from_ctx(
        {
            "review_examples": True,
            "last_grounding": {
                "mode": "cloud",
                "selected_examples": [{"module": "auth"}],
                "pinned": ["auth"],
                "excluded": [],
            },
            "grounding_review_decisions": [
                {"module": "auth", "decision": "accept", "phase": "pre"}
            ],
        }
    )
    assert kwargs["reviewed"] is True
    assert kwargs["grounding"]["mode"] == "cloud"


def test_output_hash_changes_with_output_content(tmp_path: Path) -> None:
    """Assert output hashes change dynamically when the file contents are updated."""
    prompt = tmp_path / "prompts" / "receipt_python.prompt"
    output = tmp_path / "receipt.py"
    prompt.parent.mkdir()
    prompt.write_text("Write a receipt.\n", encoding="utf-8")
    output.write_text("first\n", encoding="utf-8")
    first_path = write_evidence_manifest(
        command="pdd generate",
        prompt_file=prompt,
        output_files=[output],
        project_root=tmp_path,
    )
    first = json.loads(first_path.read_text(encoding="utf-8"))

    output.write_text("second\n", encoding="utf-8")
    second_path = write_evidence_manifest(
        command="pdd generate",
        prompt_file=prompt,
        output_files=[output],
        project_root=tmp_path,
    )
    second = json.loads(second_path.read_text(encoding="utf-8"))

    assert first["outputs"][0]["sha256"] != second["outputs"][0]["sha256"]


def test_nested_include_records_and_expanded_hash(tmp_path: Path) -> None:
    """Nested includes resolve beside the parent file and appear in context.includes."""
    nested = tmp_path / "context" / "nested.prompt"
    middle = tmp_path / "context" / "a.prompt"
    prompt = tmp_path / "prompts" / "main_python.prompt"
    nested.parent.mkdir(parents=True)
    prompt.parent.mkdir()
    nested.write_text("nested line\n", encoding="utf-8")
    middle.write_text("middle ```<nested.prompt>```\n", encoding="utf-8")
    prompt_text = "top ```<context/a.prompt>```\n"
    prompt.write_text(prompt_text, encoding="utf-8")

    manifest_path = write_evidence_manifest(
        command="pdd generate",
        prompt_file=prompt,
        project_root=tmp_path,
    )
    manifest = json.loads(manifest_path.read_text(encoding="utf-8"))

    include_paths = {record["path"] for record in manifest["context"]["includes"]}
    assert "context/a.prompt" in include_paths
    assert "context/nested.prompt" in include_paths
    assert manifest["prompt"]["expanded_sha256"] == _expected_preprocessed_hash(
        prompt_text, tmp_path
    )
    assert len(manifest["context"]["includes"]) == 2


def test_path_attribute_include_records_primary_path(tmp_path: Path) -> None:
    """Attributed includes must record the path= target, not the body fallback."""
    source = tmp_path / "docs" / "source.md"
    fallback = tmp_path / "fallback.md"
    prompt = tmp_path / "prompts" / "attr_python.prompt"
    source.parent.mkdir(parents=True)
    prompt.parent.mkdir()
    source.write_text("primary body\n", encoding="utf-8")
    fallback.write_text("fallback body\n", encoding="utf-8")
    prompt.write_text(
        '<include path="docs/source.md">fallback.md</include>\n',
        encoding="utf-8",
    )

    manifest_path = write_evidence_manifest(
        command="pdd generate",
        prompt_file=prompt,
        project_root=tmp_path,
    )
    manifest = json.loads(manifest_path.read_text(encoding="utf-8"))
    include_paths = {record["path"] for record in manifest["context"]["includes"]}
    assert "docs/source.md" in include_paths
    assert "fallback.md" not in include_paths


def test_self_closing_include_is_recorded(tmp_path: Path) -> None:
    prompt = tmp_path / "prompts" / "self_close_python.prompt"
    include = tmp_path / "context" / "note.prompt"
    prompt.parent.mkdir()
    include.parent.mkdir(parents=True)
    include.write_text("note body\n", encoding="utf-8")
    prompt.write_text('<include path="context/note.prompt" />\n', encoding="utf-8")

    manifest_path = write_evidence_manifest(
        command="pdd generate",
        prompt_file=prompt,
        project_root=tmp_path,
    )
    manifest = json.loads(manifest_path.read_text(encoding="utf-8"))
    include_paths = {record["path"] for record in manifest["context"]["includes"]}
    assert "context/note.prompt" in include_paths


def test_include_inside_code_fence_is_not_recorded(tmp_path: Path) -> None:
    secret = tmp_path / "secrets" / "secret.prompt"
    prompt = tmp_path / "prompts" / "fenced_python.prompt"
    secret.parent.mkdir(parents=True)
    prompt.parent.mkdir()
    secret.write_text("secret\n", encoding="utf-8")
    prompt.write_text("```xml\n<include>secret.prompt</include>\n```\n", encoding="utf-8")

    manifest_path = write_evidence_manifest(
        command="pdd generate",
        prompt_file=prompt,
        project_root=tmp_path,
    )
    manifest = json.loads(manifest_path.read_text(encoding="utf-8"))
    include_paths = {record["path"] for record in manifest["context"]["includes"]}
    assert "secret.prompt" not in include_paths


def test_validation_from_sync_maps_completed_operations() -> None:
    """Sync evidence must reflect operations that actually ran."""
    validation = validation_from_sync(
        {
            "overall_success": True,
            "results_by_language": {
                "python": {
                    "success": True,
                    "operations_completed": ["test", "crash", "verify"],
                }
            },
        },
        skip_tests=False,
        skip_verify=False,
    )
    assert validation["unit_tests"] == "passed"
    assert validation["verify"] == "passed"
    assert validation["detect_stories"] == "not_applicable"


def test_validation_from_sync_dry_run_stays_not_available() -> None:
    validation = validation_from_sync(
        {
            "overall_success": True,
            "results_by_language": {
                "python": {"success": True, "operations_completed": ["verify"]},
            },
        },
        skip_tests=False,
        skip_verify=False,
        dry_run=True,
    )
    assert validation["unit_tests"] == "not_available"
    assert validation["verify"] == "not_available"


def test_dynamic_prompt_records_expansion_as_unavailable(tmp_path: Path) -> None:
    """Check that dynamic prompts with non-deterministic tags are flagged correctly."""
    prompt = tmp_path / "prompts" / "dynamic_python.prompt"
    prompt.parent.mkdir()
    prompt.write_text("<shell>date</shell>\n", encoding="utf-8")

    manifest_path = write_evidence_manifest(
        command="pdd generate",
        prompt_file=prompt,
        project_root=tmp_path,
    )
    manifest = json.loads(manifest_path.read_text(encoding="utf-8"))

    assert manifest["prompt"]["uses_nondeterministic_tags"] is True
    assert manifest["prompt"]["expanded_sha256"] is None


def test_preprocessed_expanded_hash_matches_preprocess_helper(tmp_path: Path) -> None:
    prompt = tmp_path / "prompts" / "hash_python.prompt"
    include = tmp_path / "context" / "body.prompt"
    prompt.parent.mkdir()
    include.parent.mkdir(parents=True)
    include.write_text("included\n", encoding="utf-8")
    prompt_text = "prefix ```<context/body.prompt>``` suffix\n"
    prompt.write_text(prompt_text, encoding="utf-8")

    assert _preprocessed_expanded_sha256(
        prompt_text, tmp_path
    ) == _expected_preprocessed_hash(prompt_text, tmp_path)


def test_resolve_generate_output_paths_uses_construct_paths(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    prompt = tmp_path / "prompts" / "widget_python.prompt"
    prompt.parent.mkdir()
    prompt.write_text("Generate widget.\n", encoding="utf-8")

    def fake_construct_paths(**_kwargs):  # type: ignore[no-untyped-def]
        return {}, {}, {"output": str(tmp_path / "pdd" / "widget.py")}, "python"

    monkeypatch.setattr("pdd.construct_paths.construct_paths", fake_construct_paths)
    from pdd.evidence_manifest import resolve_generate_output_paths

    resolved = resolve_generate_output_paths(prompt, quiet=True)
    assert resolved == [str(tmp_path / "pdd" / "widget.py")]
