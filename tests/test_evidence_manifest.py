"""Tests for routine evidence manifest emission."""
from __future__ import annotations

import hashlib
import json
from pathlib import Path

import jsonschema

from pdd.evidence_manifest import write_evidence_manifest


def _hash(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def _schema() -> dict:
    schema_path = Path(__file__).parents[1] / "pdd" / "schemas" / "evidence_manifest.schema.json"
    return json.loads(schema_path.read_text(encoding="utf-8"))


def test_writes_schema_valid_run_and_latest_manifest(tmp_path: Path) -> None:
    """Verify that a valid evidence manifest is written according to the schema."""
    prompt = tmp_path / "prompts" / "refund_python.prompt"
    output = tmp_path / "src" / "refund.py"
    include = tmp_path / "context" / "policy.prompt"
    prompt.parent.mkdir()
    output.parent.mkdir()
    include.parent.mkdir()
    include.write_text("Policy context.\n", encoding="utf-8")
    prompt.write_text("Use ```<context/policy.prompt>```.\n", encoding="utf-8")
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
    expanded = "Use Policy context.\n.\n".encode("utf-8")
    assert manifest["prompt"]["expanded_sha256"] == hashlib.sha256(expanded).hexdigest()
    assert manifest["outputs"] == [{"path": "src/refund.py", "sha256": _hash(output)}]
    assert manifest["contracts"]["status"] == "not_applicable"
    latest = tmp_path / ".pdd" / "evidence" / "devunits" / "refund.latest.json"
    assert json.loads(latest.read_text(encoding="utf-8")) == manifest


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
