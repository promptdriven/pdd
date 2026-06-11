from __future__ import annotations


import sys
from pathlib import Path

# Add project root to sys.path to ensure local code is prioritized
# This allows testing local changes without installing the package
project_root = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(project_root))

import json
from pathlib import Path

import pytest

from pdd.context_snapshot import (
    ContextSnapshotRecorder,
    detect_dynamic_tags,
    redact_snapshot_text,
    replay_snapshot,
    start_snapshot_run,
)


@pytest.fixture
def evidence_root(tmp_path: Path) -> Path:
    root = tmp_path / ".pdd" / "evidence"
    root.mkdir(parents=True, exist_ok=True)
    return root


@pytest.fixture
def prompt_file(tmp_path: Path) -> Path:
    p = tmp_path / "example.prompt"
    p.write_text("hello world", encoding="utf-8")
    return p


def test_detect_dynamic_tags_finds_shell_web_query():
    text = '<shell cmd="ls"></shell> <web url="x"/> <include query="foo" path="y"/>'
    tags = detect_dynamic_tags(text)
    assert set(tags) == {"shell", "web", "query_include"}


def test_detect_dynamic_tags_empty_on_plain_text():
    assert detect_dynamic_tags("just some prompt text") == []


def test_redact_snapshot_text_bearer_and_authorization():
    text = "Authorization: Bearer abc123XYZ456_token\nhello"
    redacted, changed, patterns = redact_snapshot_text(text)
    assert changed
    assert "abc123XYZ456_token" not in redacted
    assert "[REDACTED]" in redacted
    assert any("authorization" in p or "bearer" in p for p in patterns)


def test_redact_snapshot_text_provider_keys():
    text = "key=sk-abcdefghijklmnopqrstuv and AIzaSyAAAAAAAAAAAAAAAAAAAAAAAAAAAA"
    redacted, changed, patterns = redact_snapshot_text(text)
    assert changed
    assert "sk-abcdefghijklmnopqrstuv" not in redacted
    assert "AIzaSy" not in redacted


def test_redact_snapshot_text_no_change():
    redacted, changed, patterns = redact_snapshot_text("nothing secret here")
    assert not changed
    assert patterns == []
    assert redacted == "nothing secret here"


def test_redact_url_userinfo():
    text = "https://user:pass@example.com/path"
    redacted, changed, _ = redact_snapshot_text(text)
    assert changed
    assert "user:pass" not in redacted


def test_start_snapshot_run_creates_unique_run_ids(prompt_file, evidence_root):
    r1 = start_snapshot_run(prompt_file, evidence_root=evidence_root, command="generate")
    r2 = start_snapshot_run(prompt_file, evidence_root=evidence_root, command="generate")
    assert r1.run_id != r2.run_id
    assert r1.run_dir.exists()
    assert r2.run_dir.exists()


def test_start_snapshot_run_default_evidence_root(prompt_file, tmp_path, monkeypatch):
    monkeypatch.chdir(tmp_path)
    rec = start_snapshot_run(prompt_file, command="x")
    assert rec.evidence_root == tmp_path / ".pdd" / "evidence"


def test_finalize_writes_manifest_with_expected_fields(prompt_file, evidence_root):
    rec = start_snapshot_run(prompt_file, evidence_root=evidence_root, command="generate")
    manifest = rec.finalize(
        expanded_prompt="EXPANDED CONTENT",
        prompt_text='<shell cmd="ls"/>raw',
    )
    assert manifest["schema_version"] == 1
    assert manifest["command"] == "generate"
    assert manifest["run_id"] == rec.run_id
    assert manifest["uses_nondeterministic_context"] is False  # only declared, no record_shell call
    assert "shell" in manifest["declared_dynamic_tags"]
    assert manifest["expanded_sha256"]
    assert manifest["prompt_sha256"]
    assert rec.run_artifact.exists()
    # File contains valid JSON
    data = json.loads(rec.run_artifact.read_text())
    assert data["run_id"] == rec.run_id
    assert data["generation"]["grounding_examples"][0]["status"] == "unavailable"


def test_record_shell_sets_dynamic_tag_and_redacts(prompt_file, evidence_root):
    rec = start_snapshot_run(prompt_file, evidence_root=evidence_root)
    rec.record_shell(
        command="curl -H 'Authorization: Bearer sk-supersecretkey1234567890' x",
        stdout="ok",
        stderr="",
        exit_code=0,
    )
    assert "shell" in rec.dynamic_tags
    assert rec.redaction_applied
    manifest = rec.finalize(expanded_prompt="E")
    assert manifest["uses_nondeterministic_context"] is True
    assert "shell" in manifest["dynamic_tags"]
    assert manifest["redaction"]["applied"] is True


def test_record_web_and_include(prompt_file, evidence_root, tmp_path):
    rec = start_snapshot_run(prompt_file, evidence_root=evidence_root)
    rec.record_web(url="https://example.com", content="<html/>", status=200)
    src = tmp_path / "inc.txt"
    src.write_text("included")
    rec.record_include(source_path=src, content="included", include_depth=0)
    rec.record_include(source_path=src, content="ignored", query="find me", output="result", include_depth=2)
    assert "web" in rec.dynamic_tags
    assert "query_include" in rec.dynamic_tags
    manifest = rec.finalize(expanded_prompt="x")
    types = {a["type"] for a in manifest["artifacts"]}
    assert {"web", "include", "query_include", "expanded_prompt"}.issubset(types)


def test_record_include_tolerates_extra_kwargs(prompt_file, evidence_root, tmp_path):
    rec = start_snapshot_run(prompt_file, evidence_root=evidence_root)
    src = tmp_path / "a.txt"
    src.write_text("a")
    # Should not raise on unknown kwargs
    rec.record_include(source_path=src, content="a", include_depth=3, future_kw="x", another=1)


def test_record_grounding_examples(prompt_file, evidence_root):
    rec = start_snapshot_run(prompt_file, evidence_root=evidence_root)
    out = rec.record_grounding_examples([{"id": "ex1", "text": "foo"}])
    assert out == [{"id": "ex1", "text": "foo"}]
    manifest = rec.finalize(expanded_prompt="z")
    assert manifest["generation"]["grounding_examples"][0]["id"] == "ex1"


def test_record_output_hashes(prompt_file, evidence_root, tmp_path):
    rec = start_snapshot_run(prompt_file, evidence_root=evidence_root)
    out = tmp_path / "out.py"
    out.write_text("print('hi')")
    missing = tmp_path / "nope.py"
    records = rec.record_output_hashes([out, missing])
    assert len(records) == 1
    assert records[0]["sha256"]


def test_replay_snapshot_success(prompt_file, evidence_root):
    rec = start_snapshot_run(prompt_file, evidence_root=evidence_root, command="generate")
    expanded = "Hello expanded prompt content"
    rec.finalize(expanded_prompt=expanded, prompt_text="raw")
    result = replay_snapshot(rec.run_artifact)
    assert result["success"] is True
    assert result["verified"] is True
    assert result["expanded_prompt"] == expanded


def test_replay_snapshot_detects_hash_mismatch(prompt_file, evidence_root):
    rec = start_snapshot_run(prompt_file, evidence_root=evidence_root)
    rec.finalize(expanded_prompt="original")
    # Tamper with expanded prompt file
    manifest = json.loads(rec.run_artifact.read_text())
    expanded_rel = manifest["expanded_prompt"]["path"]
    tampered = rec.run_dir / expanded_rel
    tampered.write_text("tampered content")
    with pytest.raises(ValueError, match=r"hash|mismatch"):
        replay_snapshot(rec.run_artifact)


def test_replay_snapshot_unsupported_schema(tmp_path):
    artifact = tmp_path / "bad.json"
    artifact.write_text(json.dumps({"schema_version": 99}))
    with pytest.raises(ValueError, match=r"schema|version|Unsupported"):
        replay_snapshot(artifact)


def test_replay_snapshot_invalid_json(tmp_path):
    artifact = tmp_path / "broken.json"
    artifact.write_text("not json{")
    with pytest.raises(ValueError, match=r"JSON|json"):
        replay_snapshot(artifact)


def test_replay_snapshot_missing_file(tmp_path):
    with pytest.raises((FileNotFoundError, ValueError)):
        replay_snapshot(tmp_path / "nope.json")


def test_replay_snapshot_rejects_path_escape(prompt_file, evidence_root, tmp_path):
    rec = start_snapshot_run(prompt_file, evidence_root=evidence_root)
    rec.finalize(expanded_prompt="abc")
    manifest = json.loads(rec.run_artifact.read_text())
    # Create an outside file and point manifest at it via escaping relative path
    outside = tmp_path / "outside.txt"
    outside.write_text("abc")
    manifest["expanded_prompt"]["path"] = "../../../outside.txt"
    rec.run_artifact.write_text(json.dumps(manifest))
    with pytest.raises(ValueError, match=r"escape|snapshot"):
        replay_snapshot(rec.run_artifact)


def test_hashes_are_deterministic(prompt_file, evidence_root):
    rec1 = start_snapshot_run(prompt_file, evidence_root=evidence_root)
    m1 = rec1.finalize(expanded_prompt="same content")
    rec2 = start_snapshot_run(prompt_file, evidence_root=evidence_root)
    m2 = rec2.finalize(expanded_prompt="same content")
    assert m1["expanded_sha256"] == m2["expanded_sha256"]


import sys
from pathlib import Path

# Add project root to sys.path to ensure local code is prioritized
# This allows testing local changes without installing the package
project_root = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(project_root))

def test_redact_secret_assignment_and_aws_key():
    text = "AWS_SECRET_ACCESS_KEY=AKIAIOSFODNN7EXAMPLE\nMY_TOKEN='abcdefghijklmno'"
    redacted, changed, patterns = redact_snapshot_text(text)
    assert changed
    assert "AKIAIOSFODNN7EXAMPLE" not in redacted
    assert "abcdefghijklmno" not in redacted


def test_redact_environment_variable_value(monkeypatch):
    monkeypatch.setenv("MY_TEST_SECRET_TOKEN", "supersecretvalue12345")
    redacted, changed, patterns = redact_snapshot_text("leaking supersecretvalue12345 here")
    assert changed
    assert "supersecretvalue12345" not in redacted
    assert any(p.startswith("environment:") for p in patterns)


def test_record_grounding_unavailable_explicit(prompt_file, evidence_root):
    rec = start_snapshot_run(prompt_file, evidence_root=evidence_root)
    out = rec.record_grounding_unavailable("no_examples_found")
    assert out[0]["status"] == "unavailable"
    assert out[0]["reason"] == "no_examples_found"
    manifest = rec.finalize(expanded_prompt="x")
    assert manifest["generation"]["grounding_examples"][0]["reason"] == "no_examples_found"


def test_run_artifact_path_layout(prompt_file, evidence_root):
    rec = start_snapshot_run(prompt_file, evidence_root=evidence_root)
    assert rec.run_artifact.parent == evidence_root / "runs"
    assert rec.run_artifact.name == f"{rec.run_id}.json"
    assert rec.run_dir == evidence_root / "runs" / rec.run_id


def test_finalize_records_outputs_and_model(prompt_file, evidence_root, tmp_path):
    rec = start_snapshot_run(prompt_file, evidence_root=evidence_root)
    out = tmp_path / "result.py"
    out.write_text("x=1")
    manifest = rec.finalize(
        expanded_prompt="EX",
        output_files=[out],
        model="gpt-x",
        provider="acme",
        grounding_examples=[{"id": "g1"}],
    )
    assert manifest["generation"]["model"] == "gpt-x"
    assert manifest["generation"]["provider"] == "acme"
    assert manifest["outputs"][0]["sha256"]
    assert manifest["generation"]["grounding_examples"][0]["id"] == "g1"


def test_manifest_json_is_sorted_and_deterministic(prompt_file, evidence_root):
    rec1 = start_snapshot_run(prompt_file, evidence_root=evidence_root)
    rec1.finalize(expanded_prompt="content")
    text1 = rec1.run_artifact.read_text()
    # Sorted keys means "command" appears before "run_id"
    assert text1.index('"command"') < text1.index('"run_id"')


def test_replay_handles_schema_v2_evidence_manifest(prompt_file, evidence_root):
    rec = start_snapshot_run(prompt_file, evidence_root=evidence_root, command="generate")
    inner_manifest = rec.finalize(expanded_prompt="hello v2 world")

    # Build a schema v2 evidence manifest pointing to the v1 snapshot manifest
    v2_path = evidence_root / "runs" / "evidence_v2.json"
    v2_payload = {
        "schema_version": 2,
        "context_snapshot": {
            "enabled": True,
            "manifest_path": rec.run_artifact.name,
            "run_id": rec.run_id,
            "snapshot_dir": rec.run_id,
            "expanded_sha256": inner_manifest["expanded_sha256"],
        },
    }
    v2_path.write_text(json.dumps(v2_payload))
    result = replay_snapshot(v2_path)
    assert result["verified"] is True
    assert result["expanded_prompt"] == "hello v2 world"


def test_replay_missing_expanded_metadata(tmp_path):
    artifact = tmp_path / "m.json"
    artifact.write_text(json.dumps({"schema_version": 1, "run_id": "x"}))
    with pytest.raises(ValueError, match=r"expanded|replay"):
        replay_snapshot(artifact)


def test_record_include_with_nonexistent_source(prompt_file, evidence_root, tmp_path):
    rec = start_snapshot_run(prompt_file, evidence_root=evidence_root)
    missing = tmp_path / "ghost.txt"
    record = rec.record_include(source_path=missing, content="payload")
    assert record["type"] == "include"
    assert "source_sha256" not in record["metadata"]


def test_record_shell_redacts_command_secrets(prompt_file, evidence_root):
    rec = start_snapshot_run(prompt_file, evidence_root=evidence_root)
    record = rec.record_shell(
        command="curl https://user:pass@api.example.com/x",
        stdout="ok",
    )
    assert record["redaction_applied"] is True
    assert "user:pass" not in record["metadata"]["command"]


def test_record_web_redacts_url(prompt_file, evidence_root):
    rec = start_snapshot_run(prompt_file, evidence_root=evidence_root)
    record = rec.record_web(url="https://user:secret@example.com", content="<html/>")
    assert record["redaction_applied"] is True
    assert "user:secret" not in record["metadata"]["url"]


def test_finalize_no_dynamic_content_marks_deterministic(prompt_file, evidence_root):
    rec = start_snapshot_run(prompt_file, evidence_root=evidence_root)
    manifest = rec.finalize(expanded_prompt="plain", prompt_text="no tags here")
    assert manifest["uses_nondeterministic_context"] is False
    assert manifest["dynamic_tags"] == []
    assert manifest["redaction"]["raw_environment_persisted"] is False
    assert manifest["redaction"]["pre_redaction_hashes_persisted"] is False