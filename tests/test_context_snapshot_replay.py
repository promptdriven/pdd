import json
from pathlib import Path

import click
import pytest
from click.testing import CliRunner

from pdd.commands.replay import replay
from pdd.context_snapshot import replay_snapshot, start_snapshot_run
from pdd.preprocess import preprocess
from pdd.preprocess_main import preprocess_main


def test_preprocess_snapshot_records_dynamic_outputs(tmp_path, monkeypatch):
    monkeypatch.chdir(tmp_path)
    include_path = tmp_path / "context.txt"
    include_path.write_text("included text\n", encoding="utf-8")

    recorder = start_snapshot_run("prompt.prompt", evidence_root=tmp_path / ".pdd" / "evidence")
    raw_prompt = (
        f"<include>{include_path}</include>\n"
        "<shell>printf shell-output</shell>\n"
        "<web>https://example.test/doc</web>\n"
    )
    recorder.record_prompt_source(raw_prompt)
    monkeypatch.setattr(
        "pdd.preprocess.get_firecrawl_cache",
        lambda: type(
            "Cache",
            (),
            {
                "get": lambda self, url: "web-output\n",
                "set": lambda self, url, content: None,
            },
        )(),
    )

    expanded = preprocess(raw_prompt, recursive=False, snapshot_recorder=recorder)
    manifest = recorder.finalize(expanded_prompt=expanded, prompt_text=raw_prompt)

    artifact_types = {artifact["type"] for artifact in manifest["artifacts"]}
    assert {"include", "shell", "web", "expanded_prompt"} <= artifact_types
    assert manifest["uses_nondeterministic_context"] is True
    assert manifest["dynamic_tags"] == ["shell", "web"]
    assert "shell-output" in expanded
    assert "web-output" in expanded


def test_snapshot_manifest_paths_are_relative_when_under_project_root(tmp_path, monkeypatch):
    monkeypatch.chdir(tmp_path)
    prompt_path = tmp_path / "prompts" / "demo.prompt"
    prompt_path.parent.mkdir()
    prompt_path.write_text("static prompt", encoding="utf-8")
    include_path = tmp_path / "context.txt"
    include_path.write_text("included", encoding="utf-8")
    output_path = tmp_path / "pdd" / "demo.py"
    output_path.parent.mkdir()
    output_path.write_text("print('ok')\n", encoding="utf-8")

    recorder = start_snapshot_run(prompt_path, evidence_root=tmp_path / ".pdd" / "evidence")
    recorder.record_include(source_path=include_path, content="included")
    manifest = recorder.finalize(
        expanded_prompt="expanded",
        prompt_text=prompt_path.read_text(encoding="utf-8"),
        output_files=[output_path],
    )

    assert manifest["prompt_path"] == "prompts/demo.prompt"
    assert manifest["manifest_path"].startswith("runs/")
    assert manifest["snapshot_dir"].startswith("runs/")
    assert manifest["expanded_prompt"]["path"] == "expanded_prompt.txt"
    assert manifest["artifacts"][0]["metadata"]["source_path"] == "context.txt"
    assert manifest["outputs"][0]["path"] == "pdd/demo.py"
    assert not any(str(tmp_path) in json.dumps(value) for value in manifest.values())


def test_declared_dynamic_tags_do_not_mark_unexecuted_context(tmp_path, monkeypatch):
    monkeypatch.chdir(tmp_path)
    raw_prompt = "Example only:\n```text\n<shell>printf nope</shell>\n```\n"
    recorder = start_snapshot_run("prompt.prompt", evidence_root=tmp_path / ".pdd" / "evidence")

    manifest = recorder.finalize(expanded_prompt=raw_prompt, prompt_text=raw_prompt)

    assert manifest["declared_dynamic_tags"] == ["shell"]
    assert manifest["dynamic_tags"] == []
    assert manifest["uses_nondeterministic_context"] is False


def test_snapshot_run_ids_do_not_overwrite(tmp_path):
    first = start_snapshot_run("prompt.prompt", evidence_root=tmp_path / ".pdd" / "evidence")
    second = start_snapshot_run("prompt.prompt", evidence_root=tmp_path / ".pdd" / "evidence")

    assert first.run_id != second.run_id
    first.finalize(expanded_prompt="one", prompt_text="one")
    second.finalize(expanded_prompt="two", prompt_text="two")
    assert first.run_artifact.exists()
    assert second.run_artifact.exists()


def test_recursive_preprocess_snapshot_records_resolved_includes(tmp_path, monkeypatch):
    monkeypatch.chdir(tmp_path)
    include_path = tmp_path / "context.txt"
    include_path.write_text("included text\n", encoding="utf-8")
    recorder = start_snapshot_run("prompt.prompt", evidence_root=tmp_path / ".pdd" / "evidence")

    expanded = preprocess(
        f"<include>{include_path}</include>",
        recursive=True,
        double_curly_brackets=False,
        snapshot_recorder=recorder,
    )
    manifest = recorder.finalize(expanded_prompt=expanded, prompt_text=f"<include>{include_path}</include>")

    assert expanded == "included text\n"
    assert any(artifact["type"] == "include" for artifact in manifest["artifacts"])


def test_replay_rejects_unsupported_schema_version(tmp_path):
    recorder = start_snapshot_run("prompt.prompt", evidence_root=tmp_path / ".pdd" / "evidence")
    manifest = recorder.finalize(expanded_prompt="expanded", prompt_text="raw")
    manifest_path = recorder.run_artifact
    payload = json.loads(manifest_path.read_text(encoding="utf-8"))
    payload["schema_version"] = 999
    manifest_path.write_text(json.dumps(payload), encoding="utf-8")

    try:
        replay_snapshot(manifest_path)
    except ValueError as exc:
        assert "Unsupported snapshot schema_version" in str(exc)
    else:
        raise AssertionError("Expected unsupported schema version to fail")


def test_replay_rejects_expanded_prompt_path_outside_run_dir(tmp_path):
    evidence_root = tmp_path / ".pdd" / "evidence"
    recorder = start_snapshot_run("prompt.prompt", evidence_root=evidence_root)
    manifest = recorder.finalize(expanded_prompt="expanded", prompt_text="raw")
    manifest_path = recorder.run_artifact
    sibling_dir = evidence_root / "devunits"
    sibling_dir.mkdir(parents=True)
    escaped_path = sibling_dir / "expanded_prompt.txt"
    escaped_path.write_text("expanded", encoding="utf-8")

    payload = json.loads(manifest_path.read_text(encoding="utf-8"))
    payload["expanded_prompt"]["path"] = "../devunits/expanded_prompt.txt"
    manifest_path.write_text(json.dumps(payload), encoding="utf-8")

    try:
        replay_snapshot(manifest_path)
    except ValueError as exc:
        assert "escapes snapshot directory" in str(exc)
    else:
        raise AssertionError("Expected replay to reject escaped artifact path")


def test_replay_verify_only_does_not_write_output(tmp_path):
    recorder = start_snapshot_run("prompt.prompt", evidence_root=tmp_path / ".pdd" / "evidence")
    manifest = recorder.finalize(expanded_prompt="expanded", prompt_text="raw")
    output_path = tmp_path / "replayed.prompt"

    result = CliRunner().invoke(
        replay,
        [str(recorder.run_artifact), "--verify-only", "--output", str(output_path), "--json"],
        obj={"quiet": True},
    )

    assert result.exit_code == 0, result.output
    assert not output_path.exists()
    payload = json.loads(result.output)
    assert payload["success"] is True
    assert payload["output_skipped"] == "verify_only"


def test_query_include_snapshot_recorded(tmp_path, monkeypatch):
    monkeypatch.chdir(tmp_path)
    source = tmp_path / "module.py"
    source.write_text("def helper():\n    return 1\n", encoding="utf-8")
    recorder = start_snapshot_run("prompt.prompt", evidence_root=tmp_path / ".pdd" / "evidence")
    raw_prompt = '<include query="return value">module.py</include>\n'

    class _FakeExtractor:
        def extract(self, *, file_path, query):  # type: ignore[no-untyped-def]
            return "extracted helper output"

    monkeypatch.setattr(
        "pdd.include_query_extractor.IncludeQueryExtractor",
        _FakeExtractor,
    )
    expanded = preprocess(raw_prompt, recursive=False, snapshot_recorder=recorder)
    manifest = recorder.finalize(expanded_prompt=expanded, prompt_text=raw_prompt)

    assert "extracted helper output" in expanded
    assert any(artifact["type"] == "query_include" for artifact in manifest["artifacts"])
    assert "query_include" in manifest["declared_dynamic_tags"]


def test_preprocess_rejects_snapshot_with_recursive_dynamic_tags(tmp_path: Path) -> None:
    prompt = tmp_path / "dynamic_python.prompt"
    prompt.write_text("<shell>printf x</shell>\n", encoding="utf-8")
    (tmp_path / "pdd").mkdir()
    ctx = click.Context(click.Command("preprocess"))
    ctx.obj = {"quiet": True, "force": False}

    with pytest.raises(click.UsageError, match="cannot be combined with --recursive"):
        preprocess_main(
            ctx,
            str(prompt),
            output=str(tmp_path / "pdd" / "dynamic_python_preprocessed.prompt"),
            xml=False,
            recursive=True,
            double=True,
            exclude=[],
            snapshot=True,
        )


def test_replay_from_evidence_manifest_with_context_snapshot(tmp_path):
    recorder = start_snapshot_run(
        tmp_path / "prompts" / "demo.prompt",
        evidence_root=tmp_path / ".pdd" / "evidence",
    )
    prompt_path = tmp_path / "prompts" / "demo.prompt"
    prompt_path.parent.mkdir(parents=True)
    prompt_path.write_text("<shell>printf x</shell>\n", encoding="utf-8")
    manifest = recorder.finalize(expanded_prompt="expanded-body", prompt_text=prompt_path.read_text())

    from pdd.evidence_manifest import write_evidence_manifest

    evidence_path = write_evidence_manifest(
        command="pdd generate",
        prompt_file=prompt_path,
        project_root=tmp_path,
        context_snapshot={
            "enabled": True,
            "run_id": manifest["run_id"],
            "manifest_path": manifest["manifest_path"],
            "snapshot_dir": manifest["snapshot_dir"],
            "expanded_prompt": manifest["expanded_prompt"],
            "uses_nondeterministic_context": manifest["uses_nondeterministic_context"],
            "dynamic_tags": manifest["dynamic_tags"],
            "declared_dynamic_tags": manifest["declared_dynamic_tags"],
            "redaction_applied": manifest["redaction"]["applied"],
            "artifacts": manifest["artifacts"],
        },
    )

    result = replay_snapshot(evidence_path)
    assert result["expanded_prompt"] == "expanded-body"
    assert result["verified"] is True
