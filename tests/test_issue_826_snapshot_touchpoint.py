"""Human-runnable touchpoint for issue #826 snapshot / replay / checkup snapshot.

Mirrors the manual QA script in examples/context_snapshot_demo/README.md without
requiring LLM keys or live web fetches.
"""
from __future__ import annotations

import json
import shutil
from pathlib import Path

import pytest
from click.testing import CliRunner

from pdd.commands.checkup import checkup
from pdd.commands.checkup_snapshot import checkup_snapshot
from pdd.commands.generate import generate
from pdd.commands.misc import preprocess
from pdd.commands.replay import replay
from pdd.preprocess import preprocess as preprocess_text
from pdd.context_snapshot import replay_snapshot
from pdd.context_snapshot_policy import check_snapshot_policy
from pdd.evidence_manifest import write_evidence_manifest

DEMO_ROOT = Path(__file__).resolve().parents[1] / "examples" / "context_snapshot_demo"


def _copy_demo(tmp_path: Path) -> Path:
    project = tmp_path / "demo-project"
    shutil.copytree(DEMO_ROOT, project)
    return project


def _mock_web(monkeypatch: pytest.MonkeyPatch) -> None:
    monkeypatch.setattr(
        "pdd.preprocess.get_firecrawl_cache",
        lambda: type(
            "Cache",
            (),
            {
                "get": lambda self, url: "demo-web-body\n",
                "set": lambda self, url, content: None,
            },
        )(),
    )


def test_issue_826_preprocess_snapshot_replay_and_policy(tmp_path: Path, monkeypatch: pytest.MonkeyPatch) -> None:
    """End-to-end: preprocess --snapshot, replay, evidence linkage, checkup snapshot."""
    project = _copy_demo(tmp_path)
    monkeypatch.chdir(project)
    _mock_web(monkeypatch)

    dynamic = project / "prompts" / "dynamic_python.prompt"
    runner = CliRunner()

    fail_policy, _ = check_snapshot_policy(dynamic, project)
    assert fail_policy is False

    # Shell/web tags are deferred when --recursive is set; snapshot needs a
    # non-recursive pass so dynamic outputs are executed and recorded.
    pre = runner.invoke(
        preprocess,
        [str(dynamic.relative_to(project)), "--snapshot"],
        obj={"quiet": True, "force": True},
    )
    assert pre.exit_code == 0, pre.output

    runs = sorted((project / ".pdd" / "evidence" / "runs").glob("*.json"))
    assert runs, "expected snapshot manifest under .pdd/evidence/runs/"
    snapshot_manifest = runs[-1]
    snapshot_payload = json.loads(snapshot_manifest.read_text(encoding="utf-8"))

    assert snapshot_payload["schema_version"] == 1
    assert snapshot_payload["uses_nondeterministic_context"] is True
    assert "shell" in snapshot_payload["dynamic_tags"]
    artifact_types = {a["type"] for a in snapshot_payload["artifacts"]}
    assert {"include", "shell", "web", "expanded_prompt"} <= artifact_types

    replay_result = replay_snapshot(snapshot_manifest)
    assert replay_result["verified"] is True
    assert "pdd-snapshot-demo-shell" in replay_result["expanded_prompt"]

    cli_replay = runner.invoke(
        replay,
        [str(snapshot_manifest), "--verify-only", "--json"],
        obj={"quiet": True},
    )
    assert cli_replay.exit_code == 0, cli_replay.output
    assert json.loads(cli_replay.output)["success"] is True

    evidence_path = write_evidence_manifest(
        command="pdd preprocess",
        prompt_file=dynamic,
        project_root=project,
        context_snapshot={
            "manifest_path": snapshot_payload["manifest_path"],
            "snapshot_dir": snapshot_payload["snapshot_dir"],
            "expanded_prompt": snapshot_payload["expanded_prompt"],
            "uses_nondeterministic_context": snapshot_payload["uses_nondeterministic_context"],
            "dynamic_tags": snapshot_payload["dynamic_tags"],
            "declared_dynamic_tags": snapshot_payload["declared_dynamic_tags"],
            "redaction": snapshot_payload.get("redaction"),
            "artifacts": snapshot_payload["artifacts"],
        },
    )
    replay_snapshot(evidence_path)

    pass_policy, _ = check_snapshot_policy(dynamic, project)
    assert pass_policy is True

    ok = runner.invoke(
        checkup_snapshot,
        [str(dynamic.relative_to(project)), "--project-root", str(project)],
    )
    assert ok.exit_code == 0, ok.output

    via_checkup = runner.invoke(
        checkup,
        ["snapshot", str(dynamic.relative_to(project)), "--project-root", str(project)],
        obj={"quiet": True},
    )
    assert via_checkup.exit_code == 0, via_checkup.output


def test_issue_826_static_prompt_policy_passes_without_snapshot(tmp_path: Path) -> None:
    """Static prompts should not require a snapshot artifact."""
    project = _copy_demo(tmp_path)
    static = project / "prompts" / "static_python.prompt"
    passed, message = check_snapshot_policy(static, project)
    assert passed is True
    assert "no active nondeterministic" in message.lower()


def test_test_plan_preprocess_foo_python_snapshot_cli(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    """Manual: ``pdd preprocess prompts/foo_python.prompt --snapshot``."""
    project = _copy_demo(tmp_path)
    monkeypatch.chdir(project)
    _mock_web(monkeypatch)
    foo = project / "prompts" / "foo_python.prompt"
    runner = CliRunner()

    result = runner.invoke(
        preprocess,
        [str(foo.relative_to(project)), "--snapshot"],
        obj={"quiet": True, "force": True},
    )
    assert result.exit_code == 0, result.output

    runs = sorted((project / ".pdd" / "evidence" / "runs").glob("*.json"))
    assert runs
    payload = json.loads(runs[-1].read_text(encoding="utf-8"))
    assert payload["uses_nondeterministic_context"] is True
    replay = replay_snapshot(runs[-1])
    assert replay["verified"] is True
    assert "pdd-snapshot-demo-shell" in replay["expanded_prompt"]


def test_test_plan_checkup_with_shell_fails_without_snapshot(tmp_path: Path) -> None:
    """Manual: ``pdd checkup snapshot prompts/with_shell_python.prompt`` (no prior snapshot)."""
    project = _copy_demo(tmp_path)
    shell_prompt = project / "prompts" / "with_shell_python.prompt"
    runner = CliRunner()

    passed, message = check_snapshot_policy(shell_prompt, project)
    assert passed is False
    assert "no replayable snapshot" in message

    result = runner.invoke(
        checkup_snapshot,
        [str(shell_prompt), "--project-root", str(project)],
    )
    assert result.exit_code == 1, result.output
    assert "no replayable snapshot" in result.output.lower()


def test_test_plan_generate_snapshot_context_evidence_and_replay_cli(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch,
) -> None:
    """Manual: ``pdd generate … --snapshot-context --evidence`` then ``pdd replay`` on run manifest."""
    project = _copy_demo(tmp_path)
    monkeypatch.chdir(project)
    _mock_web(monkeypatch)
    foo = project / "prompts" / "foo_python.prompt"
    output_py = project / "pdd" / "foo.py"
    runner = CliRunner()

    def _stub_code_generator_main(
        ctx,
        prompt_file,
        output,
        original_prompt_file_path=None,
        force_incremental_flag=False,
        env_vars=None,
        unit_test_file=None,
        exclude_tests=False,
        snapshot_context=False,
    ):
        prompt_path = Path(prompt_file)
        if not prompt_path.is_absolute():
            prompt_path = (project / prompt_path).resolve()
        text = prompt_path.read_text(encoding="utf-8")
        recorder = None
        expanded = text
        if snapshot_context:
            from pdd.context_snapshot import start_snapshot_run

            recorder = start_snapshot_run(str(prompt_path), command="pdd generate")
            recorder.record_prompt_source(text)
            expanded = preprocess_text(
                text,
                recursive=False,
                double_curly_brackets=False,
                snapshot_recorder=recorder,
            )
        output_py.parent.mkdir(parents=True, exist_ok=True)
        output_py.write_text('"""Generated stub."""\n', encoding="utf-8")
        if snapshot_context and recorder is not None:
            manifest = recorder.finalize(
                expanded_prompt=expanded,
                prompt_text=text,
                output_files=[str(output_py)],
                model="stub-model",
            )
            ctx.ensure_object(dict)
            ctx.obj["context_snapshot"] = {
                "run_id": manifest.get("run_id"),
                "manifest_path": manifest.get("manifest_path"),
                "snapshot_dir": manifest.get("snapshot_dir"),
                "expanded_prompt": manifest.get("expanded_prompt"),
                "uses_nondeterministic_context": manifest.get("uses_nondeterministic_context"),
                "dynamic_tags": manifest.get("dynamic_tags", []),
                "declared_dynamic_tags": manifest.get("declared_dynamic_tags", []),
                "redaction_applied": manifest.get("redaction", {}).get("applied", False),
                "redaction": manifest.get("redaction"),
                "artifacts": manifest.get("artifacts", []),
            }
        return '"""Generated stub."""\n', False, 0.0, "stub-model"

    import pdd.commands.generate as generate_cmd

    monkeypatch.setattr(
        "pdd.code_generator_main.code_generator_main",
        _stub_code_generator_main,
    )
    generate_cmd.code_generator_main = _stub_code_generator_main

    gen = runner.invoke(
        generate,
        [
            str(foo.relative_to(project)),
            "--output",
            str(output_py.relative_to(project)),
            "--snapshot-context",
            "--evidence",
        ],
        obj={"quiet": True, "force": True},
    )
    assert gen.exit_code == 0, gen.output

    run_manifests = sorted((project / ".pdd" / "evidence" / "runs").glob("*.json"))
    assert run_manifests
    run_path = run_manifests[-1]

    devunit_manifests = list((project / ".pdd" / "evidence" / "devunits").glob("*.json"))
    assert devunit_manifests, "expected evidence manifest from --evidence"

    evidence_payload = json.loads(devunit_manifests[-1].read_text(encoding="utf-8"))
    context_snapshot = evidence_payload.get("context_snapshot") or {}
    assert context_snapshot.get("enabled") is True
    linked_run = project / ".pdd" / "evidence" / context_snapshot["manifest_path"]
    assert linked_run.exists()

    cli_replay = runner.invoke(
        replay,
        [str(run_path), "--verify-only", "--json"],
        obj={"quiet": True},
    )
    assert cli_replay.exit_code == 0, cli_replay.output
    assert json.loads(cli_replay.output)["success"] is True

    replay_snapshot(linked_run)
