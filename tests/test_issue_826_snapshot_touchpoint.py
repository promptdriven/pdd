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
from pdd.commands.misc import preprocess
from pdd.commands.replay import replay
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
