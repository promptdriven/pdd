"""Tests for nondeterministic snapshot policy enforcement."""
from __future__ import annotations

from pathlib import Path

from click.testing import CliRunner

from pdd.commands.policy import snapshot as policy_snapshot
from pdd.context_snapshot import start_snapshot_run
from pdd.context_snapshot_policy import check_snapshot_policy, declared_nondeterministic_tags
from pdd.preprocess import preprocess


def test_declared_tags_ignore_documentation_fences() -> None:
    prompt = "Example:\n```xml\n<shell>date</shell>\n```\n"
    assert declared_nondeterministic_tags(prompt) == []


def test_policy_fails_without_snapshot(tmp_path: Path) -> None:
    prompt = tmp_path / "prompts" / "risky.prompt"
    prompt.parent.mkdir()
    prompt.write_text("<shell>date</shell>\n", encoding="utf-8")

    passed, message = check_snapshot_policy(prompt, tmp_path)
    assert passed is False
    assert "no replayable snapshot" in message


def test_policy_passes_with_snapshot(tmp_path: Path, monkeypatch) -> None:
    monkeypatch.chdir(tmp_path)
    prompt = tmp_path / "prompts" / "risky.prompt"
    prompt.parent.mkdir()
    prompt.write_text("<shell>printf ok</shell>\n", encoding="utf-8")

    recorder = start_snapshot_run(prompt, evidence_root=tmp_path / ".pdd" / "evidence")
    expanded = preprocess(
        prompt.read_text(encoding="utf-8"),
        recursive=False,
        snapshot_recorder=recorder,
    )
    recorder.finalize(expanded_prompt=expanded, prompt_text=prompt.read_text(encoding="utf-8"))

    passed, _ = check_snapshot_policy(prompt, tmp_path)
    assert passed is True


def test_policy_cli_exit_code(tmp_path: Path, monkeypatch) -> None:
    prompt = tmp_path / "dynamic.prompt"
    prompt.write_text("<web>https://example.test</web>\n", encoding="utf-8")

    fail = CliRunner().invoke(
        policy_snapshot,
        [str(prompt), "--project-root", str(tmp_path)],
    )
    assert fail.exit_code == 1

    monkeypatch.chdir(tmp_path)
    recorder = start_snapshot_run(prompt, evidence_root=tmp_path / ".pdd" / "evidence")
    monkeypatch.setattr(
        "pdd.preprocess.get_firecrawl_cache",
        lambda: type(
            "Cache",
            (),
            {
                "get": lambda self, url: "cached",
                "set": lambda self, url, content: None,
            },
        )(),
    )
    expanded = preprocess(
        prompt.read_text(encoding="utf-8"),
        recursive=False,
        snapshot_recorder=recorder,
    )
    recorder.finalize(expanded_prompt=expanded, prompt_text=prompt.read_text(encoding="utf-8"))

    ok = CliRunner().invoke(
        policy_snapshot,
        [str(prompt), "--project-root", str(tmp_path)],
    )
    assert ok.exit_code == 0, ok.output
