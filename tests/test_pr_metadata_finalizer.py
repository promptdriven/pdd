from __future__ import annotations

import json
import subprocess
from pathlib import Path


def _git(repo: Path, *args: str) -> str:
    result = subprocess.run(
        ["git", *args],
        cwd=repo,
        capture_output=True,
        check=True,
        text=True,
    )
    return result.stdout.strip()


def _make_repo(tmp_path: Path) -> Path:
    repo = tmp_path / "repo"
    repo.mkdir()
    _git(repo, "init", "--initial-branch=main")
    _git(repo, "config", "user.name", "Test User")
    _git(repo, "config", "user.email", "test@example.com")

    (repo / ".gitignore").write_text(".pdd/\n", encoding="utf-8")
    (repo / ".pddrc").write_text("# marker\n", encoding="utf-8")
    (repo / "prompts").mkdir()
    (repo / "examples").mkdir()
    (repo / "tests").mkdir()
    (repo / "prompts" / "foo_python.prompt").write_text(
        "<pdd-reason>Foo module.</pdd-reason>\n"
        "<pdd-interface>{\"type\":\"module\",\"module\":{\"functions\":[]}}</pdd-interface>\n"
        "\n"
        "% Generate foo.\n",
        encoding="utf-8",
    )
    (repo / "foo.py").write_text("VALUE = 1\n", encoding="utf-8")
    (repo / "examples" / "foo_example.py").write_text("import foo\n", encoding="utf-8")
    (repo / "tests" / "test_foo.py").write_text("def test_foo(): pass\n", encoding="utf-8")
    (repo / "architecture.json").write_text(
        json.dumps(
            [
                {
                    "filename": "foo_python.prompt",
                    "filepath": "foo.py",
                    "reason": "Foo module.",
                    "dependencies": [],
                    "interface": {"type": "module", "module": {"functions": []}},
                }
            ],
            indent=2,
        ),
        encoding="utf-8",
    )
    _git(
        repo,
        "add",
        ".gitignore",
        ".pddrc",
        "architecture.json",
        "prompts/foo_python.prompt",
        "foo.py",
        "examples/foo_example.py",
        "tests/test_foo.py",
    )
    _git(repo, "commit", "-m", "base")

    tracked_meta = repo / ".pdd" / "meta" / "bar_python.json"
    tracked_meta.parent.mkdir(parents=True)
    tracked_meta.write_text('{"old": true}\n', encoding="utf-8")
    _git(repo, "add", "-f", ".pdd/meta/bar_python.json")
    _git(repo, "commit", "-m", "track unrelated meta")
    return repo


def test_finalize_pr_metadata_stages_only_expected_fingerprint(tmp_path: Path) -> None:
    from pdd.pr_metadata_finalizer import finalize_pr_metadata

    repo = _make_repo(tmp_path)
    run_report = repo / ".pdd" / "meta" / "foo_python_run.json"
    run_report.write_text('{"keep": true}\n', encoding="utf-8")
    _git(repo, "add", "-f", ".pdd/meta/foo_python_run.json")
    _git(repo, "commit", "-m", "track run report")

    (repo / "foo.py").write_text("VALUE = 2\n", encoding="utf-8")
    (repo / ".pdd" / "meta" / "bar_python.json").write_text(
        '{"unrelated": true}\n',
        encoding="utf-8",
    )

    result = finalize_pr_metadata(repo, changed_paths=["foo.py", ".pdd/meta/bar_python.json"])

    assert result.ok, result.message
    assert result.metadata_paths == (".pdd/meta/foo_python.json",)
    cached = _git(repo, "diff", "--cached", "--name-only").splitlines()
    assert cached == [".pdd/meta/foo_python.json"]
    assert run_report.read_text(encoding="utf-8") == '{"keep": true}\n'
    assert _git(repo, "status", "--short", ".pdd/meta/foo_python_run.json") == ""

    fingerprint = json.loads((repo / ".pdd" / "meta" / "foo_python.json").read_text())
    assert fingerprint["prompt_hash"]
    assert fingerprint["code_hash"]
    assert fingerprint["example_hash"]
    assert fingerprint["test_hash"]
    assert fingerprint["test_files"]


def test_stage_paths_scoped_skips_unexpected_pdd_meta(tmp_path: Path) -> None:
    from pdd.pr_metadata_finalizer import stage_paths_scoped

    repo = _make_repo(tmp_path)
    (repo / "foo.py").write_text("VALUE = 2\n", encoding="utf-8")
    (repo / ".pdd" / "meta" / "bar_python.json").write_text(
        '{"unrelated": true}\n',
        encoding="utf-8",
    )

    ok, message = stage_paths_scoped(repo, ["foo.py", ".pdd/meta/bar_python.json"])

    assert ok, message
    assert _git(repo, "diff", "--cached", "--name-only").splitlines() == ["foo.py"]


def test_finalize_pr_metadata_ignores_fixture_prompts_outside_prompt_root(
    tmp_path: Path,
) -> None:
    from pdd.pr_metadata_finalizer import finalize_pr_metadata

    repo = _make_repo(tmp_path)
    fixture_dir = repo / "context" / "change" / "1"
    fixture_dir.mkdir(parents=True)
    (fixture_dir / "foo_python.prompt").write_text("% Fixture prompt\n", encoding="utf-8")

    result = finalize_pr_metadata(
        repo,
        changed_paths=["context/change/1/foo_python.prompt"],
        stage=False,
    )

    assert result.ok, result.message
    assert result.metadata_paths == ()


def test_checkup_commit_scopes_pdd_meta_staging(tmp_path: Path, monkeypatch) -> None:
    import pdd.checkup_review_loop as mod

    repo = _make_repo(tmp_path)
    (repo / "foo.py").write_text("VALUE = 2\n", encoding="utf-8")
    (repo / ".pdd" / "meta" / "bar_python.json").write_text(
        '{"unrelated": true}\n',
        encoding="utf-8",
    )
    monkeypatch.setattr(mod, "push_with_retry", lambda *args, **kwargs: (True, ""))

    ok, message = mod._commit_and_push_if_changed(
        repo,
        {
            "clone_url": "https://github.com/promptdriven/pdd.git",
            "head_ref": "feature",
            "head_owner": "promptdriven",
            "head_repo": "pdd",
        },
        "fix: scoped metadata",
    )

    assert ok, message
    committed = _git(repo, "show", "--name-only", "--pretty=", "HEAD").splitlines()
    assert "foo.py" in committed
    assert ".pdd/meta/foo_python.json" in committed
    assert ".pdd/meta/bar_python.json" not in committed
    assert _git(repo, "diff", "--name-only", ".pdd/meta/bar_python.json") == ".pdd/meta/bar_python.json"


def test_cli_pr_flows_are_wired_to_metadata_finalizer() -> None:
    root = Path(__file__).resolve().parents[1]

    bug = (root / "pdd" / "agentic_bug_orchestrator.py").read_text(encoding="utf-8")
    change = (root / "pdd" / "agentic_change_orchestrator.py").read_text(encoding="utf-8")
    fix = (root / "pdd" / "agentic_e2e_fix_orchestrator.py").read_text(encoding="utf-8")
    checkup = (root / "pdd" / "checkup_review_loop.py").read_text(encoding="utf-8")
    change_pr_prompt = (
        root / "pdd" / "prompts" / "agentic_change_step13_create_pr_LLM.prompt"
    ).read_text(encoding="utf-8")

    assert "finalize_pr_metadata(\n                current_work_dir" in bug
    assert "finalize_pr_metadata(\n            current_work_dir" in change
    assert "finalize_pr_metadata(cwd, changed_paths=files_to_commit" in fix
    assert "finalize_pr_metadata(worktree, changed_paths=changed" in checkup
    assert "**Stage all changes**" not in change_pr_prompt
    assert "Do not run `git add -A`" in change_pr_prompt
    assert "stage_paths_scoped(current_work_dir, changed_files)" in change
