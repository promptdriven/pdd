from __future__ import annotations

import json
import subprocess
from pathlib import Path
from types import SimpleNamespace


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


def test_finalize_pr_metadata_anchors_subproject_metadata(
    tmp_path: Path,
    monkeypatch,
) -> None:
    import pdd.pr_metadata_finalizer as mod

    repo = _make_repo(tmp_path)
    sub = repo / "pkg"
    (sub / "prompts").mkdir(parents=True)
    (sub / ".pddrc").write_text(
        "contexts:\n"
        "  default:\n"
        "    paths:\n"
        "      - \"**\"\n"
        "    defaults:\n"
        "      prompts_dir: prompts\n"
        "      generate_output_path: \"\"\n"
        "      test_output_path: tests/\n"
        "      example_output_path: examples/\n"
        "      default_language: python\n",
        encoding="utf-8",
    )
    (sub / "prompts" / "bar_python.prompt").write_text(
        "<pdd-reason>Bar module.</pdd-reason>\n"
        "<pdd-interface>{\"type\":\"module\",\"module\":{\"functions\":[]}}</pdd-interface>\n"
        "\n"
        "% Generate bar.\n",
        encoding="utf-8",
    )
    (sub / "bar.py").write_text("VALUE = 1\n", encoding="utf-8")
    _git(repo, "add", "pkg/.pddrc", "pkg/prompts/bar_python.prompt", "pkg/bar.py")
    _git(repo, "commit", "-m", "add subproject")

    (sub / "bar.py").write_text("VALUE = 2\n", encoding="utf-8")
    monkeypatch.setattr(
        mod,
        "run_metadata_sync",
        lambda *args, **kwargs: SimpleNamespace(ok=True),
    )

    result = mod.finalize_pr_metadata(repo, changed_paths=["pkg/bar.py"])

    assert result.ok, result.message
    assert result.metadata_paths == ("pkg/.pdd/meta/bar_python.json",)
    assert (sub / ".pdd" / "meta" / "bar_python.json").is_file()
    assert _git(repo, "diff", "--cached", "--name-only").splitlines() == [
        "pkg/.pdd/meta/bar_python.json"
    ]


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
    checkup_pr_prompt = (
        root / "pdd" / "prompts" / "agentic_checkup_step8_create_pr_LLM.prompt"
    ).read_text(encoding="utf-8")

    assert "finalize_pr_metadata(" in bug
    assert "current_work_dir" in bug
    assert "finalize_pr_metadata(" in change
    assert "current_work_dir" in change
    assert "finalize_pr_metadata(cwd, changed_paths=files_to_commit" in fix
    assert "finalize_pr_metadata(worktree, changed_paths=changed" in checkup
    assert "**Stage all changes**" not in change_pr_prompt
    assert "Do not run `git add -A`" in change_pr_prompt
    assert "- Use `git add -A`" not in checkup_pr_prompt
    assert "\ngit add -A\n" not in checkup_pr_prompt
    assert "stage_paths_scoped(current_work_dir, changed_files)" in change


def test_finalize_restores_prompt_and_arch_side_effects_issue_1317(
    tmp_path: Path,
    monkeypatch,
) -> None:
    """FM2: run_metadata_sync rewrites the prompt (tag block) and architecture.json
    as a side effect, but finalization stages ONLY fingerprints. Those rewrites
    must be rolled back so a code-only PR never leaves an unstaged prompt/arch
    change (a fingerprint for content not in the PR).

    On the unfixed finalizer the sync's writes persist: the prompt and
    architecture.json are left modified in the working tree.
    """
    import pdd.pr_metadata_finalizer as mod

    repo = _make_repo(tmp_path)
    prompt = repo / "prompts" / "foo_python.prompt"
    arch = repo / "architecture.json"
    prompt_before = prompt.read_text(encoding="utf-8")
    arch_before = arch.read_text(encoding="utf-8")

    (repo / "foo.py").write_text("VALUE = 2\n", encoding="utf-8")  # code-only change

    def fake_sync(prompt_path, code_path=None, *, repo_root=None, architecture_path=None, **kw):
        # Simulate run_metadata_sync's real side effects (tag-block prepend +
        # architecture entry rewrite) so the restore is exercised.
        Path(prompt_path).write_text("% REWRITTEN BY SYNC\n", encoding="utf-8")
        if architecture_path is not None:
            Path(architecture_path).write_text('[{"rewritten": true}]\n', encoding="utf-8")
        return SimpleNamespace(ok=True)

    monkeypatch.setattr(mod, "run_metadata_sync", fake_sync)

    result = mod.finalize_pr_metadata(repo, changed_paths=["foo.py"])

    assert result.ok, result.message
    # The sync's prompt/arch rewrites must be restored to the as-committed state.
    assert prompt.read_text(encoding="utf-8") == prompt_before, "prompt rewrite leaked"
    assert arch.read_text(encoding="utf-8") == arch_before, "architecture.json rewrite leaked"
    # Only the fingerprint is staged; no prompt/arch left dirty in the tree.
    cached = _git(repo, "diff", "--cached", "--name-only").splitlines()
    assert cached == [".pdd/meta/foo_python.json"]
    dirty = _git(repo, "status", "--short").splitlines()
    assert not any("prompts/foo_python.prompt" in line for line in dirty), dirty
    assert not any("architecture.json" in line for line in dirty), dirty


def test_finalize_uses_nearest_architecture_for_nested_module_issue_1317(
    tmp_path: Path,
    monkeypatch,
) -> None:
    """FM3: a nested subproject must finalize against its OWN architecture.json,
    not the root's. find_architecture_for_project returns the root first, so the
    finalizer must pick the nearest-ancestor architecture per module.

    On the unfixed finalizer the root architecture.json is passed for every
    module, so a nested same-named prompt inherits the parent's entry.
    """
    import pdd.pr_metadata_finalizer as mod

    repo = _make_repo(tmp_path)
    sub = repo / "pkg"
    (sub / "prompts").mkdir(parents=True)
    (sub / ".pddrc").write_text(
        "contexts:\n  default:\n    paths:\n      - \"**\"\n"
        "    defaults:\n      prompts_dir: prompts\n      generate_output_path: \"\"\n"
        "      test_output_path: tests/\n      example_output_path: examples/\n"
        "      default_language: python\n",
        encoding="utf-8",
    )
    (sub / "prompts" / "bar_python.prompt").write_text(
        "<pdd-reason>Bar.</pdd-reason>\n% Generate bar.\n", encoding="utf-8"
    )
    (sub / "bar.py").write_text("VALUE = 1\n", encoding="utf-8")
    (sub / "architecture.json").write_text(
        json.dumps([{"filename": "bar_python.prompt", "filepath": "bar.py",
                     "reason": "Bar.", "dependencies": []}], indent=2),
        encoding="utf-8",
    )
    _git(repo, "add", "pkg/.pddrc", "pkg/prompts/bar_python.prompt", "pkg/bar.py",
         "pkg/architecture.json")
    _git(repo, "commit", "-m", "add subproject")
    (sub / "bar.py").write_text("VALUE = 2\n", encoding="utf-8")

    seen: dict = {}

    def spy_sync(prompt_path, code_path=None, *, repo_root=None, architecture_path=None, **kw):
        seen[Path(prompt_path).name] = architecture_path
        return SimpleNamespace(ok=True)

    monkeypatch.setattr(mod, "run_metadata_sync", spy_sync)

    result = mod.finalize_pr_metadata(repo, changed_paths=["pkg/bar.py"])

    assert result.ok, result.message
    arch_used = seen.get("bar_python.prompt")
    assert arch_used is not None, seen
    assert Path(arch_used).resolve() == (sub / "architecture.json").resolve(), (
        f"nested module finalized against {arch_used}, not its own architecture.json"
    )


def test_commit_and_push_finalizes_fixer_committed_changes_issue_1317(
    tmp_path: Path,
    monkeypatch,
) -> None:
    """FM1: a fixer subprocess can COMMIT a PDD-owned change inside the worktree
    and leave the tree clean. _commit_and_push_if_changed must still finalize the
    fixer's committed range (pre_fix_sha..HEAD) so the pushed branch carries a
    fresh fingerprint — not push the commit with a missing one.

    On the unfixed loop, finalization is gated behind working-tree drift, so the
    fixer commit pushes with no .pdd/meta fingerprint.
    """
    import pdd.checkup_review_loop as mod

    repo = _make_repo(tmp_path)
    pre_fix_sha = _git(repo, "rev-parse", "HEAD")

    # Fixer subprocess commits a code change directly, WITHOUT a fingerprint.
    (repo / "foo.py").write_text("VALUE = 99\n", encoding="utf-8")
    _git(repo, "add", "foo.py")
    _git(repo, "commit", "-m", "Codex Local Autoheal")

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
        pre_fix_sha=pre_fix_sha,
    )

    assert ok, message
    assert (repo / ".pdd" / "meta" / "foo_python.json").is_file(), (
        "fixer-committed change must get a finalized fingerprint"
    )
    # The fingerprint must be COMMITTED (not just left in the working tree).
    head_files = _git(repo, "show", "--name-only", "--pretty=", "HEAD").splitlines()
    assert ".pdd/meta/foo_python.json" in head_files, head_files
