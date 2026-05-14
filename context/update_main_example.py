"""
Example demonstrating how to use ``pdd.update_main``.

``update_main`` is the CLI wrapper for updating prompts based on modified
code.  It supports three modes:

  1. True update:        prompt + old code + modified code  -> updated prompt
  2. Regeneration:       modified code only                 -> brand-new prompt
  3. Repo mode:          scan repo for changed pairs, update each

Public helpers exposed by the module:

  - ``update_main()``              — main entry point.
  - ``resolve_prompt_code_pair()`` — derive a prompt path from a code path.
  - ``find_and_resolve_all_pairs()`` — scan a directory tree for code/prompt pairs.
  - ``get_git_changed_files()``    — get the set of changed files vs a base branch.
  - ``derive_basename_and_language()`` — derive a fingerprint key from a code path.
  - ``is_code_changed()``          — has a code file effectively changed?
  - ``update_file_pair()``         — update a single (prompt, code) pair.
  - ``_run_single_file_metadata_sync()`` — finalize metadata after a single update.

All costs are in USD.

This example mocks external services so it runs offline.
"""

from __future__ import annotations

import os
import sys
import tempfile
import subprocess
from pathlib import Path
from types import SimpleNamespace
from unittest.mock import patch, MagicMock

# Ensure project root is importable regardless of cwd.
project_root = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(project_root))

import click  # noqa: E402

from pdd.update_main import (  # noqa: E402
    derive_basename_and_language,
    find_and_resolve_all_pairs,
    get_git_changed_files,
    is_code_changed,
    resolve_prompt_code_pair,
    update_file_pair,
    update_main,
    _run_single_file_metadata_sync,
)


def _make_ctx(quiet: bool = True) -> click.Context:
    """Build a Click context with the standard ctx.obj keys."""
    ctx = click.Context(click.Command("update"))
    ctx.obj = {
        "strength": 0.5,
        "temperature": 0.0,
        "verbose": False,
        "quiet": quiet,
        "time": 0.25,
        "force": True,
        "context": None,
        "confirm_callback": None,
    }
    return ctx


def example_resolve_prompt_code_pair() -> None:
    """Derive a prompt path from a code file path; create the file if absent."""
    print("=" * 60)
    print("Example 1: resolve_prompt_code_pair")
    print("=" * 60)

    with tempfile.TemporaryDirectory() as tmp:
        tmp_path = Path(tmp).resolve()
        code_file = tmp_path / "src" / "calculator.py"
        code_file.parent.mkdir(parents=True, exist_ok=True)
        code_file.write_text("def add(a, b):\n    return a + b\n", encoding="utf-8")

        def fake_run(cmd, **kwargs):
            res = SimpleNamespace(returncode=0, stdout="", stderr="")
            if cmd[:2] == ["git", "rev-parse"]:
                res.stdout = str(tmp_path) + "\n"
            return res

        # Skip .pddrc resolution so we get the predictable prompts/ fallback,
        # and force the repo root to be the tmp dir.
        with patch("pdd.update_main._resolve_prompt_from_pddrc", return_value=None), \
             patch("pdd.update_main.subprocess.run", side_effect=fake_run):
            prompt_path, code_path = resolve_prompt_code_pair(code_file, quiet=True)

        print(f"  code   : {code_path.relative_to(tmp_path)}")
        print(f"  prompt : {prompt_path.relative_to(tmp_path)}")
        print(f"  prompt exists: {prompt_path.exists()}")
    print()


def example_derive_basename_and_language() -> None:
    """Show that nested code paths produce collision-free basenames."""
    print("=" * 60)
    print("Example 2: derive_basename_and_language")
    print("=" * 60)

    with tempfile.TemporaryDirectory() as tmp:
        repo = Path(tmp).resolve()
        files = [
            repo / "src" / "api" / "handler.py",
            repo / "lib" / "utils.py",
        ]
        for f in files:
            f.parent.mkdir(parents=True, exist_ok=True)
            f.write_text("# placeholder\n", encoding="utf-8")
            basename, lang = derive_basename_and_language(f, repo)
            print(f"  {f.relative_to(repo)}  ->  basename={basename!r}, lang={lang!r}")
    print()


def example_get_git_changed_files() -> None:
    """Show how get_git_changed_files combines diff + untracked results."""
    print("=" * 60)
    print("Example 3: get_git_changed_files (mocked git)")
    print("=" * 60)

    with tempfile.TemporaryDirectory() as tmp:
        repo = Path(tmp).resolve()

        def fake_run(cmd, **kwargs):
            res = SimpleNamespace(returncode=0, stdout="", stderr="")
            if cmd[:2] == ["git", "diff"] and "main...HEAD" in cmd:
                res.stdout = "src/handler.py\n"
            elif cmd[:2] == ["git", "diff"]:
                res.stdout = "src/util.py\n"
            elif cmd[:3] == ["git", "ls-files", "--others"]:
                res.stdout = "new_file.py\n"
            return res

        with patch("pdd.update_main.subprocess.run", side_effect=fake_run):
            changed = get_git_changed_files(repo, base_branch="main")

        print(f"  {len(changed)} changed files:")
        for c in sorted(changed):
            print(f"    {Path(c).relative_to(repo)}")
    print()


def example_is_code_changed() -> None:
    """Without a fingerprint, fall back to the git-changed set."""
    print("=" * 60)
    print("Example 4: is_code_changed (no fingerprint)")
    print("=" * 60)

    with tempfile.TemporaryDirectory() as tmp:
        repo = Path(tmp).resolve()
        code_file = repo / "module.py"
        code_file.write_text("def hello(): pass\n", encoding="utf-8")
        abs_code = str(code_file.resolve())

        # Scenario A: file in the git-changed set
        changed, reason = is_code_changed(code_file, repo, git_changed_files={abs_code})
        print(f"  in git-changed set : changed={changed}, reason={reason!r}")

        # Scenario B: file NOT in the git-changed set
        changed, reason = is_code_changed(code_file, repo, git_changed_files=set())
        print(f"  not in git-changed : changed={changed}, reason={reason!r}")
    print()


def example_update_main_true_update() -> None:
    """True update with `simple=True` so we avoid the agentic path."""
    print("=" * 60)
    print("Example 5: update_main — true update (simple=True)")
    print("=" * 60)

    with tempfile.TemporaryDirectory() as tmp:
        tmp_path = Path(tmp).resolve()
        prompt_file = tmp_path / "calc_python.prompt"
        prompt_file.write_text("% Goal\nImplement add.\n", encoding="utf-8")
        original_code = tmp_path / "calc_old.py"
        original_code.write_text("def add(a, b): return a + b\n", encoding="utf-8")
        modified_code = tmp_path / "calc.py"
        modified_code.write_text(
            "def add(a, b): return a + b\n"
            "def mul(a, b): return a * b\n",
            encoding="utf-8",
        )

        updated_prompt = "% Goal\nImplement add and mul.\n"

        with patch(
            "pdd.update_main.update_prompt",
            return_value=(updated_prompt, 0.05, "claude-3-5-sonnet"),
        ), patch(
            "pdd.update_main._run_single_file_metadata_sync",
            return_value=True,
        ):
            result = update_main(
                ctx=_make_ctx(),
                input_prompt_file=str(prompt_file),
                modified_code_file=str(modified_code),
                input_code_file=str(original_code),
                output=None,
                use_git=False,
                repo=False,
                extensions=None,
                directory=None,
                strength=None,
                temperature=None,
                simple=True,
            )

    if result is None:
        print("  Result: None (error)")
    else:
        prompt_text, cost, model = result
        print(f"  prompt (head): {prompt_text.splitlines()[0]!r}")
        print(f"  cost (USD)  : ${cost:.4f}")
        print(f"  model       : {model}")
    print()


def example_update_main_regeneration() -> None:
    """Regeneration mode: only modified_code_file is supplied."""
    print("=" * 60)
    print("Example 6: update_main — regeneration (simple=True)")
    print("=" * 60)

    with tempfile.TemporaryDirectory() as tmp:
        tmp_path = Path(tmp).resolve()
        code_file = tmp_path / "calculator.py"
        code_file.write_text(
            "def add(a: int, b: int) -> int:\n    return a + b\n",
            encoding="utf-8",
        )

        regen_prompt = "% Goal\nImplement add.\n"

        with patch(
            "pdd.update_main.update_prompt",
            return_value=(regen_prompt, 0.03, "test-model"),
        ), patch(
            "pdd.update_main._run_single_file_metadata_sync",
            return_value=True,
        ):
            result = update_main(
                ctx=_make_ctx(),
                input_prompt_file=None,
                modified_code_file=str(code_file),
                input_code_file=None,
                output=None,
                use_git=False,
                repo=False,
                extensions=None,
                directory=None,
                strength=None,
                temperature=None,
                simple=True,
            )

    if result is None:
        print("  Result: None")
    else:
        prompt_text, cost, model = result
        print(f"  prompt (head): {prompt_text.splitlines()[0]!r}")
        print(f"  cost (USD)  : ${cost:.4f}")
        print(f"  model       : {model}")
    print()


def example_update_main_repo_mode() -> None:
    """Repo mode: detect changed pairs and update each."""
    print("=" * 60)
    print("Example 7: update_main — repo mode (mocked)")
    print("=" * 60)

    with tempfile.TemporaryDirectory() as tmp:
        repo = Path(tmp).resolve()
        original_cwd = Path.cwd()
        try:
            os.chdir(repo)
            (repo / ".git").mkdir()  # marker for the git-toplevel check

            code = repo / "src" / "handler.py"
            code.parent.mkdir(parents=True)
            code.write_text("def handle(): pass\n", encoding="utf-8")
            prompt = repo / "prompts" / "handler_python.prompt"
            prompt.parent.mkdir(parents=True)
            prompt.write_text("", encoding="utf-8")

            pair_result = {
                "prompt_file": str(prompt),
                "status": "updated",
                "cost": 0.04,
                "model": "test-model",
                "error": "",
            }

            def fake_run(cmd, **kwargs):
                # Mock the very first git rev-parse so repo-root detection
                # succeeds; everything else returns empty.
                res = SimpleNamespace(returncode=0, stdout="", stderr="")
                if cmd[:2] == ["git", "rev-parse"]:
                    res.stdout = str(repo) + "\n"
                return res

            with patch("pdd.update_main.subprocess.run", side_effect=fake_run), \
                 patch("pdd.update_main.find_and_resolve_all_pairs",
                       return_value=[(prompt, code)]), \
                 patch("pdd.update_main.get_git_changed_files",
                       return_value={str(code.resolve())}), \
                 patch("pdd.update_main.is_code_changed",
                       return_value=(True, "git reports change")), \
                 patch("pdd.update_main.update_file_pair",
                       return_value=pair_result):
                result = update_main(
                    ctx=_make_ctx(),
                    input_prompt_file=None,
                    modified_code_file=None,
                    input_code_file=None,
                    output=None,
                    use_git=False,
                    repo=True,
                    extensions=None,
                    directory=None,
                    strength=None,
                    temperature=None,
                    simple=True,
                )
        finally:
            os.chdir(original_cwd)

    if result is None:
        print("  Result: None (no changes)")
    else:
        msg, cost, models = result
        print(f"  message       : {msg}")
        print(f"  total cost USD: ${cost:.4f}")
        print(f"  models used   : {models}")
    print()


def example_run_single_file_metadata_sync() -> None:
    """The single-file metadata helper returns True for an ``ok`` orchestrator result."""
    print("=" * 60)
    print("Example 8: _run_single_file_metadata_sync (mocked orchestrator)")
    print("=" * 60)

    with tempfile.TemporaryDirectory() as tmp:
        tmp_path = Path(tmp).resolve()
        prompt = tmp_path / "demo.prompt"
        code = tmp_path / "demo.py"
        prompt.write_text("body\n", encoding="utf-8")
        code.write_text("def x(): pass\n", encoding="utf-8")

        fake_result = SimpleNamespace(
            ok=True,
            dry_run=False,
            stages={
                "prompt": SimpleNamespace(status="ok", reason=None, detail=None),
                "fingerprint": SimpleNamespace(status="ok", reason=None, detail=None),
            },
        )
        with patch("pdd.metadata_sync.run_metadata_sync", return_value=fake_result):
            ok = _run_single_file_metadata_sync(prompt, code, dry_run=False)
        print(f"  helper returned: {ok}")

        fake_failed = SimpleNamespace(
            ok=False,
            dry_run=False,
            stages={
                "prompt": SimpleNamespace(status="ok", reason=None, detail=None),
                "fingerprint": SimpleNamespace(
                    status="failed", reason="disk full", detail=None
                ),
            },
        )
        with patch("pdd.metadata_sync.run_metadata_sync", return_value=fake_failed):
            ok2 = _run_single_file_metadata_sync(prompt, code, dry_run=False)
        print(f"  helper on failure: {ok2}")
    print()


def example_update_file_pair() -> None:
    """update_file_pair tries agentic first; on no-agents-available it falls back."""
    print("=" * 60)
    print("Example 9: update_file_pair (legacy fallback)")
    print("=" * 60)

    with tempfile.TemporaryDirectory() as tmp:
        tmp_path = Path(tmp).resolve()
        prompt = tmp_path / "demo_python.prompt"
        code = tmp_path / "demo.py"
        prompt.write_text("% existing\n", encoding="utf-8")
        code.write_text("def x(): pass\n", encoding="utf-8")
        ctx = _make_ctx()
        with patch(
            "pdd.update_main.git_update",
            return_value=("% updated prompt\n", 0.02, "test-model"),
        ):
            result = update_file_pair(prompt, code, ctx, repo=True, simple=True)
        print(f"  status: {result['status']}")
        print(f"  cost  : ${result['cost']:.4f}")
        print(f"  model : {result['model']}")
    print()


def main() -> None:
    print("pdd.update_main — usage examples")
    print()
    example_resolve_prompt_code_pair()
    example_derive_basename_and_language()
    example_get_git_changed_files()
    example_is_code_changed()
    example_update_main_true_update()
    example_update_main_regeneration()
    example_update_main_repo_mode()
    example_run_single_file_metadata_sync()
    example_update_file_pair()
    print("All examples completed.")


if __name__ == "__main__":
    main()
