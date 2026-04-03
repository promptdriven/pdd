from __future__ import annotations

"""
Example demonstrating how to use pdd.update_main.

update_main is the CLI wrapper for updating prompts based on modified code.
It supports three modes:
  1. True update: prompt + code + git/original code -> updated prompt
  2. Regeneration: only code file -> generate new prompt from scratch
  3. Repo mode: scan entire repo, detect changes, update changed pairs

Key public functions:
  - update_main(): Main entry point, returns (prompt, cost_usd, model) or None
  - resolve_prompt_code_pair(): Derive prompt path from code file path
  - find_and_resolve_all_pairs(): Scan repo for all code/prompt pairs
  - get_git_changed_files(): Get set of changed files vs base branch
  - derive_basename_and_language(): Extract basename and language from code path
  - is_code_changed(): Check if code changed since last fingerprint
  - update_file_pair(): Update a single prompt/code pair

Costs are in USD (e.g., 0.05 means $0.05).
"""

import os
import sys
import tempfile
from pathlib import Path
from unittest.mock import patch, MagicMock

import click

# Ensure project root is importable
project_root = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(project_root))

from pdd.update_main import (
    resolve_prompt_code_pair,
    find_and_resolve_all_pairs,
    get_git_changed_files,
    derive_basename_and_language,
    is_code_changed,
    update_main,
)


def example_resolve_prompt_code_pair() -> None:
    """Derive prompt path from a code file, creating missing dirs/files."""
    print("=" * 60)
    print("Example 1: resolve_prompt_code_pair")
    print("=" * 60)

    with tempfile.TemporaryDirectory() as tmp:
        tmp_path = Path(tmp)

        # Create a code file
        code_file = tmp_path / "src" / "calculator.py"
        code_file.parent.mkdir(parents=True, exist_ok=True)
        code_file.write_text("def add(a, b):\n    return a + b\n")

        # Mock git.Repo to avoid needing a real repo
        mock_repo = MagicMock()
        mock_repo.working_tree_dir = str(tmp_path)

        # Mock _find_nearest_pddrc_for_file where it's imported from (construct_paths)
        with patch("pdd.update_main.git.Repo", return_value=mock_repo), \
             patch("pdd.update_main._resolve_prompt_from_pddrc", return_value=None), \
             patch("pdd.construct_paths._find_nearest_pddrc_for_file", return_value=(None, tmp_path)):
            prompt_path, code_path = resolve_prompt_code_pair(
                str(code_file), quiet=True
            )

        print(f"  Code file  : {os.path.relpath(code_path, tmp)}")
        print(f"  Prompt file: {os.path.relpath(prompt_path, tmp)}")
        print(f"  Prompt exists: {Path(prompt_path).exists()}")
        print()


def example_derive_basename_and_language() -> None:
    """Extract basename (relative path stem) and language from a code path."""
    print("=" * 60)
    print("Example 2: derive_basename_and_language")
    print("=" * 60)

    with tempfile.TemporaryDirectory() as tmp:
        tmp_path = Path(tmp)

        # Create code files in different directories
        files = [
            tmp_path / "src" / "api" / "handler.py",
            tmp_path / "lib" / "utils.ts",
            tmp_path / "main.go",
        ]
        for f in files:
            f.parent.mkdir(parents=True, exist_ok=True)
            f.write_text("// placeholder\n")

        for f in files:
            basename, language = derive_basename_and_language(str(f), str(tmp_path))
            print(f"  {os.path.relpath(f, tmp_path)}")
            print(f"    basename: {basename}, language: {language}")

        print()


def example_get_git_changed_files() -> None:
    """Get the set of files changed relative to a base branch."""
    print("=" * 60)
    print("Example 3: get_git_changed_files (mocked)")
    print("=" * 60)

    with tempfile.TemporaryDirectory() as tmp:
        # Mock subprocess calls to simulate git output
        def mock_run(cmd, **kwargs):
            result = MagicMock()
            result.stdout = ""
            result.returncode = 0
            if "merge-base" in cmd:
                result.stdout = "abc123\n"
            elif "diff" in cmd and "name-only" in cmd:
                if "HEAD" in cmd and "abc123" in cmd:
                    result.stdout = "src/handler.py\nlib/utils.ts\n"
                else:
                    result.stdout = "README.md\n"
            elif "ls-files" in cmd and "--others" in cmd:
                result.stdout = "new_file.py\n"
            return result

        with patch("pdd.update_main.subprocess.run", side_effect=mock_run):
            changed = get_git_changed_files(tmp, base_branch="main")

        print(f"  Changed files ({len(changed)}):")
        for f in sorted(changed):
            print(f"    {os.path.relpath(f, tmp)}")
        print()


def example_is_code_changed() -> None:
    """Check whether a code file has changed since last sync."""
    print("=" * 60)
    print("Example 4: is_code_changed")
    print("=" * 60)

    with tempfile.TemporaryDirectory() as tmp:
        tmp_path = Path(tmp)
        code_file = tmp_path / "module.py"
        code_file.write_text("def hello(): pass\n")

        # Scenario A: No fingerprint, file in git changed set
        with patch("pdd.update_main.read_fingerprint", return_value=None):
            changed, reason = is_code_changed(
                str(code_file),
                str(tmp_path),
                git_changed_files={str(code_file)},
            )
        print(f"  No fingerprint, in git changed set:")
        print(f"    changed={changed}, reason='{reason}'")

        # Scenario B: No fingerprint, file NOT in git changed set
        with patch("pdd.update_main.read_fingerprint", return_value=None):
            changed, reason = is_code_changed(
                str(code_file),
                str(tmp_path),
                git_changed_files=set(),
            )
        print(f"  No fingerprint, not in git changed set:")
        print(f"    changed={changed}, reason='{reason}'")

        print()


def example_update_main_regeneration() -> None:
    """Regeneration mode: generate a new prompt from a code file only."""
    print("=" * 60)
    print("Example 5: update_main -- regeneration mode")
    print("=" * 60)

    with tempfile.TemporaryDirectory() as tmp:
        tmp_path = Path(tmp)
        code_file = tmp_path / "calculator.py"
        code_file.write_text(
            "def add(a: int, b: int) -> int:\n"
            "    return a + b\n\n"
            "def subtract(a: int, b: int) -> int:\n"
            "    return a - b\n"
        )

        ctx = click.Context(click.Command("update"))
        ctx.obj = {
            "strength": 0.5,
            "temperature": 0.0,
            "verbose": False,
            "quiet": True,
            "time": 0.25,
            "force": True,
            "context": None,
            "confirm_callback": None,
        }

        mock_prompt = "% Goal\nImplement add and subtract functions."

        # Mock dependencies: agentic unavailable, legacy update_prompt returns result
        with patch("pdd.update_main.get_available_agents", return_value=[]), \
             patch("pdd.update_main.update_prompt", return_value=(mock_prompt, 0.03, "gemini/gemini-2.5-pro")), \
             patch("pdd.update_main.resolve_prompt_code_pair", return_value=(str(tmp_path / "calculator_python.prompt"), str(code_file))):
            result = update_main(
                ctx=ctx,
                input_prompt_file=None,
                modified_code_file=str(code_file),
                input_code_file=None,
                output=None,
                use_git=False,
                repo=False,
                simple=True,
            )

        if result:
            prompt_text, cost, model = result
            print(f"  Prompt: {prompt_text[:60]}...")
            print(f"  Cost (USD): ${cost:.4f}")
            print(f"  Model: {model}")
        else:
            print("  Result: None (error)")
        print()


def example_update_main_true_update() -> None:
    """True update mode: update an existing prompt from code changes."""
    print("=" * 60)
    print("Example 6: update_main -- true update mode (with --git)")
    print("=" * 60)

    with tempfile.TemporaryDirectory() as tmp:
        tmp_path = Path(tmp)

        prompt_file = tmp_path / "calc_python.prompt"
        prompt_file.write_text("% Goal\nImplement add function.")
        code_file = tmp_path / "calc.py"
        code_file.write_text("def add(a, b): return a + b\ndef mul(a, b): return a * b\n")

        ctx = click.Context(click.Command("update"))
        ctx.obj = {
            "strength": 0.8,
            "temperature": 0.0,
            "verbose": False,
            "quiet": True,
            "time": 0.25,
            "force": True,
            "context": None,
            "confirm_callback": None,
        }

        updated_prompt = "% Goal\nImplement add and mul functions."

        with patch("pdd.update_main.get_available_agents", return_value=[]), \
             patch("pdd.update_main.construct_paths", return_value=(
                 {},
                 {"input_prompt_file": prompt_file.read_text(), "modified_code_file": code_file.read_text()},
                 {"output": str(prompt_file)},
                 "python",
             )), \
             patch("pdd.update_main.git_update", return_value=(updated_prompt, 0.05, "claude-3-5-sonnet")):
            result = update_main(
                ctx=ctx,
                input_prompt_file=str(prompt_file),
                modified_code_file=str(code_file),
                input_code_file=None,
                output=None,
                use_git=True,
                repo=False,
                simple=True,
            )

        if result:
            prompt_text, cost, model = result
            print(f"  Updated prompt: {prompt_text}")
            print(f"  Cost (USD): ${cost:.4f}")
            print(f"  Model: {model}")
        else:
            print("  Result: None (error)")
        print()


def example_update_main_repo_mode() -> None:
    """Repo mode: scan repo, detect changes, update changed pairs."""
    print("=" * 60)
    print("Example 7: update_main -- repo mode")
    print("=" * 60)

    with tempfile.TemporaryDirectory() as tmp:
        tmp_path = Path(tmp)

        # Save original cwd so we can restore it
        original_cwd = os.getcwd()

        try:
            os.chdir(tmp_path)

            # Create a fake git repo structure
            (tmp_path / ".git").mkdir()
            code_file = tmp_path / "src" / "handler.py"
            code_file.parent.mkdir(parents=True)
            code_file.write_text("def handle(): pass\n")
            prompt_file = tmp_path / "prompts" / "handler_python.prompt"
            prompt_file.parent.mkdir(parents=True)
            prompt_file.write_text("")  # empty = needs generation

            ctx = click.Context(click.Command("update"))
            ctx.obj = {
                "strength": 0.5,
                "temperature": 0.0,
                "verbose": False,
                "quiet": True,
                "time": 0.25,
                "force": True,
                "context": None,
                "confirm_callback": None,
            }

            mock_repo = MagicMock()
            mock_repo.working_tree_dir = str(tmp_path)
            mock_repo.untracked_files = []

            update_result = {
                "prompt_file": str(prompt_file),
                "status": "\u2705 Success",
                "cost": 0.04,
                "model": "gemini/gemini-2.5-pro",
                "error": "",
            }

            with patch("pdd.update_main.git.Repo", return_value=mock_repo), \
                 patch("pdd.update_main.find_and_resolve_all_pairs", return_value=[(str(prompt_file), str(code_file))]), \
                 patch("pdd.update_main.get_git_changed_files", return_value={str(code_file)}), \
                 patch("pdd.update_main.is_code_changed", return_value=(True, "no fingerprint")), \
                 patch("pdd.update_main.update_file_pair", return_value=update_result), \
                 patch("pdd.architecture_registry.find_architecture_for_project", return_value=[]), \
                 patch("pdd.operation_log.save_fingerprint"), \
                 patch("pdd.operation_log.infer_module_identity", return_value=("handler", "python")):
                result = update_main(
                    ctx=ctx,
                    input_prompt_file=None,
                    modified_code_file=None,
                    input_code_file=None,
                    output=None,
                    repo=True,
                    simple=True,
                )

            if result:
                msg, cost, models = result
                print(f"  Message: {msg}")
                print(f"  Total cost (USD): ${cost:.4f}")
                print(f"  Models used: {models}")
            else:
                print("  Result: None (no changes)")
        finally:
            os.chdir(original_cwd)

        print()


def main() -> None:
    """Run all examples demonstrating update_main functionality."""
    print("pdd.update_main -- Usage Examples")
    print("=" * 60)
    print()

    example_resolve_prompt_code_pair()
    example_derive_basename_and_language()
    example_get_git_changed_files()
    example_is_code_changed()
    example_update_main_regeneration()
    example_update_main_true_update()
    example_update_main_repo_mode()

    print("All examples completed successfully.")


if __name__ == "__main__":
    main()
