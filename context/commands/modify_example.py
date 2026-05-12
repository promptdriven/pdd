#!/usr/bin/env python
"""
Example usage of pdd.commands.modify (split, change, update).

This script demonstrates how to invoke the three Click commands exported
by `pdd.commands.modify` using Click's CliRunner. External dependencies
(split_main, change_main, agentic runners, update_main) are mocked so the
script runs offline, without API keys or a real git repository.

Commands:
  - split:  Split large dev units. Agentic mode (default) takes 1 arg
            (TARGET_FILE). Legacy mode (--legacy) takes 3 args
            (INPUT_PROMPT, INPUT_CODE, EXAMPLE_CODE).
  - change: Modify a prompt based on a change prompt or issue. Agentic
            mode (default) takes 1 arg (ISSUE_URL). Manual mode (--manual)
            takes 3 args (CHANGE_PROMPT, INPUT_CODE, INPUT_PROMPT), or
            with --csv takes 2 args (CSV_FILE, CODE_DIRECTORY).
  - update: Update a prompt based on code changes. Repo mode (no args,
            or --all). Regeneration mode (1 arg: MODIFIED_CODE). Git mode
            (2 args + --git: PROMPT, MODIFIED_CODE). Manual mode (3 args:
            PROMPT, MODIFIED_CODE, ORIGINAL_CODE).

Each command uses the @track_cost decorator and (when successful) returns
a 3-tuple: (result_data, total_cost_usd, model_name).

Run from anywhere:
    python context/commands/modify_example.py
"""

from __future__ import annotations

import os
import sys
import tempfile
from pathlib import Path
from unittest.mock import patch

# Make `pdd` importable regardless of cwd.
sys.path.insert(0, os.path.join(os.path.dirname(__file__), "..", ".."))

import click
from click.testing import CliRunner

from pdd.commands.modify import split, change, update


def _print_result(label: str, result) -> None:
    """Print a CliRunner result in a compact form."""
    print(f"--- {label} ---")
    print(f"  exit_code: {result.exit_code}")
    out = (result.output or "").strip()
    if out:
        for line in out.splitlines():
            print(f"  | {line}")
    if result.exception is not None and not isinstance(result.exception, SystemExit):
        print(f"  exception: {type(result.exception).__name__}: {result.exception}")
    print()


def example_split_legacy() -> None:
    """`pdd split --legacy PROMPT CODE EXAMPLE` delegates to split_main."""
    print("=" * 60)
    print("Example 1: split (legacy mode)")
    print("=" * 60)

    with tempfile.TemporaryDirectory() as tmp:
        tmp_path = Path(tmp)
        prompt = tmp_path / "prompt.txt"
        code = tmp_path / "code.py"
        example = tmp_path / "example.py"
        for p in (prompt, code, example):
            p.write_text("placeholder\n", encoding="utf-8")

        with patch("pdd.commands.modify.split_main") as mock_split_main:
            # split_main contract: (result_data, total_cost_usd, model_name)
            mock_split_main.return_value = (
                {"sub_prompt_content": "sub", "modified_prompt_content": "mod"},
                0.01,
                "mock-model",
            )

            runner = CliRunner()
            result = runner.invoke(
                split,
                [
                    "--legacy",
                    str(prompt),
                    str(code),
                    str(example),
                    "--output-sub",
                    str(tmp_path / "sub.prompt"),
                    "--output-modified",
                    str(tmp_path / "mod.prompt"),
                ],
                catch_exceptions=False,
            )

        _print_result("legacy split", result)
        print(f"  split_main called: {mock_split_main.called}")
        kwargs = mock_split_main.call_args.kwargs
        print(f"  forwarded input_prompt_file: {kwargs['input_prompt_file'] == str(prompt)}")
        print(f"  forwarded output_sub:        {kwargs['output_sub'].endswith('sub.prompt')}")
        print()


def example_split_agentic() -> None:
    """`pdd split TARGET_FILE` (agentic, default) delegates to run_agentic_split."""
    print("=" * 60)
    print("Example 2: split (agentic mode, default)")
    print("=" * 60)

    with tempfile.TemporaryDirectory() as tmp:
        target = Path(tmp) / "target.py"
        target.write_text("def f():\n    return 1\n", encoding="utf-8")

        with patch("pdd.commands.modify.run_agentic_split") as mock_agentic:
            # run_agentic_split contract:
            #   (success, message, cost_usd, model, changed_files)
            mock_agentic.return_value = (
                True,
                "Split complete",
                0.1234,
                "mock-model",
                [str(target)],
            )

            runner = CliRunner()
            result = runner.invoke(
                split,
                [str(target), "--intent", "reduce", "--no-phase-extraction"],
                catch_exceptions=False,
            )

        _print_result("agentic split", result)
        kwargs = mock_agentic.call_args.kwargs
        print(f"  intent forwarded:              {kwargs['intent']!r}")
        print(f"  no_phase_extraction forwarded: {kwargs['no_phase_extraction']}")
        print(f"  use_github_state default True: {kwargs['use_github_state']}")
        print()


def example_change_manual_standard() -> None:
    """`pdd change --manual CHANGE CODE PROMPT` (3 args) delegates to change_main."""
    print("=" * 60)
    print("Example 3: change (manual standard mode)")
    print("=" * 60)

    with tempfile.TemporaryDirectory() as tmp:
        tmp_path = Path(tmp)
        change_file = tmp_path / "change.prompt"
        code_file = tmp_path / "code.py"
        prompt_file = tmp_path / "input.prompt"
        for p in (change_file, code_file, prompt_file):
            p.write_text("placeholder\n", encoding="utf-8")

        with patch("pdd.commands.modify.change_main") as mock_change_main:
            mock_change_main.return_value = ("modified prompt body", 0.02, "mock-model")

            runner = CliRunner()
            result = runner.invoke(
                change,
                [
                    "--manual",
                    str(change_file),
                    str(code_file),
                    str(prompt_file),
                ],
                catch_exceptions=False,
            )

        _print_result("manual standard change", result)
        kwargs = mock_change_main.call_args.kwargs
        print(f"  use_csv: {kwargs['use_csv']}")
        print(f"  budget:  {kwargs['budget']}  (default 5.0)")
        print()


def example_change_manual_csv() -> None:
    """`pdd change --manual --csv CSV_FILE CODE_DIR` (2 args)."""
    print("=" * 60)
    print("Example 4: change (manual CSV batch mode)")
    print("=" * 60)

    with tempfile.TemporaryDirectory() as tmp:
        tmp_path = Path(tmp)
        csv_file = tmp_path / "batch.csv"
        csv_file.write_text("prompt_name,change_instructions\n", encoding="utf-8")
        code_dir = tmp_path / "src"
        code_dir.mkdir()

        with patch("pdd.commands.modify.change_main") as mock_change_main:
            mock_change_main.return_value = ("batch result", 0.04, "mock-model")

            runner = CliRunner()
            result = runner.invoke(
                change,
                ["--manual", "--csv", str(csv_file), str(code_dir)],
                catch_exceptions=False,
            )

        _print_result("manual CSV change", result)
        kwargs = mock_change_main.call_args.kwargs
        print(f"  use_csv: {kwargs['use_csv']}")
        print()


def example_change_agentic() -> None:
    """`pdd change ISSUE_URL` (agentic, default) delegates to run_agentic_change."""
    print("=" * 60)
    print("Example 5: change (agentic mode, default)")
    print("=" * 60)

    issue_url = "https://github.com/example/repo/issues/42"

    with patch("pdd.commands.modify.run_agentic_change") as mock_agentic:
        # run_agentic_change contract:
        #   (success, message, cost_usd, model, changed_files)
        mock_agentic.return_value = (
            True,
            "Change complete",
            0.5678,
            "mock-model",
            ["prompts/foo_python.prompt"],
        )

        runner = CliRunner()
        result = runner.invoke(
            change,
            [issue_url, "--no-github-state"],
            catch_exceptions=False,
        )

    _print_result("agentic change", result)
    kwargs = mock_agentic.call_args.kwargs
    print(f"  issue_url forwarded:    {kwargs['issue_url'] == issue_url}")
    print(f"  use_github_state=False: {kwargs['use_github_state'] is False}")
    print()


def example_update_repo_mode() -> None:
    """`pdd update` (no args) runs repo-wide update_main."""
    print("=" * 60)
    print("Example 6: update (repo-wide mode)")
    print("=" * 60)

    with patch("pdd.commands.modify.update_main") as mock_update_main:
        mock_update_main.return_value = ("repo updated", 0.0, "mock-model")

        runner = CliRunner()
        result = runner.invoke(update, [], catch_exceptions=False)

    _print_result("repo update", result)
    kwargs = mock_update_main.call_args.kwargs
    print(f"  repo:                {kwargs['repo']}")
    print(f"  input_prompt_file:   {kwargs['input_prompt_file']!r}")
    print(f"  modified_code_file:  {kwargs['modified_code_file']!r}")
    print(f"  base_branch default: {kwargs['base_branch']!r}")
    print(f"  sync_metadata:       {kwargs['sync_metadata']}")
    print()


def example_update_regeneration() -> None:
    """`pdd update CODE_FILE` (1 arg) runs regeneration mode."""
    print("=" * 60)
    print("Example 7: update (regeneration, 1 arg)")
    print("=" * 60)

    with patch("pdd.commands.modify.update_main") as mock_update_main:
        mock_update_main.return_value = ("regenerated prompt", 0.03, "mock-model")

        runner = CliRunner()
        result = runner.invoke(update, ["src/foo.py", "--sync-metadata"], catch_exceptions=False)

    _print_result("regeneration update", result)
    kwargs = mock_update_main.call_args.kwargs
    print(f"  repo:               {kwargs['repo']}")
    print(f"  modified_code_file: {kwargs['modified_code_file']!r}")
    print(f"  sync_metadata:      {kwargs['sync_metadata']}")
    print()


def example_update_git() -> None:
    """`pdd update --git PROMPT CODE` (2 args + --git)."""
    print("=" * 60)
    print("Example 8: update (git mode, 2 args + --git)")
    print("=" * 60)

    with patch("pdd.commands.modify.update_main") as mock_update_main:
        mock_update_main.return_value = ("git-updated prompt", 0.05, "mock-model")

        runner = CliRunner()
        result = runner.invoke(
            update,
            ["--git", "prompts/foo_python.prompt", "src/foo.py"],
            catch_exceptions=False,
        )

    _print_result("git update", result)
    kwargs = mock_update_main.call_args.kwargs
    print(f"  use_git:             {kwargs['use_git']}")
    print(f"  input_prompt_file:   {kwargs['input_prompt_file']!r}")
    print(f"  modified_code_file:  {kwargs['modified_code_file']!r}")
    print(f"  input_code_file:     {kwargs['input_code_file']!r}")
    print()


def example_update_validation_errors() -> None:
    """Demonstrate update's pre-try validation (UsageError surfaces as exit code 2)."""
    print("=" * 60)
    print("Example 9: update validation errors (no LLM calls)")
    print("=" * 60)

    runner = CliRunner()

    # 2 args without --git is invalid.
    result_a = runner.invoke(update, ["prompts/foo.prompt", "src/foo.py"])
    print(f"  '2 args without --git'  -> exit_code={result_a.exit_code} (expect 2)")

    # 3 args with --git is invalid.
    result_b = runner.invoke(update, ["--git", "p", "m", "o"])
    print(f"  '3 args with --git'     -> exit_code={result_b.exit_code} (expect 2)")

    # --all combined with paths is invalid.
    result_c = runner.invoke(update, ["--all", "src/foo.py"])
    print(f"  '--all + file path'     -> exit_code={result_c.exit_code} (expect 2)")

    # --budget <= 0 is invalid.
    result_d = runner.invoke(update, ["--budget", "0"])
    print(f"  '--budget 0'            -> exit_code={result_d.exit_code} (expect 2)")
    print()


def main() -> None:
    print("pdd.commands.modify -- Usage Examples")
    print()
    example_split_legacy()
    example_split_agentic()
    example_change_manual_standard()
    example_change_manual_csv()
    example_change_agentic()
    example_update_repo_mode()
    example_update_regeneration()
    example_update_git()
    example_update_validation_errors()
    print("All examples completed successfully.")


if __name__ == "__main__":
    main()
