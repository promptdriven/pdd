from __future__ import annotations

"""
Example demonstrating how to use pdd.update_main.

update_main is the CLI wrapper for updating prompts based on modified code.
It supports three modes:
  1. True update: prompt + code + (git OR original code) -> updated prompt
  2. Regeneration: only code file -> generate / regenerate prompt
  3. Repo mode: scan repo, detect changes, update changed pairs

Key public functions in pdd.update_main:
  - update_main(): Main entry point. Returns (prompt, cost_usd, model) or None.
  - resolve_prompt_code_pair(code_file_path: Path, quiet: bool, output_dir):
        Derive prompt path from code file path (creates dirs/empty file).
  - find_and_resolve_all_pairs(repo_root: Path, quiet, extensions, output_dir):
        Scan repo for all (prompt, code) pairs respecting exclusion rules.
  - get_git_changed_files(repo_root: Path, base_branch: str) -> Set[str]:
        Union of merge-base diff, uncommitted, staged, and untracked files.
  - derive_basename_and_language(code_file_path: Path, repo_root: Path):
        (basename, language) used as fingerprint key.
  - is_code_changed(code_file_path, repo_root, git_changed_files,
                    prompt_file_path=None) -> (bool, reason)
  - update_file_pair(prompt_file, code_file, ctx, repo, simple) -> dict

All costs are in USD (e.g. 0.05 means $0.05).
"""

import os
import sys
import tempfile
from pathlib import Path
from unittest.mock import patch, MagicMock

import click

# Ensure project root is importable when running standalone.
_PROJECT_ROOT = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(_PROJECT_ROOT))

from pdd.update_main import (  # noqa: E402
    resolve_prompt_code_pair,
    find_and_resolve_all_pairs,
    get_git_changed_files,
    derive_basename_and_language,
    is_code_changed,
    update_file_pair,
    update_main,
)


def _build_ctx(**overrides) -> click.Context:
    """Build a minimal Click context with a populated obj dict."""
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
    ctx.obj.update(overrides)
    return ctx


def example_resolve_prompt_code_pair() -> None:
    """Derive a prompt path from a code file, creating missing dirs/files."""
    print("=" * 60)
    print("Example 1: resolve_prompt_code_pair")
    print("=" * 60)

    with tempfile.TemporaryDirectory() as tmp:
        tmp_path = Path(tmp).resolve()
        (tmp_path / ".git").mkdir()  # fake repo root marker
        code_file = tmp_path / "src" / "calculator.py"
        code_file.parent.mkdir(parents=True, exist_ok=True)
        code_file.write_text("def add(a, b):\n    return a + b\n")

        prompt_path, code_path = resolve_prompt_code_pair(
            code_file, quiet=True
        )

        print(f"  code  : {code_path.relative_to(tmp_path)}")
        print(f"  prompt: {prompt_path.relative_to(tmp_path)}")
        print(f"  prompt exists: {prompt_path.exists()}")
    print()


def example_derive_basename_and_language() -> None:
    """Extract (basename, language) from a code path relative to the repo root."""
    print("=" * 60)
    print("Example 2: derive_basename_and_language")
    print("=" * 60)

    with tempfile.TemporaryDirectory() as tmp:
        tmp_path = Path(tmp).resolve()
        files = [
            tmp_path / "src" / "api" / "handler.py",
            tmp_path / "lib" / "utils.ts",
            tmp_path / "main.go",
        ]
        for f in files:
            f.parent.mkdir(parents=True, exist_ok=True)
            f.write_text("// stub\n")

        for f in files:
            basename, language = derive_basename_and_language(f, tmp_path)
            print(f"  {f.relative_to(tmp_path)}")
            print(f"    basename={basename!r}, language={language!r}")
    print()


def example_get_git_changed_files() -> None:
    """Combine merge-base diff, uncommitted, staged, and untracked files."""
    print("=" * 60)
    print("Example 3: get_git_changed_files (subprocess mocked)")
    print("=" * 60)

    with tempfile.TemporaryDirectory() as tmp:
        tmp_path = Path(tmp).resolve()

        def fake_run(cmd, **kwargs):
            res = MagicMock()
            res.returncode = 0
            res.stdout = ""
            args = list(cmd)
            if "merge-base" in args:
                res.stdout = "abc1234\n"
            elif args[2:4] == ["diff", "--name-only"]:
                # Either the merge-base diff or uncommitted/staged diff
                if len(args) >= 6 and args[4] == "abc1234":
                    res.stdout = "src/handler.py\n"
                elif "--staged" in args:
                    res.stdout = "lib/utils.ts\n"
                else:
                    res.stdout = "README.md\n"
            elif "ls-files" in args and "--others" in args:
                res.stdout = "new_file.py\n"
            return res

        with patch(
            "pdd.update_main.subprocess.run", side_effect=fake_run
        ):
            changed = get_git_changed_files(tmp_path, base_branch="main")

        print(f"  Changed files: {len(changed)}")
        for f in sorted(changed):
            try:
                rel = Path(f).relative_to(tmp_path)
            except ValueError:
                rel = Path(f)
            print(f"    {rel}")
    print()


def example_is_code_changed() -> None:
    """Decide whether a code file should be re-synced."""
    print("=" * 60)
    print("Example 4: is_code_changed")
    print("=" * 60)

    with tempfile.TemporaryDirectory() as tmp:
        tmp_path = Path(tmp).resolve()
        code_file = tmp_path / "module.py"
        code_file.write_text("def hello(): pass\n")

        # No fingerprint, in git changed set -> changed=True
        with patch("pdd.update_main._load_fingerprint", return_value=None):
            changed, reason = is_code_changed(
                code_file, tmp_path,
                git_changed_files={str(code_file.resolve())},
            )
        print(f"  no fingerprint + in git set : changed={changed}, "
              f"reason={reason!r}")

        # No fingerprint, NOT in git changed set -> changed=False
        with patch("pdd.update_main._load_fingerprint", return_value=None):
            changed, reason = is_code_changed(
                code_file, tmp_path, git_changed_files=set(),
            )
        print(f"  no fingerprint + not in set : changed={changed}, "
              f"reason={reason!r}")

        # Fingerprint with matching hash -> changed=False
        import hashlib
        current = hashlib.sha256(code_file.read_bytes()).hexdigest()
        with patch(
            "pdd.update_main._load_fingerprint",
            return_value={"code_hash": current, "include_deps": {}},
        ):
            changed, reason = is_code_changed(
                code_file, tmp_path, git_changed_files=set(),
            )
        print(f"  fingerprint matches         : changed={changed}, "
              f"reason={reason!r}")

        # Fingerprint with mismatched hash -> changed=True
        with patch(
            "pdd.update_main._load_fingerprint",
            return_value={"code_hash": "deadbeef", "include_deps": {}},
        ):
            changed, reason = is_code_changed(
                code_file, tmp_path, git_changed_files=set(),
            )
        print(f"  fingerprint mismatched      : changed={changed}, "
              f"reason={reason!r}")
    print()


def example_update_main_regeneration() -> None:
    """Regeneration mode: only modified_code_file is supplied."""
    print("=" * 60)
    print("Example 5: update_main -- regeneration mode")
    print("=" * 60)

    with tempfile.TemporaryDirectory() as tmp:
        tmp_path = Path(tmp).resolve()
        (tmp_path / ".git").mkdir()
        code_file = tmp_path / "calculator.py"
        code_file.write_text(
            "def add(a: int, b: int) -> int:\n    return a + b\n"
        )

        ctx = _build_ctx()
        mock_prompt = "% Goal\nImplement add and subtract functions."

        with patch(
            "pdd.update_main.update_prompt",
            return_value=(mock_prompt, 0.03, "mock-llm"),
        ), patch(
            "pdd.update_main._try_agentic_update", return_value=None
        ), patch(
            "pdd.update_main._save_fingerprint_safe"
        ):
            result = update_main(
                ctx=ctx,
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

        if result:
            prompt_text, cost, model = result
            print(f"  prompt: {prompt_text!r}")
            print(f"  cost  : ${cost:.4f}")
            print(f"  model : {model}")
        else:
            print("  Result: None (error)")
    print()


def example_update_main_true_update_with_git() -> None:
    """True update mode using --use-git."""
    print("=" * 60)
    print("Example 6: update_main -- true update (use_git=True)")
    print("=" * 60)

    with tempfile.TemporaryDirectory() as tmp:
        tmp_path = Path(tmp).resolve()
        prompt_file = tmp_path / "calc_python.prompt"
        prompt_file.write_text("% Goal\nImplement add function.")
        code_file = tmp_path / "calc.py"
        code_file.write_text(
            "def add(a, b): return a + b\n"
            "def mul(a, b): return a * b\n"
        )

        ctx = _build_ctx()
        updated_prompt = "% Goal\nImplement add and mul functions."

        with patch(
            "pdd.update_main.git_update",
            return_value=(updated_prompt, 0.05, "mock-git-llm"),
        ), patch(
            "pdd.update_main._try_agentic_update", return_value=None
        ), patch(
            "pdd.update_main._save_fingerprint_safe"
        ), patch(
            "pdd.update_main.construct_paths"
        ):
            result = update_main(
                ctx=ctx,
                input_prompt_file=str(prompt_file),
                modified_code_file=str(code_file),
                input_code_file=None,
                output=None,
                use_git=True,
                repo=False,
                extensions=None,
                directory=None,
                strength=None,
                temperature=None,
                simple=True,
            )

        if result:
            text, cost, model = result
            print(f"  prompt: {text!r}")
            print(f"  cost  : ${cost:.4f}")
            print(f"  model : {model}")
        else:
            print("  Result: None (error)")
    print()


def example_update_main_true_update_with_input_code() -> None:
    """True update mode using --input-code-file (no git)."""
    print("=" * 60)
    print("Example 7: update_main -- true update (input_code_file)")
    print("=" * 60)

    with tempfile.TemporaryDirectory() as tmp:
        tmp_path = Path(tmp).resolve()
        prompt_file = tmp_path / "demo_python.prompt"
        prompt_file.write_text("% Goal\nAdd two numbers.")
        original_code = tmp_path / "demo_orig.py"
        original_code.write_text("def add(a, b): return a + b\n")
        modified_code = tmp_path / "demo.py"
        modified_code.write_text("def mul(a, b): return a * b\n")

        ctx = _build_ctx()
        updated_prompt = "% Goal\nMultiply two numbers."

        with patch(
            "pdd.update_main.update_prompt",
            return_value=(updated_prompt, 0.02, "mock-llm"),
        ), patch(
            "pdd.update_main._try_agentic_update", return_value=None
        ), patch(
            "pdd.update_main._save_fingerprint_safe"
        ), patch(
            "pdd.update_main.construct_paths"
        ):
            result = update_main(
                ctx=ctx,
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

        if result:
            text, cost, model = result
            print(f"  prompt: {text!r}")
            print(f"  cost  : ${cost:.4f}")
            print(f"  model : {model}")
        else:
            print("  Result: None (error)")
    print()


def example_mutual_exclusion() -> None:
    """use_git and input_code_file are mutually exclusive -> returns None."""
    print("=" * 60)
    print("Example 8: mutual exclusion (use_git + input_code_file)")
    print("=" * 60)

    with tempfile.TemporaryDirectory() as tmp:
        tmp_path = Path(tmp).resolve()
        prompt_file = tmp_path / "p.prompt"
        prompt_file.write_text("x")
        code_file = tmp_path / "c.py"
        code_file.write_text("x")
        ic_file = tmp_path / "ic.py"
        ic_file.write_text("x")

        ctx = _build_ctx(quiet=True)

        result = update_main(
            ctx=ctx,
            input_prompt_file=str(prompt_file),
            modified_code_file=str(code_file),
            input_code_file=str(ic_file),
            output=None,
            use_git=True,
            repo=False,
            extensions=None,
            directory=None,
            strength=None,
            temperature=None,
            simple=True,
        )
        print(f"  result: {result} (expected None)")
    print()


def example_update_file_pair() -> None:
    """Single-pair update returning a result dict."""
    print("=" * 60)
    print("Example 9: update_file_pair (legacy path)")
    print("=" * 60)

    with tempfile.TemporaryDirectory() as tmp:
        tmp_path = Path(tmp).resolve()
        prompt_file = tmp_path / "mod_python.prompt"
        prompt_file.write_text("% existing prompt content")
        code_file = tmp_path / "mod.py"
        code_file.write_text("def foo(): return 1\n")

        ctx = _build_ctx()

        with patch(
            "pdd.update_main.git_update",
            return_value=("% new content", 0.02, "mock-llm"),
        ), patch(
            "pdd.update_main._try_agentic_update", return_value=None
        ), patch(
            "pdd.update_main._save_fingerprint_safe"
        ):
            res = update_file_pair(
                prompt_file, code_file, ctx, repo=False, simple=True,
            )

        for k, v in res.items():
            print(f"  {k}: {v}")
    print()


def example_repo_mode() -> None:
    """Repo mode: scan, detect changes, update."""
    print("=" * 60)
    print("Example 10: update_main -- repo mode")
    print("=" * 60)

    with tempfile.TemporaryDirectory() as tmp:
        tmp_path = Path(tmp).resolve()
        (tmp_path / ".git").mkdir()
        code_file = tmp_path / "src" / "handler.py"
        code_file.parent.mkdir(parents=True)
        code_file.write_text("def handle(): pass\n")
        prompt_file = tmp_path / "prompts" / "handler_python.prompt"
        prompt_file.parent.mkdir(parents=True)
        prompt_file.write_text("")  # empty triggers update regardless

        ctx = _build_ctx()
        update_result = {
            "prompt_file": str(prompt_file),
            "code_file": str(code_file),
            "status": "updated (legacy)",
            "cost": 0.04,
            "model": "mock-llm",
            "error": "",
        }

        with patch(
            "pdd.update_main.find_and_resolve_all_pairs",
            return_value=[(prompt_file, code_file)],
        ), patch(
            "pdd.update_main.get_git_changed_files",
            return_value={str(code_file)},
        ), patch(
            "pdd.update_main.update_file_pair", return_value=update_result
        ):
            result = update_main(
                ctx=ctx,
                input_prompt_file=None,
                modified_code_file=None,
                input_code_file=None,
                output=None,
                use_git=False,
                repo=True,
                extensions=None,
                directory=str(tmp_path),
                strength=None,
                temperature=None,
                simple=True,
            )

        if result:
            msg, cost, models = result
            print(f"  message    : {msg}")
            print(f"  total cost : ${cost:.4f}")
            print(f"  models     : {models}")
        else:
            print("  Result: None (no changes)")
    print()


def example_find_and_resolve_all_pairs() -> None:
    """Walk a tiny repo and resolve eligible code/prompt pairs."""
    print("=" * 60)
    print("Example 11: find_and_resolve_all_pairs")
    print("=" * 60)

    with tempfile.TemporaryDirectory() as tmp:
        tmp_path = Path(tmp).resolve()
        (tmp_path / ".git").mkdir()
        # Eligible
        good = tmp_path / "src" / "module.py"
        good.parent.mkdir(parents=True)
        good.write_text("def func(): return 1\n")
        # Excluded — test_ prefix
        skip_test = tmp_path / "src" / "test_module.py"
        skip_test.write_text("def test_thing(): pass\n")
        # Excluded — *_example suffix
        skip_example = tmp_path / "src" / "module_example.py"
        skip_example.write_text("def demo(): pass\n")
        # Excluded — config suffix
        skip_config = tmp_path / "jest.config.js"
        skip_config.write_text("module.exports = {};\n")
        # Excluded — markdown
        skip_md = tmp_path / "README.md"
        skip_md.write_text("# hello\n")

        # Force os.walk fallback (no real git available)
        with patch("pdd.update_main._git_ls_files", return_value=None):
            pairs = find_and_resolve_all_pairs(
                tmp_path, quiet=True, extensions=None, output_dir=None,
            )

        print(f"  pairs found: {len(pairs)}")
        for prompt_p, code_p in pairs:
            print(f"    code   : {code_p.relative_to(tmp_path)}")
            print(f"    prompt : {prompt_p.relative_to(tmp_path)}")
    print()


def main() -> None:
    print("pdd.update_main -- Usage Examples")
    print("=" * 60)
    print()

    example_resolve_prompt_code_pair()
    example_derive_basename_and_language()
    example_get_git_changed_files()
    example_is_code_changed()
    example_update_main_regeneration()
    example_update_main_true_update_with_git()
    example_update_main_true_update_with_input_code()
    example_mutual_exclusion()
    example_update_file_pair()
    example_repo_mode()
    example_find_and_resolve_all_pairs()

    print("All examples completed successfully.")


if __name__ == "__main__":
    main()
