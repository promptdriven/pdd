"""
Example usage of change-detection functions (now in update_main).

Demonstrates the core logic of change detection used by `pdd update` in
repo-wide mode, which scans a repo for changed code files and reverse-syncs
them back into their prompt files using `update_file_pair`.

This example mocks Git operations, fingerprint lookups, and the update
pipeline so it can run without a real repository or LLM calls.

Run:
    python context/sync_code_main_example.py
"""

import hashlib
import os
import shutil
from dataclasses import dataclass
from pathlib import Path
from typing import Optional
from unittest.mock import MagicMock, patch

import click
from rich.console import Console

from pdd.update_main import (
    derive_basename_and_language,
    get_git_changed_files,
    is_code_changed,
    update_main,
)

console = Console()


# ---------------------------------------------------------------------------
# Helpers
# ---------------------------------------------------------------------------

def _sha256(text: str) -> str:
    """Return the SHA-256 hex digest of a string."""
    return hashlib.sha256(text.encode("utf-8")).hexdigest()


def _write(path: Path, content: str) -> None:
    """Write *content* to *path*, creating parent directories as needed."""
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(content, encoding="utf-8")


@dataclass
class FakeFingerprint:
    """Minimal stand-in for the real Fingerprint dataclass."""
    code_hash: Optional[str] = None


# ---------------------------------------------------------------------------
# Scenario 1 – derive_basename_and_language
# ---------------------------------------------------------------------------

def demo_derive_basename_and_language() -> None:
    """Show how derive_basename_and_language extracts stem + language."""
    console.rule("[bold green]1. derive_basename_and_language[/bold green]")

    samples = [
        "/repo/src/calculator.py",
        "/repo/src/utils.js",
        "/repo/docs/README.md",       # unknown extension
        "/repo/src/server.ts",
    ]
    for path in samples:
        basename, lang = derive_basename_and_language(path, "/repo")
        print(f"  {path:40s} -> basename={basename!r:15s} language={lang!r}")
    print()


# ---------------------------------------------------------------------------
# Scenario 2 – is_code_changed (fingerprint vs git fallback)
# ---------------------------------------------------------------------------

def demo_is_code_changed(output_dir: Path) -> None:
    """Demonstrate the two change-detection strategies."""
    console.rule("[bold green]2. is_code_changed[/bold green]")

    code_file = output_dir / "calculator.py"
    code_content = "def add(a, b): return a + b\n"
    _write(code_file, code_content)

    code_path = str(code_file)
    repo_root = str(output_dir)

    # 2a – Fingerprint hash matches -> not changed
    matching_fp = FakeFingerprint(code_hash=_sha256(code_content))
    with patch("pdd.update_main.read_fingerprint", return_value=matching_fp):
        changed, reason = is_code_changed(code_path, repo_root, set())
    print(f"  2a  hash matches fingerprint:   changed={changed}  reason={reason!r}")

    # 2b – Fingerprint hash differs -> changed
    stale_fp = FakeFingerprint(code_hash="stale_hash_000")
    with patch("pdd.update_main.read_fingerprint", return_value=stale_fp):
        changed, reason = is_code_changed(code_path, repo_root, set())
    print(f"  2b  hash differs from fingerprint: changed={changed}  reason={reason!r}")

    # 2c – No fingerprint, file in git changed set -> changed
    with patch("pdd.update_main.read_fingerprint", return_value=None):
        changed, reason = is_code_changed(
            code_path, repo_root, {os.path.abspath(code_path)}
        )
    print(f"  2c  no fingerprint, in git set: changed={changed}  reason={reason!r}")

    # 2d – No fingerprint, file NOT in git changed set -> not changed
    with patch("pdd.update_main.read_fingerprint", return_value=None):
        changed, reason = is_code_changed(code_path, repo_root, set())
    print(f"  2d  no fingerprint, not in git: changed={changed}  reason={reason!r}")
    print()


# ---------------------------------------------------------------------------
# Scenario 3 – full update_main repo-mode pipeline (mocked)
# ---------------------------------------------------------------------------

def demo_update_main_repo_mode(output_dir: Path) -> None:
    """Run the full update_main in repo mode with mocked dependencies."""
    console.rule("[bold green]3. update_main repo-mode (full pipeline)[/bold green]")

    # Create mock project files
    prompts_dir = output_dir / "prompts"
    _write(prompts_dir / "calculator_python.prompt", "Create an add function.")
    _write(output_dir / "calculator.py", "def add(a, b): return a + b\n")
    _write(prompts_dir / "utils_python.prompt", "Create utility helpers.")
    _write(output_dir / "utils.py", "def clamp(v, lo, hi): return max(lo, min(hi, v))\n")

    # Build a Click context
    ctx = click.Context(click.Command("update"))
    ctx.obj = {
        "strength": 0.5,
        "temperature": 0.1,
        "verbose": False,
        "quiet": False,
        "force": False,
    }

    # Mock pairs returned by find_and_resolve_all_pairs
    mock_pairs = [
        (str(prompts_dir / "calculator_python.prompt"), str(output_dir / "calculator.py")),
        (str(prompts_dir / "utils_python.prompt"), str(output_dir / "utils.py")),
    ]

    # Mock update_file_pair to simulate successful update results
    def fake_update_file_pair(prompt_path, code_path, ctx, repo, simple=False):
        """Return a fake result dict mimicking update_file_pair output."""
        return {
            "prompt_file": prompt_path,
            "status": "updated",
            "cost": 0.012,
            "model": "mock-model-v1",
            "error": "",
        }

    # Mock is_code_changed to mark only calculator as changed
    def fake_is_code_changed(code_path, repo_root, git_changed):
        """Only calculator.py is considered changed."""
        if "calculator" in code_path:
            return True, "code hash differs from fingerprint"
        return False, "code hash matches fingerprint"

    # Mock git.Repo to avoid needing a real repo
    mock_repo = MagicMock()
    mock_repo.working_tree_dir = str(output_dir)

    patches = [
        patch("pdd.update_main.git.Repo", return_value=mock_repo),
        patch("pdd.update_main.find_and_resolve_all_pairs", return_value=mock_pairs),
        patch("pdd.update_main.get_git_changed_files", return_value=set()),
        patch("pdd.update_main.is_code_changed", side_effect=fake_is_code_changed),
        patch("pdd.update_main.update_file_pair", side_effect=fake_update_file_pair),
        patch("pdd.update_main.update_architecture_from_prompt", return_value={"success": False, "updated": False, "changes": {}}),
    ]
    for p in patches:
        p.start()
    try:
        result = update_main(
            ctx=ctx,
            input_prompt_file=None,
            modified_code_file=None,
            input_code_file=None,
            output=None,
            repo=True,
            base_branch="main",
        )
    finally:
        for p in patches:
            p.stop()

    if result is not None:
        summary, total_cost, models = result
        print(f"\n  Summary:    {summary}")
        print(f"  Total cost: ${total_cost:.6f}")
        print(f"  Models:     {models}")
    else:
        print("\n  No changes detected (result is None).")
    print()


# ---------------------------------------------------------------------------
# Main
# ---------------------------------------------------------------------------

def main() -> None:
    """Run all examples."""
    output_dir = Path("./output").resolve()
    if output_dir.exists():
        shutil.rmtree(output_dir)
    output_dir.mkdir(parents=True)

    demo_derive_basename_and_language()
    demo_is_code_changed(output_dir)
    demo_update_main_repo_mode(output_dir)

    # Cleanup
    shutil.rmtree(output_dir, ignore_errors=True)
    console.rule("[bold blue]Done[/bold blue]")


if __name__ == "__main__":
    main()
