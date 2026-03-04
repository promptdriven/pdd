#!/usr/bin/env python
"""
Example: Using the `pdd extracts prune` CLI command
=======================================================

This module demonstrates how to invoke the ``extracts prune`` subcommand
programmatically and from the command line.

Overview
--------
The ``extracts prune`` command scans every ``.prompt`` file in your project
for ``<include path="..." query="...">`` tags, determines which
``.pdd/extracts/`` entries are still referenced, and deletes any orphaned
cache files (``.md`` + ``.meta.json``).

Command-line usage
------------------
    # Interactive mode – shows a table of orphaned entries and asks for
    # confirmation before deleting:
    pdd extracts prune

    # Non-interactive mode – skip the confirmation prompt:
    pdd extracts prune --force

Programmatic usage (Click testing / CliRunner)
----------------------------------------------
See the code below for how to invoke the command via Click's ``CliRunner``,
which is useful for integration tests or scripted workflows.

Directory layout assumed by the command
---------------------------------------
    <project_root>/
    └── .pdd/
    │   └── extracts/
    │       └── <cache_key>.md            # extracted content
    │       └── <cache_key>.meta.json     # metadata (source_path, query, …)
    └── prompts/
    │   └── example.prompt                # contains <include … query="…"> tags
    └── src/
        └── app.py                        # source file referenced by include tags

Cache key formula
-----------------
    cache_key = sha256(resolved_source_path + "\\n" + query).hexdigest()

Parameters & flags
------------------
    --force : bool, default False
        When set, orphaned entries are deleted without an interactive
        confirmation prompt.  The global ``--force`` flag (``ctx.obj["force"]``)
        is also honoured.

Output
------
    - A rich table (or plain-text fallback) listing each orphaned entry's
      truncated cache key, source path, and query text.
    - A summary line: "Pruned N orphaned cache entry/entries."
    - If the cache directory is missing or empty, an informational message
      is printed and the command exits cleanly.
"""

from __future__ import annotations

import hashlib
import json
import os
import tempfile
from pathlib import Path

from click.testing import CliRunner


# ---------------------------------------------------------------------------
# Helper: set up a realistic temporary project so the command has something
# to work with.  In real usage you would simply run ``pdd extracts prune``
# inside your project directory.
# ---------------------------------------------------------------------------

def _setup_sample_project(tmp: Path) -> tuple[str, str]:
    """
    Create a minimal project tree with one .prompt file, one source file,
    and two cache entries – one referenced and one orphaned.

    Returns
    -------
    referenced_key : str
        The cache key that *is* referenced by the prompt file.
    orphaned_key : str
        The cache key that is *not* referenced (should be pruned).
    """
    # Source file referenced by the prompt
    src = tmp / "src" / "app.py"
    src.parent.mkdir(parents=True, exist_ok=True)
    src.write_text("def main(): pass\n", encoding="utf-8")

    # Prompt file with an <include> tag that has a query attribute
    prompts_dir = tmp / "prompts"
    prompts_dir.mkdir(parents=True, exist_ok=True)
    prompt_file = prompts_dir / "example.prompt"
    prompt_file.write_text(
        '<include path="../src/app.py" query="Explain the main function" />\n',
        encoding="utf-8",
    )

    # Cache directory
    cache_dir = tmp / ".pdd" / "extracts"
    cache_dir.mkdir(parents=True, exist_ok=True)

    # Compute the referenced cache key (same formula the real code uses)
    resolved_path = str(src.resolve())
    query = "Explain the main function"
    referenced_key = hashlib.sha256(
        (resolved_path + "\n" + query).encode()
    ).hexdigest()

    # Write the referenced cache entry
    (cache_dir / f"{referenced_key}.md").write_text(
        "# Explanation\n`main` does nothing yet.\n", encoding="utf-8"
    )
    (cache_dir / f"{referenced_key}.meta.json").write_text(
        json.dumps({
            "source_path": resolved_path,
            "query": query,
            "source_hash": "abc123",
            "timestamp": "2025-01-01T00:00:00Z",
            "token_count": 12,
        }),
        encoding="utf-8",
    )

    # Write an orphaned cache entry (not referenced by any prompt)
    orphaned_key = hashlib.sha256(b"old/file.py\nsome old query").hexdigest()
    (cache_dir / f"{orphaned_key}.md").write_text(
        "Stale content.\n", encoding="utf-8"
    )
    (cache_dir / f"{orphaned_key}.meta.json").write_text(
        json.dumps({
            "source_path": "old/file.py",
            "query": "some old query",
            "source_hash": "def456",
            "timestamp": "2024-06-15T12:00:00Z",
            "token_count": 5,
        }),
        encoding="utf-8",
    )

    return referenced_key, orphaned_key


# ---------------------------------------------------------------------------
# Example 1: Invoke via Click's CliRunner (useful in tests / scripts)
# ---------------------------------------------------------------------------

def example_prune_with_cli_runner():
    """
    Demonstrate invoking ``extracts prune --force`` programmatically.

    This is the recommended approach for integration tests.  The CliRunner
    captures stdout/stderr so you can assert on the output.
    """
    # We import the click group defined in the module.
    # In a real project this import path would be:
    #     from pdd.commands.extracts import extracts
    # Here we import it directly since we're demonstrating usage.
    try:
        from pdd.commands.extracts import extracts
    except ImportError:
        print(
            "Could not import pdd.commands.extracts – "
            "make sure the pdd package is installed or on PYTHONPATH."
        )
        return

    runner = CliRunner()

    with tempfile.TemporaryDirectory() as tmp_str:
        tmp = Path(tmp_str)
        referenced_key, orphaned_key = _setup_sample_project(tmp)

        cache_dir = tmp / ".pdd" / "extracts"

        # Patch the working directory so get_config() picks up project_root
        old_cwd = os.getcwd()
        os.chdir(tmp)
        try:
            # Invoke the prune subcommand with --force to skip confirmation
            result = runner.invoke(
                extracts,
                ["prune", "--force"],
                obj={"force": False},  # ctx.obj must be a dict
                catch_exceptions=False,
            )
        finally:
            os.chdir(old_cwd)

        # ---- Inspect results ----
        print("Exit code:", result.exit_code)
        print("Output:\n", result.output)

        # The orphaned .md and .meta.json should be gone
        orphaned_md = cache_dir / f"{orphaned_key}.md"
        orphaned_meta = cache_dir / f"{orphaned_key}.meta.json"
        print(f"Orphaned .md   still exists? {orphaned_md.exists()}")   # False
        print(f"Orphaned .meta still exists? {orphaned_meta.exists()}") # False

        # The referenced entry should still be present
        ref_md = cache_dir / f"{referenced_key}.md"
        print(f"Referenced .md still exists? {ref_md.exists()}")        # True


# ---------------------------------------------------------------------------
# Example 2: Show how to call the internal helpers directly
# ---------------------------------------------------------------------------

def example_inspect_orphans():
    """
    Demonstrate using the internal helpers to list orphaned cache keys
    without deleting anything.  Useful for dry-run / audit scripts.
    """
    try:
        from pdd.commands.extracts import (
            _cache_dir,
            _collect_referenced_keys,
        )
        from pdd.config import get_config
    except ImportError:
        print(
            "Could not import pdd internals – "
            "make sure the pdd package is installed or on PYTHONPATH."
        )
        return

    with tempfile.TemporaryDirectory() as tmp_str:
        tmp = Path(tmp_str)
        _setup_sample_project(tmp)

        old_cwd = os.getcwd()
        os.chdir(tmp)
        try:
            cfg = get_config()
            project_root = Path(cfg.get("project_root", ".")).resolve()

            # Collect referenced keys from all .prompt files
            referenced = _collect_referenced_keys(project_root)
            print(f"Referenced cache keys ({len(referenced)}):")
            for k in sorted(referenced):
                print(f"  {k[:16]}…")

            # List keys on disk
            cache = _cache_dir()
            if cache is not None:
                on_disk = {p.stem for p in cache.glob("*.md")}
                orphaned = sorted(on_disk - referenced)
                print(f"\nOrphaned cache keys ({len(orphaned)}):")
                for k in orphaned:
                    meta_path = cache / f"{k}.meta.json"
                    if meta_path.exists():
                        meta = json.loads(meta_path.read_text(encoding="utf-8"))
                        print(f"  {k[:16]}…  src={meta.get('source_path')}  "
                              f"query={meta.get('query')}")
                    else:
                        print(f"  {k[:16]}…  (no metadata)")
        finally:
            os.chdir(old_cwd)


# ---------------------------------------------------------------------------
# Main
# ---------------------------------------------------------------------------

if __name__ == "__main__":
    print("=" * 70)
    print("Example 1: Prune orphaned cache entries via CliRunner")
    print("=" * 70)
    example_prune_with_cli_runner()

    print()
    print("=" * 70)
    print("Example 2: Inspect orphaned keys without deleting")
    print("=" * 70)
    example_inspect_orphans()
