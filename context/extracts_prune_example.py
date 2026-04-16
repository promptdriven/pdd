#!/usr/bin/env python
"""
Example: Using the `pdd extracts prune` CLI command
=======================================================

This module demonstrates how to invoke the ``extracts prune`` subcommand
programmatically and from the command line.

Overview
--------
The ``extracts prune`` command scans every ``.prompt`` file in your project
for ``<include query="...">file</include>`` tags, determines which
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
    │   └── example.prompt                # contains <include query="…">…</include> tags
    └── src/
        └── app.py                        # source file referenced by include tags

Cache key formula
-----------------
    cache_key = sha256(normpath(project_relative_source_path) + "\\n" + query).hexdigest()

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

Requirements demonstrated
-------------------------
1. Structure: ``extracts`` (click group) + ``prune`` (subcommand)
2. Scanning: Scans .prompt files for include tags with queries
3. Cache Keys: Uses project-relative path before hashing
4. Orphans: Identifies .md files not in the referenced set
5. Display: Shows table with Key, Source Path, Query from .meta.json
6. Safety: Prompts for confirmation; --force and ctx.obj["force"] skip it
7. Deletion: Removes both .md and .meta.json for each orphan
8. Testing Support: try/except ImportError stubs for pdd imports
"""

from __future__ import annotations

import hashlib
import json
import os
import sys
import tempfile
from pathlib import Path
from unittest.mock import patch

sys.path.insert(0, os.path.abspath(os.path.join(os.path.dirname(__file__), "..")))

from click.testing import CliRunner


# ---------------------------------------------------------------------------
# Helper: set up a realistic temporary project
# ---------------------------------------------------------------------------

def _setup_sample_project(tmp: Path) -> tuple[str, str]:
    """
    Create a minimal project tree with one .prompt file, one source file,
    and two cache entries – one referenced and one orphaned.

    Returns (referenced_key, orphaned_key).
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
        '<include query="Explain the main function">../src/app.py</include>\n',
        encoding="utf-8",
    )

    # Cache directory
    cache_dir = tmp / ".pdd" / "extracts"
    cache_dir.mkdir(parents=True, exist_ok=True)

    # Compute the referenced cache key using project-relative path
    resolved_path = src.resolve()
    relative_path = str(resolved_path.relative_to(tmp.resolve()))
    query = "Explain the main function"
    referenced_key = hashlib.sha256(
        (os.path.normpath(relative_path) + "\n" + query).encode()
    ).hexdigest()

    # Write the referenced cache entry
    (cache_dir / f"{referenced_key}.md").write_text(
        "# Explanation\n`main` does nothing yet.\n", encoding="utf-8"
    )
    (cache_dir / f"{referenced_key}.meta.json").write_text(
        json.dumps({
            "source_path": relative_path,
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
# Example 1: Prune with --force (Req 1, 2, 3, 4, 5, 6, 7)
# ---------------------------------------------------------------------------

def example_prune_with_force():
    """
    Invoke ``extracts prune --force`` via CliRunner.

    Demonstrates:
    - Structure: extracts group + prune subcommand (Req 1)
    - Scanning: .prompt files are scanned for include tags (Req 2)
    - Cache Keys: project-relative paths are used for hashing (Req 3)
    - Orphans: unreferenced entries are identified (Req 4)
    - Display: orphaned entries shown in a table (Req 5)
    - Safety: --force skips confirmation (Req 6)
    - Deletion: both .md and .meta.json are removed (Req 7)
    """
    from pdd.extracts_prune import extracts

    runner = CliRunner()

    with tempfile.TemporaryDirectory() as tmp_str:
        tmp = Path(tmp_str)
        referenced_key, orphaned_key = _setup_sample_project(tmp)
        cache_dir = tmp / ".pdd" / "extracts"

        with patch(
            "pdd.extracts_prune.find_project_root_from_path",
            return_value=str(tmp),
        ):
            result = runner.invoke(
                extracts,
                ["prune", "--force"],
                obj={"force": False},
                catch_exceptions=False,
            )

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
# Example 2: Interactive confirmation (Req 6 – safety prompt)
# ---------------------------------------------------------------------------

def example_prune_interactive():
    """
    Invoke ``extracts prune`` without --force, simulating user confirmation.

    Demonstrates the safety prompt requirement (Req 6).
    """
    from pdd.extracts_prune import extracts

    runner = CliRunner()

    with tempfile.TemporaryDirectory() as tmp_str:
        tmp = Path(tmp_str)
        _setup_sample_project(tmp)

        with patch(
            "pdd.extracts_prune.find_project_root_from_path",
            return_value=str(tmp),
        ):
            # Simulate user typing "y" at the confirmation prompt
            result = runner.invoke(
                extracts,
                ["prune"],
                input="y\n",
                obj={"force": False},
                catch_exceptions=False,
            )

        print("Exit code:", result.exit_code)
        print("Output:\n", result.output)


# ---------------------------------------------------------------------------
# Example 3: Global --force via ctx.obj (Req 6)
# ---------------------------------------------------------------------------

def example_prune_global_force():
    """
    Invoke ``extracts prune`` with ctx.obj["force"]=True (global force flag).

    Demonstrates that the global force flag also skips confirmation (Req 6).
    """
    from pdd.extracts_prune import extracts

    runner = CliRunner()

    with tempfile.TemporaryDirectory() as tmp_str:
        tmp = Path(tmp_str)
        _, orphaned_key = _setup_sample_project(tmp)
        cache_dir = tmp / ".pdd" / "extracts"

        with patch(
            "pdd.extracts_prune.find_project_root_from_path",
            return_value=str(tmp),
        ):
            result = runner.invoke(
                extracts,
                ["prune"],
                obj={"force": True},  # global force
                catch_exceptions=False,
            )

        print("Exit code:", result.exit_code)
        print("Output:\n", result.output)
        print(f"Orphaned entry deleted? {not (cache_dir / f'{orphaned_key}.md').exists()}")


# ---------------------------------------------------------------------------
# Example 4: Empty/missing cache (Req 4 – early exit)
# ---------------------------------------------------------------------------

def example_prune_no_cache():
    """
    Invoke ``extracts prune`` when there is no .pdd/extracts/ directory.

    Demonstrates clean early exit when there's nothing to prune.
    """
    from pdd.extracts_prune import extracts

    runner = CliRunner()

    with tempfile.TemporaryDirectory() as tmp_str:
        tmp = Path(tmp_str)

        with patch(
            "pdd.extracts_prune.find_project_root_from_path",
            return_value=str(tmp),
        ):
            result = runner.invoke(
                extracts,
                ["prune"],
                obj={"force": False},
                catch_exceptions=False,
            )

        print("Exit code:", result.exit_code)
        print("Output:\n", result.output)


# ---------------------------------------------------------------------------
# Example 5: Inspect orphans using internal helpers (Req 2, 3, 4)
# ---------------------------------------------------------------------------

def example_inspect_orphans():
    """
    Use internal helpers to list orphaned cache keys without deleting.
    Useful for dry-run / audit scripts.
    """
    from pdd.extracts_prune import _cache_dir, _collect_referenced_keys

    with tempfile.TemporaryDirectory() as tmp_str:
        tmp = Path(tmp_str)
        _setup_sample_project(tmp)

        with patch(
            "pdd.extracts_prune.find_project_root_from_path",
            return_value=str(tmp),
        ):
            project_root = tmp.resolve()

            # Collect referenced keys from all .prompt files (Req 2, 3)
            referenced = _collect_referenced_keys(project_root)
            print(f"Referenced cache keys ({len(referenced)}):")
            for k in sorted(referenced):
                print(f"  {k[:16]}...")

            # List keys on disk (Req 4)
            cache = _cache_dir()
            if cache is not None:
                on_disk = {p.stem for p in cache.glob("*.md")}
                orphaned = sorted(on_disk - referenced)
                print(f"\nOrphaned cache keys ({len(orphaned)}):")
                for k in orphaned:
                    meta_path = cache / f"{k}.meta.json"
                    if meta_path.exists():
                        meta = json.loads(meta_path.read_text(encoding="utf-8"))
                        print(f"  {k[:16]}...  src={meta.get('source_path')}  "
                              f"query={meta.get('query')}")
                    else:
                        print(f"  {k[:16]}...  (no metadata)")


# ---------------------------------------------------------------------------
# Example 6: Testing support – stubs (Req 8)
# ---------------------------------------------------------------------------

def example_testing_support():
    """
    Demonstrate that the module loads even when pdd.config, pdd.preprocess
    are not available, thanks to try/except ImportError stubs (Req 8).

    In a test environment you would mock these:
        patch("pdd.extracts_prune.get_config", return_value={...})
        patch("pdd.extracts_prune.compute_cache_key", ...)
        patch("pdd.extracts_prune.parse_include_tags", ...)
    """
    from pdd.extracts_prune import extracts, compute_cache_key, parse_include_tags
    import click

    print(f"extracts is a click.Group: {isinstance(extracts, click.Group)}")
    print(f"'prune' registered: {'prune' in extracts.commands}")

    # The stub compute_cache_key works standalone
    key = compute_cache_key("src/app.py", "explain main")
    print(f"compute_cache_key('src/app.py', 'explain main') = {key[:16]}...")

    # The stub parse_include_tags works standalone
    tags = parse_include_tags('<include query="find bugs">lib/utils.py</include>')
    print(f"parse_include_tags found: {tags}")


# ---------------------------------------------------------------------------
# Main
# ---------------------------------------------------------------------------

if __name__ == "__main__":
    examples = [
        ("Example 1: Prune orphaned entries with --force", example_prune_with_force),
        ("Example 2: Interactive confirmation prompt", example_prune_interactive),
        ("Example 3: Global --force via ctx.obj", example_prune_global_force),
        ("Example 4: No cache directory (early exit)", example_prune_no_cache),
        ("Example 5: Inspect orphans without deleting", example_inspect_orphans),
        ("Example 6: Testing support / stubs", example_testing_support),
    ]

    for title, fn in examples:
        print()
        print("=" * 70)
        print(title)
        print("=" * 70)
        fn()
