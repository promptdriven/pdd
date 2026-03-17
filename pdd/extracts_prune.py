"""CLI commands for managing the .pdd/extracts/ directory."""

from __future__ import annotations

import hashlib
import json
import os
import re
from pathlib import Path

import click

# ---------------------------------------------------------------------------
# Import helpers from the rest of the pdd package.  When running under the
# test-suite the real modules may not be available, so we fall back to
# minimal stubs that the tests will patch out anyway.
# ---------------------------------------------------------------------------
try:
    from pdd.config import get_config
except ImportError:
    def get_config():  # type: ignore[misc]
        return {"project_root": "."}

try:
    from pdd.include_query_extractor import compute_cache_key
except ImportError:
    def compute_cache_key(source_file_path: str, query: str) -> str:  # type: ignore[misc]
        normalized = os.path.normpath(source_file_path)
        return hashlib.sha256((normalized + "\n" + query).encode()).hexdigest()


def parse_include_tags(text: str) -> list[tuple[str, str]]:
    """Parse <include query="...">file</include> tags.

    Returns list of (file_path, query) tuples.
    """
    results: list[tuple[str, str]] = []
    # <include query="...">file</include>
    for m in re.finditer(
        r'<include\s+[^>]*?query\s*=\s*["\']([^"\']*)["\'][^>]*?>\s*(.*?)\s*</include>',
        text,
    ):
        item = (m.group(2), m.group(1))
        if item not in results:
            results.append(item)
    # <include path="..." query="..." />
    for m in re.finditer(
        r'<include\s+[^>]*?path\s*=\s*["\']([^"\']*)["\'][^>]*?query\s*=\s*["\']([^"\']*)["\'][^>]*?/?>',
        text,
    ):
        item = (m.group(1), m.group(2))
        if item not in results:
            results.append(item)
    # <include query="..." path="..." />
    for m in re.finditer(
        r'<include\s+[^>]*?query\s*=\s*["\']([^"\']*)["\'][^>]*?path\s*=\s*["\']([^"\']*)["\'][^>]*?/?>',
        text,
    ):
        item = (m.group(2), m.group(1))
        if item not in results:
            results.append(item)
    return results


# ---------------------------------------------------------------------------
# Click group & command
# ---------------------------------------------------------------------------

@click.group("extracts")
def extracts():
    """Manage the extracts cache."""
    pass


_EXCLUDED_DIRS = frozenset({
    "node_modules", ".git", ".hg", ".svn", "__pycache__",
    ".venv", "venv", ".env", "env", ".tox", ".mypy_cache",
    ".pytest_cache", "dist", "build",
})


def _find_prompt_files(project_root: Path) -> list[Path]:
    """Return all .prompt files under *project_root*, excluding common non-project dirs."""
    results: list[Path] = []
    for root, dirs, files in os.walk(project_root):
        # Prune excluded directories in-place so os.walk doesn't descend into them
        dirs[:] = [d for d in dirs if d not in _EXCLUDED_DIRS]
        for f in files:
            if f.endswith(".prompt"):
                results.append(Path(root) / f)
    return sorted(results)


def _collect_referenced_keys(project_root: Path) -> set[str]:
    """Scan every .prompt file and return the set of cache keys still in use."""
    referenced: set[str] = set()
    for prompt_file in _find_prompt_files(project_root):
        try:
            text = prompt_file.read_text(encoding="utf-8")
        except OSError:
            continue
        for raw_path, query in parse_include_tags(text):
            # Try prompt-parent-relative first, then project-root-relative
            # (mirrors the cwd_then_package_then_repo resolution in
            # path_resolution.py / preprocess.py).
            candidate = (prompt_file.parent / raw_path).resolve()
            if not candidate.exists():
                candidate = (project_root / raw_path).resolve()
            if not candidate.exists():
                # Source file no longer exists – skip (orphaned by definition)
                continue
            # Convert to project-relative path before hashing
            try:
                relative = str(candidate.relative_to(project_root.resolve()))
            except ValueError:
                relative = str(candidate)
            relative = os.path.normpath(relative)
            key = compute_cache_key(relative, query)
            referenced.add(key)
    return referenced


def _cache_dir() -> Path | None:
    """Return the extracts directory or *None* if it doesn't exist."""
    cfg = get_config()
    root = Path(cfg.get("project_root", ".")).resolve()
    d = root / ".pdd" / "extracts"
    return d if d.is_dir() else None


@extracts.command()
@click.option("--force", is_flag=True, default=False, help="Skip confirmation prompt.")
@click.pass_context
def prune(ctx: click.Context, force: bool) -> None:
    """Delete orphaned extracts cache entries not referenced by any prompt file."""
    # Honour both the local --force and the global --force flag.
    force = force or (ctx.obj or {}).get("force", False)

    cache = _cache_dir()
    if cache is None:
        click.echo("No extracts directory found (.pdd/extracts/) – nothing to do.")
        return

    cached_md_files = sorted(cache.glob("*.md"))
    if not cached_md_files:
        click.echo("Extracts cache is empty – nothing to prune.")
        return

    # Map cache key -> md path for every entry currently on disk.
    on_disk: dict[str, Path] = {}
    for md_path in cached_md_files:
        on_disk[md_path.stem] = md_path

    cfg = get_config()
    project_root = Path(cfg.get("project_root", ".")).resolve()
    referenced = _collect_referenced_keys(project_root)

    orphaned_keys = sorted(set(on_disk.keys()) - referenced)

    if not orphaned_keys:
        click.echo("No orphaned cache entries found – cache is clean.")
        return

    # ------------------------------------------------------------------
    # Display orphaned entries
    # ------------------------------------------------------------------
    try:
        from rich.console import Console
        from rich.table import Table

        console = Console()
        table = Table(title="Orphaned extracts cache entries")
        table.add_column("Cache Key", style="dim", no_wrap=True, max_width=16)
        table.add_column("Source Path")
        table.add_column("Query")

        for key in orphaned_keys:
            source_path = "<unknown>"
            query_text = "<unknown>"
            meta_file = cache / f"{key}.meta.json"
            if meta_file.exists():
                try:
                    meta = json.loads(meta_file.read_text(encoding="utf-8"))
                    source_path = meta.get("source_path", source_path)
                    query_text = meta.get("query", query_text)
                except (json.JSONDecodeError, OSError):
                    pass
            table.add_row(key[:16] + "…", source_path, query_text)

        console.print(table)
    except ImportError:
        # Fallback when rich is not installed.
        click.echo("Orphaned extracts cache entries:")
        for key in orphaned_keys:
            source_path = "<unknown>"
            query_text = "<unknown>"
            meta_file = cache / f"{key}.meta.json"
            if meta_file.exists():
                try:
                    meta = json.loads(meta_file.read_text(encoding="utf-8"))
                    source_path = meta.get("source_path", source_path)
                    query_text = meta.get("query", query_text)
                except (json.JSONDecodeError, OSError):
                    pass
            click.echo(f"  {key[:16]}…  {source_path}  {query_text}")

    # ------------------------------------------------------------------
    # Confirm & delete
    # ------------------------------------------------------------------
    count = len(orphaned_keys)
    if not force:
        if not click.confirm(f"Delete {count} orphaned cache entr{'y' if count == 1 else 'ies'}?"):
            click.echo("Aborted.")
            return

    deleted = 0
    for key in orphaned_keys:
        md_file = cache / f"{key}.md"
        meta_file = cache / f"{key}.meta.json"
        try:
            md_file.unlink(missing_ok=True)
            meta_file.unlink(missing_ok=True)
            deleted += 1
        except OSError as exc:
            click.echo(f"Warning: could not delete {key}: {exc}", err=True)

    click.echo(f"Pruned {deleted} orphaned cache entr{'y' if deleted == 1 else 'ies'}.")
