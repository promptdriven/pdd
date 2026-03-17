"""
REST API endpoints for browsing the .pdd/extracts/ LLM extraction cache.

Provides endpoints for listing, inspecting, checking freshness, and pruning
cached LLM extracts used by the pdd connect web UI.
"""

from __future__ import annotations

import hashlib
import json
import os
import re
from datetime import datetime
from pathlib import Path
from typing import Annotated, List, Optional

from fastapi import APIRouter, Depends, HTTPException, Query
from pydantic import BaseModel, Field

try:
    from rich.console import Console
    console = Console()
except ImportError:
    class Console:
        def print(self, *args, **kwargs) -> None:
            import builtins
            builtins.print(*args)
    console = Console()

# Import compute_cache_key from the canonical location
try:
    from pdd.include_query_extractor import compute_cache_key
except ImportError:
    def compute_cache_key(source_path: str, query: str) -> str:  # type: ignore[misc]
        """Fallback cache key computation when pdd.include_query_extractor is unavailable."""
        normalized = os.path.normpath(source_path)
        return hashlib.sha256((normalized + "\n" + query).encode("utf-8")).hexdigest()


# ---------------------------------------------------------------------------
# Pydantic response models
# ---------------------------------------------------------------------------

class ExtractMetadata(BaseModel):
    """Metadata for a single cached extract."""
    cache_key: str
    source_path: str
    query: str
    timestamp: Optional[str] = None
    source_hash: Optional[str] = None
    is_fresh: Optional[bool] = None


class ExtractContent(BaseModel):
    """Full content plus metadata for a single cached extract."""
    cache_key: str
    source_path: str
    query: str
    timestamp: Optional[str] = None
    source_hash: Optional[str] = None
    is_fresh: Optional[bool] = None
    content: str


class ExtractListResponse(BaseModel):
    """Response for the list extracts endpoint."""
    extracts: List[ExtractMetadata]
    total: int
    stale_count: int


class PromptExtractInfo(BaseModel):
    """Information about an extract referenced by a prompt file."""
    include_path: str
    query: str
    cache_key: str
    has_cached_entry: bool
    source_path: Optional[str] = None
    timestamp: Optional[str] = None
    is_fresh: Optional[bool] = None


class PruneResponse(BaseModel):
    """Response for the prune extracts endpoint."""
    deleted_count: int
    orphaned_keys: List[str]
    message: str


# ---------------------------------------------------------------------------
# Dependency injection for project root
# ---------------------------------------------------------------------------

_project_root: Optional[Path] = None


def get_project_root() -> Path:
    """Dependency to get the project root path."""
    if _project_root is None:
        raise RuntimeError("Project root not configured")
    return _project_root


def set_project_root(root: Optional[Path]) -> None:
    """Configure the project root path."""
    global _project_root
    _project_root = root


# ---------------------------------------------------------------------------
# Helpers
# ---------------------------------------------------------------------------

# Regex for <include query="...">file_path</include> tags
# The query is an attribute; the file path is the body content.
_INCLUDE_PATTERN = re.compile(
    r'<include\s+[^>]*?query\s*=\s*["\']([^"\']*)["\'][^>]*>([^<]+)</include>',
    re.DOTALL,
)

_CACHE_KEY_PATTERN = re.compile(r'^[0-9a-fA-F]{64}$')


def _sha256_file(path: Path) -> Optional[str]:
    """Compute SHA-256 hex digest of a file's content. Returns None on error."""
    try:
        h = hashlib.sha256()
        with open(path, "rb") as f:
            while True:
                chunk = f.read(65536)
                if not chunk:
                    break
                h.update(chunk)
        return h.hexdigest()
    except Exception:
        return None


def _check_freshness(
    source_path: str,
    source_hash: Optional[str],
    project_root: Path,
) -> Optional[bool]:
    """
    Check whether a cached extract is still fresh.

    Returns True if the source file exists and its hash matches,
    False if the source file is missing/unreadable or hash differs,
    None if source_hash is not available.
    """
    if source_hash is None:
        return None

    abs_source = project_root / source_path
    current_hash = _sha256_file(abs_source)
    if current_hash is None:
        # Source file missing or unreadable → stale
        return False
    return current_hash == source_hash


def _parse_meta_file(
    meta_path: Path,
    project_root: Path,
    check_freshness: bool,
) -> Optional[ExtractMetadata]:
    """Parse a .meta.json file into an ExtractMetadata object."""
    try:
        with open(meta_path, "r", encoding="utf-8") as f:
            data = json.load(f)
    except Exception:
        return None

    # Derive cache_key from filename: {cache_key}.meta.json
    cache_key = meta_path.name
    if cache_key.endswith(".meta.json"):
        cache_key = cache_key[: -len(".meta.json")]
    else:
        return None

    source_path = data.get("source_path", "")
    query = data.get("query", "")
    timestamp = data.get("timestamp")
    source_hash = data.get("source_hash")

    is_fresh: Optional[bool] = None
    if check_freshness:
        is_fresh = _check_freshness(source_path, source_hash, project_root)
    
    return ExtractMetadata(
        cache_key=cache_key,
        source_path=source_path,
        query=query,
        timestamp=timestamp,
        source_hash=source_hash,
        is_fresh=is_fresh,
    )


def _parse_include_tags(content: str) -> list[tuple[str, str]]:
    """
    Parse <include query="...">file_path</include> tags from prompt content.

    Returns list of (file_path, query) tuples.
    """
    results: list[tuple[str, str]] = []
    seen: set[tuple[str, str]] = set()

    for match in _INCLUDE_PATTERN.finditer(content):
        query = match.group(1)
        file_path = match.group(2).strip()
        key = (file_path, query)
        if key not in seen:
            seen.add(key)
            results.append(key)

    return results


# ---------------------------------------------------------------------------
# Router
# ---------------------------------------------------------------------------

router = APIRouter(prefix="/api/v1/extracts", tags=["extracts"])


@router.get("", response_model=ExtractListResponse)
@router.get("/", response_model=ExtractListResponse, include_in_schema=False)
async def list_extracts(
    check_freshness: Annotated[
        bool, Query(description="Check freshness of each extract against source files")
    ] = True,
    project_root: Path = Depends(get_project_root),
) -> ExtractListResponse:
    """
    List all cached extracts.

    Scans *.meta.json files in .pdd/extracts/, parses each into ExtractMetadata,
    and returns them sorted by timestamp descending.
    """
    extracts_dir = project_root / ".pdd" / "extracts"

    if not extracts_dir.exists() or not extracts_dir.is_dir():
        return ExtractListResponse(extracts=[], total=0, stale_count=0)

    extracts: list[ExtractMetadata] = []
    for meta_path in extracts_dir.glob("*.meta.json"):
        entry = _parse_meta_file(meta_path, project_root, check_freshness)
        if entry is not None:
            extracts.append(entry)

    # Sort by timestamp descending; None timestamps sort last because
    # "" < any ISO-8601 string, so reverse=True pushes them to the end.
    extracts.sort(
        key=lambda e: e.timestamp if e.timestamp is not None else "",
        reverse=True,
    )

    stale_count = sum(1 for e in extracts if e.is_fresh is False)

    return ExtractListResponse(
        extracts=extracts,
        total=len(extracts),
        stale_count=stale_count,
    )


@router.get("/for-prompt", response_model=List[PromptExtractInfo])
async def extracts_for_prompt(
    prompt_path: Annotated[
        str, Query(description="Project-relative path to the prompt file")
    ],
    project_root: Path = Depends(get_project_root),
) -> list[PromptExtractInfo]:
    """
    List extracts relevant to a specific prompt file.

    Reads the prompt file, parses <include path="..." query="..."> tags,
    computes the cache key for each, and checks whether a cached entry exists.
    """
    abs_prompt = (project_root / prompt_path).resolve()
    if not abs_prompt.is_relative_to(project_root.resolve()):
        raise HTTPException(status_code=403, detail="Path traversal is not allowed")
    if not abs_prompt.exists() or not abs_prompt.is_file():
        raise HTTPException(status_code=404, detail=f"Prompt file not found: {prompt_path}")

    try:
        content = abs_prompt.read_text(encoding="utf-8")
    except Exception as exc:
        raise HTTPException(status_code=400, detail=f"Cannot read prompt file: {exc}")

    includes = _parse_include_tags(content)
    extracts_dir = project_root / ".pdd" / "extracts"
    prompt_parent = abs_prompt.parent

    results: list[PromptExtractInfo] = []
    for include_path, query in includes:
        # Resolve include path relative to the prompt file's parent directory
        resolved = (prompt_parent / include_path).resolve()
        try:
            source_path = str(resolved.relative_to(project_root.resolve()))
        except ValueError:
            # Path is outside project root — skip to avoid leaking absolute paths
            continue

        cache_key = compute_cache_key(source_path, query)

        meta_path = extracts_dir / f"{cache_key}.meta.json"
        md_path = extracts_dir / f"{cache_key}.md"
        has_cached = meta_path.exists() and md_path.exists()

        info = PromptExtractInfo(
            include_path=include_path,
            query=query,
            cache_key=cache_key,
            has_cached_entry=has_cached,
        )

        if has_cached:
            entry = _parse_meta_file(meta_path, project_root, check_freshness=True)
            if entry is not None:
                info.source_path = entry.source_path
                info.timestamp = entry.timestamp
                info.is_fresh = entry.is_fresh

        results.append(info)

    return results


@router.post("/prune", response_model=PruneResponse)
async def prune_extracts(
    dry_run: Annotated[
        bool, Query(description="If true, report orphaned entries without deleting")
    ] = False,
    project_root: Path = Depends(get_project_root),
) -> PruneResponse:
    """
    Prune orphaned extracts cache entries not referenced by any prompt file.

    Scans all .prompt files to find referenced cache keys, then deletes any
    cached entries that are no longer referenced.
    """
    extracts_dir = project_root / ".pdd" / "extracts"

    if not extracts_dir.exists() or not extracts_dir.is_dir():
        return PruneResponse(deleted_count=0, orphaned_keys=[], message="No extracts directory found.")

    # Collect on-disk cache keys
    cached_md_files = sorted(extracts_dir.glob("*.md"))
    if not cached_md_files:
        return PruneResponse(deleted_count=0, orphaned_keys=[], message="Extracts cache is empty.")

    on_disk: dict[str, Path] = {}
    for md_path in cached_md_files:
        on_disk[md_path.stem] = md_path

    # Collect referenced keys by scanning all .prompt files
    try:
        from pdd.extracts_prune import _collect_referenced_keys
        referenced = _collect_referenced_keys(project_root)
    except ImportError:
        # Fallback: scan locally (same logic as extracts_prune.py)
        _EXCLUDED_DIRS = frozenset({
            "node_modules", ".git", ".hg", ".svn", "__pycache__",
            ".venv", "venv", ".env", "env", ".tox", ".mypy_cache",
            ".pytest_cache", "dist", "build",
        })
        prompt_files: list[Path] = []
        for root, dirs, files in os.walk(project_root):
            dirs[:] = [d for d in dirs if d not in _EXCLUDED_DIRS]
            for f in files:
                if f.endswith(".prompt"):
                    prompt_files.append(Path(root) / f)

        referenced: set[str] = set()
        for prompt_file in sorted(prompt_files):
            try:
                text = prompt_file.read_text(encoding="utf-8")
            except OSError:
                continue
            for match in _INCLUDE_PATTERN.finditer(text):
                query = match.group(1)
                file_path = match.group(2).strip()
                resolved = (prompt_file.parent / file_path).resolve()
                if not resolved.exists():
                    resolved = (project_root / file_path).resolve()
                if not resolved.exists():
                    continue
                try:
                    relative = str(resolved.relative_to(project_root.resolve()))
                except ValueError:
                    relative = str(resolved)
                relative = os.path.normpath(relative)
                key = compute_cache_key(relative, query)
                referenced.add(key)

    orphaned_keys = sorted(set(on_disk.keys()) - referenced)

    if not orphaned_keys:
        return PruneResponse(deleted_count=0, orphaned_keys=[], message="No orphaned entries found — cache is clean.")

    if dry_run:
        return PruneResponse(
            deleted_count=0,
            orphaned_keys=orphaned_keys,
            message=f"Found {len(orphaned_keys)} orphaned entr{'y' if len(orphaned_keys) == 1 else 'ies'} (dry run, nothing deleted).",
        )

    # Delete orphaned entries
    deleted = 0
    for key in orphaned_keys:
        md_file = extracts_dir / f"{key}.md"
        meta_file = extracts_dir / f"{key}.meta.json"
        try:
            md_file.unlink(missing_ok=True)
            meta_file.unlink(missing_ok=True)
            deleted += 1
        except OSError:
            pass

    return PruneResponse(
        deleted_count=deleted,
        orphaned_keys=orphaned_keys,
        message=f"Pruned {deleted} orphaned cache entr{'y' if deleted == 1 else 'ies'}.",
    )


@router.get("/{cache_key}", response_model=ExtractContent)
async def get_extract(
    cache_key: str,
    project_root: Path = Depends(get_project_root),
) -> ExtractContent:
    """
    Return full content plus metadata for a single cached extract.

    Validates that cache_key is a 64-character hex string.
    """
    if not _CACHE_KEY_PATTERN.match(cache_key):
        raise HTTPException(status_code=404, detail="Invalid cache key format")

    extracts_dir = project_root / ".pdd" / "extracts"
    md_path = extracts_dir / f"{cache_key}.md"
    meta_path = extracts_dir / f"{cache_key}.meta.json"

    if not md_path.exists():
        raise HTTPException(status_code=404, detail=f"Extract not found: {cache_key}")

    # Read content
    try:
        content = md_path.read_text(encoding="utf-8")
    except Exception as exc:
        raise HTTPException(status_code=500, detail=f"Cannot read extract content: {exc}")

    # Read metadata
    source_path = ""
    query = ""
    timestamp: Optional[str] = None
    source_hash: Optional[str] = None
    is_fresh: Optional[bool] = None

    if meta_path.exists():
        try:
            with open(meta_path, "r", encoding="utf-8") as f:
                data = json.load(f)
            source_path = data.get("source_path", "")
            query = data.get("query", "")
            timestamp = data.get("timestamp")
            source_hash = data.get("source_hash")
            is_fresh = _check_freshness(source_path, source_hash, project_root)
        except Exception:
            console.print(f"[yellow]Warning: could not parse metadata for {cache_key}[/yellow]")

    return ExtractContent(
        cache_key=cache_key,
        source_path=source_path,
        query=query,
        timestamp=timestamp,
        source_hash=source_hash,
        is_fresh=is_fresh,
        content=content,
    )