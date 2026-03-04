"""Semantic extraction from files using LLMs with persistent caching."""

from __future__ import annotations

import hashlib
import json
import os
import time
from pathlib import Path

# ---------------------------------------------------------------------------
# Import helpers – fall back to stubs when the real package isn't available
# (e.g. during isolated test runs).
# ---------------------------------------------------------------------------
try:
    from pdd.config import get_config
except ImportError:
    def get_config():  # type: ignore[misc]
        return {"project_root": "."}

try:
    from pdd.utils import llm_invoke
except ImportError:
    def llm_invoke(*, prompt: str, input_json: dict, strength: str) -> str:  # type: ignore[misc]
        return ""

try:
    from pdd.preprocess import preprocess
except ImportError:
    def preprocess(text: str, recursive: bool = False, double_curly_brackets: bool = True, exclude_keys: list[str] | None = None) -> str:  # type: ignore[misc]
        return text

try:
    from pdd.prompt_loader import load_prompt_template
except ImportError:
    def load_prompt_template(name: str) -> str:  # type: ignore[misc]
        return ""

try:
    from rich.console import Console
    _console = Console()
except ImportError:
    class _FallbackConsole:
        def print(self, *args, **kwargs):
            pass
    _console = _FallbackConsole()  # type: ignore[assignment]


# ---------------------------------------------------------------------------
# Constants
# ---------------------------------------------------------------------------
EXTRACTION_STRENGTH = "strong"
_ENV_CACHE_ENABLE = "EXTRACTS_CACHE_ENABLE"


# ---------------------------------------------------------------------------
# Helpers
# ---------------------------------------------------------------------------

def compute_cache_key(source_file_path: str, query: str) -> str:
    """Deterministic cache key: sha256(normpath(source_file_path) + '\\n' + query).

    The path is normalized via ``os.path.normpath`` so that trivial
    variations like ``./src.py`` vs ``src.py`` produce the same key.
    """
    normalized = os.path.normpath(source_file_path)
    return hashlib.sha256((normalized + "\n" + query).encode()).hexdigest()


def _file_content_hash(content: str) -> str:
    """SHA-256 hex digest of file content."""
    return hashlib.sha256(content.encode()).hexdigest()


def _cache_enabled() -> bool:
    """Return whether the extracts cache is enabled (default ``True``)."""
    val = os.environ.get(_ENV_CACHE_ENABLE, "true").strip().lower()
    return val not in ("false", "0", "no")


def _cache_dir() -> Path:
    """Return the extracts cache directory, creating it if necessary."""
    cfg = get_config()
    root = Path(cfg.get("project_root", ".")).resolve()
    d = root / ".pdd" / "extracts"
    d.mkdir(parents=True, exist_ok=True)
    return d


def _project_relative_path(resolved: Path) -> str:
    """Return the project-relative path string for *resolved*.

    Falls back to the absolute path if the file is not under the
    project root.
    """
    cfg = get_config()
    project_root = Path(cfg.get("project_root", ".")).resolve()
    try:
        return str(resolved.relative_to(project_root))
    except ValueError:
        return str(resolved)


# ---------------------------------------------------------------------------
# Main class
# ---------------------------------------------------------------------------

class IncludeQueryExtractor:
    """Extract semantically relevant content from a file via an LLM.

    Results are persistently cached under ``.pdd/extracts/`` so that
    subsequent builds are reproducible and token-efficient.
    """

    # Allow tests to override helpers via class-level attributes
    _llm_invoke = staticmethod(llm_invoke)
    _preprocess = staticmethod(preprocess)
    _load_prompt_template = staticmethod(load_prompt_template)

    def extract(self, file_path: str, query: str) -> str:
        """Return the extracted content for *query* against *file_path*.

        Parameters
        ----------
        file_path:
            Absolute or project-relative path to the source file.
        query:
            Natural-language query describing what to extract.

        Returns
        -------
        str
            The extracted content (Markdown).
        """
        resolved = Path(file_path).resolve()
        source_content = resolved.read_text(encoding="utf-8")
        source_hash = _file_content_hash(source_content)

        # Use project-relative path for cache key so that CLI and API
        # produce the same cache entries for the same file.
        rel_path = _project_relative_path(resolved)
        cache_key = compute_cache_key(rel_path, query)
        cache = _cache_dir()
        md_path = cache / f"{cache_key}.md"
        meta_path = cache / f"{cache_key}.meta.json"

        # ----- cache lookup ------------------------------------------------
        if _cache_enabled() and md_path.exists() and meta_path.exists():
            try:
                meta = json.loads(meta_path.read_text(encoding="utf-8"))
                if meta.get("source_hash") == source_hash:
                    _console.print(
                        f"[dim]Using cached extract for[/dim] "
                        f"[bold]{resolved.name}[/bold] [dim]query=[/dim]'{query}'"
                    )
                    return md_path.read_text(encoding="utf-8")
                else:
                    # Stale – remove before re-extracting.
                    md_path.unlink(missing_ok=True)
                    meta_path.unlink(missing_ok=True)
            except (json.JSONDecodeError, OSError):
                # Corrupted cache entry – remove and re-extract.
                md_path.unlink(missing_ok=True)
                meta_path.unlink(missing_ok=True)

        # ----- LLM extraction ---------------------------------------------
        _console.print(
            f"[bold yellow]Querying...[/bold yellow] "
            f"[bold]{resolved.name}[/bold] query='{query}'"
        )

        template = self._load_prompt_template("include_query_extractor_LLM")
        processed_template = self._preprocess(
            template,
            recursive=False,
            double_curly_brackets=True,
            exclude_keys=["file_content", "query"],
        )

        result = self._llm_invoke(
            prompt=processed_template,
            input_json={"file_content": source_content, "query": query},
            strength=EXTRACTION_STRENGTH,
        )

        # ----- write cache -------------------------------------------------
        if _cache_enabled():
            token_count = len(result.split()) if result else 0
            md_path.write_text(result, encoding="utf-8")
            meta = {
                "source_path": str(resolved),
                "source_hash": source_hash,
                "query": query,
                "timestamp": time.strftime("%Y-%m-%dT%H:%M:%S"),
                "token_count": token_count,
            }
            meta_path.write_text(json.dumps(meta, indent=2), encoding="utf-8")

        return result
