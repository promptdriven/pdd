"""Example usage of the IncludeQueryExtractor module.\n\nThis script demonstrates how to use the ``IncludeQueryExtractor`` class to\nperform semantic extraction from a source file via an LLM, with persistent\ncaching under ``.pdd/extracts/``.\n\nKey concepts\n------------\n* **extract(file_path, query)**\n    - ``file_path`` (str): Absolute or project-relative path to the file you\n      want to query.  The file must exist and be UTF-8 encoded.\n    - ``query`` (str): A natural-language description of what information to\n      extract from the file (e.g. \"List all public function signatures\").\n    - Returns ``str``: The extracted content in Markdown format.\n\n* **Caching** – Results are stored in ``.pdd/extracts/`` as two files per\n  entry:\n    - ``<cache_key>.md``        – the extracted Markdown content.\n    - ``<cache_key>.meta.json`` – provenance metadata (source path, content\n      hash, query, timestamp, approximate token count).\n  On subsequent calls the cache is checked first; if the source file has not\n  changed the cached result is returned immediately.\n\n* **Cache control** – Set the environment variable ``EXTRACTS_CACHE_ENABLE=false``\n  to bypass the cache entirely (always re-extract via the LLM).\n\n* **Cache key** – Deterministic: ``sha256(resolved_file_path + '\\\
' + query)``.\n  You can compute it yourself with ``compute_cache_key(path, query)``.\n"""

from __future__ import annotations

import os
import tempfile
import shutil
from pathlib import Path

# ---------------------------------------------------------------------------
# The imports below come from the include_query_extractor module.
# Adjust the import path to match your project layout.
# ---------------------------------------------------------------------------
from pdd.include_query_extractor import (
    IncludeQueryExtractor,
    compute_cache_key,
)


def main() -> None:
    # -----------------------------------------------------------------
    # 1. Create a sample source file to query against.
    # -----------------------------------------------------------------
    sample_content = """\\\n# API Reference\n\n## Authentication\n\ndef login(username: str, password: str) -> str:\n    \"\"\"Authenticate a user and return a JWT token.\"\"\"\n    ...\n\ndef logout(token: str) -> None:\n    \"\"\"Invalidate the given JWT token.\"\"\"\n    ...\n\n## Data Access\n\ndef get_records(token: str, limit: int = 100) -> list[dict]:\n    \"\"\"Fetch up to *limit* records for the authenticated user.\"\"\"\n    ...\n\ndef delete_record(token: str, record_id: int) -> bool:\n    \"\"\"Delete a single record. Returns True on success.\"\"\"\n    ...\n"""

    # Write the sample file to a temporary location.
    tmp = Path(tempfile.mkdtemp())
    try:
        source_file = tmp / "api_reference.py"
        source_file.write_text(sample_content, encoding="utf-8")

        # -----------------------------------------------------------------
        # 2. Instantiate the extractor.
        # -----------------------------------------------------------------
        extractor = IncludeQueryExtractor()

        # -----------------------------------------------------------------
        # 3. Define a semantic query.
        #    The query is free-form natural language describing what you want
        #    extracted from the file.
        # -----------------------------------------------------------------
        query = "List all public function signatures with their docstrings"

        # -----------------------------------------------------------------
        # 4. (Optional) Inspect the deterministic cache key.
        #    Useful for debugging or manually inspecting cache entries.
        # -----------------------------------------------------------------
        resolved_path = str(source_file.resolve())
        cache_key = compute_cache_key(resolved_path, query)
        print(f"Cache key: {cache_key[:16]}…")

        # -----------------------------------------------------------------
        # 5. Run the extraction.
        #    On the first call the LLM is invoked and the result is cached.
        #    On subsequent calls (same file content + same query) the cached
        #    Markdown is returned instantly.
        # -----------------------------------------------------------------
        result = extractor.extract(
            file_path=str(source_file),   # absolute or project-relative path
            query=query,                  # natural-language extraction query
        )

        print("\
--- Extracted content ---")
        print(result)
        print("--- End ---\
")

        # -----------------------------------------------------------------
        # 6. Call again – this time the cache is hit (no LLM call).
        # -----------------------------------------------------------------
        result_cached = extractor.extract(str(source_file), query)
        assert result_cached == result, "Cached result should match"
        print("Second call returned cached result ✓")

        # -----------------------------------------------------------------
        # 7. Disable the cache via environment variable.
        #    When EXTRACTS_CACHE_ENABLE=false every call goes to the LLM.
        # -----------------------------------------------------------------
        os.environ["EXTRACTS_CACHE_ENABLE"] = "false"
        result_uncached = extractor.extract(str(source_file), query)
        print(f"Uncached result length: {len(result_uncached)} chars")

        # Re-enable for subsequent calls.
        os.environ["EXTRACTS_CACHE_ENABLE"] = "true"

        # -----------------------------------------------------------------
        # 8. Modify the source file – the cache detects staleness.
        #    The content hash changes, so the extractor re-invokes the LLM
        #    and writes a fresh cache entry.
        # -----------------------------------------------------------------
        source_file.write_text(
            sample_content + "\
def health_check() -> dict:\
    ...\
",
            encoding="utf-8",
        )
        result_refreshed = extractor.extract(str(source_file), query)
        print(f"Refreshed result length: {len(result_refreshed)} chars")

    finally:
        # -----------------------------------------------------------------
        # Cleanup
        # -----------------------------------------------------------------
        shutil.rmtree(tmp, ignore_errors=True)
        print("\
Done.")


if __name__ == "__main__":
    main()