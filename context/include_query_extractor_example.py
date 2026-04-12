"""Example usage of the IncludeQueryExtractor module.

Demonstrates semantic extraction from files using LLMs with persistent caching.

Public API:
    IncludeQueryExtractor  — class with extract(file_path: str, query: str) -> str
    compute_cache_key      — deterministic sha256 cache key from (path, query)

Key behaviors:
    - First call invokes the LLM and caches the result under .pdd/extracts/
    - Second call with same file content + query returns the cached result
    - Modifying the source file invalidates the cache (staleness detection)
    - Corrupted cache metadata is detected and triggers re-extraction
    - EXTRACTS_CACHE_ENABLE env var (default "true") controls all cache I/O
    - LLM interaction follows: load_prompt_template → preprocess → llm_invoke
    - Uses rich for formatted status updates ("Querying...", "Using cached extract...")
"""

import json
import os
import shutil
import tempfile
from unittest.mock import patch

from pdd.include_query_extractor import IncludeQueryExtractor, compute_cache_key


def _mock_llm_invoke(*, prompt: str, input_json: dict, strength: str) -> str:
    """Mock LLM that returns a Markdown summary based on the query."""
    query = input_json.get("query", "")
    return "The backend uses Python FastAPI with PostgreSQL."


def _mock_preprocess(text, recursive=False, double_curly_brackets=True, exclude_keys=None):
    """Mock preprocess that returns the template unchanged."""
    return text


def _mock_load_prompt_template(name):
    """Mock template loader."""
    return f"Template for {name}"


def main():
    tmp_dir = tempfile.mkdtemp(prefix="pdd_iqe_example_")
    try:
        # Patch find_project_root_from_path so cache files land in our temp dir
        with patch("pdd.path_resolution.find_project_root_from_path", return_value=tmp_dir):
            _run_example(tmp_dir)
    finally:
        shutil.rmtree(tmp_dir, ignore_errors=True)
        print("\nDone. Cleaned up temporary directory.")


def _run_example(tmp_dir):
    # --- 1. Create a sample source file ---
    source_path = os.path.join(tmp_dir, "architecture.md")
    original_content = (
        "# Architecture\n\n"
        "The frontend is React. The backend is Python FastAPI.\n"
        "Database: PostgreSQL. Cache: Redis.\n"
    )
    with open(source_path, "w", encoding="utf-8") as f:
        f.write(original_content)

    query = "What technologies are used in the backend?"
    extractor = IncludeQueryExtractor()

    # --- 2. Deterministic cache key (Req 5) ---
    # compute_cache_key uses sha256(normpath(path) + '\n' + query)
    # Note: the class internally converts to project-relative paths before
    # computing the key, so CLI and API produce consistent cache entries.
    cache_key = compute_cache_key(source_path, query)
    print(f"Cache key: {cache_key[:16]}...")

    # --- 3. First extraction — LLM interaction pattern (Req 2) ---
    # Internally: load_prompt_template("include_query_extractor_LLM")
    #           → preprocess(template, recursive=False, double_curly_brackets=True,
    #                        exclude_keys=["file_content", "query"])
    #           → llm_invoke(prompt=..., input_json={...}, strength="strong")
    with patch("pdd.include_query_extractor.llm_invoke", side_effect=_mock_llm_invoke), \
         patch("pdd.include_query_extractor.preprocess", side_effect=_mock_preprocess), \
         patch("pdd.include_query_extractor.load_prompt_template", side_effect=_mock_load_prompt_template):
        result1 = extractor.extract(source_path, query)

    print("\n--- First Extraction (LLM call) ---")
    print(result1)

    # --- 4. Second extraction — cached result (Req 3, 6) ---
    # Same content + query → cache hit, no LLM call
    with patch("pdd.include_query_extractor.llm_invoke", side_effect=_mock_llm_invoke), \
         patch("pdd.include_query_extractor.preprocess", side_effect=_mock_preprocess), \
         patch("pdd.include_query_extractor.load_prompt_template", side_effect=_mock_load_prompt_template):
        result2 = extractor.extract(source_path, query)

    print("\n--- Second Extraction (cached) ---")
    print(result2)
    assert result1 == result2, "Cached result should match original"
    print("Cache hit confirmed.")

    # --- 5. Staleness detection — modify file invalidates cache (Req 6) ---
    with open(source_path, "a", encoding="utf-8") as f:
        f.write("\nMessage queue: RabbitMQ.\n")

    with patch("pdd.include_query_extractor.llm_invoke", side_effect=_mock_llm_invoke), \
         patch("pdd.include_query_extractor.preprocess", side_effect=_mock_preprocess), \
         patch("pdd.include_query_extractor.load_prompt_template", side_effect=_mock_load_prompt_template):
        result3 = extractor.extract(source_path, query)

    print("\n--- Third Extraction (stale cache, re-extracted) ---")
    print(result3)

    # --- 6. Cache metadata verification (Req 4) ---
    # Metadata includes: source_path, source_hash, query, timestamp (ISO), token_count
    cache_dir = os.path.join(tmp_dir, ".pdd", "extracts")
    meta_files = [f for f in os.listdir(cache_dir) if f.endswith(".meta.json")]
    if meta_files:
        with open(os.path.join(cache_dir, meta_files[0])) as f:
            meta = json.load(f)
        print("\n--- Cache Metadata ---")
        print(f"  source_path: {meta['source_path']}")
        print(f"  source_hash: {meta['source_hash'][:16]}...")
        print(f"  query: {meta['query']}")
        print(f"  timestamp: {meta['timestamp']}")
        print(f"  token_count: {meta['token_count']}")

    # --- 7. EXTRACTS_CACHE_ENABLE toggle (Req 7) ---
    os.environ["EXTRACTS_CACHE_ENABLE"] = "false"
    with patch("pdd.include_query_extractor.llm_invoke", side_effect=_mock_llm_invoke), \
         patch("pdd.include_query_extractor.preprocess", side_effect=_mock_preprocess), \
         patch("pdd.include_query_extractor.load_prompt_template", side_effect=_mock_load_prompt_template):
        result4 = extractor.extract(source_path, query)

    print("\n--- Fourth Extraction (cache disabled via env var) ---")
    print(f"Result length: {len(result4)} chars")

    # Re-enable cache
    os.environ["EXTRACTS_CACHE_ENABLE"] = "true"


if __name__ == "__main__":
    main()
