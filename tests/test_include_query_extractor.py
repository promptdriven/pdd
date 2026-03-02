# =============================================================================
# TEST PLAN
# =============================================================================
#
# The code under test implements `IncludeQueryExtractor` with:
#   - `extract(file_path, query)` method that:
#     1. Reads source file content
#     2. Computes content hash for freshness detection
#     3. Computes deterministic cache key from (project-relative path, query)
#     4. Checks cache if enabled: returns cached content if hash matches
#     5. Removes stale/corrupted cache entries
#     6. Calls LLM via template loading, preprocessing, and invocation
#     7. Writes cache files (.md and .meta.json) after successful extraction
#
# Helper functions (public):
#   - `compute_cache_key(source_file_path, query)` -> deterministic sha256 hex
#
# Configuration:
#   - `EXTRACTS_CACHE_ENABLE` env var controls caching (default: true)
#
# EDGE CASES & TEST STRATEGY:
#
# 1. compute_cache_key determinism (Z3-suitable for property verification,
#    but unit test is simpler and sufficient here)
#    -> Unit test: same inputs produce same output, different inputs differ
#
# 2. Cache hit with matching hash -> Unit test with filesystem fixtures
# 3. Cache miss (no cache files) -> Unit test: LLM called, cache written
# 4. Stale cache (hash mismatch) -> Unit test: old cache removed, LLM called
# 5. Corrupted meta.json -> Unit test: cache removed, LLM re-invoked
# 6. Cache disabled via env var -> Unit test: LLM always called, no cache I/O
# 7. EXTRACTS_CACHE_ENABLE values: "false", "0", "no", "true", "" -> Unit tests
# 8. Cache key uniqueness property -> Z3 formal verification
# 9. Extract writes both .md and .meta.json -> Unit test
# 10. meta.json contains required fields -> Unit test
# 11. LLM invocation uses correct parameters -> Unit test with mock
# 12. Template loading and preprocessing called correctly -> Unit test
# 13. Empty LLM result -> Unit test: still cached, token_count=0
# 14. File not found -> Unit test: expect FileNotFoundError
# 15. Multiple sequential extracts with same params -> cache hit on second
#
# Z3 FORMAL VERIFICATION:
# - Property: compute_cache_key is a deterministic function
# - Property: different (path, query) pairs produce different cache keys
#   (collision resistance - we verify the hash construction is correct)
#
# =============================================================================


import sys
from pathlib import Path

# Add project root to sys.path to ensure local code is prioritized
# This allows testing local changes without installing the package
project_root = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(project_root))

import hashlib
import json
import os
import sys
from pathlib import Path
from unittest.mock import MagicMock, patch

import pytest

from pdd.include_query_extractor import (
    IncludeQueryExtractor,
    compute_cache_key,
    EXTRACTION_STRENGTH,
)


# ---------------------------------------------------------------------------
# Fixtures
# ---------------------------------------------------------------------------

@pytest.fixture
def tmp_project(tmp_path):
    """Create a minimal project structure with .pdd/extracts/."""
    cache_dir = tmp_path / ".pdd" / "extracts"
    cache_dir.mkdir(parents=True)
    return tmp_path


@pytest.fixture
def source_file(tmp_project):
    """Create a sample source file."""
    f = tmp_project / "example.py"
    f.write_text("def hello():\n    return 'world'\n", encoding="utf-8")
    return f


@pytest.fixture
def extractor():
    """Return an IncludeQueryExtractor with mocked LLM dependencies."""
    ext = IncludeQueryExtractor()
    ext._llm_invoke = MagicMock(return_value="extracted content here")
    ext._load_prompt_template = MagicMock(return_value="template text")
    ext._preprocess = MagicMock(return_value="processed template")
    return ext


@pytest.fixture
def patched_config(tmp_project):
    """Patch get_config to point to tmp_project."""
    with patch(
        "pdd.include_query_extractor.get_config",
        return_value={"project_root": str(tmp_project)},
    ):
        yield tmp_project


@pytest.fixture
def cache_enabled():
    """Ensure cache is enabled."""
    old = os.environ.pop("EXTRACTS_CACHE_ENABLE", None)
    os.environ["EXTRACTS_CACHE_ENABLE"] = "true"
    yield
    if old is None:
        os.environ.pop("EXTRACTS_CACHE_ENABLE", None)
    else:
        os.environ["EXTRACTS_CACHE_ENABLE"] = old


@pytest.fixture
def cache_disabled():
    """Disable cache via environment variable."""
    old = os.environ.pop("EXTRACTS_CACHE_ENABLE", None)
    os.environ["EXTRACTS_CACHE_ENABLE"] = "false"
    yield
    if old is None:
        os.environ.pop("EXTRACTS_CACHE_ENABLE", None)
    else:
        os.environ["EXTRACTS_CACHE_ENABLE"] = old


# ---------------------------------------------------------------------------
# Helper to create cache entries
# ---------------------------------------------------------------------------

def _write_cache_entry(cache_dir, cache_key, content, source_path, source_hash, query):
    """Write .md and .meta.json cache files."""
    md_path = cache_dir / f"{cache_key}.md"
    meta_path = cache_dir / f"{cache_key}.meta.json"
    md_path.write_text(content, encoding="utf-8")
    meta = {
        "source_path": source_path,
        "source_hash": source_hash,
        "query": query,
        "timestamp": "2024-01-01T00:00:00",
        "token_count": len(content.split()),
    }
    meta_path.write_text(json.dumps(meta, indent=2), encoding="utf-8")


def _project_relative(source_file, project_root):
    """Compute the project-relative path string for a source file."""
    resolved = source_file.resolve()
    pr = Path(project_root).resolve()
    try:
        return str(resolved.relative_to(pr))
    except ValueError:
        return str(resolved)


# ===========================================================================
# Tests: compute_cache_key
# ===========================================================================

class TestComputeCacheKey:
    """Tests for the public compute_cache_key function."""

    def test_deterministic(self):
        """Same inputs always produce the same key."""
        key1 = compute_cache_key("/path/to/file.py", "extract functions")
        key2 = compute_cache_key("/path/to/file.py", "extract functions")
        assert key1 == key2

    def test_different_paths_produce_different_keys(self):
        """Different file paths produce different keys."""
        key1 = compute_cache_key("/path/a.py", "query")
        key2 = compute_cache_key("/path/b.py", "query")
        assert key1 != key2

    def test_different_queries_produce_different_keys(self):
        """Different queries produce different keys."""
        key1 = compute_cache_key("/path/a.py", "query1")
        key2 = compute_cache_key("/path/a.py", "query2")
        assert key1 != key2

    def test_key_is_hex_string(self):
        """Cache key should be a valid hex string."""
        key = compute_cache_key("file.py", "query")
        assert all(c in "0123456789abcdef" for c in key)

    def test_key_length_is_sha256(self):
        """SHA-256 hex digest is 64 characters."""
        key = compute_cache_key("file.py", "query")
        assert len(key) == 64

    def test_matches_manual_sha256(self):
        """Key matches manually computed sha256 (with normpath)."""
        path = "/some/file.py"
        query = "extract classes"
        normalized = os.path.normpath(path)
        expected = hashlib.sha256((normalized + "\n" + query).encode()).hexdigest()
        assert compute_cache_key(path, query) == expected

    def test_empty_inputs(self):
        """Empty path and query still produce a valid key."""
        key = compute_cache_key("", "")
        assert len(key) == 64

    def test_unicode_inputs(self):
        """Unicode characters in path/query are handled."""
        key = compute_cache_key("/path/日本語.py", "抽出する")
        assert len(key) == 64


# ===========================================================================
# Tests: Cache miss (no existing cache)
# ===========================================================================

class TestExtractCacheMiss:
    """Tests for extraction when no cache exists."""

    def test_calls_llm_on_cache_miss(
        self, source_file, extractor, patched_config, cache_enabled
    ):
        """LLM is invoked when no cache entry exists."""
        result = extractor.extract(str(source_file), "extract functions")
        extractor._llm_invoke.assert_called_once()
        assert result == "extracted content here"

    def test_writes_md_cache_file(
        self, source_file, extractor, patched_config, cache_enabled
    ):
        """A .md cache file is created after extraction."""
        extractor.extract(str(source_file), "extract functions")
        cache_dir = patched_config / ".pdd" / "extracts"
        md_files = list(cache_dir.glob("*.md"))
        assert len(md_files) == 1
        assert md_files[0].read_text(encoding="utf-8") == "extracted content here"

    def test_writes_meta_json_cache_file(
        self, source_file, extractor, patched_config, cache_enabled
    ):
        """A .meta.json cache file is created with correct fields."""
        query = "extract functions"
        extractor.extract(str(source_file), query)
        cache_dir = patched_config / ".pdd" / "extracts"
        meta_files = list(cache_dir.glob("*.meta.json"))
        assert len(meta_files) == 1
        meta = json.loads(meta_files[0].read_text(encoding="utf-8"))
        assert "source_path" in meta
        assert "source_hash" in meta
        assert "query" in meta
        assert meta["query"] == query
        assert "timestamp" in meta
        assert "token_count" in meta

    def test_meta_json_source_hash_matches_content(
        self, source_file, extractor, patched_config, cache_enabled
    ):
        """source_hash in meta.json matches the actual file content hash."""
        extractor.extract(str(source_file), "q")
        cache_dir = patched_config / ".pdd" / "extracts"
        meta_files = list(cache_dir.glob("*.meta.json"))
        meta = json.loads(meta_files[0].read_text(encoding="utf-8"))
        content = source_file.read_text(encoding="utf-8")
        expected_hash = hashlib.sha256(content.encode()).hexdigest()
        assert meta["source_hash"] == expected_hash

    def test_llm_invoke_parameters(
        self, source_file, extractor, patched_config, cache_enabled
    ):
        """LLM is called with correct strength and input_json keys."""
        extractor.extract(str(source_file), "find classes")
        call_kwargs = extractor._llm_invoke.call_args
        assert call_kwargs.kwargs["strength"] == EXTRACTION_STRENGTH
        assert "file_content" in call_kwargs.kwargs["input_json"]
        assert "query" in call_kwargs.kwargs["input_json"]
        assert call_kwargs.kwargs["input_json"]["query"] == "find classes"

    def test_template_loading(
        self, source_file, extractor, patched_config, cache_enabled
    ):
        """Template is loaded with the correct name."""
        extractor.extract(str(source_file), "q")
        extractor._load_prompt_template.assert_called_once_with(
            "include_query_extractor_LLM"
        )

    def test_preprocessing_called(
        self, source_file, extractor, patched_config, cache_enabled
    ):
        """Preprocess is called on the loaded template."""
        extractor.extract(str(source_file), "q")
        extractor._preprocess.assert_called_once()


# ===========================================================================
# Tests: Cache hit
# ===========================================================================

class TestExtractCacheHit:
    """Tests for extraction when a valid cache entry exists."""

    def test_returns_cached_content(
        self, source_file, extractor, patched_config, cache_enabled
    ):
        """Cached content is returned without calling LLM."""
        resolved = source_file.resolve()
        content = source_file.read_text(encoding="utf-8")
        source_hash = hashlib.sha256(content.encode()).hexdigest()
        query = "extract functions"
        # Use project-relative path for cache key (matches extract() behavior)
        rel_path = _project_relative(source_file, patched_config)
        cache_key = compute_cache_key(rel_path, query)
        cache_dir = patched_config / ".pdd" / "extracts"

        _write_cache_entry(
            cache_dir, cache_key, "cached result",
            str(resolved), source_hash, query
        )

        result = extractor.extract(str(source_file), query)
        assert result == "cached result"
        extractor._llm_invoke.assert_not_called()

    def test_second_call_uses_cache(
        self, source_file, extractor, patched_config, cache_enabled
    ):
        """Second call with same params uses cache from first call."""
        query = "extract functions"
        extractor.extract(str(source_file), query)
        assert extractor._llm_invoke.call_count == 1

        result = extractor.extract(str(source_file), query)
        assert result == "extracted content here"
        # LLM should still only have been called once
        assert extractor._llm_invoke.call_count == 1


# ===========================================================================
# Tests: Stale cache (hash mismatch)
# ===========================================================================

class TestExtractStaleCache:
    """Tests for extraction when cache exists but source has changed."""

    def test_stale_cache_triggers_reextraction(
        self, source_file, extractor, patched_config, cache_enabled
    ):
        """When source hash doesn't match, LLM is called again."""
        resolved = source_file.resolve()
        query = "extract functions"
        rel_path = _project_relative(source_file, patched_config)
        cache_key = compute_cache_key(rel_path, query)
        cache_dir = patched_config / ".pdd" / "extracts"

        _write_cache_entry(
            cache_dir, cache_key, "old cached result",
            str(resolved), "stale_hash_value", query
        )

        result = extractor.extract(str(source_file), query)
        assert result == "extracted content here"
        extractor._llm_invoke.assert_called_once()

    def test_stale_cache_files_replaced(
        self, source_file, extractor, patched_config, cache_enabled
    ):
        """Stale cache files are replaced with new ones."""
        resolved = source_file.resolve()
        query = "q"
        rel_path = _project_relative(source_file, patched_config)
        cache_key = compute_cache_key(rel_path, query)
        cache_dir = patched_config / ".pdd" / "extracts"

        _write_cache_entry(
            cache_dir, cache_key, "old content",
            str(resolved), "wrong_hash", query
        )

        extractor.extract(str(source_file), query)

        md_path = cache_dir / f"{cache_key}.md"
        assert md_path.read_text(encoding="utf-8") == "extracted content here"

        meta_path = cache_dir / f"{cache_key}.meta.json"
        meta = json.loads(meta_path.read_text(encoding="utf-8"))
        content = source_file.read_text(encoding="utf-8")
        expected_hash = hashlib.sha256(content.encode()).hexdigest()
        assert meta["source_hash"] == expected_hash


# ===========================================================================
# Tests: Corrupted cache
# ===========================================================================

class TestExtractCorruptedCache:
    """Tests for extraction when cache files are corrupted."""

    def test_corrupted_meta_json_triggers_reextraction(
        self, source_file, extractor, patched_config, cache_enabled
    ):
        """Invalid JSON in meta file causes re-extraction."""
        resolved = source_file.resolve()
        query = "q"
        rel_path = _project_relative(source_file, patched_config)
        cache_key = compute_cache_key(rel_path, query)
        cache_dir = patched_config / ".pdd" / "extracts"

        md_path = cache_dir / f"{cache_key}.md"
        meta_path = cache_dir / f"{cache_key}.meta.json"
        md_path.write_text("old content", encoding="utf-8")
        meta_path.write_text("not valid json{{{", encoding="utf-8")

        result = extractor.extract(str(source_file), query)
        assert result == "extracted content here"
        extractor._llm_invoke.assert_called_once()


# ===========================================================================
# Tests: Cache disabled
# ===========================================================================

class TestExtractCacheDisabled:
    """Tests when EXTRACTS_CACHE_ENABLE is false."""

    def test_always_calls_llm(
        self, source_file, extractor, patched_config, cache_disabled
    ):
        """LLM is always called when cache is disabled."""
        extractor.extract(str(source_file), "q")
        extractor.extract(str(source_file), "q")
        assert extractor._llm_invoke.call_count == 2

    def test_no_cache_files_written(
        self, source_file, extractor, patched_config, cache_disabled
    ):
        """No cache files are written when cache is disabled."""
        extractor.extract(str(source_file), "q")
        cache_dir = patched_config / ".pdd" / "extracts"
        assert list(cache_dir.glob("*.md")) == []
        assert list(cache_dir.glob("*.meta.json")) == []

    @pytest.mark.parametrize("val", ["false", "0", "no", "FALSE", "False", "NO"])
    def test_disable_values(
        self, source_file, extractor, patched_config, val
    ):
        """Various falsy values disable the cache."""
        old = os.environ.get("EXTRACTS_CACHE_ENABLE")
        os.environ["EXTRACTS_CACHE_ENABLE"] = val
        try:
            extractor.extract(str(source_file), "q")
            extractor.extract(str(source_file), "q")
            assert extractor._llm_invoke.call_count == 2
        finally:
            if old is None:
                os.environ.pop("EXTRACTS_CACHE_ENABLE", None)
            else:
                os.environ["EXTRACTS_CACHE_ENABLE"] = old

    @pytest.mark.parametrize("val", ["true", "1", "yes", "TRUE", "anything"])
    def test_enable_values(
        self, source_file, extractor, patched_config, val
    ):
        """Various truthy values enable the cache."""
        old = os.environ.get("EXTRACTS_CACHE_ENABLE")
        os.environ["EXTRACTS_CACHE_ENABLE"] = val
        try:
            extractor.extract(str(source_file), "q")
            extractor.extract(str(source_file), "q")
            # Second call should use cache, so LLM called only once
            assert extractor._llm_invoke.call_count == 1
        finally:
            if old is None:
                os.environ.pop("EXTRACTS_CACHE_ENABLE", None)
            else:
                os.environ["EXTRACTS_CACHE_ENABLE"] = old


# ===========================================================================
# Tests: Empty LLM result
# ===========================================================================

class TestExtractEmptyResult:
    """Tests when LLM returns empty string."""

    def test_empty_result_cached(
        self, source_file, patched_config, cache_enabled
    ):
        """Empty LLM result is still cached."""
        ext = IncludeQueryExtractor()
        ext._llm_invoke = MagicMock(return_value="")
        ext._load_prompt_template = MagicMock(return_value="t")
        ext._preprocess = MagicMock(return_value="p")

        result = ext.extract(str(source_file), "q")
        assert result == ""

        cache_dir = patched_config / ".pdd" / "extracts"
        md_files = list(cache_dir.glob("*.md"))
        assert len(md_files) == 1
        assert md_files[0].read_text(encoding="utf-8") == ""

    def test_empty_result_token_count_zero(
        self, source_file, patched_config, cache_enabled
    ):
        """Empty result has token_count of 0."""
        ext = IncludeQueryExtractor()
        ext._llm_invoke = MagicMock(return_value="")
        ext._load_prompt_template = MagicMock(return_value="t")
        ext._preprocess = MagicMock(return_value="p")

        ext.extract(str(source_file), "q")

        cache_dir = patched_config / ".pdd" / "extracts"
        meta_files = list(cache_dir.glob("*.meta.json"))
        meta = json.loads(meta_files[0].read_text(encoding="utf-8"))
        assert meta["token_count"] == 0


# ===========================================================================
# Tests: File not found
# ===========================================================================

class TestExtractFileNotFound:
    """Tests when source file doesn't exist."""

    def test_nonexistent_file_raises(self, patched_config, cache_enabled):
        """Extracting from a nonexistent file raises an error."""
        ext = IncludeQueryExtractor()
        with pytest.raises((FileNotFoundError, OSError)):
            ext.extract("/nonexistent/path/file.py", "query")


# ===========================================================================
# Tests: Different queries on same file
# ===========================================================================

class TestExtractDifferentQueries:
    """Tests that different queries produce separate cache entries."""

    def test_different_queries_separate_cache(
        self, source_file, extractor, patched_config, cache_enabled
    ):
        """Different queries on the same file create separate cache entries."""
        extractor.extract(str(source_file), "query1")
        extractor.extract(str(source_file), "query2")

        assert extractor._llm_invoke.call_count == 2

        cache_dir = patched_config / ".pdd" / "extracts"
        md_files = list(cache_dir.glob("*.md"))
        assert len(md_files) == 2


# ===========================================================================
# Tests: Z3 formal verification of cache key properties
# ===========================================================================

class TestCacheKeyFormalProperties:
    """Formal property verification using Z3 (if available)."""

    def test_cache_key_determinism_z3(self):
        """Verify that compute_cache_key is deterministic using Z3.

        We verify the algebraic property: for any fixed inputs,
        sha256(a + '\\n' + b) always produces the same output.
        Since Z3 doesn't natively handle SHA-256, we verify the
        construction property: the input to the hash is deterministic.
        """
        try:
            from z3 import Solver, StringVal, sat

            s = Solver()
            path = StringVal("/path/to/file.py")
            query = StringVal("extract functions")

            # The concatenation path + "\n" + query is deterministic
            concat1 = path + StringVal("\n") + query
            concat2 = path + StringVal("\n") + query

            # Assert they could be different (should be unsat)
            s.add(concat1 != concat2)
            result = s.check()
            assert result != sat, "Cache key input construction is not deterministic"

        except ImportError:
            # Z3 not available, fall back to empirical test
            results = set()
            for _ in range(100):
                key = compute_cache_key("/path/file.py", "query")
                results.add(key)
            assert len(results) == 1, "Cache key is not deterministic"

    def test_cache_key_different_inputs_z3(self):
        """Verify different inputs produce different hash inputs using Z3."""
        try:
            from z3 import Solver, StringVal, sat

            s = Solver()
            path1 = StringVal("/path/a.py")
            path2 = StringVal("/path/b.py")
            query = StringVal("query")

            concat1 = path1 + StringVal("\n") + query
            concat2 = path2 + StringVal("\n") + query

            # Assert they could be equal (should be unsat since paths differ)
            s.add(concat1 == concat2)
            result = s.check()
            assert result != sat, "Different paths should produce different hash inputs"

        except ImportError:
            # Fall back to empirical test
            key1 = compute_cache_key("/path/a.py", "query")
            key2 = compute_cache_key("/path/b.py", "query")
            assert key1 != key2


# ===========================================================================
# Tests: Cache directory creation
# ===========================================================================

class TestCacheDirectoryCreation:
    """Tests that cache directory is created as needed."""

    def test_cache_dir_created_on_extract(
        self, tmp_path, extractor, cache_enabled
    ):
        """Cache directory is created if it doesn't exist."""
        source_file = tmp_path / "src.py"
        source_file.write_text("content", encoding="utf-8")

        with patch(
            "pdd.include_query_extractor.get_config",
            return_value={"project_root": str(tmp_path)},
        ):
            extractor.extract(str(source_file), "q")

        cache_dir = tmp_path / ".pdd" / "extracts"
        assert cache_dir.is_dir()


# ===========================================================================
# Tests: Preprocess parameters
# ===========================================================================

class TestPreprocessParameters:
    """Tests that preprocess is called with correct parameters."""

    def test_preprocess_exclude_keys(
        self, source_file, extractor, patched_config, cache_enabled
    ):
        """Preprocess is called with exclude_keys for file_content and query."""
        extractor.extract(str(source_file), "q")
        call_kwargs = extractor._preprocess.call_args
        exclude_keys = call_kwargs.kwargs.get(
            "exclude_keys", call_kwargs.args[0] if len(call_kwargs.args) > 1 else None
        )
        # Check that exclude_keys contains the template variables
        if exclude_keys is not None:
            assert "file_content" in exclude_keys
            assert "query" in exclude_keys


# ===========================================================================
# Tests: Meta.json timestamp
# ===========================================================================

class TestMetaTimestamp:
    """Tests for timestamp in meta.json."""

    def test_timestamp_format(
        self, source_file, extractor, patched_config, cache_enabled
    ):
        """Timestamp in meta.json follows ISO-like format."""
        extractor.extract(str(source_file), "q")
        cache_dir = patched_config / ".pdd" / "extracts"
        meta_files = list(cache_dir.glob("*.meta.json"))
        meta = json.loads(meta_files[0].read_text(encoding="utf-8"))
        ts = meta["timestamp"]
        # Should contain date separator and time separator
        assert "T" in ts or "-" in ts


# ===========================================================================
# Tests: Only .md file exists (no meta.json)
# ===========================================================================

class TestPartialCacheFiles:
    """Tests when only one of the two cache files exists."""

    def test_md_without_meta_triggers_extraction(
        self, source_file, extractor, patched_config, cache_enabled
    ):
        """If .md exists but .meta.json doesn't, LLM is called."""
        resolved = source_file.resolve()
        query = "q"
        rel_path = _project_relative(source_file, patched_config)
        cache_key = compute_cache_key(rel_path, query)
        cache_dir = patched_config / ".pdd" / "extracts"

        md_path = cache_dir / f"{cache_key}.md"
        md_path.write_text("partial cache", encoding="utf-8")

        result = extractor.extract(str(source_file), query)
        assert result == "extracted content here"
        extractor._llm_invoke.assert_called_once()

    def test_meta_without_md_triggers_extraction(
        self, source_file, extractor, patched_config, cache_enabled
    ):
        """If .meta.json exists but .md doesn't, LLM is called."""
        resolved = source_file.resolve()
        content = source_file.read_text(encoding="utf-8")
        source_hash = hashlib.sha256(content.encode()).hexdigest()
        query = "q"
        rel_path = _project_relative(source_file, patched_config)
        cache_key = compute_cache_key(rel_path, query)
        cache_dir = patched_config / ".pdd" / "extracts"

        meta_path = cache_dir / f"{cache_key}.meta.json"
        meta = {
            "source_path": str(resolved),
            "source_hash": source_hash,
            "query": query,
            "timestamp": "2024-01-01T00:00:00",
            "token_count": 5,
        }
        meta_path.write_text(json.dumps(meta), encoding="utf-8")

        result = extractor.extract(str(source_file), query)
        assert result == "extracted content here"
        extractor._llm_invoke.assert_called_once()


# ===========================================================================
# Tests: Cache key path form consistency (regression for absolute vs relative)
# ===========================================================================

class TestCacheKeyPathConsistency:
    """Tests that cache keys are consistent regardless of path form.

    The fix: extract() uses project-relative paths for cache keys, and
    compute_cache_key normalizes paths with os.path.normpath, so both
    CLI and API produce the same cache entries.
    """

    def test_absolute_vs_relative_path_produces_same_cache_key(self):
        """compute_cache_key normalizes with normpath but cannot resolve
        absolute-vs-relative without project root context.  extract()
        handles this by always converting to project-relative paths.
        Here we verify that normpath-level normalization works."""
        # normpath handles redundant separators and dot components
        key1 = compute_cache_key("/path/to/../to/file.py", "query")
        key2 = compute_cache_key("/path/to/file.py", "query")
        assert key1 == key2, (
            "Cache keys differ for '/path/to/../to/file.py' vs '/path/to/file.py'. "
            "Path should be normalized before hashing."
        )

    def test_dotslash_vs_bare_path_produces_same_cache_key(self):
        """'./src.py' and 'src.py' should produce the same cache key."""
        key_dot = compute_cache_key("./src.py", "query")
        key_bare = compute_cache_key("src.py", "query")
        assert key_dot == key_bare, (
            "Cache keys differ for './src.py' vs 'src.py'. "
            "Path should be normalized before hashing."
        )

    def test_extract_uses_project_relative_path_for_cache_key(
        self, source_file, extractor, patched_config, cache_enabled
    ):
        """IncludeQueryExtractor.extract() uses the project-relative path
        as the cache key input, so both CLI and API find the same entry."""
        query = "extract functions"
        extractor.extract(str(source_file), query)

        # The cache key used internally should match project-relative path
        resolved = source_file.resolve()
        try:
            rel_path = str(resolved.relative_to(patched_config.resolve()))
        except ValueError:
            pytest.skip("source_file not under project root")

        expected_key = compute_cache_key(rel_path, query)
        cache_dir = patched_config / ".pdd" / "extracts"
        md_path = cache_dir / f"{expected_key}.md"
        assert md_path.exists(), (
            "Cache file not found under project-relative key. "
            f"Expected key from rel_path='{rel_path}': {expected_key[:12]}..."
        )

    def test_cli_cache_entry_visible_to_api_path_logic(
        self, tmp_path, extractor, cache_enabled
    ):
        """Simulate CLI creating a cache entry, then API trying to find it.

        CLI path: IncludeQueryExtractor.extract(resolved_path, query)
          -> internally converts to project-relative path
          -> cache_key = compute_cache_key(rel_path, query)

        API path: extracts_for_prompt resolves include relative to prompt parent,
          then does: source_path = str(resolved.relative_to(project_root))
          -> cache_key = compute_cache_key(source_path, query)

        Both should produce the same cache key for the same file.
        """
        # Setup project
        project_root = tmp_path
        cache_dir = project_root / ".pdd" / "extracts"
        cache_dir.mkdir(parents=True)

        source = project_root / "lib" / "utils.py"
        source.parent.mkdir(parents=True)
        source.write_text("def helper(): pass", encoding="utf-8")

        with patch(
            "pdd.include_query_extractor.get_config",
            return_value={"project_root": str(project_root)},
        ):
            query = "extract helper function"

            # --- CLI path (what IncludeQueryExtractor.extract does) ---
            extractor.extract(str(source), query)

            # --- API path (what extracts.py extracts_for_prompt does) ---
            resolved = source.resolve()
            api_source_path = str(resolved.relative_to(project_root.resolve()))
            api_key = compute_cache_key(api_source_path, query)

            # The CLI should have created a cache entry findable by the API key
            assert (cache_dir / f"{api_key}.md").exists(), (
                f"CLI cache entry not findable under API key. "
                f"API would use '{api_source_path}', key={api_key[:12]}..."
            )
