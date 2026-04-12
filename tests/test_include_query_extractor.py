"""Tests for include_query_extractor module.

Tests are structured around the prompt requirements:
  1. IncludeQueryExtractor.extract(file_path, query) -> str
  2. LLM interaction pattern (load_prompt_template, preprocess, llm_invoke)
  3. Persistent caching in .pdd/extracts/
  4. Metadata fields (source_path, source_hash, query, timestamp, token_count)
  5. Cache key determinism via sha256(normpath(project_relative_path) + '\\n' + query)
  6. Freshness & error handling (stale, corrupted)
  7. EXTRACTS_CACHE_ENABLE env var
  8. Rich status output
"""

import hashlib
import json
import os
from pathlib import Path
from unittest.mock import MagicMock, call

import pytest

from pdd.include_query_extractor import (
    IncludeQueryExtractor,
    compute_cache_key,
    _ENV_CACHE_ENABLE,
)


# ---------------------------------------------------------------------------
# Fixtures
# ---------------------------------------------------------------------------

@pytest.fixture
def temp_project(tmp_path, monkeypatch):
    """Sets up a temporary project with mocked config, LLM, and cache enabled."""
    monkeypatch.setattr(
        "pdd.path_resolution.find_project_root_from_path",
        lambda *args, **kwargs: str(tmp_path),
    )
    monkeypatch.setenv(_ENV_CACHE_ENABLE, "true")

    source_file = tmp_path / "test_doc.txt"
    source_file.write_text("Hello World. This is a test document.", encoding="utf-8")

    return tmp_path, source_file


@pytest.fixture
def mock_llm(monkeypatch):
    """Mock module-level LLM dependencies (not class internals)."""
    llm = MagicMock(return_value="Extracted content from LLM")
    load_template = MagicMock(return_value="RAW_TEMPLATE")
    preprocess_fn = MagicMock(return_value="PROCESSED_TEMPLATE")

    monkeypatch.setattr("pdd.include_query_extractor.llm_invoke", llm)
    monkeypatch.setattr("pdd.include_query_extractor.load_prompt_template", load_template)
    monkeypatch.setattr("pdd.include_query_extractor.preprocess", preprocess_fn)

    return {
        "llm_invoke": llm,
        "load_prompt_template": load_template,
        "preprocess": preprocess_fn,
    }


# ---------------------------------------------------------------------------
# Req 1: IncludeQueryExtractor.extract(file_path, query) -> str
# ---------------------------------------------------------------------------

class TestExtractBasic:
    def test_extract_returns_string(self, temp_project, mock_llm):
        _, source_file = temp_project
        extractor = IncludeQueryExtractor()
        result = extractor.extract(str(source_file), "summarize")
        assert isinstance(result, str)
        assert result == "Extracted content from LLM"

    def test_extract_reads_file_content(self, temp_project, mock_llm):
        _, source_file = temp_project
        extractor = IncludeQueryExtractor()
        extractor.extract(str(source_file), "summarize")

        # The LLM should receive the file content
        call_kwargs = mock_llm["llm_invoke"].call_args
        assert "Hello World" in call_kwargs.kwargs["input_json"]["file_content"]

    def test_extract_passes_query_to_llm(self, temp_project, mock_llm):
        _, source_file = temp_project
        extractor = IncludeQueryExtractor()
        extractor.extract(str(source_file), "find the greeting")

        call_kwargs = mock_llm["llm_invoke"].call_args
        assert call_kwargs.kwargs["input_json"]["query"] == "find the greeting"


# ---------------------------------------------------------------------------
# Req 2: LLM interaction pattern
# ---------------------------------------------------------------------------

class TestLLMInteractionPattern:
    def test_loads_correct_prompt_template(self, temp_project, mock_llm):
        _, source_file = temp_project
        extractor = IncludeQueryExtractor()
        extractor.extract(str(source_file), "query")

        mock_llm["load_prompt_template"].assert_called_once_with(
            "include_query_extractor_LLM"
        )

    def test_preprocesses_template_correctly(self, temp_project, mock_llm):
        _, source_file = temp_project
        extractor = IncludeQueryExtractor()
        extractor.extract(str(source_file), "query")

        mock_llm["preprocess"].assert_called_once_with(
            "RAW_TEMPLATE",
            recursive=False,
            double_curly_brackets=True,
            exclude_keys=["file_content", "query"],
        )

    def test_calls_llm_with_strong_strength(self, temp_project, mock_llm):
        _, source_file = temp_project
        extractor = IncludeQueryExtractor()
        extractor.extract(str(source_file), "query")

        call_kwargs = mock_llm["llm_invoke"].call_args
        assert call_kwargs.kwargs["strength"] == 1.0

    def test_llm_receives_preprocessed_template(self, temp_project, mock_llm):
        _, source_file = temp_project
        extractor = IncludeQueryExtractor()
        extractor.extract(str(source_file), "query")

        call_kwargs = mock_llm["llm_invoke"].call_args
        assert call_kwargs.kwargs["prompt"] == "PROCESSED_TEMPLATE"


# ---------------------------------------------------------------------------
# Req 3 & 4: Persistent caching and metadata
# ---------------------------------------------------------------------------

class TestCaching:
    def test_creates_cache_files(self, temp_project, mock_llm):
        tmp_path, source_file = temp_project
        extractor = IncludeQueryExtractor()
        extractor.extract(str(source_file), "query")

        cache_dir = tmp_path / ".pdd" / "extracts"
        md_files = list(cache_dir.glob("*.md"))
        json_files = list(cache_dir.glob("*.meta.json"))

        assert len(md_files) == 1
        assert len(json_files) == 1

    def test_cache_md_contains_result(self, temp_project, mock_llm):
        tmp_path, source_file = temp_project
        extractor = IncludeQueryExtractor()
        extractor.extract(str(source_file), "query")

        cache_dir = tmp_path / ".pdd" / "extracts"
        md_file = list(cache_dir.glob("*.md"))[0]
        assert md_file.read_text(encoding="utf-8") == "Extracted content from LLM"

    def test_metadata_has_required_fields(self, temp_project, mock_llm):
        tmp_path, source_file = temp_project
        extractor = IncludeQueryExtractor()
        extractor.extract(str(source_file), "query")

        cache_dir = tmp_path / ".pdd" / "extracts"
        meta_file = list(cache_dir.glob("*.meta.json"))[0]
        meta = json.loads(meta_file.read_text(encoding="utf-8"))

        assert "source_path" in meta
        assert "source_hash" in meta
        assert "query" in meta
        assert "timestamp" in meta
        assert "token_count" in meta

    def test_metadata_source_path_is_project_relative(self, temp_project, mock_llm):
        tmp_path, source_file = temp_project
        extractor = IncludeQueryExtractor()
        extractor.extract(str(source_file), "query")

        cache_dir = tmp_path / ".pdd" / "extracts"
        meta_file = list(cache_dir.glob("*.meta.json"))[0]
        meta = json.loads(meta_file.read_text(encoding="utf-8"))

        # source_path must be project-relative, not absolute
        assert not os.path.isabs(meta["source_path"]), (
            f"source_path should be relative, got: {meta['source_path']}"
        )
        assert meta["source_path"] == "test_doc.txt"

    def test_metadata_source_hash_is_sha256(self, temp_project, mock_llm):
        tmp_path, source_file = temp_project
        extractor = IncludeQueryExtractor()
        extractor.extract(str(source_file), "query")

        content = source_file.read_text(encoding="utf-8")
        expected_hash = hashlib.sha256(content.encode()).hexdigest()

        cache_dir = tmp_path / ".pdd" / "extracts"
        meta_file = list(cache_dir.glob("*.meta.json"))[0]
        meta = json.loads(meta_file.read_text(encoding="utf-8"))
        assert meta["source_hash"] == expected_hash

    def test_metadata_query_matches(self, temp_project, mock_llm):
        tmp_path, source_file = temp_project
        extractor = IncludeQueryExtractor()
        extractor.extract(str(source_file), "find the greeting")

        cache_dir = tmp_path / ".pdd" / "extracts"
        meta_file = list(cache_dir.glob("*.meta.json"))[0]
        meta = json.loads(meta_file.read_text(encoding="utf-8"))
        assert meta["query"] == "find the greeting"

    def test_metadata_timestamp_is_iso_format(self, temp_project, mock_llm):
        tmp_path, source_file = temp_project
        extractor = IncludeQueryExtractor()
        extractor.extract(str(source_file), "query")

        cache_dir = tmp_path / ".pdd" / "extracts"
        meta_file = list(cache_dir.glob("*.meta.json"))[0]
        meta = json.loads(meta_file.read_text(encoding="utf-8"))

        # ISO format: YYYY-MM-DDTHH:MM:SS (at minimum)
        ts = meta["timestamp"]
        assert "T" in ts, f"Timestamp should be ISO format, got: {ts}"
        # Should have date and time parts
        parts = ts.split("T")
        assert len(parts) == 2
        assert len(parts[0].split("-")) == 3  # YYYY-MM-DD

    def test_metadata_token_count_is_word_count(self, temp_project, mock_llm):
        mock_llm["llm_invoke"].return_value = "one two three four five"
        tmp_path, source_file = temp_project
        extractor = IncludeQueryExtractor()
        extractor.extract(str(source_file), "query")

        cache_dir = tmp_path / ".pdd" / "extracts"
        meta_file = list(cache_dir.glob("*.meta.json"))[0]
        meta = json.loads(meta_file.read_text(encoding="utf-8"))
        assert meta["token_count"] == 5

    def test_metadata_source_path_nested_file(self, temp_project, mock_llm):
        tmp_path, _ = temp_project
        nested = tmp_path / "sub" / "dir" / "deep.txt"
        nested.parent.mkdir(parents=True, exist_ok=True)
        nested.write_text("nested content", encoding="utf-8")

        extractor = IncludeQueryExtractor()
        extractor.extract(str(nested), "query")

        cache_dir = tmp_path / ".pdd" / "extracts"
        meta_files = [f for f in cache_dir.glob("*.meta.json")]
        # Find the meta for the nested file
        for mf in meta_files:
            meta = json.loads(mf.read_text(encoding="utf-8"))
            if "deep.txt" in meta["source_path"]:
                assert meta["source_path"] == os.path.join("sub", "dir", "deep.txt")
                return
        pytest.fail("Did not find metadata for nested file")

    def test_cache_hit_skips_llm(self, temp_project, mock_llm):
        _, source_file = temp_project
        extractor = IncludeQueryExtractor()

        result1 = extractor.extract(str(source_file), "query")
        result2 = extractor.extract(str(source_file), "query")

        assert mock_llm["llm_invoke"].call_count == 1
        assert result1 == result2

    def test_different_query_creates_separate_cache(self, temp_project, mock_llm):
        tmp_path, source_file = temp_project
        extractor = IncludeQueryExtractor()

        extractor.extract(str(source_file), "query A")
        extractor.extract(str(source_file), "query B")

        assert mock_llm["llm_invoke"].call_count == 2

        cache_dir = tmp_path / ".pdd" / "extracts"
        md_files = list(cache_dir.glob("*.md"))
        assert len(md_files) == 2


# ---------------------------------------------------------------------------
# Req 5: Cache key determinism
# ---------------------------------------------------------------------------

class TestCacheKey:
    def test_same_inputs_produce_same_key(self):
        key1 = compute_cache_key("/some/path.py", "query")
        key2 = compute_cache_key("/some/path.py", "query")
        assert key1 == key2

    def test_different_query_produces_different_key(self):
        key1 = compute_cache_key("/some/path.py", "query A")
        key2 = compute_cache_key("/some/path.py", "query B")
        assert key1 != key2

    def test_different_path_produces_different_key(self):
        key1 = compute_cache_key("/some/path_a.py", "query")
        key2 = compute_cache_key("/some/path_b.py", "query")
        assert key1 != key2

    def test_normpath_normalizes_trivial_variations(self):
        key1 = compute_cache_key("./src.py", "query")
        key2 = compute_cache_key("src.py", "query")
        assert key1 == key2

    def test_normpath_collapses_double_slash(self):
        key1 = compute_cache_key("a//b.py", "query")
        key2 = compute_cache_key("a/b.py", "query")
        assert key1 == key2

    def test_key_is_sha256_hex(self):
        key = compute_cache_key("file.py", "query")
        assert len(key) == 64
        assert all(c in "0123456789abcdef" for c in key)

    def test_key_matches_expected_sha256(self):
        path = "file.py"
        query = "query"
        expected = hashlib.sha256(
            (os.path.normpath(path) + "\n" + query).encode()
        ).hexdigest()
        assert compute_cache_key(path, query) == expected


# ---------------------------------------------------------------------------
# Req 6: Freshness & error handling
# ---------------------------------------------------------------------------

class TestFreshnessAndErrorHandling:
    def test_stale_cache_triggers_re_extraction(self, temp_project, mock_llm):
        _, source_file = temp_project
        extractor = IncludeQueryExtractor()

        extractor.extract(str(source_file), "query")
        assert mock_llm["llm_invoke"].call_count == 1

        # Modify source file → hash changes → stale
        source_file.write_text("Modified content.", encoding="utf-8")

        extractor.extract(str(source_file), "query")
        assert mock_llm["llm_invoke"].call_count == 2

    def test_stale_cache_removes_old_files_before_re_extract(self, temp_project, mock_llm):
        tmp_path, source_file = temp_project
        extractor = IncludeQueryExtractor()

        extractor.extract(str(source_file), "query")

        cache_dir = tmp_path / ".pdd" / "extracts"
        md_file = list(cache_dir.glob("*.md"))[0]
        meta_file = list(cache_dir.glob("*.meta.json"))[0]

        # Modify source
        source_file.write_text("New content.", encoding="utf-8")

        mock_llm["llm_invoke"].return_value = "New extraction"
        extractor.extract(str(source_file), "query")

        # Files should be updated with new content
        assert md_file.read_text(encoding="utf-8") == "New extraction"
        new_meta = json.loads(meta_file.read_text(encoding="utf-8"))
        expected_hash = hashlib.sha256("New content.".encode()).hexdigest()
        assert new_meta["source_hash"] == expected_hash

    def test_corrupted_metadata_triggers_re_extraction(self, temp_project, mock_llm):
        tmp_path, source_file = temp_project
        extractor = IncludeQueryExtractor()

        extractor.extract(str(source_file), "query")
        assert mock_llm["llm_invoke"].call_count == 1

        # Corrupt the metadata file
        cache_dir = tmp_path / ".pdd" / "extracts"
        meta_file = list(cache_dir.glob("*.meta.json"))[0]
        meta_file.write_text("NOT VALID JSON {{{", encoding="utf-8")

        extractor.extract(str(source_file), "query")
        assert mock_llm["llm_invoke"].call_count == 2

    def test_missing_md_file_triggers_re_extraction(self, temp_project, mock_llm):
        tmp_path, source_file = temp_project
        extractor = IncludeQueryExtractor()

        extractor.extract(str(source_file), "query")
        assert mock_llm["llm_invoke"].call_count == 1

        # Delete just the .md file
        cache_dir = tmp_path / ".pdd" / "extracts"
        md_file = list(cache_dir.glob("*.md"))[0]
        md_file.unlink()

        extractor.extract(str(source_file), "query")
        assert mock_llm["llm_invoke"].call_count == 2

    def test_missing_meta_file_triggers_re_extraction(self, temp_project, mock_llm):
        tmp_path, source_file = temp_project
        extractor = IncludeQueryExtractor()

        extractor.extract(str(source_file), "query")
        assert mock_llm["llm_invoke"].call_count == 1

        # Delete just the .meta.json file
        cache_dir = tmp_path / ".pdd" / "extracts"
        meta_file = list(cache_dir.glob("*.meta.json"))[0]
        meta_file.unlink()

        extractor.extract(str(source_file), "query")
        assert mock_llm["llm_invoke"].call_count == 2


# ---------------------------------------------------------------------------
# Req 7: EXTRACTS_CACHE_ENABLE env var
# ---------------------------------------------------------------------------

class TestCacheEnableEnvVar:
    def test_cache_disabled_no_files_created(self, temp_project, mock_llm, monkeypatch):
        tmp_path, source_file = temp_project
        monkeypatch.setenv(_ENV_CACHE_ENABLE, "false")

        extractor = IncludeQueryExtractor()
        extractor.extract(str(source_file), "query")

        cache_dir = tmp_path / ".pdd" / "extracts"
        if cache_dir.exists():
            assert len(list(cache_dir.glob("*.md"))) == 0
            assert len(list(cache_dir.glob("*.meta.json"))) == 0

    def test_cache_disabled_always_calls_llm(self, temp_project, mock_llm, monkeypatch):
        _, source_file = temp_project
        monkeypatch.setenv(_ENV_CACHE_ENABLE, "false")

        extractor = IncludeQueryExtractor()
        extractor.extract(str(source_file), "query")
        extractor.extract(str(source_file), "query")

        assert mock_llm["llm_invoke"].call_count == 2

    def test_cache_disabled_with_zero(self, temp_project, mock_llm, monkeypatch):
        _, source_file = temp_project
        monkeypatch.setenv(_ENV_CACHE_ENABLE, "0")

        extractor = IncludeQueryExtractor()
        extractor.extract(str(source_file), "query")
        extractor.extract(str(source_file), "query")

        assert mock_llm["llm_invoke"].call_count == 2

    def test_cache_disabled_with_no(self, temp_project, mock_llm, monkeypatch):
        _, source_file = temp_project
        monkeypatch.setenv(_ENV_CACHE_ENABLE, "no")

        extractor = IncludeQueryExtractor()
        extractor.extract(str(source_file), "query")
        extractor.extract(str(source_file), "query")

        assert mock_llm["llm_invoke"].call_count == 2

    def test_cache_enabled_by_default(self, temp_project, mock_llm, monkeypatch):
        tmp_path, source_file = temp_project
        monkeypatch.delenv(_ENV_CACHE_ENABLE, raising=False)

        extractor = IncludeQueryExtractor()
        extractor.extract(str(source_file), "query")

        cache_dir = tmp_path / ".pdd" / "extracts"
        assert len(list(cache_dir.glob("*.md"))) == 1


# ---------------------------------------------------------------------------
# Edge cases
# ---------------------------------------------------------------------------

class TestEdgeCases:
    def test_empty_query(self, temp_project, mock_llm):
        _, source_file = temp_project
        extractor = IncludeQueryExtractor()
        result = extractor.extract(str(source_file), "")
        assert isinstance(result, str)

    def test_empty_llm_result(self, temp_project, mock_llm):
        mock_llm["llm_invoke"].return_value = ""
        tmp_path, source_file = temp_project
        extractor = IncludeQueryExtractor()
        result = extractor.extract(str(source_file), "query")
        assert result == ""

        # token_count should be 0 for empty result
        cache_dir = tmp_path / ".pdd" / "extracts"
        meta_file = list(cache_dir.glob("*.meta.json"))[0]
        meta = json.loads(meta_file.read_text(encoding="utf-8"))
        assert meta["token_count"] == 0

    def test_file_not_found_raises(self, temp_project, mock_llm):
        _, _ = temp_project
        extractor = IncludeQueryExtractor()
        with pytest.raises((FileNotFoundError, OSError)):
            extractor.extract("/nonexistent/file.txt", "query")

    def test_cache_files_named_by_cache_key(self, temp_project, mock_llm):
        tmp_path, source_file = temp_project
        extractor = IncludeQueryExtractor()
        extractor.extract(str(source_file), "query")

        cache_dir = tmp_path / ".pdd" / "extracts"
        md_files = list(cache_dir.glob("*.md"))
        meta_files = list(cache_dir.glob("*.meta.json"))

        # File stems should be valid sha256 hex digests (64 chars)
        md_stem = md_files[0].stem
        meta_stem = meta_files[0].name.replace(".meta.json", "")
        assert len(md_stem) == 64
        assert len(meta_stem) == 64
        assert md_stem == meta_stem


# ---------------------------------------------------------------------------
# Atomic cache writes
# ---------------------------------------------------------------------------

class TestAtomicCacheWrites:
    """Cache writes should be atomic — no partial/zombie files on crash."""

    def test_interrupted_write_leaves_no_partial_md(self, temp_project, mock_llm, monkeypatch):
        """If meta write fails after md write, no orphan .md should remain."""
        tmp_path, source_file = temp_project
        cache_dir = tmp_path / ".pdd" / "extracts"
        cache_dir.mkdir(parents=True, exist_ok=True)

        original_write = Path.write_text
        write_count = {"n": 0}

        def crashing_write(self, content, *args, **kwargs):
            write_count["n"] += 1
            # Let the first write (temp file for md) succeed, crash on second (temp file for meta)
            if write_count["n"] == 2:
                raise OSError("Simulated crash during meta write")
            return original_write(self, content, *args, **kwargs)

        monkeypatch.setattr(Path, "write_text", crashing_write)

        extractor = IncludeQueryExtractor()
        with pytest.raises(OSError, match="Simulated crash"):
            extractor.extract(str(source_file), "query")

        # No .md or .meta.json should exist in the cache (no partial state)
        md_files = list(cache_dir.glob("*.md"))
        meta_files = list(cache_dir.glob("*.meta.json"))
        assert len(md_files) == 0, f"Orphan .md files found: {md_files}"
        assert len(meta_files) == 0, f"Orphan .meta.json files found: {meta_files}"


# ---------------------------------------------------------------------------
# Path handling bug tests (issue #603)
# ---------------------------------------------------------------------------

class TestCacheKeyPathConsistency:
    """compute_cache_key should produce the same key for the same physical
    file regardless of how the path is expressed (relative, absolute,
    different CWD). Currently it uses os.path.normpath which does NOT
    resolve to absolute paths, so these tests fail."""

    def test_relative_vs_absolute_path_same_key(self):
        """Same file referenced as 'src/file.py' vs its absolute path
        should produce the same cache key."""
        abs_path = os.path.abspath("src/file.py")
        key_rel = compute_cache_key("src/file.py", "summarize this")
        key_abs = compute_cache_key(abs_path, "summarize this")
        assert key_rel == key_abs, (
            f"Same file produces different cache keys when referenced by "
            f"relative vs absolute path. Relative key: {key_rel[:16]}..., "
            f"Absolute key: {key_abs[:16]}..."
        )

    def test_different_relative_paths_same_file(self):
        """'./subdir/../src/file.py' and 'src/file.py' refer to the same
        file — normpath resolves them identically, so this already works."""
        key1 = compute_cache_key("./subdir/../src/file.py", "query")
        key2 = compute_cache_key("src/file.py", "query")
        assert key1 == key2, (
            "normpath should collapse '../' — if this fails, normpath behavior changed"
        )

    def test_repo_root_relative_paths_are_stable(self):
        """Repo-root-relative paths (the format used after the CSV path fix)
        produce consistent cache keys regardless of trivial variations."""
        key1 = compute_cache_key("src/file.py", "query")
        key2 = compute_cache_key("./src/file.py", "query")
        key3 = compute_cache_key("src//file.py", "query")
        assert key1 == key2 == key3, (
            f"Trivial path variations should produce the same cache key. "
            f"'src/file.py': {key1[:16]}..., "
            f"'./src/file.py': {key2[:16]}..., "
            f"'src//file.py': {key3[:16]}..."
        )

    def test_absolute_vs_relative_path_same_cache_key(self, tmp_path):
        """Bug #4 from PR #763: absolute and relative paths for the same file
        should produce identical cache keys after normalization to
        project-relative form."""
        from unittest.mock import patch

        pdd_dir = tmp_path / "pdd"
        pdd_dir.mkdir()
        (pdd_dir / "utils.py").write_text("def helper(): pass")

        with patch(
            "pdd.path_resolution.find_project_root_from_path",
            return_value=str(tmp_path),
        ):
            key_relative = compute_cache_key("pdd/utils.py", "What functions are available?")
            key_absolute = compute_cache_key(
                str(tmp_path / "pdd" / "utils.py"), "What functions are available?"
            )

        assert key_relative == key_absolute, (
            f"Bug #4: Cache keys differ for same file. "
            f"Relative: {key_relative[:16]}..., Absolute: {key_absolute[:16]}.... "
            "compute_cache_key should normalize paths to project-relative form."
        )
