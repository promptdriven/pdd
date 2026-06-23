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
    _ENV_EXTRACTION_STRENGTH,
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
            exclude=["file_content", "query"],
        )

    def test_calls_llm_with_strong_strength(self, temp_project, mock_llm, monkeypatch):
        _, source_file = temp_project
        monkeypatch.delenv(_ENV_EXTRACTION_STRENGTH, raising=False)

        extractor = IncludeQueryExtractor()
        extractor.extract(str(source_file), "query")

        call_kwargs = mock_llm["llm_invoke"].call_args
        assert call_kwargs.kwargs["strength"] == 1.0

    def test_extraction_strength_can_be_overridden(self, temp_project, mock_llm, monkeypatch):
        _, source_file = temp_project
        monkeypatch.setenv(_ENV_EXTRACTION_STRENGTH, "0.5")

        extractor = IncludeQueryExtractor()
        extractor.extract(str(source_file), "query")

        call_kwargs = mock_llm["llm_invoke"].call_args
        assert call_kwargs.kwargs["strength"] == 0.5

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

    def test_absolute_path_cache_key_stable_across_cwds(
        self, tmp_path, monkeypatch
    ):
        """When compute_cache_key is given an absolute path, the cache key
        must be identical regardless of CWD. Path normalization to
        project-relative form uses the file's own project root (found by
        walking up from the file), not CWD's project root — so moving CWD
        to an unrelated directory must not change the key.
        """
        project = tmp_path / "proj"
        project.mkdir()
        (project / ".pddrc").touch()
        pdd_dir = project / "pdd"
        pdd_dir.mkdir()
        (pdd_dir / "utils.py").write_text("def helper(): pass")
        abs_path = str((pdd_dir / "utils.py").resolve())
        query = "list helper functions"

        # CWD inside the project
        monkeypatch.chdir(project)
        key_from_inside = compute_cache_key(abs_path, query)

        # CWD in a sibling directory with no markers — project root for "."
        # would resolve to something other than `project`.
        outside = tmp_path / "elsewhere"
        outside.mkdir()
        monkeypatch.chdir(outside)
        key_from_outside = compute_cache_key(abs_path, query)

        assert key_from_inside == key_from_outside, (
            f"Cache key must depend only on the file's project root, "
            f"not on CWD. Got inside={key_from_inside[:16]}..., "
            f"outside={key_from_outside[:16]}..."
        )


# ---------------------------------------------------------------------------
# Req 10: Session-level extraction guard (issue #1711)
# ---------------------------------------------------------------------------
#
# pdd sync repeatedly issued the same <include query="..."> LLM extraction
# call because IncludeQueryExtractor.extract() had no session-level guard.
# The disk cache is the only deduplication mechanism, but its validity check
# requires an exact source_hash match. When pdd sync operations (generate,
# fix, update) modify the referenced source file, the hash changes, the disk
# cache is invalidated, and a fresh LLM call fires unconditionally — up to
# 6+ times in a single run, burning ~$1.70 with no useful output.
#
# The fix adds:
#   MAX_SESSION_EXTRACTIONS = 2                                (constant)
#   IncludeQueryExtractor._session_extraction_counts: dict    (class-level)
#   IncludeQueryExtractor.reset_session()                     (classmethod)
#   RepeatedRetrievalQueryError                               (exception)
#
# All tests in TestSessionExtractionGuard FAIL on current buggy code and
# PASS after the fix. Tests in TestIssue1711BugDocumentation document the
# current behavior and PASS on both old and new code.

# The reported query string from issue #1711
_ISSUE_1711_QUERY = (
    "implementation of the multi-step orchestrator pipeline and error handling"
)

# Maximum LLM calls allowed per (file, query) pair per session.
# Must match the constant the fix adds to include_query_extractor.py.
_MAX_SESSION_EXTRACTIONS = 2

# How many times the bug caused the query to fire in the reported incident
_REPORTED_REPEAT_COUNT = 6


@pytest.fixture
def issue_1711_source_file(tmp_path, monkeypatch):
    """Temporary project with orchestrator.py as the source file (matches issue #1711)."""
    monkeypatch.setattr(
        "pdd.path_resolution.find_project_root_from_path",
        lambda *args, **kwargs: str(tmp_path),
    )
    monkeypatch.setenv(_ENV_CACHE_ENABLE, "true")
    source_file = tmp_path / "orchestrator.py"
    source_file.write_text(
        "# initial content\ndef orchestrate(): pass",
        encoding="utf-8",
    )
    return tmp_path, source_file


class TestSessionExtractionGuard:
    """Req 10: session-level guard prevents repeated identical (file, query) LLM calls.

    All tests FAIL on the current (buggy) code (no guard exists) and PASS
    after the fix adds MAX_SESSION_EXTRACTIONS, _session_extraction_counts,
    reset_session(), and RepeatedRetrievalQueryError.
    """

    @pytest.fixture(autouse=True)
    def reset_session_state(self):
        """Clear session extraction counts before and after each test.

        Safe to call when reset_session() does not yet exist (pre-fix code):
        the fixture is a no-op in that case.
        """
        reset = getattr(IncludeQueryExtractor, "reset_session", None)
        if reset is not None:
            reset()
        yield
        reset = getattr(IncludeQueryExtractor, "reset_session", None)
        if reset is not None:
            reset()

    def test_session_guard_caps_llm_calls_same_instance(
        self, issue_1711_source_file, mock_llm
    ):
        """Session guard caps LLM calls when source file changes between iterations (same instance).

        Reproduces the exact scenario from issue #1711: pdd sync modifies the
        source file (via generate/fix/update) between iterations. Each modification
        causes a cache miss and a fresh LLM call with no upper bound.

        FAILS on current buggy code: llm_invoke fires 6 times, no guard exists.
        PASSES after fix: guard fires at or before MAX_SESSION_EXTRACTIONS calls.
        """
        _, source_file = issue_1711_source_file
        extractor = IncludeQueryExtractor()

        try:
            for i in range(_REPORTED_REPEAT_COUNT):
                # Simulate generate/fix/update modifying the source file.
                source_file.write_text(
                    f"# version {i}\ndef orchestrate_v{i}(): pass",
                    encoding="utf-8",
                )
                extractor.extract(str(source_file), _ISSUE_1711_QUERY)
        except Exception:
            # Fail-fast guard raising an exception is an acceptable implementation.
            pass

        assert mock_llm["llm_invoke"].call_count <= _MAX_SESSION_EXTRACTIONS, (
            f"Bug #1711: session guard missing — llm_invoke fired "
            f"{mock_llm['llm_invoke'].call_count} times "
            f"(expected ≤ {_MAX_SESSION_EXTRACTIONS}) when the source file changed "
            "on every sync iteration."
        )

    def test_session_guard_works_across_new_instances(
        self, issue_1711_source_file, mock_llm
    ):
        """Session guard enforces limit when a new IncludeQueryExtractor is created per call.

        Production pattern: preprocess.py:712 creates a new IncludeQueryExtractor()
        on every process_include_tags() call. A guard that lives only in instance
        state would be discarded on every call and never fire. The guard MUST be
        class-level or module-level to survive instance turnover.

        FAILS on current buggy code: every new instance has no session memory.
        PASSES after fix: class-level counter spans instance boundaries.
        """
        _, source_file = issue_1711_source_file

        try:
            for i in range(_REPORTED_REPEAT_COUNT):
                source_file.write_text(
                    f"# version {i}\ndef orchestrate_v{i}(): pass",
                    encoding="utf-8",
                )
                # New instance per call — same as the real sync loop via preprocess.py:712
                IncludeQueryExtractor().extract(str(source_file), _ISSUE_1711_QUERY)
        except Exception:
            pass

        assert mock_llm["llm_invoke"].call_count <= _MAX_SESSION_EXTRACTIONS, (
            f"Bug #1711: session guard must be class/module-level. "
            f"Got {mock_llm['llm_invoke'].call_count} LLM calls across "
            f"{_REPORTED_REPEAT_COUNT} new IncludeQueryExtractor instances "
            f"(expected ≤ {_MAX_SESSION_EXTRACTIONS})."
        )

    def test_guard_does_not_make_extra_llm_call_after_limit(
        self, issue_1711_source_file, mock_llm
    ):
        """After the session limit is reached, llm_invoke is not called again.

        Whether the guard raises an exception (fail-fast) or returns a stale
        result (tolerant), the LLM must NOT be called beyond MAX_SESSION_EXTRACTIONS.
        Both valid implementations satisfy this test.

        FAILS on current buggy code: no guard exists, so the LLM is called
        unconditionally on every cache miss.
        """
        _, source_file = issue_1711_source_file
        extractor = IncludeQueryExtractor()

        try:
            for i in range(_MAX_SESSION_EXTRACTIONS + 1):
                source_file.write_text(
                    f"# version {i}\ndef orchestrate_v{i}(): pass",
                    encoding="utf-8",
                )
                extractor.extract(str(source_file), _ISSUE_1711_QUERY)
        except Exception:
            # Fail-fast guard: exception at or before the limit is acceptable.
            pass

        assert mock_llm["llm_invoke"].call_count <= _MAX_SESSION_EXTRACTIONS, (
            f"Bug #1711: guard must prevent LLM call #{_MAX_SESSION_EXTRACTIONS + 1}. "
            f"Got {mock_llm['llm_invoke'].call_count} calls."
        )

    def test_session_guard_tracks_per_file_query_pair_independently(
        self, issue_1711_source_file, mock_llm
    ):
        """Session guard counts independently for each (file, query) pair.

        Different queries on the same file each get their own counter keyed on
        cache_key = sha256(rel_path + '\\n' + query). A global counter would
        incorrectly block legitimate new queries after another is exhausted.

        FAILS on current buggy code: no guard at all, so all calls go through
        (3 queries × 6 iterations = 18 calls > expected maximum of 6).
        PASSES after fix: each query capped independently at MAX_SESSION_EXTRACTIONS.
        """
        _, source_file = issue_1711_source_file
        extractor = IncludeQueryExtractor()

        queries = [
            "orchestrator pipeline implementation",
            "error handling strategy",
            "retry logic",
        ]
        try:
            for query in queries:
                for i in range(_REPORTED_REPEAT_COUNT):
                    source_file.write_text(
                        f"# version {i} for {query[:10]}", encoding="utf-8"
                    )
                    extractor.extract(str(source_file), query)
        except Exception:
            pass

        # Each query may trigger at most _MAX_SESSION_EXTRACTIONS LLM calls.
        expected_max = len(queries) * _MAX_SESSION_EXTRACTIONS
        assert mock_llm["llm_invoke"].call_count <= expected_max, (
            f"Bug #1711: per-(file, query) guard must allow independent queries. "
            f"Expected ≤ {expected_max} calls for {len(queries)} distinct queries "
            f"× {_MAX_SESSION_EXTRACTIONS} allowed each. "
            f"Got {mock_llm['llm_invoke'].call_count}."
        )

    def test_reset_session_allows_re_extraction_after_limit(
        self, issue_1711_source_file, mock_llm
    ):
        """reset_session() clears the counter so fresh extractions are permitted.

        Tests and sync_orchestration.py can call reset_session() at the start
        of each top-level pdd sync run to allow the full quota again.

        FAILS on current buggy code: IncludeQueryExtractor.reset_session() does
        not exist (raises AttributeError).
        PASSES after fix: reset_session() clears _session_extraction_counts.
        """
        _, source_file = issue_1711_source_file
        extractor = IncludeQueryExtractor()

        # Exhaust the session limit
        try:
            for i in range(_MAX_SESSION_EXTRACTIONS + 1):
                source_file.write_text(f"# version {i}", encoding="utf-8")
                extractor.extract(str(source_file), _ISSUE_1711_QUERY)
        except Exception:
            pass

        calls_before_reset = mock_llm["llm_invoke"].call_count

        # This raises AttributeError on buggy code (reset_session doesn't exist),
        # which correctly marks this test as failing until the fix is applied.
        IncludeQueryExtractor.reset_session()

        # After reset, a further call on a freshly-changed file should invoke the LLM.
        source_file.write_text("# version after reset\ndef orchestrate_reset(): pass", encoding="utf-8")
        extractor.extract(str(source_file), _ISSUE_1711_QUERY)

        assert mock_llm["llm_invoke"].call_count > calls_before_reset, (
            "Bug #1711: After reset_session(), extract() should permit a new LLM call "
            "for the same (file, query) pair on a freshly-changed file."
        )

    def test_querying_console_output_bounded_by_session_guard(
        self, issue_1711_source_file, mock_llm, monkeypatch
    ):
        """The 'Querying...' Rich message is emitted ≤ MAX_SESSION_EXTRACTIONS times.

        This directly covers the user-visible symptom from issue #1711: the same
        \"query='implementation of the multi-step orchestrator pipeline and error\"
        line was printed 6× to the user before the run exited 1 with
        \"Overall status: Failed\".

        FAILS on current buggy code: the message is printed once per LLM call,
        with no session bound, so it appears 6 times.
        PASSES after fix: guard fires before the 3rd print.
        """
        _, source_file = issue_1711_source_file

        console_prints: list[str] = []
        mock_console = MagicMock()
        mock_console.print.side_effect = lambda *args, **kwargs: console_prints.append(
            args[0] if args else ""
        )
        monkeypatch.setattr("pdd.include_query_extractor._console", mock_console)

        extractor = IncludeQueryExtractor()

        try:
            for i in range(_REPORTED_REPEAT_COUNT):
                source_file.write_text(
                    f"# version {i}\ndef orchestrate_v{i}(): pass",
                    encoding="utf-8",
                )
                extractor.extract(str(source_file), _ISSUE_1711_QUERY)
        except Exception:
            pass

        querying_prints = [
            msg for msg in console_prints
            if isinstance(msg, str) and "Querying" in msg
        ]

        assert len(querying_prints) <= _MAX_SESSION_EXTRACTIONS, (
            f"Bug #1711: 'Querying...' was printed {len(querying_prints)} times — "
            "this is the exact repeated output users saw. "
            f"Session guard should cap it at {_MAX_SESSION_EXTRACTIONS}."
        )

    def test_session_guard_applies_when_cache_disabled(
        self, issue_1711_source_file, mock_llm, monkeypatch
    ):
        """Session guard must apply even when EXTRACTS_CACHE_ENABLE=false.

        With no disk cache, the session guard is the ONLY deduplication mechanism.
        If the guard lives inside the `if _cache_enabled():` branch, it would be
        bypassed entirely when the cache is disabled, leaving the LLM unguarded.

        FAILS on current buggy code: no guard exists anywhere.
        PASSES after fix: guard sits in the unconditional extraction path.
        """
        _, source_file = issue_1711_source_file
        monkeypatch.setenv(_ENV_CACHE_ENABLE, "false")

        extractor = IncludeQueryExtractor()

        try:
            for i in range(_REPORTED_REPEAT_COUNT):
                source_file.write_text(
                    f"# version {i}\ndef orchestrate_v{i}(): pass",
                    encoding="utf-8",
                )
                extractor.extract(str(source_file), _ISSUE_1711_QUERY)
        except Exception:
            pass

        assert mock_llm["llm_invoke"].call_count <= _MAX_SESSION_EXTRACTIONS, (
            f"Bug #1711: session guard must apply even when disk cache is disabled. "
            f"Got {mock_llm['llm_invoke'].call_count} LLM calls with "
            f"EXTRACTS_CACHE_ENABLE=false (expected ≤ {_MAX_SESSION_EXTRACTIONS})."
        )

    def test_process_include_tags_integration_bounded_by_session_guard(
        self, issue_1711_source_file, mock_llm, monkeypatch
    ):
        """Session guard propagates through the full process_include_tags() call chain.

        preprocess.py:712 creates a new IncludeQueryExtractor() on every
        process_include_tags() call. The guard must cap total LLM calls even
        through this real integration path, mirroring the actual pdd sync loop
        where preprocess() is invoked for every operation (generate, fix, update).

        FAILS on current buggy code: 6 LLM calls, one per sync iteration.
        PASSES after fix: class-level guard caps calls at MAX_SESSION_EXTRACTIONS.
        """
        from pdd.preprocess import process_include_tags

        _, source_file = issue_1711_source_file

        prompt_template = (
            f'<include query="{_ISSUE_1711_QUERY}">'
            f"{source_file}</include>"
        )

        monkeypatch.setattr(
            "pdd.preprocess.get_file_path",
            lambda p: str(source_file),
        )

        try:
            for i in range(_REPORTED_REPEAT_COUNT):
                source_file.write_text(
                    f"# orchestrator version {i}", encoding="utf-8"
                )
                process_include_tags(prompt_template, recursive=False)
        except Exception:
            pass

        assert mock_llm["llm_invoke"].call_count <= _MAX_SESSION_EXTRACTIONS, (
            f"Bug #1711: process_include_tags fired the LLM "
            f"{mock_llm['llm_invoke'].call_count} times across "
            f"{_REPORTED_REPEAT_COUNT} sync iterations "
            f"(expected ≤ {_MAX_SESSION_EXTRACTIONS}). "
            "Session guard must survive the new-instance-per-call pattern in preprocess.py."
        )


# ---------------------------------------------------------------------------
# Reproduction tests from Step 5 — issue #1711
# ---------------------------------------------------------------------------
# These tests document the current (buggy) behavior and verify the existing
# disk-cache behavior that must not regress after the fix.

class TestIssue1711BugDocumentation:
    """Document bug #1711 behavior — these tests PASS on current (buggy) code.

    test_file_change_triggers_cache_miss_and_repeated_llm_call asserts the
    buggy call count (6). After the fix is applied, this assertion should be
    updated to assert call_count <= _MAX_SESSION_EXTRACTIONS.
    """

    @pytest.fixture(autouse=True)
    def reset_session_state(self):
        reset = getattr(IncludeQueryExtractor, "reset_session", None)
        if reset is not None:
            reset()
        yield
        reset = getattr(IncludeQueryExtractor, "reset_session", None)
        if reset is not None:
            reset()

    def test_file_change_triggers_cache_miss_and_repeated_llm_call(
        self, issue_1711_source_file, mock_llm
    ):
        """DOCUMENTS BUG #1711: each file-content change causes a fresh LLM call.

        When pdd sync modifies the source file between iterations, the disk
        cache's source_hash check fails, the stale cache is deleted, and
        llm_invoke fires unconditionally — 6 times in the reported incident.

        This test PASSES on the current (buggy) code to document the observed
        behavior. See TestSessionExtractionGuard for the post-fix assertions.
        """
        _, source_file = issue_1711_source_file
        extractor = IncludeQueryExtractor()

        for i in range(_REPORTED_REPEAT_COUNT):
            source_file.write_text(
                f"# version {i}\ndef orchestrate_v{i}(): pass",
                encoding="utf-8",
            )
            extractor.extract(str(source_file), _ISSUE_1711_QUERY)

        # Documents the bug: N calls for N file versions with no guard.
        # After the fix, update this to: call_count <= _MAX_SESSION_EXTRACTIONS
        assert mock_llm["llm_invoke"].call_count == _REPORTED_REPEAT_COUNT, (
            f"Bug #1711 documented: the same query fired {_REPORTED_REPEAT_COUNT} "
            "times when the source file changed between each sync iteration. "
            "This is a documentation test — see TestSessionExtractionGuard for "
            "the assertions that verify the fix."
        )


class TestIssue1711BaselineCacheBehavior:
    """Confirm existing disk-cache behavior when the file does NOT change.

    These tests pass today and must continue passing after the fix is applied.
    """

    @pytest.fixture(autouse=True)
    def reset_session_state(self):
        reset = getattr(IncludeQueryExtractor, "reset_session", None)
        if reset is not None:
            reset()
        yield
        reset = getattr(IncludeQueryExtractor, "reset_session", None)
        if reset is not None:
            reset()

    def test_cache_hit_prevents_repeated_llm_call_same_content(
        self, issue_1711_source_file, mock_llm
    ):
        """Unchanged file across N calls → only 1 LLM call (disk cache hit).

        The disk cache is keyed on (rel_path, query) and validated against the
        file's SHA-256 content hash. When the file does not change, the cache
        hit path returns early with no LLM call.
        """
        _, source_file = issue_1711_source_file
        extractor = IncludeQueryExtractor()

        for _ in range(_REPORTED_REPEAT_COUNT):
            extractor.extract(str(source_file), _ISSUE_1711_QUERY)

        assert mock_llm["llm_invoke"].call_count == 1, (
            "Disk cache should prevent repeated LLM calls when the file is unchanged. "
            f"Got {mock_llm['llm_invoke'].call_count} calls."
        )

    def test_new_extractor_instance_still_hits_cache_for_unchanged_file(
        self, issue_1711_source_file, mock_llm
    ):
        """Fresh IncludeQueryExtractor instance on the same unchanged file uses disk cache.

        Critical: process_include_tags() creates a new IncludeQueryExtractor()
        on every call (preprocess.py:712). The disk cache must serve subsequent
        calls even when instance state is discarded between calls.
        """
        _, source_file = issue_1711_source_file

        # First call populates disk cache
        IncludeQueryExtractor().extract(str(source_file), _ISSUE_1711_QUERY)

        # Subsequent calls with new instances — same as the real sync loop
        for _ in range(_REPORTED_REPEAT_COUNT - 1):
            IncludeQueryExtractor().extract(str(source_file), _ISSUE_1711_QUERY)

        assert mock_llm["llm_invoke"].call_count == 1, (
            "Disk cache should serve subsequent calls even with new extractor instances."
        )
