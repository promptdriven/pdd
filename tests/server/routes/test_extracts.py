"""
Tests for pdd/server/routes/extracts.py — the extracts browsing API.

Tests target the three public endpoints and the public get/set_project_root
dependency. Only external behaviors (HTTP responses, freshness checks against
the filesystem) are tested — no mocking of private helpers.
"""

import hashlib
import json
import os
from pathlib import Path

import pytest
from fastapi import FastAPI
from fastapi.testclient import TestClient

from pdd.server.routes.extracts import (
    router,
    get_project_root,
    set_project_root,
    compute_cache_key,
)


# ---------------------------------------------------------------------------
# Helpers
# ---------------------------------------------------------------------------

def _cache_key(source_path: str, query: str) -> str:
    """Compute a cache key the same way the module does (normpath + sha256)."""
    normalized = os.path.normpath(source_path)
    return hashlib.sha256((normalized + "\n" + query).encode("utf-8")).hexdigest()


def _write_extract(extracts_dir: Path, source_path: str, query: str,
                   content: str, source_hash: str,
                   timestamp: str = "2024-01-15T10:00:00Z") -> str:
    """Write a .md + .meta.json pair and return the cache key."""
    key = _cache_key(source_path, query)
    (extracts_dir / f"{key}.md").write_text(content)
    (extracts_dir / f"{key}.meta.json").write_text(json.dumps({
        "source_path": source_path,
        "query": query,
        "timestamp": timestamp,
        "source_hash": source_hash,
    }))
    return key


# ---------------------------------------------------------------------------
# Fixtures
# ---------------------------------------------------------------------------

@pytest.fixture
def app():
    a = FastAPI()
    a.include_router(router)
    return a


@pytest.fixture
def client(app):
    return TestClient(app)


@pytest.fixture
def project(tmp_path):
    """Set up a minimal project with one source file and one cached extract."""
    extracts_dir = tmp_path / ".pdd" / "extracts"
    extracts_dir.mkdir(parents=True)

    # Source file
    src = tmp_path / "src.py"
    src.write_text("print('hello')")
    src_hash = hashlib.sha256(b"print('hello')").hexdigest()

    # Cached extract
    _write_extract(extracts_dir, "src.py", "find prints", "extracted content", src_hash)

    set_project_root(tmp_path)
    yield tmp_path
    set_project_root(None)


# ===================================================================
# Requirement 6: project root dependency injection (get/set pattern)
# ===================================================================

class TestProjectRootDependency:
    def test_set_and_get(self, tmp_path):
        set_project_root(tmp_path)
        assert get_project_root() == tmp_path
        set_project_root(None)

    def test_raises_when_not_configured(self):
        set_project_root(None)
        with pytest.raises(RuntimeError):
            get_project_root()


# ===================================================================
# Requirement 1: Pydantic response model field names/types
# ===================================================================

class TestResponseModels:
    def test_extract_list_response_shape(self, client, project):
        resp = client.get("/api/v1/extracts")
        assert resp.status_code == 200
        data = resp.json()
        # ExtractListResponse fields
        assert "extracts" in data
        assert "total" in data
        assert "stale_count" in data
        assert isinstance(data["extracts"], list)
        assert isinstance(data["total"], int)
        assert isinstance(data["stale_count"], int)

    def test_extract_metadata_shape(self, client, project):
        resp = client.get("/api/v1/extracts")
        ext = resp.json()["extracts"][0]
        for field in ("cache_key", "source_path", "query", "timestamp",
                       "source_hash", "is_fresh"):
            assert field in ext, f"Missing field: {field}"

    def test_extract_content_shape(self, client, project):
        key = _cache_key("src.py", "find prints")
        resp = client.get(f"/api/v1/extracts/{key}")
        assert resp.status_code == 200
        data = resp.json()
        for field in ("cache_key", "source_path", "query", "timestamp",
                       "source_hash", "is_fresh", "content"):
            assert field in data, f"Missing field: {field}"

    def test_prompt_extract_info_shape(self, client, project):
        prompt = project / "test.prompt"
        prompt.write_text('<include query="find prints">src.py</include>')
        resp = client.get("/api/v1/extracts/for-prompt",
                          params={"prompt_path": "test.prompt"})
        assert resp.status_code == 200
        info = resp.json()[0]
        for field in ("include_path", "query", "cache_key",
                       "has_cached_entry", "source_path", "timestamp", "is_fresh"):
            assert field in info, f"Missing field: {field}"


# ===================================================================
# Requirement 2: GET / — list all cached extracts
# ===================================================================

class TestListExtracts:
    def test_returns_extracts(self, client, project):
        resp = client.get("/api/v1/extracts")
        assert resp.status_code == 200
        data = resp.json()
        assert data["total"] == 1
        assert data["extracts"][0]["source_path"] == "src.py"

    def test_empty_when_dir_missing(self, client, tmp_path):
        """Return empty list when .pdd/extracts/ does not exist."""
        set_project_root(tmp_path)
        resp = client.get("/api/v1/extracts")
        assert resp.status_code == 200
        data = resp.json()
        assert data["total"] == 0
        assert data["extracts"] == []
        set_project_root(None)

    def test_skips_corrupted_meta(self, client, project):
        """Gracefully skip corrupted .meta.json files."""
        extracts_dir = project / ".pdd" / "extracts"
        bad = extracts_dir / ("badbadbad" + "0" * 55 + ".meta.json")
        bad.write_text("NOT JSON {{{")
        resp = client.get("/api/v1/extracts")
        assert resp.status_code == 200
        # Should still return the one valid extract
        assert resp.json()["total"] == 1

    def test_sorted_by_timestamp_descending(self, client, tmp_path):
        """Extracts should be sorted by timestamp descending."""
        extracts_dir = tmp_path / ".pdd" / "extracts"
        extracts_dir.mkdir(parents=True)

        src = tmp_path / "a.py"
        src.write_text("a")
        h = hashlib.sha256(b"a").hexdigest()

        _write_extract(extracts_dir, "a.py", "q1", "c1", h, "2024-01-01T00:00:00Z")
        _write_extract(extracts_dir, "a.py", "q3", "c3", h, "2024-03-01T00:00:00Z")
        _write_extract(extracts_dir, "a.py", "q2", "c2", h, "2024-02-01T00:00:00Z")

        set_project_root(tmp_path)
        resp = client.get("/api/v1/extracts")
        timestamps = [e["timestamp"] for e in resp.json()["extracts"]]
        assert timestamps == sorted(timestamps, reverse=True)
        set_project_root(None)


# ===================================================================
# Requirement 3: check_freshness query param
# ===================================================================

class TestFreshness:
    def test_fresh_when_hash_matches(self, client, project):
        resp = client.get("/api/v1/extracts")
        ext = resp.json()["extracts"][0]
        assert ext["is_fresh"] is True

    def test_stale_when_source_changed(self, client, project):
        """Stale when source file content changes."""
        (project / "src.py").write_text("print('changed')")
        resp = client.get("/api/v1/extracts")
        data = resp.json()
        assert data["extracts"][0]["is_fresh"] is False
        assert data["stale_count"] == 1

    def test_stale_when_source_missing(self, client, project):
        """Stale when source file is deleted."""
        (project / "src.py").unlink()
        resp = client.get("/api/v1/extracts")
        assert resp.json()["extracts"][0]["is_fresh"] is False

    def test_check_freshness_false(self, client, project):
        """When check_freshness=false, is_fresh should be null."""
        resp = client.get("/api/v1/extracts", params={"check_freshness": "false"})
        assert resp.json()["extracts"][0]["is_fresh"] is None

    def test_check_freshness_default_true(self, client, project):
        """Default check_freshness is true."""
        resp = client.get("/api/v1/extracts")
        # is_fresh should be a boolean, not None
        assert resp.json()["extracts"][0]["is_fresh"] is not None


# ===================================================================
# Requirement 4: GET /{cache_key} — single extract with content
# ===================================================================

class TestGetExtract:
    def test_returns_content_and_metadata(self, client, project):
        key = _cache_key("src.py", "find prints")
        resp = client.get(f"/api/v1/extracts/{key}")
        assert resp.status_code == 200
        data = resp.json()
        assert data["cache_key"] == key
        assert data["source_path"] == "src.py"
        assert data["content"] == "extracted content"
        assert data["is_fresh"] is True

    def test_invalid_cache_key_format(self, client, project):
        """Non-64-char-hex key returns 404."""
        resp = client.get("/api/v1/extracts/not-hex")
        assert resp.status_code == 404

    def test_valid_key_but_not_found(self, client, project):
        """Valid 64-char hex but no .md file returns 404."""
        resp = client.get(f"/api/v1/extracts/{'a' * 64}")
        assert resp.status_code == 404

    def test_includes_freshness(self, client, project):
        key = _cache_key("src.py", "find prints")
        resp = client.get(f"/api/v1/extracts/{key}")
        assert resp.json()["is_fresh"] is True

        # Now make it stale
        (project / "src.py").write_text("changed!")
        resp = client.get(f"/api/v1/extracts/{key}")
        assert resp.json()["is_fresh"] is False


# ===================================================================
# Requirement 5 & 8: GET /for-prompt — extracts for a prompt file
# ===================================================================

class TestExtractsForPrompt:
    def test_finds_cached_extract(self, client, project):
        """Parses <include query="...">file</include> and finds cached entry."""
        prompt = project / "test.prompt"
        prompt.write_text('<include query="find prints">src.py</include>')

        resp = client.get("/api/v1/extracts/for-prompt",
                          params={"prompt_path": "test.prompt"})
        assert resp.status_code == 200
        data = resp.json()
        assert len(data) == 1
        assert data[0]["include_path"] == "src.py"
        assert data[0]["query"] == "find prints"
        assert data[0]["has_cached_entry"] is True
        assert data[0]["is_fresh"] is True

    def test_missing_prompt_returns_404(self, client, project):
        resp = client.get("/api/v1/extracts/for-prompt",
                          params={"prompt_path": "no_such.prompt"})
        assert resp.status_code == 404

    def test_uncached_include(self, client, project):
        """Include tag with no matching cache entry."""
        prompt = project / "test.prompt"
        prompt.write_text('<include query="new query">src.py</include>')

        resp = client.get("/api/v1/extracts/for-prompt",
                          params={"prompt_path": "test.prompt"})
        data = resp.json()
        assert len(data) == 1
        assert data[0]["has_cached_entry"] is False

    def test_multiple_includes(self, client, project):
        """Multiple include tags parsed correctly."""
        prompt = project / "test.prompt"
        prompt.write_text(
            '<include query="q1">src.py</include>\n'
            '<include query="q2">src.py</include>\n'
        )
        resp = client.get("/api/v1/extracts/for-prompt",
                          params={"prompt_path": "test.prompt"})
        data = resp.json()
        assert len(data) == 2
        queries = {item["query"] for item in data}
        assert queries == {"q1", "q2"}

    def test_relative_path_resolution(self, client, project):
        """Include path resolved relative to prompt file's parent directory."""
        subdir = project / "prompts"
        subdir.mkdir(exist_ok=True)
        prompt = subdir / "review.prompt"
        prompt.write_text('<include query="find prints">../src.py</include>')

        resp = client.get("/api/v1/extracts/for-prompt",
                          params={"prompt_path": "prompts/review.prompt"})
        data = resp.json()
        assert len(data) == 1
        assert data[0]["has_cached_entry"] is True

    def test_duplicate_includes_deduplicated(self, client, project):
        """Duplicate include tags should be deduplicated."""
        prompt = project / "test.prompt"
        prompt.write_text(
            '<include query="find prints">src.py</include>\n'
            '<include query="find prints">src.py</include>\n'
        )
        resp = client.get("/api/v1/extracts/for-prompt",
                          params={"prompt_path": "test.prompt"})
        assert len(resp.json()) == 1


# ===================================================================
# Requirement 7: compute_cache_key uses normpath + sha256
# ===================================================================

class TestComputeCacheKey:
    def test_basic_key(self):
        """Public compute_cache_key produces expected sha256."""
        key = compute_cache_key("src.py", "query")
        expected = hashlib.sha256(b"src.py\nquery").hexdigest()
        assert key == expected

    def test_normpath_applied(self):
        """Paths like ./src.py and src.py produce the same key."""
        assert compute_cache_key("./src.py", "q") == compute_cache_key("src.py", "q")

    def test_different_queries_different_keys(self):
        assert compute_cache_key("f.py", "a") != compute_cache_key("f.py", "b")


# ===================================================================
# Cache key consistency: CLI and API must produce same keys
# ===================================================================

class TestCacheKeyConsistency:
    def test_api_finds_cli_created_cache(self, client, tmp_path):
        """Cache entry created with CLI-style key is findable by the API."""
        project_root = tmp_path
        extracts_dir = project_root / ".pdd" / "extracts"
        extracts_dir.mkdir(parents=True)

        source = project_root / "lib" / "mod.py"
        source.parent.mkdir(parents=True)
        source.write_text("def foo(): return 42")
        src_hash = hashlib.sha256(b"def foo(): return 42").hexdigest()

        query = "extract foo"
        rel_path = str(source.resolve().relative_to(project_root.resolve()))
        _write_extract(extracts_dir, rel_path, query, "foo content", src_hash)

        prompt = project_root / "my.prompt"
        prompt.write_text(f'<include query="{query}">lib/mod.py</include>')

        set_project_root(project_root)
        try:
            resp = client.get("/api/v1/extracts/for-prompt",
                              params={"prompt_path": "my.prompt"})
            assert resp.status_code == 200
            data = resp.json()
            assert len(data) == 1
            assert data[0]["has_cached_entry"] is True
        finally:
            set_project_root(None)

    def test_subdirectory_prompt_with_relative_path(self, client, tmp_path):
        """Prompt in subdirectory using ../ still matches CLI-created cache."""
        project_root = tmp_path
        extracts_dir = project_root / ".pdd" / "extracts"
        extracts_dir.mkdir(parents=True)

        readme = project_root / "README.md"
        readme.write_text("# Project")
        src_hash = hashlib.sha256(b"# Project").hexdigest()

        query = "summarize"
        rel_path = str(readme.resolve().relative_to(project_root.resolve()))
        _write_extract(extracts_dir, rel_path, query, "summary", src_hash)

        prompts_dir = project_root / "prompts"
        prompts_dir.mkdir()
        prompt = prompts_dir / "my.prompt"
        prompt.write_text(f'<include query="{query}">../README.md</include>')

        set_project_root(project_root)
        try:
            resp = client.get("/api/v1/extracts/for-prompt",
                              params={"prompt_path": "prompts/my.prompt"})
            data = resp.json()
            assert len(data) == 1
            assert data[0]["has_cached_entry"] is True
        finally:
            set_project_root(None)
