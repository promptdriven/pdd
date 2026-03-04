# Test Plan:
# 1. Test `get_project_root` and `set_project_root` to ensure dependency injection works.
# 2. Test `_fallback_compute_cache_key` to ensure it computes the correct SHA256 hash.
# 3. Test `_sha256_file` to ensure it correctly hashes file contents and handles missing files.
# 4. Test `_check_freshness` to ensure it correctly identifies fresh and stale extracts.
# 5. Test `_parse_meta_file` to ensure it correctly parses metadata JSON files.
# 6. Test `_parse_include_tags` to ensure it correctly extracts path and query from prompt content.
# 7. Test `list_extracts` endpoint to ensure it lists all extracts, handles empty directories, and sorts by timestamp.
# 8. Test `extracts_for_prompt` endpoint to ensure it finds extracts for a given prompt file.
# 9. Test `get_extract` endpoint to ensure it returns the correct extract content and metadata, and handles 404s.


import sys
from pathlib import Path

# Add project root to sys.path to ensure local code is prioritized
# This allows testing local changes without installing the package
project_root = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(project_root))

import json
import hashlib
from pathlib import Path
import pytest
from fastapi import FastAPI
from fastapi.testclient import TestClient

from pdd.server.routes.extracts import (
    router,
    get_project_root,
    set_project_root,
    _fallback_compute_cache_key,
    _sha256_file,
    _check_freshness,
    _parse_meta_file,
    _parse_include_tags,
)

@pytest.fixture
def app():
    app = FastAPI()
    app.include_router(router)
    return app

@pytest.fixture
def client(app):
    return TestClient(app)

@pytest.fixture
def temp_project(tmp_path):
    # Setup a temporary project structure
    extracts_dir = tmp_path / ".pdd" / "extracts"
    extracts_dir.mkdir(parents=True)
    
    # Create a source file
    source_file = tmp_path / "src.py"
    source_file.write_text("print('hello')")
    source_hash = hashlib.sha256(b"print('hello')").hexdigest()
    
    # Create an extract
    cache_key = _fallback_compute_cache_key("src.py", "extract print")
    meta_path = extracts_dir / f"{cache_key}.meta.json"
    md_path = extracts_dir / f"{cache_key}.md"
    
    meta_data = {
        "source_path": "src.py",
        "query": "extract print",
        "timestamp": "2023-10-01T12:00:00Z",
        "source_hash": source_hash
    }
    meta_path.write_text(json.dumps(meta_data))
    md_path.write_text("```python\nprint('hello')\n```")
    
    # Create a prompt file
    prompt_file = tmp_path / "test.prompt"
    prompt_file.write_text(f'<include path="src.py" query="extract print">')
    
    set_project_root(tmp_path)
    yield tmp_path
    set_project_root(None)

def test_project_root_dependency(tmp_path):
    set_project_root(tmp_path)
    assert get_project_root() == tmp_path
    
    set_project_root(None)
    with pytest.raises(RuntimeError):
        get_project_root()

def test_fallback_compute_cache_key():
    key = _fallback_compute_cache_key("test.py", "query")
    expected = hashlib.sha256(b"test.py\nquery").hexdigest()
    assert key == expected

def test_sha256_file(tmp_path):
    test_file = tmp_path / "test.txt"
    test_file.write_text("hello world")
    expected = hashlib.sha256(b"hello world").hexdigest()
    assert _sha256_file(test_file) == expected
    
    assert _sha256_file(tmp_path / "nonexistent.txt") is None

def test_check_freshness(tmp_path):
    test_file = tmp_path / "test.txt"
    test_file.write_text("hello world")
    expected_hash = hashlib.sha256(b"hello world").hexdigest()
    
    assert _check_freshness("test.txt", expected_hash, tmp_path) is True
    assert _check_freshness("test.txt", "wronghash", tmp_path) is False
    assert _check_freshness("missing.txt", expected_hash, tmp_path) is False
    assert _check_freshness("test.txt", None, tmp_path) is None

def test_parse_meta_file(temp_project):
    extracts_dir = temp_project / ".pdd" / "extracts"
    meta_files = list(extracts_dir.glob("*.meta.json"))
    assert len(meta_files) == 1
    
    meta = _parse_meta_file(meta_files[0], temp_project, check_freshness=True)
    assert meta is not None
    assert meta.source_path == "src.py"
    assert meta.query == "extract print"
    assert meta.is_fresh is True

def test_parse_include_tags():
    content = """
    <include path="file1.py" query="q1">
    <include query="q2" path="file2.py">
    <include path='file3.py' query='q3'/>
    """
    tags = _parse_include_tags(content)
    assert len(tags) == 3
    assert ("file1.py", "q1") in tags
    assert ("file2.py", "q2") in tags
    assert ("file3.py", "q3") in tags

def test_list_extracts(client, temp_project):
    response = client.get("/api/v1/extracts")
    assert response.status_code == 200
    data = response.json()
    assert data["total"] == 1
    assert data["stale_count"] == 0
    assert len(data["extracts"]) == 1
    assert data["extracts"][0]["source_path"] == "src.py"
    assert data["extracts"][0]["is_fresh"] is True

def test_list_extracts_no_dir(client, tmp_path):
    set_project_root(tmp_path)
    response = client.get("/api/v1/extracts")
    assert response.status_code == 200
    data = response.json()
    assert data["total"] == 0
    assert data["extracts"] == []

def test_extracts_for_prompt(client, temp_project):
    response = client.get("/api/v1/extracts/for-prompt?prompt_path=test.prompt")
    assert response.status_code == 200
    data = response.json()
    assert len(data) == 1
    assert data[0]["include_path"] == "src.py"
    assert data[0]["query"] == "extract print"
    assert data[0]["has_cached_entry"] is True
    assert data[0]["is_fresh"] is True

def test_extracts_for_prompt_not_found(client, temp_project):
    response = client.get("/api/v1/extracts/for-prompt?prompt_path=missing.prompt")
    assert response.status_code == 404

def test_get_extract(client, temp_project):
    cache_key = _fallback_compute_cache_key("src.py", "extract print")
    response = client.get(f"/api/v1/extracts/{cache_key}")
    assert response.status_code == 200
    data = response.json()
    assert data["cache_key"] == cache_key
    assert data["source_path"] == "src.py"
    assert "print('hello')" in data["content"]

def test_get_extract_invalid_key(client, temp_project):
    response = client.get("/api/v1/extracts/invalidkey")
    assert response.status_code == 404

def test_get_extract_not_found(client, temp_project):
    valid_key = "a" * 64
    response = client.get(f"/api/v1/extracts/{valid_key}")
    assert response.status_code == 404


# ===========================================================================
# Tests: Cache key consistency between CLI and API (regression)
# ===========================================================================

class TestCacheKeyConsistencyWithCLI:
    """Tests that the API can find cache entries created by the CLI.

    Both the CLI (IncludeQueryExtractor.extract) and the API
    (extracts_for_prompt) now use project-relative paths for cache keys:
        CLI:  rel_path = str(resolved.relative_to(project_root))
              cache_key = compute_cache_key(rel_path, query)
        API:  source_path = str(resolved.relative_to(project_root))
              cache_key = compute_cache_key(source_path, query)

    These must produce the same key for the same file, or the API will
    not find CLI-created cache entries (and vice versa).
    """

    def test_api_finds_cli_created_cache_entry(self, client, tmp_path):
        """Cache entry created by CLI should be found by API."""
        project_root = tmp_path
        extracts_dir = project_root / ".pdd" / "extracts"
        extracts_dir.mkdir(parents=True)

        # Create source file in a subdirectory
        source = project_root / "lib" / "module.py"
        source.parent.mkdir(parents=True)
        source.write_text("def foo(): return 42", encoding="utf-8")
        source_hash = hashlib.sha256(b"def foo(): return 42").hexdigest()

        query = "extract foo function"

        # Simulate CLI: extract() now uses project-relative path
        rel_path = str(source.resolve().relative_to(project_root.resolve()))
        cli_key = _fallback_compute_cache_key(rel_path, query)
        meta_data = {
            "source_path": rel_path,
            "query": query,
            "timestamp": "2024-01-01T12:00:00Z",
            "source_hash": source_hash,
        }
        (extracts_dir / f"{cli_key}.meta.json").write_text(json.dumps(meta_data))
        (extracts_dir / f"{cli_key}.md").write_text("extracted foo content")

        # Create prompt file that includes lib/module.py
        prompt = project_root / "my.prompt"
        prompt.write_text('<include path="lib/module.py" query="extract foo function"/>')

        set_project_root(project_root)
        try:
            response = client.get(
                "/api/v1/extracts/for-prompt?prompt_path=my.prompt"
            )
            assert response.status_code == 200
            data = response.json()
            assert len(data) == 1
            assert data[0]["has_cached_entry"] is True, (
                "API could not find cache entry created by CLI. "
                f"CLI key: {cli_key[:12]}..., "
                f"API key: {data[0]['cache_key'][:12]}..."
            )
        finally:
            set_project_root(None)

    def test_api_cache_key_matches_cli_cache_key(self, tmp_path):
        """Directly compare the cache keys computed by CLI vs API logic."""
        project_root = tmp_path
        source = project_root / "src" / "app.py"
        source.parent.mkdir(parents=True)
        source.write_text("app = Flask(__name__)", encoding="utf-8")

        query = "find Flask app"

        # CLI logic (from include_query_extractor.py):
        #   resolved = Path(file_path).resolve()
        #   rel_path = _project_relative_path(resolved)  # project-relative
        #   cache_key = compute_cache_key(rel_path, query)
        cli_rel_path = str(source.resolve().relative_to(project_root.resolve()))
        cli_key = _fallback_compute_cache_key(cli_rel_path, query)

        # API logic (from extracts.py lines 309-315):
        #   resolved = (prompt_parent / include_path).resolve()
        #   source_path = str(resolved.relative_to(project_root.resolve()))
        #   cache_key = compute_cache_key(source_path, query)
        prompt_parent = project_root  # prompt at project root
        include_path = "src/app.py"
        resolved = (prompt_parent / include_path).resolve()
        api_source_path = str(resolved.relative_to(project_root.resolve()))
        api_key = _fallback_compute_cache_key(api_source_path, query)

        assert cli_key == api_key, (
            f"CLI and API compute different cache keys for the same file!\n"
            f"  CLI input: '{cli_rel_path}' -> key {cli_key[:16]}...\n"
            f"  API input: '{api_source_path}' -> key {api_key[:16]}...\n"
            f"This means the API cannot find cache entries created by the CLI."
        )

    def test_prompt_in_subdirectory_with_relative_include(self, client, tmp_path):
        """When prompt is in a subdirectory and uses '../' relative path,
        the API should still compute the same cache key as the CLI."""
        project_root = tmp_path
        extracts_dir = project_root / ".pdd" / "extracts"
        extracts_dir.mkdir(parents=True)

        # Source file at project root
        readme = project_root / "README.md"
        readme.write_text("# My Project\nThis is PDD.", encoding="utf-8")
        source_hash = hashlib.sha256(b"# My Project\nThis is PDD.").hexdigest()

        query = "What is this project?"

        # Simulate CLI creating cache with project-relative path
        rel_path = str(readme.resolve().relative_to(project_root.resolve()))
        cli_key = _fallback_compute_cache_key(rel_path, query)
        meta_data = {
            "source_path": rel_path,
            "query": query,
            "timestamp": "2024-01-01T12:00:00Z",
            "source_hash": source_hash,
        }
        (extracts_dir / f"{cli_key}.meta.json").write_text(json.dumps(meta_data))
        (extracts_dir / f"{cli_key}.md").write_text("This is a PDD project.")

        # Prompt in subdirectory referencing ../README.md
        prompts_dir = project_root / "prompts"
        prompts_dir.mkdir()
        prompt = prompts_dir / "my.prompt"
        prompt.write_text(
            '<include path="../README.md" query="What is this project?"/>'
        )

        set_project_root(project_root)
        try:
            response = client.get(
                "/api/v1/extracts/for-prompt?prompt_path=prompts/my.prompt"
            )
            assert response.status_code == 200
            data = response.json()
            assert len(data) == 1
            assert data[0]["has_cached_entry"] is True, (
                "API could not find CLI-created cache for ../README.md include. "
                f"CLI key: {cli_key[:12]}..., "
                f"API key: {data[0]['cache_key'][:12]}..."
            )
        finally:
            set_project_root(None)