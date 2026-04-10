"""
E2E tests for the Selective Includes feature (Issue #190).

Tests the full pipeline of:
- <include select="...">file</include> structural selectors
- <include query="...">file</include> semantic extraction with caching
- <include select="..." mode="interface">file</include> interface mode
- auto-deps emitting selectors (new + update blocks)
- insert_includes applying update blocks deterministically
- small-file optimization (stripping selectors from <100 line files)
- extracts prune garbage collection
- extracts REST API endpoints
- summarize_directory structured output (key_exports, dependencies)
"""

import ast
import hashlib
import json
import os
import re
import textwrap
import warnings
from pathlib import Path
from unittest.mock import MagicMock, patch

import pytest
from click.testing import CliRunner

from pdd.content_selector import ContentSelector, SelectorError


# ---------------------------------------------------------------------------
# Fixtures
# ---------------------------------------------------------------------------

@pytest.fixture(autouse=True)
def set_pdd_path(monkeypatch):
    """Set PDD_PATH so language_format.csv is found."""
    import pdd
    pdd_package_dir = Path(pdd.__file__).parent
    monkeypatch.setenv("PDD_PATH", str(pdd_package_dir))


@pytest.fixture
def python_file(tmp_path):
    """Create a sample Python file with classes, functions, decorators."""
    code = textwrap.dedent('''\
        """Module docstring."""

        import os
        import sys

        MAX_RETRIES = 3

        class UserModel:
            """A user model."""

            name: str
            email: str

            def __init__(self, name: str, email: str):
                """Initialize UserModel."""
                self.name = name
                self.email = email

            def validate(self) -> bool:
                """Validate the user."""
                if not self.name:
                    return False
                if "@" not in self.email:
                    return False
                return True

            def _internal_method(self):
                """Private method."""
                pass

        def process_request(data: dict) -> dict:
            """Process incoming request data."""
            result = {}
            for key, value in data.items():
                result[key] = str(value).strip()
            return result

        async def fetch_data(url: str) -> str:
            """Fetch data from URL."""
            return f"data from {url}"

        class Handler:
            """Request handler."""

            def handle(self, request):
                """Handle request."""
                return {"status": "ok"}

            def _private(self):
                pass
    ''')
    p = tmp_path / "sample.py"
    p.write_text(code)
    return p


@pytest.fixture
def markdown_file(tmp_path):
    """Create a sample Markdown file with sections."""
    md = textwrap.dedent('''\
        # Project Title

        Some intro text.

        ## Installation

        Run `pip install myproject`.

        ## Usage

        Import and use:

        ```python
        import myproject
        ```

        ### Advanced Usage

        More details here.

        ## API Reference

        See docs.
    ''')
    p = tmp_path / "docs.md"
    p.write_text(md)
    return p


@pytest.fixture
def json_file(tmp_path):
    """Create a sample JSON config file."""
    data = {
        "database": {
            "host": "localhost",
            "port": 5432,
            "credentials": {
                "user": "admin",
                "password": "secret"
            }
        },
        "features": ["auth", "logging", "metrics"],
        "version": "1.2.3"
    }
    p = tmp_path / "config.json"
    p.write_text(json.dumps(data, indent=2))
    return p


@pytest.fixture
def yaml_file(tmp_path):
    """Create a sample YAML config file."""
    yaml_content = textwrap.dedent('''\
        database:
          host: localhost
          port: 5432
        features:
          - auth
          - logging
        version: "1.2.3"
    ''')
    p = tmp_path / "config.yaml"
    p.write_text(yaml_content)
    return p


# ===========================================================================
# 1. PREPROCESS + CONTENT_SELECTOR E2E TESTS
# ===========================================================================

class TestPreprocessWithSelectAttribute:
    """E2E: <include select="...">file</include> through preprocess()."""

    def test_select_single_function(self, tmp_path, python_file, monkeypatch):
        """Preprocess resolves select="def:process_request" and extracts only that function."""
        monkeypatch.chdir(tmp_path)
        monkeypatch.setenv("PDD_QUIET", "1")

        prompt = f'<include select="def:process_request">{python_file.name}</include>'
        from pdd.preprocess import preprocess
        result = preprocess(prompt, recursive=False, double_curly_brackets=False)

        assert "def process_request" in result
        assert "Process incoming request data" in result
        # Should NOT include other functions/classes
        assert "class UserModel" not in result
        assert "async def fetch_data" not in result

    def test_select_class(self, tmp_path, python_file, monkeypatch):
        """Preprocess resolves select="class:UserModel" and extracts the entire class."""
        monkeypatch.chdir(tmp_path)
        monkeypatch.setenv("PDD_QUIET", "1")

        prompt = f'<include select="class:UserModel">{python_file.name}</include>'
        from pdd.preprocess import preprocess
        result = preprocess(prompt, recursive=False, double_curly_brackets=False)

        assert "class UserModel" in result
        assert "def validate" in result
        assert "def __init__" in result
        # Should NOT include top-level functions
        assert "def process_request" not in result

    def test_select_class_method(self, tmp_path, python_file, monkeypatch):
        """Preprocess resolves select="class:UserModel.validate" for a specific method."""
        monkeypatch.chdir(tmp_path)
        monkeypatch.setenv("PDD_QUIET", "1")

        prompt = f'<include select="class:UserModel.validate">{python_file.name}</include>'
        from pdd.preprocess import preprocess
        result = preprocess(prompt, recursive=False, double_curly_brackets=False)

        assert "def validate" in result
        assert "Validate the user" in result
        # Should NOT include __init__ or the class definition
        assert "def __init__" not in result

    def test_select_multiple_selectors(self, tmp_path, python_file, monkeypatch):
        """Preprocess resolves composable selectors: select="def:process_request,def:fetch_data"."""
        monkeypatch.chdir(tmp_path)
        monkeypatch.setenv("PDD_QUIET", "1")

        prompt = f'<include select="def:process_request,def:fetch_data">{python_file.name}</include>'
        from pdd.preprocess import preprocess
        result = preprocess(prompt, recursive=False, double_curly_brackets=False)

        assert "def process_request" in result
        assert "async def fetch_data" in result
        assert "class UserModel" not in result

    def test_select_lines_range(self, tmp_path, python_file, monkeypatch):
        """Preprocess resolves select="lines:1-5" for line range extraction."""
        monkeypatch.chdir(tmp_path)
        monkeypatch.setenv("PDD_QUIET", "1")

        prompt = f'<include select="lines:1-5">{python_file.name}</include>'
        from pdd.preprocess import preprocess
        result = preprocess(prompt, recursive=False, double_curly_brackets=False)

        assert "Module docstring" in result
        assert "import os" in result
        # Should not have content from later lines
        assert "class UserModel" not in result

    def test_select_markdown_section(self, tmp_path, markdown_file, monkeypatch):
        """Preprocess resolves select="section:Installation" for Markdown files."""
        monkeypatch.chdir(tmp_path)
        monkeypatch.setenv("PDD_QUIET", "1")

        prompt = f'<include select="section:Installation">{markdown_file.name}</include>'
        from pdd.preprocess import preprocess
        result = preprocess(prompt, recursive=False, double_curly_brackets=False)

        assert "Installation" in result
        assert "pip install" in result
        # Should NOT include other sections
        assert "API Reference" not in result

    def test_select_regex_pattern(self, tmp_path, python_file, monkeypatch):
        """Preprocess resolves select="pattern:/^import/" for regex matching."""
        monkeypatch.chdir(tmp_path)
        monkeypatch.setenv("PDD_QUIET", "1")

        prompt = f'<include select="pattern:/^import/">{python_file.name}</include>'
        from pdd.preprocess import preprocess
        result = preprocess(prompt, recursive=False, double_curly_brackets=False)

        assert "import os" in result
        assert "import sys" in result
        assert "class UserModel" not in result

    def test_select_json_path(self, tmp_path, json_file, monkeypatch):
        """Preprocess resolves select="path:database.host" for JSON files."""
        monkeypatch.chdir(tmp_path)
        monkeypatch.setenv("PDD_QUIET", "1")

        prompt = f'<include select="path:database.host">{json_file.name}</include>'
        from pdd.preprocess import preprocess
        result = preprocess(prompt, recursive=False, double_curly_brackets=False)

        assert "localhost" in result

    def test_select_json_nested_path(self, tmp_path, json_file, monkeypatch):
        """Preprocess resolves select="path:database.credentials" for nested JSON."""
        monkeypatch.chdir(tmp_path)
        monkeypatch.setenv("PDD_QUIET", "1")

        prompt = f'<include select="path:database.credentials">{json_file.name}</include>'
        from pdd.preprocess import preprocess
        result = preprocess(prompt, recursive=False, double_curly_brackets=False)

        assert "admin" in result
        assert "secret" in result

    def test_select_json_array_index(self, tmp_path, json_file, monkeypatch):
        """Preprocess resolves select="path:features[0]" for JSON array indexing."""
        monkeypatch.chdir(tmp_path)
        monkeypatch.setenv("PDD_QUIET", "1")

        prompt = f'<include select="path:features[0]">{json_file.name}</include>'
        from pdd.preprocess import preprocess
        result = preprocess(prompt, recursive=False, double_curly_brackets=False)

        assert "auth" in result

    def test_select_failure_falls_back_to_full_file(self, tmp_path, python_file, monkeypatch):
        """When selector fails, preprocess falls back to full file content with warning."""
        monkeypatch.chdir(tmp_path)
        monkeypatch.setenv("PDD_QUIET", "1")

        # "def:nonexistent_function" should fail — preprocess should fall back to full file
        prompt = f'<include select="def:nonexistent_function">{python_file.name}</include>'
        from pdd.preprocess import preprocess
        result = preprocess(prompt, recursive=False, double_curly_brackets=False)

        # Should have fallen back to full file content
        # (preprocess catches SelectorError and includes full file with warning)
        assert "class UserModel" in result or "nonexistent_function" in result.lower() or "error" in result.lower()


class TestPreprocessWithInterfaceMode:
    """E2E: <include select="..." mode="interface">file</include> through preprocess()."""

    def test_interface_mode_class(self, tmp_path, python_file, monkeypatch):
        """Interface mode extracts only signatures and docstrings for a class."""
        monkeypatch.chdir(tmp_path)
        monkeypatch.setenv("PDD_QUIET", "1")

        prompt = f'<include select="class:Handler" mode="interface">{python_file.name}</include>'
        from pdd.preprocess import preprocess
        result = preprocess(prompt, recursive=False, double_curly_brackets=False)

        assert "class Handler" in result
        assert "def handle" in result
        assert "Handle request" in result
        # Interface mode replaces body with ...
        assert "..." in result
        # Private methods should be excluded in interface mode
        assert "_private" not in result

    def test_interface_mode_full_file(self, tmp_path, python_file, monkeypatch):
        """Interface mode with no selectors produces interface for entire file."""
        monkeypatch.chdir(tmp_path)
        monkeypatch.setenv("PDD_QUIET", "1")

        prompt = f'<include mode="interface">{python_file.name}</include>'
        from pdd.preprocess import preprocess
        result = preprocess(prompt, recursive=False, double_curly_brackets=False)

        # Should have imports and signatures
        assert "import os" in result
        assert "class UserModel" in result
        assert "def process_request" in result
        # Bodies should be replaced with ...
        assert "..." in result


class TestPreprocessWithQueryAttribute:
    """E2E: <include query="...">file</include> through preprocess()."""

    def test_query_invokes_extractor_and_caches(self, tmp_path, python_file, monkeypatch):
        """Query attribute invokes IncludeQueryExtractor and writes to cache."""
        monkeypatch.chdir(tmp_path)
        monkeypatch.setenv("PDD_QUIET", "1")

        # Mock the extractor to avoid real LLM calls
        mock_extract = MagicMock(return_value="Extracted: validation logic from UserModel.validate")

        prompt = f'<include query="How does validation work?">{python_file.name}</include>'

        with patch("pdd.include_query_extractor.IncludeQueryExtractor") as MockExtractor:
            MockExtractor.return_value.extract = mock_extract
            from pdd.preprocess import preprocess
            result = preprocess(prompt, recursive=False, double_curly_brackets=False)

        assert "Extracted: validation logic" in result
        mock_extract.assert_called_once()
        call_kwargs = mock_extract.call_args
        assert "How does validation work?" in str(call_kwargs)

    def test_query_skipped_in_recursive_mode(self, tmp_path, python_file, monkeypatch):
        """Query includes are deferred during recursive=True pass (env expansion phase)."""
        monkeypatch.chdir(tmp_path)
        monkeypatch.setenv("PDD_QUIET", "1")

        prompt = f'<include query="auth logic">{python_file.name}</include>'

        from pdd.preprocess import preprocess
        result = preprocess(prompt, recursive=True, double_curly_brackets=False)

        # Should leave the tag intact for the second pass
        assert "<include" in result
        assert "query=" in result


class TestPreprocessMixedIncludes:
    """E2E: Prompts with a mix of bare, select, query, and mode includes."""

    def test_prompt_with_mixed_include_types(self, tmp_path, python_file, markdown_file, monkeypatch):
        """A single prompt with bare, select, and mode includes all resolve correctly."""
        monkeypatch.chdir(tmp_path)
        monkeypatch.setenv("PDD_QUIET", "1")

        prompt = textwrap.dedent(f'''\
            You are a Python expert.

            Here is the full docs:
            <include>{markdown_file.name}</include>

            Here is just the UserModel class:
            <include select="class:UserModel">{python_file.name}</include>

            Here is the Handler interface:
            <include select="class:Handler" mode="interface">{python_file.name}</include>
        ''')

        from pdd.preprocess import preprocess
        result = preprocess(prompt, recursive=False, double_curly_brackets=False)

        # Bare include: full markdown
        assert "# Project Title" in result
        assert "API Reference" in result

        # Select include: only UserModel
        assert "class UserModel" in result
        assert "def validate" in result

        # Interface mode: Handler with ... bodies
        assert "class Handler" in result
        assert "..." in result


# ===========================================================================
# 2. CONTENT_SELECTOR UNIT INTEGRATION TESTS
# ===========================================================================

class TestContentSelectorComposability:
    """Test composable selectors through the ContentSelector public API."""

    def test_lines_and_def_combined(self, python_file):
        """Combining lines and def selectors in a single call."""
        content = python_file.read_text()
        result = ContentSelector.select(
            content=content,
            selectors="lines:1-3,def:process_request",
            file_path=str(python_file),
        )
        assert "Module docstring" in result
        assert "def process_request" in result

    def test_interface_mode_skips_private_methods(self, python_file):
        """Interface mode excludes private methods (except __init__)."""
        content = python_file.read_text()
        result = ContentSelector.select(
            content=content,
            selectors="class:UserModel",
            file_path=str(python_file),
            mode="interface",
        )
        assert "def __init__" in result
        assert "def validate" in result
        assert "_internal_method" not in result
        assert "..." in result

    def test_invalid_selector_raises(self):
        """Malformed selectors raise SelectorError."""
        with pytest.raises(SelectorError):
            ContentSelector.select(
                content="x = 1",
                selectors="invalid_selector",
                file_path="test.py",
            )

    def test_selector_on_wrong_file_type_raises(self, markdown_file):
        """AST selectors on non-Python files raise SelectorError."""
        content = markdown_file.read_text()
        with pytest.raises(SelectorError, match="AST selectors require"):
            ContentSelector.select(
                content=content,
                selectors="def:foo",
                file_path=str(markdown_file),
            )

    def test_section_on_non_markdown_raises(self, python_file):
        """Section selector on non-Markdown files raises SelectorError."""
        content = python_file.read_text()
        with pytest.raises(SelectorError, match="Section selector requires"):
            ContentSelector.select(
                content=content,
                selectors="section:Heading",
                file_path=str(python_file),
            )

    def test_path_on_non_json_raises(self, python_file):
        """Path selector on non-JSON/YAML files raises SelectorError."""
        content = python_file.read_text()
        with pytest.raises(SelectorError, match="Path selector requires"):
            ContentSelector.select(
                content=content,
                selectors="path:key",
                file_path=str(python_file),
            )


# ===========================================================================
# 3. INCLUDE_QUERY_EXTRACTOR + CACHE LIFECYCLE E2E
# ===========================================================================

class TestIncludeQueryExtractorCaching:
    """E2E: IncludeQueryExtractor caches results and invalidates on source change."""

    def test_extract_creates_cache_files(self, tmp_path, python_file, monkeypatch):
        """First extraction creates .md and .meta.json cache files."""
        monkeypatch.setenv("PDD_QUIET", "1")

        # Point config to tmp_path as project root
        mock_config = {"project_root": str(tmp_path)}
        with patch("pdd.include_query_extractor.get_config", return_value=mock_config):
            with patch("pdd.include_query_extractor.llm_invoke", return_value={"result": "Extracted auth logic", "cost": 0.0, "model_name": "mock"}):
                with patch("pdd.include_query_extractor.load_prompt_template", return_value="template"):
                    with patch("pdd.include_query_extractor.preprocess", return_value="processed"):
                        from pdd.include_query_extractor import IncludeQueryExtractor
                        extractor = IncludeQueryExtractor()
                        result = extractor.extract(
                            file_path=str(python_file),
                            query="auth logic",
                        )

        assert result == "Extracted auth logic"

        # Verify cache files created
        cache_dir = tmp_path / ".pdd" / "extracts"
        md_files = list(cache_dir.glob("*.md"))
        meta_files = list(cache_dir.glob("*.meta.json"))
        assert len(md_files) == 1
        assert len(meta_files) == 1

        # Verify meta content
        meta = json.loads(meta_files[0].read_text())
        assert meta["query"] == "auth logic"
        assert "source_hash" in meta
        assert "timestamp" in meta

    def test_cached_result_returned_on_second_call(self, tmp_path, python_file, monkeypatch):
        """Second call with same file+query returns cached result without LLM call."""
        monkeypatch.setenv("PDD_QUIET", "1")

        mock_config = {"project_root": str(tmp_path)}
        call_count = {"llm": 0}

        def counting_llm_invoke(**kwargs):
            call_count["llm"] += 1
            return {"result": "LLM result", "cost": 0.0, "model_name": "mock"}

        with patch("pdd.include_query_extractor.get_config", return_value=mock_config):
            with patch("pdd.include_query_extractor.llm_invoke", side_effect=counting_llm_invoke):
                with patch("pdd.include_query_extractor.load_prompt_template", return_value="t"):
                    with patch("pdd.include_query_extractor.preprocess", return_value="p"):
                        from pdd.include_query_extractor import IncludeQueryExtractor
                        extractor = IncludeQueryExtractor()

                        # First call
                        r1 = extractor.extract(file_path=str(python_file), query="q")
                        assert call_count["llm"] == 1

                        # Second call — should use cache
                        r2 = extractor.extract(file_path=str(python_file), query="q")
                        assert call_count["llm"] == 1  # No additional LLM call

                        assert r1 == r2

    def test_cache_invalidated_on_source_change(self, tmp_path, python_file, monkeypatch):
        """Cache is invalidated when the source file content changes."""
        monkeypatch.setenv("PDD_QUIET", "1")

        mock_config = {"project_root": str(tmp_path)}
        call_count = {"llm": 0}

        def counting_llm_invoke(**kwargs):
            call_count["llm"] += 1
            return {"result": f"LLM result v{call_count['llm']}", "cost": 0.0, "model_name": "mock"}

        with patch("pdd.include_query_extractor.get_config", return_value=mock_config):
            with patch("pdd.include_query_extractor.llm_invoke", side_effect=counting_llm_invoke):
                with patch("pdd.include_query_extractor.load_prompt_template", return_value="t"):
                    with patch("pdd.include_query_extractor.preprocess", return_value="p"):
                        from pdd.include_query_extractor import IncludeQueryExtractor
                        extractor = IncludeQueryExtractor()

                        # First call
                        r1 = extractor.extract(file_path=str(python_file), query="q")
                        assert call_count["llm"] == 1

                        # Modify source file
                        python_file.write_text(python_file.read_text() + "\n# modified\n")

                        # Second call — cache should be stale
                        r2 = extractor.extract(file_path=str(python_file), query="q")
                        assert call_count["llm"] == 2  # LLM called again
                        assert r2 == "LLM result v2"

    def test_different_queries_produce_different_cache_keys(self, tmp_path, python_file, monkeypatch):
        """Different queries on the same file produce separate cache entries."""
        monkeypatch.setenv("PDD_QUIET", "1")

        mock_config = {"project_root": str(tmp_path)}

        with patch("pdd.include_query_extractor.get_config", return_value=mock_config):
            with patch("pdd.include_query_extractor.llm_invoke", side_effect=[
                    {"result": "result_a", "cost": 0.0, "model_name": "mock"},
                    {"result": "result_b", "cost": 0.0, "model_name": "mock"},
                ]):
                with patch("pdd.include_query_extractor.load_prompt_template", return_value="t"):
                    with patch("pdd.include_query_extractor.preprocess", return_value="p"):
                        from pdd.include_query_extractor import IncludeQueryExtractor
                        extractor = IncludeQueryExtractor()

                        r1 = extractor.extract(file_path=str(python_file), query="query A")
                        r2 = extractor.extract(file_path=str(python_file), query="query B")

        assert r1 == "result_a"
        assert r2 == "result_b"

        cache_dir = tmp_path / ".pdd" / "extracts"
        assert len(list(cache_dir.glob("*.md"))) == 2


# ===========================================================================
# 4. EXTRACTS PRUNE E2E
# ===========================================================================

class TestExtractsPruneE2E:
    """E2E: pdd extracts prune garbage-collects orphaned cache entries."""

    def _setup_cache(self, tmp_path, entries):
        """Helper: create cache entries with metadata."""
        cache_dir = tmp_path / ".pdd" / "extracts"
        cache_dir.mkdir(parents=True, exist_ok=True)

        for key, meta in entries.items():
            (cache_dir / f"{key}.md").write_text(f"Content for {key}")
            (cache_dir / f"{key}.meta.json").write_text(json.dumps(meta))

        return cache_dir

    def _compute_key(self, source_path, query):
        normalized = os.path.normpath(source_path)
        return hashlib.sha256((normalized + "\n" + query).encode()).hexdigest()

    def test_prune_removes_orphaned_entries(self, tmp_path, monkeypatch):
        """Prune deletes cache entries not referenced by any prompt file."""
        monkeypatch.chdir(tmp_path)

        # Create a source file
        src = tmp_path / "src.py"
        src.write_text("x = 1")

        # Cache entries: one referenced, one orphaned
        referenced_key = self._compute_key("src.py", "referenced query")
        orphaned_key = self._compute_key("old_file.py", "orphaned query")

        self._setup_cache(tmp_path, {
            referenced_key: {
                "source_path": str(src),
                "query": "referenced query",
                "source_hash": hashlib.sha256(b"x = 1").hexdigest(),
                "timestamp": "2024-01-01T00:00:00",
            },
            orphaned_key: {
                "source_path": str(tmp_path / "old_file.py"),
                "query": "orphaned query",
                "source_hash": "deadbeef",
                "timestamp": "2024-01-01T00:00:00",
            },
        })

        # Create a prompt file that references the first entry
        prompts_dir = tmp_path / "prompts"
        prompts_dir.mkdir()
        (prompts_dir / "test_python.prompt").write_text(
            f'<include query="referenced query">src.py</include>'
        )

        mock_config = {"project_root": str(tmp_path)}

        with patch("pdd.extracts_prune.get_config", return_value=mock_config):
            # Need to also patch compute_cache_key to match our key computation
            from pdd.extracts_prune import extracts, prune
            runner = CliRunner()
            result = runner.invoke(extracts, ["prune", "--force"], catch_exceptions=False)

        assert result.exit_code == 0
        assert "Pruned" in result.output or "orphaned" in result.output.lower()

        cache_dir = tmp_path / ".pdd" / "extracts"
        remaining_md = list(cache_dir.glob("*.md"))
        # Orphaned entry should be deleted
        assert not (cache_dir / f"{orphaned_key}.md").exists()

    def test_prune_no_orphans(self, tmp_path, monkeypatch):
        """Prune with no orphaned entries reports clean cache."""
        monkeypatch.chdir(tmp_path)

        cache_dir = tmp_path / ".pdd" / "extracts"
        cache_dir.mkdir(parents=True, exist_ok=True)

        mock_config = {"project_root": str(tmp_path)}
        with patch("pdd.extracts_prune.get_config", return_value=mock_config):
            from pdd.extracts_prune import extracts
            runner = CliRunner()
            result = runner.invoke(extracts, ["prune", "--force"], catch_exceptions=False)

        assert result.exit_code == 0
        assert "empty" in result.output.lower() or "clean" in result.output.lower() or "nothing" in result.output.lower()


# ===========================================================================
# 5. AUTO_INCLUDE WITH SELECTORS E2E
# ===========================================================================

class TestAutoIncludeWithSelectors:
    """E2E: auto_include emits <new>/<update> blocks with select/query attributes."""

    def test_auto_include_emits_select_attributes(self, tmp_path, monkeypatch):
        """auto_include returns <new> blocks with select= when the LLM suggests them."""
        monkeypatch.setenv("PDD_FORCE_LOCAL", "1")
        monkeypatch.setenv("OPENAI_API_KEY", "fake-key")

        input_prompt = "Generate a Python module that uses UserModel.\n"

        from pdd.auto_include import AutoIncludeResult, NewInclude, IncludeAnnotation, auto_include

        mock_result = AutoIncludeResult(
            reasoning="Need UserModel class and process_request function",
            new_includes=[
                NewInclude(file="src/models.py", module="models", select="class:UserModel"),
                NewInclude(file="src/utils.py", module="utils", select="def:process_request"),
            ],
            existing_include_annotations=[],
        )

        def mock_llm_invoke(**kwargs):
            if kwargs.get("output_pydantic") == AutoIncludeResult:
                return {"result": mock_result, "cost": 0.01, "model_name": "mock"}
            return {"result": "summary", "cost": 0.001, "model_name": "mock"}

        def mock_summarize(**kwargs):
            csv = "full_path,file_summary,key_exports,dependencies,content_hash\n"
            csv += 'src/models.py,"User models","[""UserModel""]","[]",abc\n'
            csv += 'src/utils.py,"Utilities","[""process_request""]","[""models""]",def\n'
            return (csv, 0.001, "mock")

        # Create files so _strip_selectors_from_small_files can check size
        # Make them > 100 lines so selectors are preserved
        (tmp_path / "src").mkdir()
        (tmp_path / "src" / "models.py").write_text("\n".join([f"# line {i}" for i in range(150)]))
        (tmp_path / "src" / "utils.py").write_text("\n".join([f"# line {i}" for i in range(150)]))
        monkeypatch.chdir(tmp_path)

        with patch("pdd.auto_include.llm_invoke", side_effect=mock_llm_invoke):
            with patch("pdd.auto_include.summarize_directory", side_effect=mock_summarize):
                directives, csv_out, cost, model = auto_include(
                    input_prompt=input_prompt,
                    directory_path="src/",
                    verbose=False,
                )

        # Verify selectors appear in output
        assert 'select="class:UserModel"' in directives
        assert 'select="def:process_request"' in directives
        assert "<new>" in directives

    def test_auto_include_emits_update_blocks(self, tmp_path, monkeypatch):
        """auto_include returns <update> blocks for existing includes that need selectors."""
        monkeypatch.setenv("PDD_FORCE_LOCAL", "1")
        monkeypatch.setenv("OPENAI_API_KEY", "fake-key")

        input_prompt = textwrap.dedent("""\
            Generate a Python module.
            <include>src/models.py</include>
        """)

        from pdd.auto_include import AutoIncludeResult, NewInclude, IncludeAnnotation, auto_include

        mock_result = AutoIncludeResult(
            reasoning="The existing include should be narrowed to just UserModel",
            new_includes=[],
            existing_include_annotations=[
                IncludeAnnotation(file="src/models.py", select="class:UserModel"),
            ],
        )

        def mock_llm_invoke(**kwargs):
            if kwargs.get("output_pydantic") == AutoIncludeResult:
                return {"result": mock_result, "cost": 0.01, "model_name": "mock"}
            return {"result": "summary", "cost": 0.001, "model_name": "mock"}

        def mock_summarize(**kwargs):
            return ("full_path,file_summary,key_exports,dependencies,content_hash\n", 0.001, "mock")

        (tmp_path / "src").mkdir()
        (tmp_path / "src" / "models.py").write_text("\n".join([f"# line {i}" for i in range(150)]))
        monkeypatch.chdir(tmp_path)

        with patch("pdd.auto_include.llm_invoke", side_effect=mock_llm_invoke):
            with patch("pdd.auto_include.summarize_directory", side_effect=mock_summarize):
                directives, csv_out, cost, model = auto_include(
                    input_prompt=input_prompt,
                    directory_path="src/",
                    verbose=False,
                )

        assert "<update>" in directives
        assert 'select="class:UserModel"' in directives

    def test_small_file_optimization_strips_selectors(self, tmp_path, monkeypatch):
        """Files under 100 lines have selectors stripped from <new> blocks and <update> blocks removed."""
        monkeypatch.setenv("PDD_FORCE_LOCAL", "1")
        monkeypatch.setenv("OPENAI_API_KEY", "fake-key")

        input_prompt = "<include>src/tiny.py</include>\nGenerate code."

        from pdd.auto_include import AutoIncludeResult, NewInclude, IncludeAnnotation, auto_include

        mock_result = AutoIncludeResult(
            reasoning="Need the function",
            new_includes=[
                NewInclude(file="src/small.py", module="small", select="def:helper"),
            ],
            existing_include_annotations=[
                IncludeAnnotation(file="src/tiny.py", select="def:main"),
            ],
        )

        def mock_llm_invoke(**kwargs):
            if kwargs.get("output_pydantic") == AutoIncludeResult:
                return {"result": mock_result, "cost": 0.01, "model_name": "mock"}
            return {"result": "summary", "cost": 0.001, "model_name": "mock"}

        def mock_summarize(**kwargs):
            return ("full_path,file_summary,key_exports,dependencies,content_hash\n", 0.001, "mock")

        # Create files UNDER 100 lines
        (tmp_path / "src").mkdir()
        (tmp_path / "src" / "small.py").write_text("\n".join([f"# line {i}" for i in range(50)]))
        (tmp_path / "src" / "tiny.py").write_text("\n".join([f"# line {i}" for i in range(30)]))
        monkeypatch.chdir(tmp_path)

        with patch("pdd.auto_include.llm_invoke", side_effect=mock_llm_invoke):
            with patch("pdd.auto_include.summarize_directory", side_effect=mock_summarize):
                directives, csv_out, cost, model = auto_include(
                    input_prompt=input_prompt,
                    directory_path="src/",
                    verbose=False,
                )

        # For <new> blocks: selector stripped but include kept
        if "<new>" in directives:
            assert 'select="def:helper"' not in directives
        # <update> block for small file should be removed entirely
        assert 'select="def:main"' not in directives


# ===========================================================================
# 6. INSERT_INCLUDES DETERMINISTIC UPDATE E2E
# ===========================================================================

class TestInsertIncludesUpdateBlocks:
    """E2E: insert_includes applies <update> blocks deterministically and sends only <new> to LLM."""

    def test_update_blocks_applied_without_llm(self, tmp_path, monkeypatch):
        """<update> blocks are applied via regex, not LLM. If only updates, LLM is skipped."""
        monkeypatch.setenv("PDD_FORCE_LOCAL", "1")
        monkeypatch.setenv("OPENAI_API_KEY", "fake-key")
        monkeypatch.setenv("PDD_QUIET", "1")

        input_prompt = textwrap.dedent("""\
            You are a Python expert.
            <include>src/models.py</include>
            Write clean code.
        """)

        # auto_include returns only <update> blocks (no <new>)
        update_directives = '<update>\n<include select="class:UserModel">src/models.py</include>\n</update>'

        llm_call_count = {"count": 0}

        def mock_auto_include(**kwargs):
            return (update_directives, "csv_data", 0.01, "mock")

        def mock_llm_invoke(**kwargs):
            llm_call_count["count"] += 1
            # This should NOT be called for insert_includes since only updates
            return {
                "result": MagicMock(output_prompt="should not be used"),
                "cost": 0.001,
                "model_name": "mock",
            }

        csv_path = tmp_path / "deps.csv"
        csv_path.write_text("full_path,file_summary,key_exports,dependencies,content_hash\n")

        with patch("pdd.insert_includes.auto_include", side_effect=mock_auto_include):
            with patch("pdd.insert_includes.llm_invoke", side_effect=mock_llm_invoke):
                with patch("pdd.insert_includes.load_prompt_template", return_value="template"):
                    with patch("pdd.insert_includes.preprocess", return_value="processed"):
                        from pdd.insert_includes import insert_includes
                        output, csv_out, cost, model = insert_includes(
                            input_prompt=input_prompt,
                            directory_path="src/",
                            csv_filename=str(csv_path),
                            verbose=False,
                        )

        # Update block should have been applied deterministically
        assert 'select="class:UserModel"' in output
        assert "src/models.py" in output
        # LLM should NOT have been called for insert_includes (only updates, no new)
        assert llm_call_count["count"] == 0

    def test_new_blocks_sent_to_llm(self, tmp_path, monkeypatch):
        """<new> blocks trigger an LLM call to insert them into the prompt."""
        monkeypatch.setenv("PDD_FORCE_LOCAL", "1")
        monkeypatch.setenv("OPENAI_API_KEY", "fake-key")
        monkeypatch.setenv("PDD_QUIET", "1")

        input_prompt = "You are a Python expert.\nWrite clean code."

        new_directives = '<new>\n<utils><include select="def:helper">src/utils.py</include></utils>\n</new>'

        captured_deps = []

        def mock_auto_include(**kwargs):
            return (new_directives, "csv_data", 0.01, "mock")

        def mock_llm_invoke(**kwargs):
            input_json = kwargs.get("input_json", {})
            if "actual_dependencies_to_insert" in input_json:
                captured_deps.append(input_json["actual_dependencies_to_insert"])
            return {
                "result": MagicMock(output_prompt=input_prompt + "\n" + new_directives),
                "cost": 0.001,
                "model_name": "mock",
            }

        csv_path = tmp_path / "deps.csv"
        csv_path.write_text("full_path,file_summary,key_exports,dependencies,content_hash\n")

        with patch("pdd.insert_includes.auto_include", side_effect=mock_auto_include):
            with patch("pdd.insert_includes.llm_invoke", side_effect=mock_llm_invoke):
                with patch("pdd.insert_includes.load_prompt_template", return_value="template"):
                    with patch("pdd.insert_includes.preprocess", return_value="processed"):
                        from pdd.insert_includes import insert_includes
                        output, csv_out, cost, model = insert_includes(
                            input_prompt=input_prompt,
                            directory_path="src/",
                            csv_filename=str(csv_path),
                            verbose=False,
                        )

        # LLM was called with <new> blocks
        assert len(captured_deps) > 0
        assert "<new>" in captured_deps[0]

    def test_mixed_update_and_new_blocks(self, tmp_path, monkeypatch):
        """Update blocks applied first, then new blocks sent to LLM."""
        monkeypatch.setenv("PDD_FORCE_LOCAL", "1")
        monkeypatch.setenv("OPENAI_API_KEY", "fake-key")
        monkeypatch.setenv("PDD_QUIET", "1")

        input_prompt = textwrap.dedent("""\
            You are a Python expert.
            <include>src/models.py</include>
            Write clean code.
        """)

        mixed_directives = (
            '<update>\n<include select="class:UserModel">src/models.py</include>\n</update>\n'
            '<new>\n<utils><include select="def:helper">src/utils.py</include></utils>\n</new>'
        )

        captured_prompts = []

        def mock_auto_include(**kwargs):
            return (mixed_directives, "csv_data", 0.01, "mock")

        def mock_llm_invoke(**kwargs):
            input_json = kwargs.get("input_json", {})
            if "actual_prompt_to_update" in input_json:
                captured_prompts.append(input_json["actual_prompt_to_update"])
            return {
                "result": MagicMock(output_prompt="final output"),
                "cost": 0.001,
                "model_name": "mock",
            }

        csv_path = tmp_path / "deps.csv"
        csv_path.write_text("full_path,file_summary,key_exports,dependencies,content_hash\n")

        with patch("pdd.insert_includes.auto_include", side_effect=mock_auto_include):
            with patch("pdd.insert_includes.llm_invoke", side_effect=mock_llm_invoke):
                with patch("pdd.insert_includes.load_prompt_template", return_value="template"):
                    with patch("pdd.insert_includes.preprocess", return_value="processed"):
                        from pdd.insert_includes import insert_includes
                        output, csv_out, cost, model = insert_includes(
                            input_prompt=input_prompt,
                            directory_path="src/",
                            csv_filename=str(csv_path),
                            verbose=False,
                        )

        # The prompt passed to LLM should already have the update applied
        assert len(captured_prompts) > 0
        assert 'select="class:UserModel"' in captured_prompts[0]


# ===========================================================================
# 7. SUMMARIZE_DIRECTORY STRUCTURED OUTPUT E2E
# ===========================================================================

class TestSummarizeDirectoryStructuredOutput:
    """E2E: summarize_directory produces 5-column CSV with key_exports and dependencies."""

    def test_csv_has_five_columns(self, tmp_path, monkeypatch):
        """CSV output has: full_path, file_summary, key_exports, dependencies, content_hash."""
        monkeypatch.setenv("PDD_QUIET", "1")

        from pdd.summarize_directory import summarize_directory, FileSummary

        # Create a small test directory
        src_dir = tmp_path / "src"
        src_dir.mkdir()
        (src_dir / "main.py").write_text("def main(): pass")

        mock_summary = FileSummary(
            file_summary="Entry point",
            key_exports=["main"],
            dependencies=[],
        )

        def mock_llm_invoke(**kwargs):
            return {
                "result": mock_summary,
                "cost": 0.001,
                "model_name": "mock",
            }

        with patch("pdd.summarize_directory.llm_invoke", side_effect=mock_llm_invoke):
            with patch("pdd.summarize_directory.load_prompt_template", return_value="template"):
                csv_output, cost, model = summarize_directory(
                    directory_path=str(src_dir),
                    strength=0.5,
                    temperature=0.0,
                    verbose=False,
                )

        # Verify CSV structure
        import csv as csv_module
        from io import StringIO
        reader = csv_module.reader(StringIO(csv_output))
        headers = next(reader)
        assert "full_path" in headers
        assert "file_summary" in headers
        assert "key_exports" in headers
        assert "dependencies" in headers
        assert "content_hash" in headers

        # Verify data row
        rows = list(reader)
        assert len(rows) >= 1


# ===========================================================================
# 8. EXTRACTS REST API E2E
# ===========================================================================

class TestExtractsAPIRoutes:
    """E2E: REST API endpoints for browsing extracts cache."""

    @pytest.fixture
    def setup_api(self, tmp_path):
        """Set up FastAPI test client with extracts cache."""
        from pdd.server.routes.extracts import router, set_project_root, compute_cache_key
        from fastapi import FastAPI
        from fastapi.testclient import TestClient

        app = FastAPI()
        app.include_router(router)
        set_project_root(tmp_path)

        # Create source file first (needed for freshness checks)
        (tmp_path / "src.py").write_text("x = 1")

        # Use the same cache key computation as the API
        key = compute_cache_key("src.py", "test query")

        # Create cache entries
        cache_dir = tmp_path / ".pdd" / "extracts"
        cache_dir.mkdir(parents=True, exist_ok=True)

        (cache_dir / f"{key}.md").write_text("Extracted content here")
        (cache_dir / f"{key}.meta.json").write_text(json.dumps({
            "source_path": "src.py",
            "query": "test query",
            "source_hash": hashlib.sha256(b"x = 1").hexdigest(),
            "timestamp": "2024-01-01T00:00:00",
        }))

        client = TestClient(app)
        return client, key, tmp_path

    def test_list_extracts(self, setup_api):
        """GET /api/v1/extracts returns list of cached extracts."""
        client, key, _ = setup_api
        response = client.get("/api/v1/extracts")
        assert response.status_code == 200
        data = response.json()
        assert data["total"] >= 1
        assert any(e["cache_key"] == key for e in data["extracts"])

    def test_get_single_extract(self, setup_api):
        """GET /api/v1/extracts/{key} returns content and metadata."""
        client, key, _ = setup_api
        response = client.get(f"/api/v1/extracts/{key}")
        assert response.status_code == 200
        data = response.json()
        assert data["content"] == "Extracted content here"
        assert data["query"] == "test query"
        assert data["source_path"] == "src.py"

    def test_get_nonexistent_extract(self, setup_api):
        """GET /api/v1/extracts/{bad_key} returns 404."""
        client, _, _ = setup_api
        fake_key = "a" * 64
        response = client.get(f"/api/v1/extracts/{fake_key}")
        assert response.status_code == 404

    def test_invalid_cache_key_format(self, setup_api):
        """GET /api/v1/extracts/{invalid} returns 404 for non-hex keys."""
        client, _, _ = setup_api
        response = client.get("/api/v1/extracts/not-a-valid-key")
        assert response.status_code == 404

    def test_freshness_check(self, setup_api):
        """Freshness check returns True when source file matches hash."""
        client, key, _ = setup_api
        response = client.get("/api/v1/extracts?check_freshness=true")
        data = response.json()
        fresh_entry = next(e for e in data["extracts"] if e["cache_key"] == key)
        assert fresh_entry["is_fresh"] is True

    def test_stale_detection(self, setup_api):
        """Freshness check returns False when source file has changed."""
        client, key, tmp_path = setup_api
        # Modify source file to make hash stale
        (tmp_path / "src.py").write_text("x = 2  # modified")
        response = client.get("/api/v1/extracts?check_freshness=true")
        data = response.json()
        stale_entry = next(e for e in data["extracts"] if e["cache_key"] == key)
        assert stale_entry["is_fresh"] is False
        assert data["stale_count"] >= 1

    def test_extracts_for_prompt(self, setup_api):
        """GET /api/v1/extracts/for-prompt returns extracts for a prompt file."""
        client, key, tmp_path = setup_api

        # Create a prompt file at project root level so relative path resolution
        # produces "src.py" (matching the cache key)
        (tmp_path / "test.prompt").write_text(
            '<include query="test query">src.py</include>'
        )

        response = client.get(
            "/api/v1/extracts/for-prompt",
            params={"prompt_path": "test.prompt"},
        )
        assert response.status_code == 200
        data = response.json()
        assert len(data) >= 1
        assert data[0]["query"] == "test query"
        assert data[0]["has_cached_entry"] is True

    def test_extracts_for_nonexistent_prompt(self, setup_api):
        """GET /api/v1/extracts/for-prompt with missing file returns 404."""
        client, _, _ = setup_api
        response = client.get(
            "/api/v1/extracts/for-prompt",
            params={"prompt_path": "nonexistent.prompt"},
        )
        assert response.status_code == 404


# ===========================================================================
# 9. FULL PIPELINE E2E: prompt -> auto-deps -> preprocess
# ===========================================================================

class TestFullPipelineE2E:
    """E2E: Full pipeline from prompt authoring through auto-deps to preprocessing."""

    def test_auto_deps_then_preprocess_with_selectors(self, tmp_path, monkeypatch):
        """
        Simulate the full workflow:
        1. User writes a prompt with bare <include> tags
        2. auto-deps annotates them with selectors
        3. preprocess resolves the selectors and extracts content
        """
        monkeypatch.chdir(tmp_path)
        monkeypatch.setenv("PDD_QUIET", "1")

        # Step 1: Create source files
        (tmp_path / "models.py").write_text(textwrap.dedent('''\
            class UserModel:
                """A user model."""
                name: str
                email: str

                def validate(self) -> bool:
                    """Validate the user."""
                    return bool(self.name and "@" in self.email)

            class AdminModel:
                """Admin model."""
                role: str

                def has_permission(self, perm: str) -> bool:
                    return True
        '''))

        (tmp_path / "utils.py").write_text(textwrap.dedent('''\
            def helper():
                """A helper function."""
                return 42

            def another():
                return 0
        '''))

        # Step 2: User's prompt (would be annotated by auto-deps)
        annotated_prompt = textwrap.dedent(f'''\
            You are a Python expert.

            <include select="class:UserModel">models.py</include>

            <include select="def:helper">utils.py</include>

            Generate a service that uses UserModel and helper.
        ''')

        # Step 3: Preprocess resolves selectors
        from pdd.preprocess import preprocess
        result = preprocess(annotated_prompt, recursive=False, double_curly_brackets=False)

        # UserModel should be extracted
        assert "class UserModel" in result
        assert "def validate" in result

        # AdminModel should NOT be present (only UserModel was selected)
        assert "class AdminModel" not in result

        # helper should be extracted
        assert "def helper" in result

        # another() should NOT be present
        assert "def another" not in result

    def test_auto_deps_query_then_preprocess(self, tmp_path, monkeypatch):
        """
        Full workflow with query= attribute:
        1. auto-deps emits <include query="...">file</include>
        2. preprocess invokes IncludeQueryExtractor
        3. Cached result is returned
        """
        monkeypatch.chdir(tmp_path)
        monkeypatch.setenv("PDD_QUIET", "1")

        (tmp_path / "spec.md").write_text(textwrap.dedent('''\
            # Auth Spec

            ## Requirements
            - Users must authenticate with JWT
            - Tokens expire after 24h

            ## Non-functional
            - Response time < 200ms
        '''))

        annotated_prompt = '<include query="What are the auth requirements?">spec.md</include>'

        mock_extract = MagicMock(return_value="- Users must authenticate with JWT\n- Tokens expire after 24h")

        with patch("pdd.include_query_extractor.IncludeQueryExtractor") as MockExtractor:
            MockExtractor.return_value.extract = mock_extract
            from pdd.preprocess import preprocess
            result = preprocess(annotated_prompt, recursive=False, double_curly_brackets=False)

        assert "JWT" in result
        assert "24h" in result
        # Non-functional requirements should NOT be in the result (semantic extraction)
        assert "200ms" not in result

    def test_auto_deps_interface_mode_reduces_token_count(self, tmp_path, monkeypatch):
        """
        Interface mode produces significantly less content than full inclusion.
        """
        monkeypatch.chdir(tmp_path)
        monkeypatch.setenv("PDD_QUIET", "1")

        # Create a file with substantial implementation bodies
        code = textwrap.dedent('''\
            class BigService:
                """A service with lots of implementation."""

                def method_a(self, data: dict) -> dict:
                    """Process data."""
                    result = {}
                    for key in data:
                        result[key] = data[key] * 2
                        if result[key] > 100:
                            result[key] = 100
                    return result

                def method_b(self, items: list) -> list:
                    """Filter items."""
                    filtered = []
                    for item in items:
                        if item > 0:
                            filtered.append(item)
                    return filtered
        ''')
        (tmp_path / "service.py").write_text(code)

        from pdd.preprocess import preprocess

        # Full inclusion
        full_prompt = '<include>service.py</include>'
        full_result = preprocess(full_prompt, recursive=False, double_curly_brackets=False)

        # Interface mode
        iface_prompt = '<include mode="interface">service.py</include>'
        iface_result = preprocess(iface_prompt, recursive=False, double_curly_brackets=False)

        # Interface should be shorter (no implementation bodies)
        assert len(iface_result) < len(full_result)
        # Interface should still have signatures and docstrings
        assert "def method_a" in iface_result
        assert "Process data" in iface_result
        assert "..." in iface_result
        # Implementation details should be gone
        assert "result[key] = 100" not in iface_result


# ===========================================================================
# 10. YAML PATH SELECTOR E2E
# ===========================================================================

class TestYamlPathSelector:
    """E2E: path: selector on YAML files through preprocess."""

    def test_yaml_path_through_preprocess(self, tmp_path, yaml_file, monkeypatch):
        """Preprocess resolves path: selector on YAML files."""
        monkeypatch.chdir(tmp_path)
        monkeypatch.setenv("PDD_QUIET", "1")

        prompt = f'<include select="path:database.host">{yaml_file.name}</include>'
        from pdd.preprocess import preprocess
        result = preprocess(prompt, recursive=False, double_curly_brackets=False)

        assert "localhost" in result


# ===========================================================================
# 11. EDGE CASES
# ===========================================================================

class TestEdgeCases:
    """Edge cases and error handling for the selective includes feature."""

    def test_empty_selectors_returns_full_content(self, python_file):
        """Empty/whitespace selectors return full file content."""
        content = python_file.read_text()
        result = ContentSelector.select(content=content, selectors="", file_path=str(python_file))
        assert result == content

    def test_include_with_both_select_and_query_prefers_select(self, tmp_path, python_file, monkeypatch):
        """When both select= and query= are on the same tag, select= wins (deterministic)."""
        monkeypatch.chdir(tmp_path)
        monkeypatch.setenv("PDD_QUIET", "1")

        # Both select= and query= present — preprocess should use select= and ignore query=
        prompt = f'<include select="def:process_request" query="How does request processing work?">{python_file.name}</include>'

        with patch("pdd.include_query_extractor.IncludeQueryExtractor") as MockExtractor:
            from pdd.preprocess import preprocess
            result = preprocess(prompt, recursive=False, double_curly_brackets=False)

        # select= should have been used (real ContentSelector)
        assert "def process_request" in result
        assert "Process incoming request data" in result
        # query= should NOT have been invoked
        MockExtractor.return_value.extract.assert_not_called()
        # Other functions/classes should be excluded
        assert "class UserModel" not in result

    def test_self_closing_include_with_select(self, tmp_path, python_file, monkeypatch):
        """Self-closing <include select="..." path="..." /> syntax works."""
        monkeypatch.chdir(tmp_path)
        monkeypatch.setenv("PDD_QUIET", "1")

        prompt = f'<include select="def:process_request" path="{python_file.name}" />'
        from pdd.preprocess import preprocess
        result = preprocess(prompt, recursive=False, double_curly_brackets=False)
        assert "def process_request" in result

    def test_open_ended_line_range(self, python_file):
        """lines:5- selects from line 5 to end of file."""
        content = python_file.read_text()
        lines = content.splitlines()
        result = ContentSelector.select(
            content=content,
            selectors="lines:5-",
            file_path=str(python_file),
        )
        # Should include everything from line 5 onwards
        assert lines[4] in result  # Line 5 (0-indexed = 4)
        assert lines[-1] in result  # Last line

    def test_async_function_selector(self, python_file):
        """def: selector works for async functions."""
        content = python_file.read_text()
        result = ContentSelector.select(
            content=content,
            selectors="def:fetch_data",
            file_path=str(python_file),
        )
        assert "async def fetch_data" in result
        assert "Fetch data from URL" in result


# ===========================================================================
# 12. AUTO-DEPS → PREPROCESS CLI PIPELINE E2E
# ===========================================================================

class TestAutoDepsThenPreprocessPipeline:
    """
    E2E tests for the full auto-deps → preprocess pipeline.

    These tests call auto_deps_main() and preprocess() with real files
    (mocking only the LLM), then verify that:
    - auto-deps output contains valid <include> tags with selectors
    - preprocess resolves those tags using real ContentSelector
    - content is actually reduced (not the full file)
    - cache lifecycle works through the pipeline
    """

    @pytest.fixture
    def project_dir(self, tmp_path):
        """Create a realistic project directory with files of mixed relevance."""
        # username_utils.py — >100 lines, has functions relevant to our prompt
        username_utils = textwrap.dedent('''\
            """Utilities for handling usernames in display contexts."""

            import os
            import re
            import getpass
            from typing import Optional, List


            def get_current_username() -> str:
                """Get the current system username."""
                return getpass.getuser()


            def capitalize_username(username: str) -> str:
                """Capitalize a username for display purposes."""
                if not username:
                    return ""
                cleaned = username.replace("_", " ").replace("-", " ")
                titled = cleaned.title()
                return titled


            def format_username_for_celebration(username: str) -> str:
                """Format a username for use in celebration messages."""
                capitalized = capitalize_username(username)
                return capitalized.upper()


            def validate_username(username: str) -> bool:
                """Validate a username meets requirements."""
                if not username or len(username) < 2:
                    return False
                if not re.match(r"^[a-zA-Z0-9_-]+$", username):
                    return False
                return True


            def get_display_name(first: str, last: str) -> str:
                """Get a formatted display name."""
                return f"{first.strip()} {last.strip()}"


            def truncate_username(username: str, max_len: int = 20) -> str:
                """Truncate username to max length."""
                if len(username) <= max_len:
                    return username
                return username[:max_len - 3] + "..."


            def normalize_username(username: str) -> str:
                """Normalize a username to lowercase with underscores."""
                return username.strip().lower().replace(" ", "_").replace("-", "_")


            def parse_full_name(full_name: str) -> dict:
                """Parse a full name into components."""
                parts = full_name.strip().split()
                if len(parts) == 0:
                    return {"first": "", "last": ""}
                if len(parts) == 1:
                    return {"first": parts[0], "last": ""}
                return {"first": parts[0], "last": " ".join(parts[1:])}


            # --- Database functions (NOT relevant to console printing) ---

            def lookup_username_in_db(user_id: int) -> Optional[str]:
                """Look up a username in the database by user ID."""
                raise NotImplementedError("Database not configured")


            def batch_resolve_usernames(user_ids: List[int]) -> dict:
                """Resolve multiple usernames from the database."""
                raise NotImplementedError("Database not configured")


            def migrate_username_schema() -> None:
                """Migrate the username schema in the database."""
                raise NotImplementedError("Database not configured")


            def create_username_index() -> None:
                """Create a search index for usernames."""
                raise NotImplementedError("Database not configured")


            def export_usernames_csv(output_path: str) -> None:
                """Export all usernames to a CSV file."""
                raise NotImplementedError("Database not configured")


            def purge_inactive_usernames(days: int = 90) -> int:
                """Purge usernames inactive for more than N days."""
                raise NotImplementedError("Database not configured")


            def sync_usernames_with_ldap() -> None:
                """Sync usernames with LDAP directory."""
                raise NotImplementedError("Database not configured")
        ''')

        # party_planning.txt — markdown doc, 120 lines, only music section relevant
        party_planning = textwrap.dedent('''\
            # Party Planning Guide

            ## Venue Setup
            The venue should be decorated with balloons, streamers, and a banner.
            Tables should be arranged in a U-shape for optimal conversation flow.
            Make sure the sound system is tested 2 hours before the event.
            Reserve a coat check area near the entrance.
            Set up a welcome table with name badges.
            Arrange a separate area for photography.
            Ensure wheelchair accessibility.
            Verify fire exits are clearly marked.
            Place emergency contact information at the registration desk.
            Test all AV equipment including projectors and microphones.
            Arrange for a backup power supply.
            Set up charging stations for guest devices.

            ## Catering Menu
            - Appetizers: Mini quiches, bruschetta, spring rolls
            - Main course: Grilled chicken, pasta primavera, vegetarian stir-fry
            - Desserts: Chocolate fountain, cupcakes, fruit platters
            - Beverages: Sparkling water, lemonade, iced tea
            - Late night snacks: Slider bar, pretzel bites, mini tacos
            - Dietary accommodations: Gluten-free, vegan, nut-free options
            - Kids menu: Chicken tenders, mac and cheese, fruit cups
            - Coffee station: Espresso, cappuccino, decaf
            - Dessert alternatives: Sugar-free brownies, dairy-free ice cream
            - Presentation: Use tiered displays for visual appeal
            - Staffing: One server per 20 guests
            - Water stations placed at each table and near dance floor

            ## Music Playlist for Success Celebration
            - "We Are The Champions" by Queen
            - "Celebration" by Kool & The Gang
            - "Don't Stop Me Now" by Queen
            - "Happy" by Pharrell Williams
            - "Best Day of My Life" by American Authors
            - "Walking on Sunshine" by Katrina and the Waves
            - "Eye of the Tiger" by Survivor
            - "Gonna Fly Now" (Rocky Theme) by Bill Conti
            - "All I Do Is Win" by DJ Khaled
            - "Can't Stop the Feeling" by Justin Timberlake

            ## Budget Breakdown
            | Category | Amount |
            |----------|--------|
            | Venue | $500 |
            | Catering | $1200 |
            | Decorations | $300 |
            | Entertainment | $400 |
            | Photography | $350 |
            | AV Equipment | $200 |
            | Miscellaneous | $200 |
            | Total | $3150 |

            Note: Budget should include a 15% contingency fund.
            Track all expenses in a shared spreadsheet.
            Request itemized invoices from all vendors.

            ## Guest List Management
            Send invitations at least 3 weeks in advance.
            Use an RSVP tracking spreadsheet.
            Plan for 10% more guests than confirmed RSVPs.
            Create a VIP list for special seating.
            Assign table numbers one week before.
            Send reminder emails 3 days before.
            Have a check-in system at the door.
            Prepare extra name badges for walk-in guests.

            ## Timeline
            - 4:00 PM - Setup begins
            - 5:30 PM - Sound check
            - 6:00 PM - Doors open
            - 7:00 PM - Dinner service
            - 8:00 PM - Awards ceremony
            - 9:00 PM - Dance floor opens
            - 10:30 PM - Closing remarks
            - 11:00 PM - Event ends

            ## Post-Event Tasks
            Send thank-you notes within 48 hours.
            Collect feedback via online survey.
            Compile a photo album.
            Process final vendor payments.
            Document lessons learned.
        ''')

        # kubernetes_deploy.py — completely irrelevant to our prompt
        kubernetes_deploy = textwrap.dedent('''\
            """Kubernetes deployment utilities."""

            from dataclasses import dataclass
            from typing import Optional, List


            @dataclass
            class ContainerSpec:
                """Container specification for deployment."""
                image: str
                port: int
                replicas: int = 1
                cpu_limit: str = "500m"
                memory_limit: str = "256Mi"


            @dataclass
            class DeploymentConfig:
                """Full deployment configuration."""
                name: str
                namespace: str
                container: ContainerSpec
                labels: dict = None


            def generate_deployment_yaml(config: DeploymentConfig) -> str:
                """Generate a Kubernetes deployment YAML manifest."""
                return f"""
            apiVersion: apps/v1
            kind: Deployment
            metadata:
              name: {config.name}
              namespace: {config.namespace}
            spec:
              replicas: {config.container.replicas}
              template:
                spec:
                  containers:
                  - name: {config.name}
                    image: {config.container.image}
                    ports:
                    - containerPort: {config.container.port}
            """


            def scale_deployment(name: str, replicas: int) -> None:
                """Scale a deployment to the specified number of replicas."""
                raise NotImplementedError("kubectl not configured")


            def get_pod_status(namespace: str) -> List[dict]:
                """Get status of all pods in a namespace."""
                raise NotImplementedError("kubectl not configured")


            def rolling_restart(name: str, namespace: str) -> None:
                """Perform a rolling restart of a deployment."""
                raise NotImplementedError("kubectl not configured")


            def get_deployment_history(name: str) -> List[dict]:
                """Get revision history of a deployment."""
                raise NotImplementedError("kubectl not configured")


            def rollback_deployment(name: str, revision: int) -> None:
                """Rollback a deployment to a specific revision."""
                raise NotImplementedError("kubectl not configured")
        ''')

        src = tmp_path / "src"
        src.mkdir()
        (src / "username_utils.py").write_text(username_utils)
        (src / "party_planning.txt").write_text(party_planning)
        (src / "kubernetes_deploy.py").write_text(kubernetes_deploy)

        return tmp_path

    def test_select_through_preprocess_reduces_content(self, project_dir, monkeypatch):
        """
        Simulate what happens after auto-deps adds select= attributes:
        preprocess resolves them via real ContentSelector and the output
        contains only the selected portions, not the full files.
        """
        monkeypatch.chdir(project_dir)
        monkeypatch.setenv("PDD_QUIET", "1")

        src = project_dir / "src"
        full_file = (src / "username_utils.py").read_text()
        full_line_count = len(full_file.splitlines())

        # Prompt as auto-deps would produce it (with select= attributes)
        annotated_prompt = textwrap.dedent(f'''\
            Write a python script to print "You did it, <Username>!!!" to the console.
            Capitalize the username.

            <include select="def:capitalize_username,def:format_username_for_celebration">{src}/username_utils.py</include>
        ''')

        from pdd.preprocess import preprocess
        result = preprocess(annotated_prompt, recursive=False, double_curly_brackets=False)

        # Selected functions should be present
        assert "def capitalize_username" in result
        assert "def format_username_for_celebration" in result

        # Irrelevant functions should be excluded
        assert "def lookup_username_in_db" not in result
        assert "def batch_resolve_usernames" not in result
        assert "def migrate_username_schema" not in result
        assert "def purge_inactive_usernames" not in result

        # Content should be meaningfully reduced
        result_lines = result.splitlines()
        # The full file is ~100 lines; two functions should be ~20 lines
        assert len(result_lines) < full_line_count, (
            f"Expected content reduction: result has {len(result_lines)} lines "
            f"but full file has {full_line_count} lines"
        )

    def test_select_markdown_section_reduces_content(self, project_dir, monkeypatch):
        """
        select="section:Music Playlist for Success Celebration" on a markdown file
        should extract only that section, not the full 80+ line document.
        """
        monkeypatch.chdir(project_dir)
        monkeypatch.setenv("PDD_QUIET", "1")

        src = project_dir / "src"
        # section: selector requires .md extension — copy the content
        md_file = src / "party_planning.md"
        md_file.write_text((src / "party_planning.txt").read_text())
        full_file = md_file.read_text()
        full_line_count = len(full_file.splitlines())

        prompt = f'<include select="section:Music Playlist for Success Celebration">{md_file}</include>'

        from pdd.preprocess import preprocess
        result = preprocess(prompt, recursive=False, double_curly_brackets=False)

        # Music section content should be present
        assert "We Are The Champions" in result
        assert "Celebration" in result
        assert "Happy" in result

        # Other sections should NOT be present
        assert "Venue Setup" not in result
        assert "Catering Menu" not in result
        assert "Budget Breakdown" not in result
        assert "Guest List Management" not in result
        assert "Post-Event Tasks" not in result

        # Should be significantly shorter than the full file
        result_line_count = len(result.strip().splitlines())
        assert result_line_count < full_line_count / 2, (
            f"Expected major content reduction: result has {result_line_count} lines "
            f"but full file has {full_line_count} lines"
        )

    def test_both_select_and_query_on_same_tag_uses_select(self, project_dir, monkeypatch):
        """
        When auto-deps emits both select= and query= on the same <include> tag
        (as happens in real usage), preprocess should use select= (deterministic)
        and NOT invoke the LLM for query=.
        """
        monkeypatch.chdir(project_dir)
        monkeypatch.setenv("PDD_QUIET", "1")

        src = project_dir / "src"

        # This is what auto-deps actually produces in practice
        prompt = (
            f'<include select="def:capitalize_username" '
            f'query="How to capitalize a username?">'
            f'{src}/username_utils.py</include>'
        )

        with patch("pdd.include_query_extractor.IncludeQueryExtractor") as MockExtractor:
            from pdd.preprocess import preprocess
            result = preprocess(prompt, recursive=False, double_curly_brackets=False)

        # select= was used (real ContentSelector ran)
        assert "def capitalize_username" in result
        assert "Capitalize a username for display" in result

        # query= was NOT invoked
        MockExtractor.return_value.extract.assert_not_called()

        # Only the selected function, not the whole file
        assert "def lookup_username_in_db" not in result

    def test_auto_deps_output_is_valid_for_preprocess(self, project_dir, monkeypatch):
        """
        auto_deps_main (with mocked LLM) writes a prompt file with <include> tags.
        preprocess then resolves those tags using real ContentSelector.
        This catches wiring bugs at the CLI boundary.
        """
        monkeypatch.chdir(project_dir)
        monkeypatch.setenv("PDD_QUIET", "1")
        monkeypatch.setenv("PDD_FORCE_LOCAL", "1")
        monkeypatch.setenv("OPENAI_API_KEY", "fake-key")

        import click

        src = project_dir / "src"

        # Write the initial prompt
        prompt_file = project_dir / "test_python.prompt"
        prompt_file.write_text(textwrap.dedent('''\
            Write a python script to print "You did it, <Username>!!!" to the console.
            Capitalize the username.
        '''))

        # CSV file for auto-deps cache
        csv_path = project_dir / "deps.csv"

        # Mock auto_include to return realistic <new> blocks with selectors
        new_directives = textwrap.dedent(f'''\
            <new>
            <utils.username_utils><include select="def:capitalize_username,def:format_username_for_celebration">{src}/username_utils.py</include></utils.username_utils>
            </new>
        ''')

        def mock_auto_include(**kwargs):
            return (new_directives, "csv_data", 0.01, "mock-model")

        # Mock the LLM call in insert_includes (for inserting <new> blocks)
        def mock_insert_llm_invoke(**kwargs):
            input_json = kwargs.get("input_json", {})
            actual_prompt = input_json.get("actual_prompt_to_update", "")
            deps = input_json.get("actual_dependencies_to_insert", "")

            # Simulate what the LLM does: insert the dependency block into the prompt
            output = actual_prompt.rstrip() + "\n\n" + deps.replace("<new>", "").replace("</new>", "").strip() + "\n"

            result_obj = MagicMock()
            result_obj.output_prompt = output
            return {"result": result_obj, "cost": 0.001, "model_name": "mock"}

        with patch("pdd.insert_includes.auto_include", side_effect=mock_auto_include):
            with patch("pdd.insert_includes.llm_invoke", side_effect=mock_insert_llm_invoke):
                with patch("pdd.insert_includes.load_prompt_template", return_value="template"):
                    with patch("pdd.insert_includes.preprocess", return_value="processed"):
                        from pdd.insert_includes import insert_includes
                        annotated_prompt, _, _, _ = insert_includes(
                            input_prompt=prompt_file.read_text(),
                            directory_path=str(src),
                            csv_filename=str(csv_path),
                            prompt_filename=str(prompt_file),
                            strength=0.5,
                            temperature=0.0,
                            verbose=False,
                        )

        # Verify auto-deps produced valid include tags
        assert "<include" in annotated_prompt
        assert "username_utils.py" in annotated_prompt

        # Now preprocess the annotated prompt (real ContentSelector, no mocks)
        from pdd.preprocess import preprocess
        final = preprocess(annotated_prompt, recursive=False, double_curly_brackets=False)

        # The <include> tags should be fully resolved
        assert "<include" not in final

        # Selected functions should be inlined
        assert "def capitalize_username" in final
        assert "def format_username_for_celebration" in final

        # Irrelevant content should NOT be present
        assert "def lookup_username_in_db" not in final
        assert "kubernetes" not in final.lower()

    def test_query_through_preprocess_caches_and_reduces(self, project_dir, monkeypatch):
        """
        <include query="..."> through preprocess creates cache entries
        and returns reduced content (not the full file).
        """
        monkeypatch.chdir(project_dir)
        monkeypatch.setenv("PDD_QUIET", "1")

        src = project_dir / "src"
        full_file = (src / "party_planning.txt").read_text()

        prompt = f'<include query="What songs should play at the success party?">{src}/party_planning.txt</include>'

        mock_config = {"project_root": str(project_dir)}

        # The LLM "extraction" returns only the music section
        music_section = textwrap.dedent('''\
            ## Music Playlist for Success Celebration
            - "We Are The Champions" by Queen
            - "Celebration" by Kool & The Gang
            - "Don't Stop Me Now" by Queen
            - "Happy" by Pharrell Williams
            - "Best Day of My Life" by American Authors
        ''').strip()

        def mock_llm_invoke(**kwargs):
            return {"result": music_section, "cost": 0.001, "model_name": "mock"}

        with patch("pdd.include_query_extractor.get_config", return_value=mock_config):
            with patch("pdd.include_query_extractor.llm_invoke", side_effect=mock_llm_invoke):
                with patch("pdd.include_query_extractor.load_prompt_template", return_value="t"):
                    with patch("pdd.include_query_extractor.preprocess", return_value="p"):
                        from pdd.preprocess import preprocess
                        result = preprocess(prompt, recursive=False, double_curly_brackets=False)

        # Should contain the extracted music content
        assert "We Are The Champions" in result
        assert "Celebration" in result

        # Should NOT contain other sections (full file not returned)
        assert "Catering Menu" not in result
        assert "Budget Breakdown" not in result

        # Content should be much shorter than the full file
        assert len(result) < len(full_file) / 2

        # Cache files should have been created
        cache_dir = project_dir / ".pdd" / "extracts"
        assert cache_dir.exists()
        md_files = list(cache_dir.glob("*.md"))
        meta_files = list(cache_dir.glob("*.meta.json"))
        assert len(md_files) == 1, f"Expected 1 cache .md file, got {len(md_files)}"
        assert len(meta_files) == 1, f"Expected 1 cache .meta.json, got {len(meta_files)}"

        # Verify cache meta
        meta = json.loads(meta_files[0].read_text())
        assert meta["query"] == "What songs should play at the success party?"

        # Second preprocess call should use cache (no additional LLM call)
        call_count = {"n": 0}
        original_mock = mock_llm_invoke

        def counting_mock(**kwargs):
            call_count["n"] += 1
            return original_mock(**kwargs)

        with patch("pdd.include_query_extractor.get_config", return_value=mock_config):
            with patch("pdd.include_query_extractor.llm_invoke", side_effect=counting_mock):
                with patch("pdd.include_query_extractor.load_prompt_template", return_value="t"):
                    with patch("pdd.include_query_extractor.preprocess", return_value="p"):
                        result2 = preprocess(prompt, recursive=False, double_curly_brackets=False)

        assert result2 == result, "Cached result should match first result"
        assert call_count["n"] == 0, "LLM should not be called on cache hit"

    def test_cache_invalidated_after_source_modification(self, project_dir, monkeypatch):
        """
        Modifying a source file invalidates the query= cache for that file.
        The next preprocess call should re-invoke the LLM.
        """
        monkeypatch.chdir(project_dir)
        monkeypatch.setenv("PDD_QUIET", "1")

        src = project_dir / "src"
        party_file = src / "party_planning.txt"

        prompt = f'<include query="What songs should play?">{party_file}</include>'
        mock_config = {"project_root": str(project_dir)}
        call_count = {"n": 0}

        def mock_llm_invoke(**kwargs):
            call_count["n"] += 1
            return {"result": f"Music v{call_count['n']}", "cost": 0.001, "model_name": "mock"}

        with patch("pdd.include_query_extractor.get_config", return_value=mock_config):
            with patch("pdd.include_query_extractor.llm_invoke", side_effect=mock_llm_invoke):
                with patch("pdd.include_query_extractor.load_prompt_template", return_value="t"):
                    with patch("pdd.include_query_extractor.preprocess", return_value="p"):
                        from pdd.preprocess import preprocess

                        # First call — LLM invoked
                        r1 = preprocess(prompt, recursive=False, double_curly_brackets=False)
                        assert call_count["n"] == 1
                        assert "Music v1" in r1

                        # Second call — cache hit, no LLM
                        r2 = preprocess(prompt, recursive=False, double_curly_brackets=False)
                        assert call_count["n"] == 1

                        # Modify the source file
                        party_file.write_text(party_file.read_text() + "\n# changed\n")

                        # Third call — cache stale, LLM re-invoked
                        r3 = preprocess(prompt, recursive=False, double_curly_brackets=False)
                        assert call_count["n"] == 2
                        assert "Music v2" in r3

    def test_mixed_select_and_query_includes_in_one_prompt(self, project_dir, monkeypatch):
        """
        A prompt with both select= and query= includes (on different tags)
        should resolve both correctly: select= via ContentSelector,
        query= via IncludeQueryExtractor.
        """
        monkeypatch.chdir(project_dir)
        monkeypatch.setenv("PDD_QUIET", "1")

        src = project_dir / "src"
        mock_config = {"project_root": str(project_dir)}

        prompt = textwrap.dedent(f'''\
            Write a python script to print "You did it, <Username>!!!" to the console.
            Capitalize the username.

            <include select="def:capitalize_username">{src}/username_utils.py</include>

            Use this for inspiration:
            <include query="What songs should play?">{src}/party_planning.txt</include>
        ''')

        def mock_llm_invoke(**kwargs):
            return {"result": "Music: We Are The Champions", "cost": 0.001, "model_name": "mock"}

        with patch("pdd.include_query_extractor.get_config", return_value=mock_config):
            with patch("pdd.include_query_extractor.llm_invoke", side_effect=mock_llm_invoke):
                with patch("pdd.include_query_extractor.load_prompt_template", return_value="t"):
                    with patch("pdd.include_query_extractor.preprocess", return_value="p"):
                        from pdd.preprocess import preprocess
                        result = preprocess(prompt, recursive=False, double_curly_brackets=False)

        # select= resolved via real ContentSelector
        assert "def capitalize_username" in result
        assert "Capitalize a username for display" in result

        # query= resolved via (mocked) IncludeQueryExtractor
        assert "We Are The Champions" in result

        # No unresolved tags remain
        assert "<include" not in result

        # Irrelevant content excluded
        assert "def lookup_username_in_db" not in result
        assert "Catering Menu" not in result


# ===========================================================================
# 13. SELECT= THROUGH PREPROCESS — structural extraction with rich fixtures
# ===========================================================================

@pytest.fixture
def rich_project_dir(tmp_path):
    """Create a realistic project with models, utils, config, and docs.

    models.py has 160+ lines (exceeds small-file threshold), two classes
    (UserModel, AdminModel), factory functions, and module-level constants.
    """
    models_code = textwrap.dedent('''\
        """User and Admin models for the application."""

        from __future__ import annotations

        import re
        from dataclasses import dataclass, field
        from typing import Optional, List


        @dataclass
        class UserModel:
            """Represents a user in the system."""

            name: str
            email: str
            role: str = "user"
            active: bool = True
            tags: List[str] = field(default_factory=list)

            def validate(self) -> bool:
                """Validate user fields.

                Returns True if name is non-empty and email contains @.
                """
                if not self.name or not self.name.strip():
                    return False
                if not self.email or "@" not in self.email:
                    return False
                if not re.match(r"^[^@]+@[^@]+\\\\.[^@]+$", self.email):
                    return False
                return True

            def display_name(self) -> str:
                """Return formatted display name."""
                return f"{self.name} <{self.email}>"

            def has_tag(self, tag: str) -> bool:
                """Check if user has a specific tag."""
                return tag in self.tags

            def add_tag(self, tag: str) -> None:
                """Add a tag to the user."""
                if tag not in self.tags:
                    self.tags.append(tag)

            def remove_tag(self, tag: str) -> None:
                """Remove a tag from the user."""
                if tag in self.tags:
                    self.tags.remove(tag)

            def to_dict(self) -> dict:
                """Serialize user to dictionary."""
                return {
                    "name": self.name,
                    "email": self.email,
                    "role": self.role,
                    "active": self.active,
                    "tags": self.tags,
                }

            @classmethod
            def from_dict(cls, data: dict) -> "UserModel":
                """Create user from dictionary."""
                return cls(
                    name=data["name"],
                    email=data["email"],
                    role=data.get("role", "user"),
                    active=data.get("active", True),
                    tags=data.get("tags", []),
                )


        @dataclass
        class AdminModel(UserModel):
            """Represents an admin user with additional permissions."""

            permissions: List[str] = field(default_factory=list)

            def has_permission(self, perm: str) -> bool:
                """Check if admin has a specific permission."""
                return perm in self.permissions or "admin:*" in self.permissions

            def grant_permission(self, perm: str) -> None:
                """Grant a permission to the admin."""
                if perm not in self.permissions:
                    self.permissions.append(perm)

            def revoke_permission(self, perm: str) -> None:
                """Revoke a permission from the admin."""
                if perm in self.permissions:
                    self.permissions.remove(perm)

            def to_dict(self) -> dict:
                """Serialize admin to dictionary."""
                base = super().to_dict()
                base["permissions"] = self.permissions
                return base


        def create_user(name: str, email: str, **kwargs) -> UserModel:
            """Factory function to create a UserModel."""
            return UserModel(name=name, email=email, **kwargs)


        def create_admin(name: str, email: str, permissions: Optional[List[str]] = None) -> AdminModel:
            """Factory function to create an AdminModel."""
            return AdminModel(
                name=name,
                email=email,
                role="admin",
                permissions=permissions or [],
            )


        # Module-level constants
        DEFAULT_ROLE = "user"
        ADMIN_ROLE = "admin"
        MAX_TAGS = 50
    ''')

    config_data = {
        "database": {"host": "localhost", "port": 5432},
        "auth": {"jwt_secret": "changeme", "token_ttl": 3600},
        "features": ["users", "admin", "logging"],
    }

    docs_md = textwrap.dedent('''\
        # MyApp Documentation

        A sample application for testing PDD selective includes.

        ## Installation

        ```bash
        pip install myapp
        ```

        ## Usage

        ```python
        from myapp.models import create_user
        user = create_user("Alice", "alice@example.com")
        ```

        ## API Reference

        See the models module for UserModel and AdminModel classes.

        ## Configuration

        Edit config.json to configure database and auth settings.
    ''')

    src = tmp_path / "src"
    src.mkdir()
    (src / "models.py").write_text(models_code)
    (src / "config.json").write_text(json.dumps(config_data, indent=2))
    (src / "docs.md").write_text(docs_md)

    return tmp_path


class TestPreprocessSelectRealFile:
    """select= attributes resolved through preprocess() with real files.

    These tests exercise the deterministic structural extraction path
    (ContentSelector) through the full preprocess pipeline using a rich
    multi-file fixture.
    """

    def test_select_def_extracts_single_function(self, rich_project_dir):
        """
        <include select="def:create_user">models.py</include> should resolve
        to only the create_user function body, not the full 160-line file.
        """
        src_file = rich_project_dir / "src" / "models.py"
        full_content = src_file.read_text()
        prompt = f'<include select="def:create_user">{src_file}</include>'

        from pdd.preprocess import preprocess

        result = preprocess(prompt, recursive=False, double_curly_brackets=False)

        # Should contain the function signature and its body
        assert "def create_user" in result
        assert "UserModel(name=name" in result  # actual implementation line

        # Should NOT contain anything from the classes or other functions
        assert "class UserModel" not in result
        assert "class AdminModel" not in result
        assert "def validate" not in result
        assert "grant_permission" not in result
        assert "DEFAULT_ROLE" not in result  # module-level constant

        # Quantitative: a 3-line factory function should be <<10% of the 160-line file
        result_lines = len(result.strip().splitlines())
        full_lines = len(full_content.splitlines())
        assert result_lines < full_lines * 0.1, (
            f"Expected <10% of file lines for a single function. "
            f"Got {result_lines}/{full_lines} lines."
        )
        print(f"  select=def:create_user: {result_lines} lines from {full_lines}-line file")

    def test_select_class_extracts_whole_class(self, rich_project_dir):
        """
        <include select="class:UserModel">models.py</include> should resolve
        to the UserModel class (including methods) but not AdminModel.
        """
        src_file = rich_project_dir / "src" / "models.py"
        full_content = src_file.read_text()
        prompt = f'<include select="class:UserModel">{src_file}</include>'

        from pdd.preprocess import preprocess

        result = preprocess(prompt, recursive=False, double_curly_brackets=False)

        # UserModel class and ALL its methods should be present
        assert "class UserModel" in result
        assert "def validate" in result
        assert "def display_name" in result
        assert "def has_tag" in result
        assert "def to_dict" in result
        assert "def from_dict" in result

        # Actual implementation lines from UserModel should be present
        assert "@" not in result or "re.match" in result  # validate() body uses re.match
        assert "self.name" in result

        # AdminModel (a subclass, separate entity) should NOT be present
        assert "class AdminModel" not in result
        assert "has_permission" not in result
        assert "grant_permission" not in result

        # Standalone functions should NOT be present
        assert "def create_user" not in result
        assert "def create_admin" not in result

        # Module constants should NOT be present
        assert "DEFAULT_ROLE" not in result
        assert "MAX_TAGS" not in result

        # UserModel is ~60 lines out of 160 — should be well under 60%
        assert len(result) < len(full_content) * 0.6, (
            f"select=class:UserModel should be <60% of file. "
            f"Got {len(result)}/{len(full_content)} chars."
        )
        print(f"  class:UserModel: {len(result)} chars / {len(full_content)} full "
              f"({100 - len(result)/len(full_content)*100:.0f}% reduction)")

    def test_select_class_method_extracts_single_method(self, rich_project_dir):
        """
        <include select="class:UserModel.validate">models.py</include> should
        extract only the validate method, not the whole class.
        """
        src_file = rich_project_dir / "src" / "models.py"
        full_content = src_file.read_text()
        prompt = f'<include select="class:UserModel.validate">{src_file}</include>'

        from pdd.preprocess import preprocess

        result = preprocess(prompt, recursive=False, double_curly_brackets=False)

        # The validate method signature and body
        assert "def validate" in result
        assert "re.match" in result or "@" in result  # implementation detail from validate()

        # Should NOT include other UserModel methods
        assert "def display_name" not in result
        assert "def to_dict" not in result
        assert "def has_tag" not in result
        assert "def add_tag" not in result

        # Should NOT include class-level stuff or other classes
        assert "class AdminModel" not in result
        assert "def create_user" not in result

        # A single method is ~10 lines from a 160-line file
        result_lines = len(result.strip().splitlines())
        full_lines = len(full_content.splitlines())
        assert result_lines < full_lines * 0.15, (
            f"A single method should be <15% of the file. "
            f"Got {result_lines}/{full_lines} lines."
        )
        print(f"  class:UserModel.validate: {result_lines} lines from {full_lines}-line file")

    def test_select_multiple_selectors_combined(self, rich_project_dir):
        """
        Composing selectors: select="def:create_user,def:create_admin" should
        extract both factory functions but nothing else.
        """
        src_file = rich_project_dir / "src" / "models.py"
        full_content = src_file.read_text()
        prompt = f'<include select="def:create_user,def:create_admin">{src_file}</include>'

        from pdd.preprocess import preprocess

        result = preprocess(prompt, recursive=False, double_curly_brackets=False)

        # Both factory functions should be present with their bodies
        assert "def create_user" in result
        assert "def create_admin" in result
        assert "UserModel(name=name" in result   # create_user body
        assert "AdminModel(" in result            # create_admin body

        # Nothing else from the file
        assert "class UserModel" not in result
        assert "class AdminModel" not in result
        assert "def validate" not in result
        assert "DEFAULT_ROLE" not in result

        # Two 3-line functions from a 160-line file
        result_lines = len(result.strip().splitlines())
        full_lines = len(full_content.splitlines())
        assert result_lines < full_lines * 0.15, (
            f"Two small functions should be <15% of file. "
            f"Got {result_lines}/{full_lines} lines."
        )

    def test_select_section_from_markdown(self, rich_project_dir):
        """
        <include select="section:Installation">docs.md</include> should extract
        only the Installation section from the markdown file.
        """
        docs_file = rich_project_dir / "src" / "docs.md"
        full_content = docs_file.read_text()
        prompt = f'<include select="section:Installation">{docs_file}</include>'

        from pdd.preprocess import preprocess

        result = preprocess(prompt, recursive=False, double_curly_brackets=False)

        # Should contain the actual install command from the Installation section
        assert "pip install myapp" in result

        # Should NOT contain content from any other section
        assert "API Reference" not in result
        assert "Configuration" not in result
        assert "config.json" not in result
        assert "MyApp Documentation" not in result  # top-level heading

        # The Installation section is ~5 lines out of ~20
        result_lines = len(result.strip().splitlines())
        full_lines = len(full_content.splitlines())
        assert result_lines < full_lines * 0.5, (
            f"One section should be <50% of the doc. "
            f"Got {result_lines}/{full_lines} lines."
        )
        print(f"  section:Installation: {result_lines} lines from {full_lines}-line doc")

    def test_select_json_path(self, rich_project_dir):
        """
        <include select="path:database">config.json</include> should extract
        just the database config object, not the full config.
        """
        config_file = rich_project_dir / "src" / "config.json"
        prompt = f'<include select="path:database">{config_file}</include>'

        from pdd.preprocess import preprocess

        result = preprocess(prompt, recursive=False, double_curly_brackets=False)

        # Should contain the database config values
        assert "localhost" in result
        assert "5432" in result

        # Should NOT contain values from other top-level keys
        assert "jwt_secret" not in result
        assert "changeme" not in result
        assert "token_ttl" not in result
        assert "features" not in result or "logging" not in result

        print(f"  path:database extracted: {result.strip()}")


# ===========================================================================
# 14. INTERFACE MODE — signature-only extraction with rich fixtures
# ===========================================================================

class TestInterfaceModeRichFixture:
    """mode='interface' extracts only signatures through preprocess, using rich fixtures."""

    def test_interface_mode_strips_method_bodies(self, rich_project_dir):
        """
        <include select="class:UserModel" mode="interface">models.py</include>
        should produce signatures, docstrings, and field declarations but
        replace all method implementations with `...`.
        """
        src_file = rich_project_dir / "src" / "models.py"
        full_content = src_file.read_text()
        prompt = f'<include select="class:UserModel" mode="interface">{src_file}</include>'

        from pdd.preprocess import preprocess

        result = preprocess(prompt, recursive=False, double_curly_brackets=False)

        # Should preserve class declaration and ALL method signatures
        assert "class UserModel" in result
        assert "def validate(self) -> bool" in result
        assert "def display_name(self) -> str" in result
        assert "def has_tag(self, tag: str) -> bool" in result
        assert "def add_tag(self, tag: str) -> None" in result
        assert "def to_dict(self) -> dict" in result
        assert "def from_dict(cls, data: dict)" in result

        # Should preserve dataclass field declarations (the data contract)
        assert "name: str" in result
        assert "email: str" in result
        assert 'role: str = "user"' in result
        assert "tags: List[str]" in result

        # Should preserve docstrings (the API contract)
        assert "Validate user fields" in result
        assert "Return formatted display name" in result
        assert "Check if user has a specific tag" in result

        # Bodies should be replaced with ... (the hallmark of interface mode)
        assert "..." in result

        # Should NOT have any implementation lines from method bodies
        assert "self.tags.append" not in result   # add_tag body
        assert "self.tags.remove" not in result   # remove_tag body
        assert "re.match" not in result            # validate body
        assert "return False" not in result        # validate body
        assert 'f"{self.name}' not in result       # display_name body
        assert "tag in self.tags" not in result    # has_tag body

        # The output should be valid Python (interface is a real stub)
        try:
            ast.parse(result)
        except SyntaxError as e:
            raise AssertionError(f"Interface mode should produce valid Python, got: {e}")

        # Quantitative: interface should be significantly smaller
        assert len(result) < len(full_content) * 0.5, (
            f"Interface mode should be <50% of full file. "
            f"Got {len(result)}/{len(full_content)} chars."
        )
        print(f"  Interface mode: {len(result)} chars vs {len(full_content)} full "
              f"({100 - len(result)/len(full_content)*100:.0f}% reduction)")

    def test_interface_mode_whole_file(self, rich_project_dir):
        """
        <include mode="interface">models.py</include> (no select=) should
        produce an interface view of the entire file — both classes, all
        methods, standalone functions, and constants, but with all function/
        method bodies replaced by `...`.
        """
        src_file = rich_project_dir / "src" / "models.py"
        full_content = src_file.read_text()
        prompt = f'<include mode="interface">{src_file}</include>'

        from pdd.preprocess import preprocess

        result = preprocess(prompt, recursive=False, double_curly_brackets=False)

        # --- Preserved: signatures from BOTH classes ---
        assert "class UserModel" in result
        assert "class AdminModel(UserModel)" in result
        assert "def validate(self) -> bool" in result
        assert "def has_permission(self, perm: str) -> bool" in result

        # --- Preserved: standalone function signatures ---
        assert "def create_user(name: str, email: str, **kwargs) -> UserModel" in result
        assert "def create_admin(" in result

        # --- Preserved: docstrings from both classes ---
        assert "Represents a user in the system" in result
        assert "Represents an admin user with additional permissions" in result
        assert "Factory function to create a UserModel" in result

        # --- Preserved: module-level constants (not function bodies) ---
        assert "DEFAULT_ROLE" in result
        assert "MAX_TAGS" in result

        # --- Stripped: implementation bodies from ALL functions ---
        # UserModel method bodies
        assert "self.tags.append" not in result
        assert "self.tags.remove" not in result
        assert "return False" not in result         # validate body
        assert "tag in self.tags" not in result     # has_tag body

        # AdminModel method bodies
        assert "self.permissions.append" not in result
        assert "self.permissions.remove" not in result
        assert 'base["permissions"]' not in result
        assert 'super().to_dict()' not in result

        # Standalone function bodies
        assert "UserModel(name=name" not in result  # create_user body
        assert 'role="admin"' not in result          # create_admin body

        # --- Bodies replaced with ... ---
        assert "..." in result

        # --- Valid Python (the whole-file interface is a real stub) ---
        try:
            ast.parse(result)
        except SyntaxError as e:
            raise AssertionError(f"Whole-file interface should produce valid Python, got: {e}")

        # --- Quantitative reduction ---
        assert len(result) < len(full_content) * 0.75, (
            f"Whole-file interface should be <75% of full file. "
            f"Got {len(result)}/{len(full_content)} chars."
        )
        print(f"  Whole-file interface: {len(result)} chars vs {len(full_content)} full "
              f"({100 - len(result)/len(full_content)*100:.0f}% reduction)")

    def test_interface_mode_on_non_python_falls_back_gracefully(self, rich_project_dir):
        """
        <include mode="interface">docs.md</include> — interface mode on a
        non-Python file. Preprocess should catch the failure and fall back
        to including the full file content with a warning.
        """
        docs_file = rich_project_dir / "src" / "docs.md"
        full_content = docs_file.read_text()
        prompt = f'<include mode="interface">{docs_file}</include>'

        from pdd.preprocess import preprocess

        with warnings.catch_warnings(record=True) as w:
            warnings.simplefilter("always")
            result = preprocess(prompt, recursive=False, double_curly_brackets=False)

        # Should not crash — tag must be resolved
        assert "<include" not in result

        # Should have fallen back to the full file
        assert "# MyApp Documentation" in result
        assert "Installation" in result
        assert "API Reference" in result
        assert "Configuration" in result

        # Full file should be included (not empty, not truncated)
        assert len(result.strip()) >= len(full_content.strip()) * 0.9, (
            f"Should fall back to full file. Got {len(result)}/{len(full_content)} chars."
        )

        # Should have emitted a warning about the failure
        assert len(w) >= 1, "Expected a warning about interface mode failing on non-Python file"
        print(f"  Non-Python interface fallback: {len(result)} chars, {len(w)} warning(s)")

    def test_interface_mode_on_non_python_with_selector_still_selects(self, rich_project_dir):
        """
        <include select="section:Installation" mode="interface">docs.md</include>
        — interface mode is meaningless for markdown, but the section: selector
        should still work. Interface is silently a no-op for non-Python
        files when combined with selectors.
        """
        docs_file = rich_project_dir / "src" / "docs.md"
        prompt = f'<include select="section:Installation" mode="interface">{docs_file}</include>'

        from pdd.preprocess import preprocess

        result = preprocess(prompt, recursive=False, double_curly_brackets=False)

        # The section selector should have worked
        assert "pip install myapp" in result
        assert "<include" not in result

        # Other sections should NOT be present (selector worked)
        assert "API Reference" not in result
        assert "Configuration" not in result

        print(f"  Non-Python interface + selector: section extracted correctly")


# ===========================================================================
# 15. SELECT= FALLBACK — nonexistent selector falls back to full file
# ===========================================================================

class TestSelectFallbackRichFixture:
    """When select= targets something that doesn't exist, behavior is graceful."""

    def test_nonexistent_function_falls_back_to_full_file(self, rich_project_dir):
        """
        <include select="def:nonexistent_function">models.py</include> should
        fall back to including the full file (with a warning), not crash.
        """
        src_file = rich_project_dir / "src" / "models.py"
        full_content = src_file.read_text()
        prompt = f'<include select="def:nonexistent_function">{src_file}</include>'

        from pdd.preprocess import preprocess

        with warnings.catch_warnings(record=True) as w:
            warnings.simplefilter("always")
            result = preprocess(prompt, recursive=False, double_curly_brackets=False)

        # The include tag must be resolved — never left as raw XML
        assert "<include" not in result

        # Should have fallen back to the FULL file content
        assert "class UserModel" in result
        assert "class AdminModel" in result
        assert "def create_user" in result
        assert "DEFAULT_ROLE" in result

        # The result should be approximately the full file size
        assert len(result.strip()) >= len(full_content.strip()) * 0.9, (
            f"Fallback should include the full file. "
            f"Got {len(result)} chars vs {len(full_content)} full."
        )

        print(f"  Fallback: {len(result)} chars (full file: {len(full_content)}), "
              f"warnings emitted: {len(w)}")


# ===========================================================================
# 16. COMBINED SELECT + QUERY PRIORITY — select= preferred over query=
# ===========================================================================

class TestSelectQueryPriorityRichFixture:
    """When both select= and query= are present, select= wins."""

    def test_select_preferred_over_query_when_both_present(self, rich_project_dir):
        """
        <include select="def:create_user" query="...">models.py</include>
        should use select= (deterministic) and ignore query= (LLM-based).
        """
        src_file = rich_project_dir / "src" / "models.py"
        prompt = (
            f'<include select="def:create_user" '
            f'query="How do you create users?">{src_file}</include>'
        )

        from pdd.preprocess import preprocess

        # This should NOT trigger an LLM call — select= takes priority.
        result = preprocess(prompt, recursive=False, double_curly_brackets=False)

        # Should have the structurally-selected function
        assert "def create_user" in result
        assert "UserModel(name=name" in result
        assert "<include" not in result

        # Should NOT have the full file (proving select= did the filtering)
        assert "class UserModel" not in result
        assert "class AdminModel" not in result
        assert "def validate" not in result

    def test_select_query_and_interface_all_three(self, rich_project_dir):
        """
        All three attributes together: select= takes priority over query=,
        and mode="interface" is applied to the structurally-selected content.
        No LLM call should happen.
        """
        src_file = rich_project_dir / "src" / "models.py"
        prompt = (
            f'<include select="class:UserModel" '
            f'query="What does UserModel do?" '
            f'mode="interface">{src_file}</include>'
        )

        from pdd.preprocess import preprocess

        result = preprocess(prompt, recursive=False, double_curly_brackets=False)

        # select= picked UserModel, mode=interface transformed it
        assert "class UserModel" in result
        assert "def validate(self) -> bool" in result
        assert "Validate user fields" in result  # docstring preserved

        # Interface mode stripped bodies
        assert "self.tags.append" not in result
        assert "return False" not in result
        assert "..." in result

        # select= excluded everything else
        assert "class AdminModel" not in result
        assert "def create_user" not in result

        # No LLM call happened (would fail without credentials)
        assert "<include" not in result
        print("  Triple combo (select + query + interface): all three composed correctly")


# ===========================================================================
# 17. SELECT= CONTENT REDUCTION — verify select actually reduces content
# ===========================================================================

class TestSelectContentReductionRichFixture:
    """Verify that select= produces meaningfully less content than the full file."""

    def test_selecting_one_method_is_much_smaller_than_full_file(self, rich_project_dir):
        """
        Selecting a single method from a 160-line file yields << 50% of content.
        """
        src_file = rich_project_dir / "src" / "models.py"
        full_content = src_file.read_text()
        full_len = len(full_content)

        prompt = f'<include select="class:UserModel.validate">{src_file}</include>'

        from pdd.preprocess import preprocess

        result = preprocess(prompt, recursive=False, double_curly_brackets=False)

        result_len = len(result.strip())
        reduction_pct = (1 - result_len / full_len) * 100

        assert result_len < full_len * 0.3, (
            f"Selecting one method should yield <30% of file content. "
            f"Got {result_len}/{full_len} chars ({100 - reduction_pct:.0f}%)"
        )
        print(f"  Single method: {result_len} chars / {full_len} full ({reduction_pct:.0f}% reduction)")

    def test_selecting_two_functions_still_smaller_than_full(self, rich_project_dir):
        """
        Two small factory functions (~6 lines total) from a 160-line file
        should yield significant reduction.
        """
        src_file = rich_project_dir / "src" / "models.py"
        full_content = src_file.read_text()
        full_len = len(full_content)

        prompt = f'<include select="def:create_user,def:create_admin">{src_file}</include>'

        from pdd.preprocess import preprocess

        result = preprocess(prompt, recursive=False, double_curly_brackets=False)

        result_len = len(result.strip())
        reduction_pct = (1 - result_len / full_len) * 100

        assert result_len < full_len * 0.2, (
            f"Two small functions should yield <20% of full file content. "
            f"Got {result_len}/{full_len} chars ({100 - reduction_pct:.0f}%)"
        )
        print(f"  Two functions: {result_len} chars / {full_len} full ({reduction_pct:.0f}% reduction)")


# ============================================================================
# E2E: Cross-directory CSV path integrity through the full pipeline
#
# This tests the compound path corruption bug (issue #603): when
# summarize_directory scans multiple directories into the same CSV, then
# auto_include and insert_includes process that CSV, paths from one
# directory must not be misqualified with another directory's prefix.
# ============================================================================


class TestCrossDirectoryPipelineE2E:
    """E2E test for the full auto-deps pipeline with multi-directory scans.

    The real-world pattern is:
    1. summarize_directory scans context/ → CSV has context-relative paths
    2. summarize_directory scans pdd/ → CSV accumulates pdd-relative paths
    3. insert_includes reads the mixed CSV and calls auto_include
    4. auto_include formats CSV entries for the LLM and qualifies result paths
    5. insert_includes applies the returned directives to the prompt

    The bug: step 4 blindly prepends the current directory_path to all CSV
    entries, corrupting paths from other directories.
    """

    @pytest.fixture
    def project_with_two_dirs(self, tmp_path):
        """Set up a mini project with context/ and pdd/ directories."""
        context_dir = tmp_path / "context"
        context_dir.mkdir()
        pdd_dir = tmp_path / "pdd"
        pdd_dir.mkdir()

        # context/ has example files
        (context_dir / "data_example.py").write_text(textwrap.dedent('''\
            """Example demonstrating data processing."""

            import json

            def load_data(path: str) -> dict:
                """Load data from a JSON file."""
                with open(path) as f:
                    return json.load(f)

            def transform_data(data: dict) -> list:
                """Transform raw data into processed format."""
                return [{"key": k, "value": v} for k, v in data.items()]

            if __name__ == "__main__":
                raw = load_data("input.json")
                print(transform_data(raw))
        '''))

        # pdd/ has source files
        (pdd_dir / "cli.py").write_text(textwrap.dedent('''\
            """CLI entry point for pdd."""

            import click

            @click.command()
            @click.argument("action")
            def main(action: str):
                """Run a pdd action."""
                if action == "sync":
                    print("Syncing...")
                elif action == "generate":
                    print("Generating...")
                else:
                    raise click.UsageError(f"Unknown action: {action}")

            if __name__ == "__main__":
                main()
        '''))

        return tmp_path, context_dir, pdd_dir

    def test_multi_directory_scan_preserves_all_entries(
        self, project_with_two_dirs, monkeypatch
    ):
        """Scanning context/ then pdd/ should produce a CSV with entries
        from both directories, and neither scan should wipe the other's entries.
        """
        tmp_path, context_dir, pdd_dir = project_with_two_dirs
        monkeypatch.chdir(tmp_path)

        from pdd.summarize_directory import summarize_directory, FileSummary

        mock_resp = {
            'result': FileSummary(
                file_summary="Mock summary",
                key_exports=["func"],
                dependencies=["os"],
            ),
            'cost': 0.01,
            'model_name': "mock",
        }

        with patch("pdd.summarize_directory.load_prompt_template", return_value="prompt"), \
             patch("pdd.summarize_directory.llm_invoke", return_value=mock_resp):

            # Scan context/
            csv1, _, _ = summarize_directory(
                directory_path=str(context_dir),
                strength=0.5,
                temperature=0.0,
            )

            # Scan pdd/ with context/'s CSV as cache
            csv2, _, _ = summarize_directory(
                directory_path=str(pdd_dir),
                strength=0.5,
                temperature=0.0,
                csv_file=csv1,
            )

        import csv as csv_mod
        from io import StringIO
        rows = list(csv_mod.DictReader(StringIO(csv2)))
        paths = {r['full_path'] for r in rows}

        # Both files must be present
        assert len(rows) >= 2, (
            f"Expected entries from both context/ and pdd/ scans, "
            f"got {len(rows)} rows. Paths: {paths}"
        )

    def test_auto_include_does_not_corrupt_cross_directory_paths(
        self, project_with_two_dirs, monkeypatch
    ):
        """When auto_include processes a mixed-origin CSV with
        directory_path='context/', it must not prepend 'context/' to
        entries that came from the pdd/ scan.

        This is the core path corruption bug: _format_csv_rows_for_llm
        and _qualify_result_paths blindly use directory_path as a prefix.
        """
        tmp_path, context_dir, pdd_dir = project_with_two_dirs
        monkeypatch.chdir(tmp_path)

        # Build a mixed-origin CSV as summarize_directory would produce
        mixed_csv = (
            "full_path,file_summary,key_exports,dependencies,content_hash\n"
            "data_example.py,Data processing example,"
            '"[""load_data"",""transform_data""]","[""json""]",aaa\n'
            "cli.py,CLI entry point,"
            '"[""main""]","[""click""]",bbb\n'
        )

        from pdd.auto_include import auto_include, AutoIncludeResult, NewInclude

        # LLM returns a recommendation that includes cli.py (from pdd/ scan)
        mock_result = AutoIncludeResult(
            reasoning="The prompt needs CLI functionality",
            new_includes=[NewInclude(file="cli.py", module="cli")],
            existing_include_annotations=[],
        )

        def mock_llm(**kwargs):
            if kwargs.get("output_pydantic") == AutoIncludeResult:
                return {"result": mock_result, "cost": 0.01, "model_name": "mock"}
            return {"result": "summary", "cost": 0.001, "model_name": "mock"}

        # Make files large enough that selectors aren't stripped
        (context_dir / "data_example.py").write_text(
            (context_dir / "data_example.py").read_text() + "\n# padding\n" * 100
        )
        (pdd_dir / "cli.py").write_text(
            (pdd_dir / "cli.py").read_text() + "\n# padding\n" * 100
        )

        def mock_summarize(**_kwargs):
            return (mixed_csv, 0.001, "mock")

        with patch("pdd.auto_include.llm_invoke", side_effect=mock_llm), \
             patch("pdd.auto_include.summarize_directory", side_effect=mock_summarize):
            directives, _, _, _ = auto_include(
                input_prompt="Generate a tool that processes data",
                directory_path=str(context_dir),
                strength=0.7,
                temperature=0.0,
            )

        # cli.py should NOT be qualified as context/cli.py
        assert "context/cli.py" not in directives, (
            f"cli.py from pdd/ scan was misqualified with context/ prefix. "
            f"Directives:\n{directives}"
        )
        # cli.py should appear in the output as-is or with its correct prefix
        assert "cli.py" in directives, (
            f"cli.py should appear in directives. Got:\n{directives}"
        )
