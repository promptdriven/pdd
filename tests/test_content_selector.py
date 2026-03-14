import sys
from pathlib import Path

# Add project root to sys.path to ensure local code is prioritized
project_root = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(project_root))

import json
import textwrap

import pytest

from pdd.content_selector import ContentSelector, SelectorError


# ==============================================================================
# Fixtures
# ==============================================================================

@pytest.fixture
def sample_text():
    """Simple multi-line text for line selector tests."""
    return "line1\nline2\nline3\nline4\nline5"


@pytest.fixture
def sample_python():
    """Sample Python source code."""
    return textwrap.dedent("""\
        import os

        CONSTANT = 42

        def hello(name: str) -> str:
            \"\"\"Say hello.\"\"\"
            return f"Hello, {name}!"

        def goodbye(name: str) -> str:
            return f"Goodbye, {name}!"

        @decorator
        class MyClass:
            \"\"\"A sample class.\"\"\"

            x: int = 0

            def __init__(self, value: int):
                self.value = value

            def public_method(self) -> int:
                \"\"\"Return the value.\"\"\"
                return self.value

            def _private_method(self) -> None:
                pass

            async def async_method(self) -> str:
                return "async"
    """)


@pytest.fixture
def sample_markdown():
    """Sample Markdown content."""
    return textwrap.dedent("""\
        # Introduction

        Some intro text.

        ## Details

        Detail paragraph 1.
        Detail paragraph 2.

        ## Another Section

        Another section content.

        # Conclusion

        Final thoughts.
    """)


@pytest.fixture
def sample_json():
    """Sample JSON content."""
    return json.dumps({
        "name": "test",
        "version": "1.0",
        "dependencies": {
            "foo": "^1.0",
            "bar": "^2.0"
        },
        "items": [
            {"id": 1, "label": "first"},
            {"id": 2, "label": "second"}
        ]
    }, indent=2)


# ==============================================================================
# Tests: Line Selectors
# ==============================================================================

class TestLineSelectors:
    """Tests for lines: selector."""

    def test_single_line(self, sample_text):
        """Select a single line by number (1-based)."""
        result = ContentSelector.select(sample_text, ["lines:3"])
        assert result == "line3"

    def test_first_line(self, sample_text):
        """Select the first line."""
        result = ContentSelector.select(sample_text, ["lines:1"])
        assert result == "line1"

    def test_last_line(self, sample_text):
        """Select the last line."""
        result = ContentSelector.select(sample_text, ["lines:5"])
        assert result == "line5"

    def test_range(self, sample_text):
        """Select a range of lines."""
        result = ContentSelector.select(sample_text, ["lines:2-4"])
        assert result == "line2\nline3\nline4"

    def test_range_from_start(self, sample_text):
        """Select from start to a specific line (-M form)."""
        result = ContentSelector.select(sample_text, ["lines:-3"])
        assert result == "line1\nline2\nline3"

    def test_range_to_end(self, sample_text):
        """Select from a specific line to end (N- form)."""
        result = ContentSelector.select(sample_text, ["lines:3-"])
        assert result == "line3\nline4\nline5"

    def test_out_of_range(self, sample_text):
        """Line number out of range raises SelectorError."""
        with pytest.raises(SelectorError, match="out of range"):
            ContentSelector.select(sample_text, ["lines:10"])

    def test_inverted_range(self, sample_text):
        """Inverted range raises SelectorError."""
        with pytest.raises(SelectorError):
            ContentSelector.select(sample_text, ["lines:4-2"])

    def test_full_range(self, sample_text):
        """Select all lines."""
        result = ContentSelector.select(sample_text, ["lines:1-5"])
        assert result == sample_text

    def test_multiple_line_specs(self, sample_text):
        """Multiple line selectors produce union of lines in file order."""
        result = ContentSelector.select(sample_text, ["lines:1", "lines:3", "lines:5"])
        assert result == "line1\nline3\nline5"

    def test_comma_in_value(self, sample_text):
        """Multiple line ranges in one selector value (comma in value)."""
        result = ContentSelector.select(sample_text, ["lines:1,3,5"])
        assert result == "line1\nline3\nline5"

    def test_single_line_content(self):
        """Content with a single line works correctly."""
        result = ContentSelector.select("only line", ["lines:1"])
        assert result == "only line"


# ==============================================================================
# Tests: Python AST Selectors - def
# ==============================================================================

class TestDefSelectors:
    """Tests for def: selector."""

    def test_extract_function(self, sample_python):
        """Extract a function by name."""
        result = ContentSelector.select(
            sample_python, ["def:hello"], file_path="test.py"
        )
        assert "def hello(name: str) -> str:" in result
        assert '"""Say hello."""' in result
        assert 'return f"Hello, {name}!"' in result

    def test_extract_another_function(self, sample_python):
        """Extract a different function."""
        result = ContentSelector.select(
            sample_python, ["def:goodbye"], file_path="test.py"
        )
        assert "def goodbye(name: str) -> str:" in result
        assert "Goodbye" in result

    def test_function_not_found(self, sample_python):
        """Non-existent function raises SelectorError."""
        with pytest.raises(SelectorError, match="not found"):
            ContentSelector.select(
                sample_python, ["def:nonexistent"], file_path="test.py"
            )

    def test_def_on_non_python_file(self, sample_python):
        """def selector on non-Python file raises SelectorError."""
        with pytest.raises(SelectorError):
            ContentSelector.select(
                sample_python, ["def:hello"], file_path="test.txt"
            )

    def test_def_with_no_file_path(self, sample_python):
        """def selector with no file_path assumes Python."""
        result = ContentSelector.select(sample_python, ["def:hello"])
        assert "def hello" in result

    def test_async_function(self):
        """Extract an async function."""
        code = textwrap.dedent("""\
            async def fetch_data(url: str) -> dict:
                return {}
        """)
        result = ContentSelector.select(code, ["def:fetch_data"], file_path="test.py")
        assert "async def fetch_data" in result

    def test_nested_function(self):
        """Extract a nested function by name."""
        code = textwrap.dedent("""\
            def outer():
                def inner():
                    pass
        """)
        result = ContentSelector.select(code, ["def:inner"])
        assert "def inner():" in result
        assert "    def inner():" in result

    def test_duplicate_function_names(self):
        """def: finds all functions with the given name (top-level and methods)."""
        code = textwrap.dedent("""\
            def foo():
                return 1

            class Bar:
                def foo(self):
                    return 2
        """)
        result = ContentSelector.select(code, ["def:foo"])
        assert "def foo():" in result
        assert "return 1" in result
        assert "def foo(self):" in result
        assert "return 2" in result

    def test_decorated_function(self):
        """Extract a function with decorators includes the decorator."""
        code = textwrap.dedent("""\
            @staticmethod
            def my_func():
                return 42
        """)
        result = ContentSelector.select(code, ["def:my_func"], file_path="test.py")
        assert "@staticmethod" in result
        assert "def my_func" in result


# ==============================================================================
# Tests: Python AST Selectors - class
# ==============================================================================

class TestClassSelectors:
    """Tests for class: selector."""

    def test_extract_whole_class(self, sample_python):
        """Extract an entire class including all members."""
        result = ContentSelector.select(
            sample_python, ["class:MyClass"], file_path="test.py"
        )
        assert "class MyClass:" in result
        assert "__init__" in result
        assert "public_method" in result
        assert "_private_method" in result

    def test_extract_class_includes_decorator(self, sample_python):
        """Extract a decorated class includes its decorator."""
        result = ContentSelector.select(
            sample_python, ["class:MyClass"], file_path="test.py"
        )
        assert "@decorator" in result
        assert "class MyClass:" in result

    def test_extract_class_method(self, sample_python):
        """Extract a specific method from a class."""
        result = ContentSelector.select(
            sample_python, ["class:MyClass.public_method"], file_path="test.py"
        )
        assert "def public_method" in result
        assert "return self.value" in result
        assert "__init__" not in result

    def test_class_not_found(self, sample_python):
        """Non-existent class raises SelectorError."""
        with pytest.raises(SelectorError, match="not found"):
            ContentSelector.select(
                sample_python, ["class:NonExistent"], file_path="test.py"
            )

    def test_method_not_found(self, sample_python):
        """Non-existent method raises SelectorError."""
        with pytest.raises(SelectorError, match="not found"):
            ContentSelector.select(
                sample_python, ["class:MyClass.no_such_method"], file_path="test.py"
            )

    def test_extract_init(self, sample_python):
        """Extract __init__ method."""
        result = ContentSelector.select(
            sample_python, ["class:MyClass.__init__"], file_path="test.py"
        )
        assert "def __init__" in result
        assert "self.value = value" in result

    def test_extract_async_method(self, sample_python):
        """Extract an async method from a class."""
        result = ContentSelector.select(
            sample_python, ["class:MyClass.async_method"], file_path="test.py"
        )
        assert "async def async_method" in result

    def test_decorated_class(self):
        """Extract a class with decorators includes the decorator."""
        code = textwrap.dedent("""\
            @dataclass
            class MyData:
                x: int = 0
                y: int = 0
        """)
        result = ContentSelector.select(code, ["class:MyData"], file_path="test.py")
        assert "@dataclass" in result
        assert "class MyData:" in result


# ==============================================================================
# Tests: Markdown Section Selector
# ==============================================================================

class TestSectionSelectors:
    """Tests for section: selector."""

    def test_extract_section(self, sample_markdown):
        """Extract a section by heading."""
        result = ContentSelector.select(
            sample_markdown, ["section:Details"], file_path="doc.md"
        )
        assert "## Details" in result
        assert "Detail paragraph 1." in result
        assert "Detail paragraph 2." in result
        assert "Another Section" not in result

    def test_extract_top_level_section(self, sample_markdown):
        """Extract a top-level section (stops at next same-or-higher heading)."""
        result = ContentSelector.select(
            sample_markdown, ["section:Introduction"], file_path="doc.md"
        )
        assert "# Introduction" in result
        assert "Some intro text." in result
        assert "Conclusion" not in result

    def test_section_not_found(self, sample_markdown):
        """Non-existent section raises SelectorError."""
        with pytest.raises(SelectorError, match="not found"):
            ContentSelector.select(
                sample_markdown, ["section:Missing"], file_path="doc.md"
            )

    def test_section_on_non_markdown(self, sample_markdown):
        """Section selector on non-Markdown file raises SelectorError."""
        with pytest.raises(SelectorError):
            ContentSelector.select(
                sample_markdown, ["section:Details"], file_path="test.py"
            )

    def test_extract_last_section(self, sample_markdown):
        """Extract the last section (no following heading)."""
        result = ContentSelector.select(
            sample_markdown, ["section:Conclusion"], file_path="doc.md"
        )
        assert "# Conclusion" in result
        assert "Final thoughts." in result

    def test_h3_section(self):
        """Extract an h3 section (stops at next same-or-higher level)."""
        content = "## Parent\n\n### Child\n\nChild content.\n\n### Sibling\n\nSibling content.\n"
        result = ContentSelector.select(
            content, ["section:Child"], file_path="doc.md"
        )
        assert "### Child" in result
        assert "Child content." in result
        assert "Sibling" not in result

    def test_section_ends_at_higher_level(self):
        """Section ends when a higher-level heading is encountered."""
        content = "## Section\n\nContent.\n\n# Top Level\n\nTop content.\n"
        result = ContentSelector.select(
            content, ["section:Section"], file_path="doc.md"
        )
        assert "## Section" in result
        assert "Content." in result
        assert "Top Level" not in result


# ==============================================================================
# Tests: Regex Pattern Selector
# ==============================================================================

class TestPatternSelectors:
    """Tests for pattern: selector."""

    def test_match_lines(self, sample_text):
        """Match lines containing a pattern."""
        result = ContentSelector.select(sample_text, ["pattern:/line[13]/"])
        assert "line1" in result
        assert "line3" in result
        assert "line2" not in result

    def test_no_matches(self, sample_text):
        """No matching lines raises SelectorError."""
        with pytest.raises(SelectorError, match="No lines matched"):
            ContentSelector.select(sample_text, ["pattern:/xyz/"])

    def test_invalid_regex(self, sample_text):
        """Invalid regex raises SelectorError."""
        with pytest.raises(SelectorError, match="Invalid regex"):
            ContentSelector.select(sample_text, ["pattern:/[invalid/"])

    def test_empty_pattern(self, sample_text):
        """Empty pattern raises SelectorError."""
        with pytest.raises(SelectorError, match="Empty regex"):
            ContentSelector.select(sample_text, ["pattern://"])

    def test_pattern_without_slashes(self, sample_text):
        """Pattern without surrounding slashes still works."""
        result = ContentSelector.select(sample_text, ["pattern:line5"])
        assert result == "line5"

    def test_pattern_matches_all(self, sample_text):
        """Pattern matching all lines returns all content."""
        result = ContentSelector.select(sample_text, ["pattern:/line/"])
        assert "line1" in result
        assert "line5" in result


# ==============================================================================
# Tests: JSON Path Selector
# ==============================================================================

class TestJsonPathSelectors:
    """Tests for path: selector on JSON files."""

    def test_top_level_key(self, sample_json):
        """Extract a top-level key."""
        result = ContentSelector.select(
            sample_json, ["path:name"], file_path="config.json"
        )
        assert json.loads(result) == "test"

    def test_nested_key(self, sample_json):
        """Extract a nested key via dot notation."""
        result = ContentSelector.select(
            sample_json, ["path:dependencies.foo"], file_path="config.json"
        )
        assert json.loads(result) == "^1.0"

    def test_array_index(self, sample_json):
        """Extract an array element by index."""
        result = ContentSelector.select(
            sample_json, ["path:items[0]"], file_path="config.json"
        )
        parsed = json.loads(result)
        assert parsed["id"] == 1
        assert parsed["label"] == "first"

    def test_array_index_dot_path(self, sample_json):
        """Extract a field from an array element."""
        result = ContentSelector.select(
            sample_json, ["path:items[1].label"], file_path="config.json"
        )
        assert json.loads(result) == "second"

    def test_missing_key(self, sample_json):
        """Missing key raises SelectorError."""
        with pytest.raises(SelectorError, match="not found"):
            ContentSelector.select(
                sample_json, ["path:nonexistent"], file_path="config.json"
            )

    def test_path_on_non_json_file(self, sample_json):
        """Path selector on non-JSON/YAML file raises SelectorError."""
        with pytest.raises(SelectorError):
            ContentSelector.select(
                sample_json, ["path:name"], file_path="test.py"
            )

    def test_invalid_json(self):
        """Invalid JSON raises SelectorError."""
        with pytest.raises(SelectorError, match="Failed to parse"):
            ContentSelector.select(
                "{invalid json", ["path:key"], file_path="bad.json"
            )

    def test_array_index_out_of_range(self, sample_json):
        """Array index out of range raises SelectorError."""
        with pytest.raises(SelectorError, match="out of range"):
            ContentSelector.select(
                sample_json, ["path:items[99]"], file_path="config.json"
            )

    def test_extract_object(self, sample_json):
        """Extract an entire nested object."""
        result = ContentSelector.select(
            sample_json, ["path:dependencies"], file_path="config.json"
        )
        parsed = json.loads(result)
        assert parsed == {"foo": "^1.0", "bar": "^2.0"}

    def test_deeply_nested_path(self):
        """Deeply nested path traversal works."""
        data = {"a": {"b": {"c": {"d": "deep"}}}}
        content = json.dumps(data)
        result = ContentSelector.select(
            content, ["path:a.b.c.d"], file_path="test.json"
        )
        assert json.loads(result) == "deep"

    def test_array_at_root(self):
        """Array at root level with index access."""
        content = json.dumps([{"name": "first"}, {"name": "second"}])
        result = ContentSelector.select(
            content, ["path:[0].name"], file_path="test.json"
        )
        assert json.loads(result) == "first"

    def test_empty_path(self):
        """Empty path raises SelectorError."""
        content = json.dumps({"key": "value"})
        with pytest.raises(SelectorError):
            ContentSelector.select(
                content, ["path:"], file_path="test.json"
            )

    def test_type_mismatch_array_on_object(self):
        """Array index on non-array raises SelectorError."""
        content = json.dumps({"key": "value"})
        with pytest.raises(SelectorError, match="Expected array"):
            ContentSelector.select(
                content, ["path:key[0]"], file_path="test.json"
            )

    def test_type_mismatch_key_on_array(self):
        """Key access on array raises SelectorError."""
        content = json.dumps([1, 2, 3])
        with pytest.raises(SelectorError, match="Expected object"):
            ContentSelector.select(
                content, ["path:key"], file_path="test.json"
            )

    def test_multiple_paths(self, sample_json):
        """Multiple path selectors return concatenated results."""
        result = ContentSelector.select(
            sample_json, ["path:name", "path:version"], file_path="config.json"
        )
        assert "test" in result
        assert "1.0" in result


# ==============================================================================
# Tests: YAML Path Selector
# ==============================================================================

class TestYamlPathSelectors:
    """Tests for path: selector on YAML files."""

    @pytest.fixture
    def sample_yaml(self):
        try:
            import yaml  # noqa: F401
            return "name: test\nversion: '1.0'\nnested:\n  key: value\nitems:\n  - first\n  - second\n"
        except ImportError:
            pytest.skip("PyYAML not installed")

    def test_yaml_top_level_key(self, sample_yaml):
        """Extract a top-level key from YAML."""
        result = ContentSelector.select(
            sample_yaml, ["path:name"], file_path="config.yaml"
        )
        assert "test" in result

    def test_yaml_nested_key(self, sample_yaml):
        """Extract a nested key from YAML."""
        result = ContentSelector.select(
            sample_yaml, ["path:nested.key"], file_path="config.yml"
        )
        assert "value" in result

    def test_yaml_array_index(self, sample_yaml):
        """Extract an array element from YAML."""
        result = ContentSelector.select(
            sample_yaml, ["path:items[0]"], file_path="config.yaml"
        )
        assert "first" in result

    def test_yaml_missing_key(self, sample_yaml):
        """Missing key in YAML raises SelectorError."""
        with pytest.raises(SelectorError, match="not found"):
            ContentSelector.select(
                sample_yaml, ["path:missing"], file_path="config.yaml"
            )


# ==============================================================================
# Tests: Interface Mode
# ==============================================================================

class TestInterfaceMode:
    """Tests for mode='interface'."""

    def test_full_interface_no_selectors(self, sample_python):
        """Interface mode with no selectors produces interface for whole file."""
        result = ContentSelector.select(
            sample_python, [], file_path="test.py", mode="interface"
        )
        assert "def hello(name: str) -> str:" in result
        assert "def goodbye(name: str) -> str:" in result
        assert "class MyClass:" in result
        assert "..." in result
        assert '"""Say hello."""' in result

    def test_interface_excludes_private(self, sample_python):
        """Interface mode excludes private methods (except __init__)."""
        result = ContentSelector.select(
            sample_python, [], file_path="test.py", mode="interface"
        )
        assert "__init__" in result
        assert "_private_method" not in result

    def test_interface_includes_imports(self, sample_python):
        """Interface mode includes import statements."""
        result = ContentSelector.select(
            sample_python, [], file_path="test.py", mode="interface"
        )
        assert "import os" in result

    def test_interface_includes_constants(self, sample_python):
        """Interface mode includes module-level constants."""
        result = ContentSelector.select(
            sample_python, [], file_path="test.py", mode="interface"
        )
        assert "CONSTANT = 42" in result

    def test_interface_removes_bodies(self, sample_python):
        """Interface mode replaces function bodies with ellipsis."""
        result = ContentSelector.select(
            sample_python, [], file_path="test.py", mode="interface"
        )
        # Body code should not appear
        assert 'return f"Hello, {name}!"' not in result
        assert 'return f"Goodbye, {name}!"' not in result

    def test_interface_with_syntax_error(self):
        """Interface mode with invalid Python raises SelectorError."""
        with pytest.raises(SelectorError, match="parse error"):
            ContentSelector.select(
                "def broken(:\n  pass", [], file_path="test.py", mode="interface"
            )

    def test_interface_with_def_selector(self, sample_python):
        """Interface mode with def selector produces interface for that function only."""
        result = ContentSelector.select(
            sample_python, ["def:hello"], file_path="test.py", mode="interface"
        )
        assert "def hello" in result
        assert "..." in result
        assert "class MyClass" not in result

    def test_interface_with_class_selector(self, sample_python):
        """Interface mode with class selector produces interface for that class."""
        result = ContentSelector.select(
            sample_python, ["class:MyClass"], file_path="test.py", mode="interface"
        )
        assert "class MyClass:" in result
        assert "..." in result


# ==============================================================================
# Tests: Multiple / Mixed Selectors
# ==============================================================================

class TestMultipleSelectors:
    """Tests for combining multiple selectors."""

    def test_multiple_line_selectors(self, sample_text):
        """Multiple line selectors produce union of lines."""
        result = ContentSelector.select(
            sample_text, ["lines:1", "lines:5"]
        )
        assert "line1" in result
        assert "line5" in result

    def test_overlapping_spans_merged(self, sample_text):
        """Overlapping line ranges are merged correctly."""
        result = ContentSelector.select(
            sample_text, ["lines:1-3", "lines:2-4"]
        )
        lines = result.split("\n")
        assert len(lines) == 4  # lines 1-4 merged
        assert lines[0] == "line1"
        assert lines[3] == "line4"

    def test_comma_separated_string(self, sample_text):
        """Selectors can be passed as a comma-separated string."""
        result = ContentSelector.select(
            sample_text, "lines:1, lines:5"
        )
        assert "line1" in result
        assert "line5" in result

    def test_multiple_def_selectors(self, sample_python):
        """Multiple def selectors extract multiple functions."""
        result = ContentSelector.select(
            sample_python, ["def:hello", "def:goodbye"], file_path="test.py"
        )
        assert "def hello" in result
        assert "def goodbye" in result

    def test_lines_and_pattern(self, sample_text):
        """Combine line and pattern selectors."""
        result = ContentSelector.select(
            sample_text, ["lines:1", "pattern:/line5/"]
        )
        assert "line1" in result
        assert "line5" in result


# ==============================================================================
# Tests: Edge Cases & Error Handling
# ==============================================================================

class TestEdgeCases:
    """Tests for edge cases and error handling."""

    def test_empty_content_with_no_selectors(self):
        """Empty content with no selectors returns empty content."""
        result = ContentSelector.select("", [])
        assert result == ""

    def test_no_selectors_returns_full_content(self, sample_text):
        """No selectors returns the full content."""
        result = ContentSelector.select(sample_text, [])
        assert result == sample_text

    def test_malformed_selector(self, sample_text):
        """Malformed selector raises SelectorError."""
        with pytest.raises(SelectorError, match="Malformed"):
            ContentSelector.select(sample_text, ["invalid_selector"])

    def test_unknown_selector_kind(self, sample_text):
        """Unknown selector kind raises SelectorError (caught by regex)."""
        with pytest.raises(SelectorError, match="Malformed"):
            ContentSelector.select(sample_text, ["unknown:value"])

    def test_empty_selector_string(self, sample_text):
        """Empty string selector is ignored, returns full content."""
        result = ContentSelector.select(sample_text, [""])
        assert result == sample_text

    def test_selectors_as_empty_list(self, sample_text):
        """Empty list of selectors returns full content."""
        result = ContentSelector.select(sample_text, [])
        assert result == sample_text

    def test_python_syntax_error_with_def_selector(self):
        """Invalid Python with def selector raises SelectorError."""
        with pytest.raises(SelectorError, match="parse error"):
            ContentSelector.select(
                "def broken(:\n  pass", ["def:broken"], file_path="test.py"
            )

    def test_blank_lines_in_range(self):
        """Blank lines within a range are preserved."""
        content = "line1\n\nline3\n\nline5"
        result = ContentSelector.select(content, ["lines:1-5"])
        assert result == content


# ==============================================================================
# Tests: SelectorError exception
# ==============================================================================

class TestSelectorError:
    """Tests for the SelectorError exception."""

    def test_selector_error_is_exception(self):
        """SelectorError is a proper Exception subclass."""
        assert issubclass(SelectorError, Exception)

    def test_selector_error_message(self):
        """SelectorError carries the error message."""
        err = SelectorError("test message")
        assert str(err) == "test message"


# ==============================================================================
# Tests: File type detection via file_path
# ==============================================================================

class TestFileTypeDetection:
    """Tests that file_path correctly determines selector behavior."""

    def test_py_extension(self, sample_python):
        """'.py' file allows def/class selectors."""
        result = ContentSelector.select(
            sample_python, ["def:hello"], file_path="module.py"
        )
        assert "def hello" in result

    def test_md_extension(self, sample_markdown):
        """'.md' file allows section selectors."""
        result = ContentSelector.select(
            sample_markdown, ["section:Details"], file_path="readme.md"
        )
        assert "Details" in result

    def test_markdown_extension(self, sample_markdown):
        """'.markdown' file allows section selectors."""
        result = ContentSelector.select(
            sample_markdown, ["section:Details"], file_path="readme.markdown"
        )
        assert "Details" in result

    def test_json_extension(self, sample_json):
        """'.json' file allows path selectors."""
        result = ContentSelector.select(
            sample_json, ["path:name"], file_path="config.json"
        )
        assert json.loads(result) == "test"

    def test_ast_selector_on_non_python(self, sample_markdown):
        """AST selector on non-Python file raises SelectorError."""
        with pytest.raises(SelectorError, match="AST selectors require a .py file"):
            ContentSelector.select("content", "def:foo", file_path="test.txt")

    def test_section_selector_on_non_markdown(self):
        """Section selector on non-Markdown file raises SelectorError."""
        with pytest.raises(SelectorError, match="Section selector requires a .md file"):
            ContentSelector.select("content", "section:Foo", file_path="test.txt")


# ==============================================================================
# Tests: Content preservation
# ==============================================================================

class TestContentPreservation:
    """Tests that selected content preserves original formatting."""

    def test_indentation_preserved(self, sample_python):
        """Indentation is preserved in extracted content."""
        result = ContentSelector.select(
            sample_python, ["class:MyClass.__init__"], file_path="test.py"
        )
        assert "        self.value = value" in result


if __name__ == "__main__":
    pytest.main([__file__])
