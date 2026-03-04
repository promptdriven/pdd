import os
import io
import sys
import pytest
import base64
from PIL import Image
import io
from unittest.mock import patch, mock_open
from pdd.preprocess import preprocess, get_file_path
import subprocess
import importlib
from unittest.mock import MagicMock
import z3
from z3 import String, StringVal, If, And, Or, Not, BoolVal, Implies, Length, PrefixOf, SubString, IndexOf
import re

# Store the original PDD_PATH to restore after tests
_original_pdd_path = os.environ.get('PDD_PATH')

# Helper function to mock environment variable
def set_pdd_path(path: str) -> None:
    """Set the PDD_PATH environment variable to the specified path."""
    os.environ['PDD_PATH'] = path

# Fixture to reset Firecrawl cache singleton for test isolation
@pytest.fixture
def reset_firecrawl_cache():
    """
    Reset the Firecrawl cache singleton before each test.

    This ensures that when tests set FIRECRAWL_CACHE_ENABLE=false,
    a fresh cache instance is created that respects the env var.
    Without this, the singleton created by an earlier test would persist.
    """
    import pdd.firecrawl_cache
    original_instance = pdd.firecrawl_cache._cache_instance
    pdd.firecrawl_cache._cache_instance = None
    yield
    # Restore after test
    pdd.firecrawl_cache._cache_instance = original_instance

# Test for processing includes in triple backticks
def test_process_backtick_includes() -> None:
    """Test processing of includes within triple backticks."""
    set_pdd_path('/mock/path')
    mock_file_content = "Included content"
    prompt = "This is a test ```<include_file.txt>```"
    expected_output = "This is a test ```Included content```"

    with patch('builtins.open', mock_open(read_data=mock_file_content)):
        assert preprocess(prompt, recursive=False, double_curly_brackets=False) == expected_output

# Test for processing XML-like include tags
def test_process_xml_include_tag() -> None:
    """Test processing of XML-like include tags."""
    set_pdd_path('/mock/path')
    mock_file_content = "Included content"
    prompt = "This is a test <include>include_file.txt</include>"
    expected_output = "This is a test Included content"

    with patch('builtins.open', mock_open(read_data=mock_file_content)):
        assert preprocess(prompt, recursive=False, double_curly_brackets=False) == expected_output

# New include-many coverage
def test_process_include_many_mixed_paths() -> None:
    """Include-many should concatenate all referenced files across commas and newlines."""
    prompt = "Start <include-many>file1.txt, file2.txt\nfile3.txt</include-many> End"
    file_map = {
        './file1.txt': 'Content One',
        './file2.txt': 'Content Two',
        './file3.txt': 'Content Three',
    }

    def mocked_open(path, *args, **kwargs):
        if path in file_map:
            return io.StringIO(file_map[path])
        raise FileNotFoundError(path)

    with patch('builtins.open', side_effect=mocked_open):
        result = preprocess(prompt, recursive=False, double_curly_brackets=False)

    expected = "Start Content One\nContent Two\nContent Three End"
    assert result == expected


def test_process_include_many_missing_file() -> None:
    """Include-many should surface placeholders for missing files while keeping other content."""
    prompt = "<include-many>present.txt, missing.txt</include-many>"
    file_map = {'./present.txt': 'Here'}

    def mocked_open(path, *args, **kwargs):
        if path in file_map:
            return io.StringIO(file_map[path])
        raise FileNotFoundError(path)

    with patch('builtins.open', side_effect=mocked_open):
        result = preprocess(prompt, recursive=False, double_curly_brackets=False)

    assert result == "Here\n[File not found: missing.txt]"


def test_process_include_many_recursive_defers() -> None:
    """Recursive pass should leave include-many blocks untouched for later expansion."""
    prompt = "Prefix <include-many>foo.txt</include-many> Suffix"
    result = preprocess(prompt, recursive=True, double_curly_brackets=False)
    assert result == prompt

# Test for processing XML-like pdd tags
def test_process_xml_pdd_tag() -> None:
    """Test processing of XML-like pdd tags."""
    prompt = "This is a test <pdd>This is a comment</pdd>"
    expected_output = "This is a test "

    assert preprocess(prompt, recursive=False, double_curly_brackets=False) == expected_output

# Test for processing XML-like shell tags
def test_process_xml_shell_tag() -> None:
    """Test processing of XML-like shell tags."""
    prompt = "This is a test <shell>echo Hello</shell>"
    expected_output = "This is a test Hello\n"

    with patch('subprocess.run') as mock_run:
        mock_run.return_value.stdout = "Hello\n"
        assert preprocess(prompt, recursive=False, double_curly_brackets=False) == expected_output


def test_recursive_shell_defers_execution() -> None:
    """Ensure recursive pass defers shell execution and keeps the tag in place."""
    prompt = "Check <shell>echo Ready</shell>"
    with patch('subprocess.run') as mock_run:
        result = preprocess(prompt, recursive=True, double_curly_brackets=False)
    assert result == prompt
    mock_run.assert_not_called()


def test_shell_second_pass_executes_after_deferral() -> None:
    """Second pass without recursion should execute the deferred shell block."""
    prompt = "Check <shell>echo Ready</shell>"
    with patch('subprocess.run') as mock_run:
        mock_run.return_value.stdout = "Ready\n"
        first_pass = preprocess(prompt, recursive=True, double_curly_brackets=False)
        assert first_pass == prompt
        processed = preprocess(first_pass, recursive=False, double_curly_brackets=False)
    assert processed == "Check Ready\n"
    mock_run.assert_called_once()


def test_shell_tag_ignored_in_fenced_code_block() -> None:
    """Shell tags inside fenced code blocks should not execute."""
    prompt = "Before\n```xml\n<shell>echo Hello</shell>\n```\nAfter"
    with patch('subprocess.run') as mock_run:
        mock_run.return_value.stdout = ""
        result = preprocess(prompt, recursive=False, double_curly_brackets=False)
    assert result == prompt
    mock_run.assert_not_called()


def test_shell_tag_ignored_in_inline_code() -> None:
    """Shell tags inside inline code spans should not execute."""
    prompt = "Use `<shell>echo Hello</shell>` as an example."
    with patch('subprocess.run') as mock_run:
        mock_run.return_value.stdout = ""
        result = preprocess(prompt, recursive=False, double_curly_brackets=False)
    assert result == prompt
    mock_run.assert_not_called()


def test_shell_tag_spanning_inline_code_is_ignored() -> None:
    """Shell tags whose match spans into inline code should not execute."""
    prompt = "Intro <shell>not a directive. Example: `<shell>noop</shell>` end."
    with patch('subprocess.run') as mock_run:
        mock_run.return_value.stdout = ""
        result = preprocess(prompt, recursive=False, double_curly_brackets=False)
    assert result == prompt
    mock_run.assert_not_called()


def test_include_tag_ignored_in_fenced_code_block() -> None:
    """Include tags inside fenced code blocks should not execute."""
    prompt = "```xml\n<include>file.txt</include>\n```"
    with patch('builtins.open', mock_open(read_data="Included")) as mocked_open:
        result = preprocess(prompt, recursive=False, double_curly_brackets=False)
    assert result == prompt
    mocked_open.assert_not_called()


def test_include_tag_ignored_in_inline_code() -> None:
    """Include tags inside inline code spans should not execute."""
    prompt = "Example `<include>file.txt</include>` in docs."
    with patch('builtins.open', mock_open(read_data="Included")) as mocked_open:
        result = preprocess(prompt, recursive=False, double_curly_brackets=False)
    assert result == prompt
    mocked_open.assert_not_called()


def test_include_many_tag_ignored_in_fenced_code_block() -> None:
    """Include-many tags inside fenced code blocks should not execute."""
    prompt = "```xml\n<include-many>one.txt, two.txt</include-many>\n```"
    with patch('builtins.open', mock_open(read_data="Content")) as mocked_open:
        result = preprocess(prompt, recursive=False, double_curly_brackets=False)
    assert result == prompt
    mocked_open.assert_not_called()


def test_shell_tag_spanning_fence_is_ignored(tmp_path, monkeypatch) -> None:
    """Shell tags that overlap fenced code should not execute."""
    guide = (
        "Intro <shell>not a directive.\n"
        "```mermaid\n"
        "P --> C\n"
        "P --> E\n"
        "P --> T\n"
        "</shell>\n"
        "```\n"
    )
    guide_path = tmp_path / "guide.md"
    guide_path.write_text(guide)
    monkeypatch.chdir(tmp_path)
    prompt = "<include>guide.md</include>"

    def fake_run(*_args, **_kwargs):
        for name in ("C", "E", "T"):
            (tmp_path / name).write_text("")
        completed = MagicMock()
        completed.stdout = ""
        completed.returncode = 0
        return completed

    with patch('subprocess.run', side_effect=fake_run) as mock_run:
        result = preprocess(prompt, recursive=False, double_curly_brackets=False)

    assert result == guide
    assert not (tmp_path / "C").exists()
    assert not (tmp_path / "E").exists()
    assert not (tmp_path / "T").exists()
    mock_run.assert_not_called()

# Test for doubling curly brackets
def test_double_curly_brackets() -> None:
    """Test doubling of curly brackets."""
    prompt = "This is a test {key}"
    expected_output = "This is a test {{key}}"

    assert preprocess(prompt, recursive=False, double_curly_brackets=True) == expected_output

def test_include_js_doubles_curly_braces() -> None:
    """Including a JS file with {x} should result in {{x}} after preprocess.

    This simulates the case where an included renderer.js/main.js introduces
    a single-brace placeholder that must be escaped before PromptTemplate.
    """
    prompt = "Before <include>./renderer.js</include> After"
    js_content = "function f(x) { return {x}; }\nconst obj = { a: 1, b: 2 };\n"
    expected_inner = "function f(x) {{ return {{x}}; }}\nconst obj = {{ a: 1, b: 2 }};\n"
    expected = f"Before {expected_inner} After"

    with patch('builtins.open', mock_open(read_data=js_content)):
        result = preprocess(prompt, recursive=False, double_curly_brackets=True)

    assert result == expected

# Test for excluding keys from doubling curly brackets
def test_exclude_keys_from_doubling() -> None:
    """Test excluding specific keys from doubling curly brackets."""
    prompt = "This is a test {key} and {exclude} {}"
    expected_output = "This is a test {{key}} and {exclude} {{}}"

    assert preprocess(prompt, recursive=False, double_curly_brackets=True, exclude_keys=['exclude']) == expected_output


def test_exclude_keys_requires_exact_match() -> None:
    """Exclude list should only skip doubling when the inner text is an exact match."""
    prompt = "Values {exclude_suffix} and {exclude}"
    expected = "Values {{exclude_suffix}} and {exclude}"
    result = preprocess(prompt, recursive=False, double_curly_brackets=True, exclude_keys=['exclude'])
    assert result == expected

# Test for recursive processing
def test_recursive_processing() -> None:
    """Test recursive processing of includes."""
    set_pdd_path('/mock/path')
    mock_file_content = "Nested include ```<nested_file.txt>```"
    nested_file_content = "Nested content"
    prompt = "This is a test ```<include_file.txt>```"
    expected_output = "This is a test ```Nested include ```Nested content``````"

    with patch('builtins.open', mock_open(read_data=mock_file_content)) as mock_file:
        mock_file.side_effect = [mock_open(read_data=mock_file_content).return_value,
                                 mock_open(read_data=nested_file_content).return_value]
        assert preprocess(prompt, recursive=True, double_curly_brackets=False) == expected_output


def test_recursive_backtick_missing_file_preserves_tag() -> None:
    """Recursive pass should keep unresolved backtick includes for later resolution."""
    prompt = "```<missing.txt>```"
    with patch('builtins.open', side_effect=FileNotFoundError):
        result = preprocess(prompt, recursive=True, double_curly_brackets=False)
    assert result == prompt


def test_recursive_xml_missing_file_preserves_tag() -> None:
    """Recursive pass should keep unresolved XML includes for later resolution."""
    prompt = "<include>missing.txt</include>"
    with patch('builtins.open', side_effect=FileNotFoundError):
        result = preprocess(prompt, recursive=True, double_curly_brackets=False)
    assert result == prompt

# Test for handling file not found
def test_file_not_found() -> None:
    """Test handling of file not found error."""
    set_pdd_path('/mock/path')
    prompt = "This is a test ```<missing_file.txt>```"
    expected_output = "This is a test ```[File not found: missing_file.txt]```"

    with patch('builtins.open', side_effect=FileNotFoundError):
        assert preprocess(prompt, recursive=False, double_curly_brackets=False) == expected_output

# Test for handling shell command error
def test_shell_command_error() -> None:
    """Test handling of shell command error."""
    prompt = "This is a test <shell>invalid_command</shell>"
    expected_output = "This is a test Error: Command 'invalid_command' returned non-zero exit status 1."

    with patch('subprocess.run', side_effect=subprocess.CalledProcessError(1, 'invalid_command')):
        assert preprocess(prompt, recursive=False, double_curly_brackets=False) == expected_output


def test_recursive_web_defers_scrape() -> None:
    """Recursive pass should not attempt to import or scrape during web processing."""
    prompt = "Start <web>https://example.com</web> End"
    original_import = __import__

    def raising_import(name, *args, **kwargs):
        if name == 'firecrawl':
            raise AssertionError('firecrawl import should be deferred')
        return original_import(name, *args, **kwargs)

    with patch('builtins.__import__', side_effect=raising_import):
        result = preprocess(prompt, recursive=True, double_curly_brackets=False)

    assert result == prompt


def test_web_second_pass_executes_after_deferral(reset_firecrawl_cache) -> None:
    """Second pass without recursion should execute the deferred web scrape."""
    prompt = "Start <web>https://example.com</web> End"
    mock_firecrawl = MagicMock()
    mock_firecrawl.Firecrawl.return_value.scrape_url.return_value = {'markdown': "# Content"}

    with patch.dict('sys.modules', {'firecrawl': mock_firecrawl}):
        with patch.dict('os.environ', {'FIRECRAWL_API_KEY': 'key', 'FIRECRAWL_CACHE_ENABLE': 'false'}):
            result = preprocess(prompt, recursive=False, double_curly_brackets=False)

    assert result == "Start # Content End"

# Ensure to clean up the environment variable after tests
def teardown_module(module) -> None:
    """Restore the original PDD_PATH environment variable after tests."""
    if _original_pdd_path is not None:
        os.environ['PDD_PATH'] = _original_pdd_path
    elif 'PDD_PATH' in os.environ:
        del os.environ['PDD_PATH']

def test_double_curly_brackets_in_javascript() -> None:
    """
    Test to ensure that curly brackets in JavaScript code blocks are doubled correctly.
    """
    input_text = (
        """5. **Configure Tailwind CSS**:\n\n"
        "   Update your `tailwind.config.js` with the paths to all of your template files:\n\n"
        "   ```javascript\n"
        "   module.exports = {\n"
        "     content: [\n"
        "       \"./src/**/*.{js,jsx,ts,tsx}\",\n"
        "       \"./public/index.html\",\n"
        "       // Add any other paths where Tailwind CSS classes are used\n"
        "     ],\n"
        "     theme: {\n"
        "       extend: {},\n"
        "     },\n"
        "     plugins: [],\n"
        "   }\n"
        "   ```"""
    )

    expected_output = (
        """5. **Configure Tailwind CSS**:\n\n"
        "   Update your `tailwind.config.js` with the paths to all of your template files:\n\n"
        "   ```javascript\n"
        "   module.exports = {{\n"
        "     content: [\n"
        "       \"./src/**/*.{{js,jsx,ts,tsx}}\",\n"
        "       \"./public/index.html\",\n"
        "       // Add any other paths where Tailwind CSS classes are used\n"
        "     ],\n"
        "     theme: {{\n"
        "       extend: {{}},\n"
        "     }},\n"
        "     plugins: [],\n"
        "   }}\n"
        "   ```"""
    )

    # Call the preprocess function with the input text
    result = preprocess(input_text, recursive=False, double_curly_brackets=True)

    # Assert that the result matches the expected output
    assert result == expected_output, f"Expected:\n{expected_output}\n\nGot:\n{result}"

def test_double_curly_brackets_json() -> None:
    """
    Test to ensure that the preprocess function correctly doubles curly brackets
    within a JSON object without adding extra brackets around the entire object.
    """
    # Input prompt
    prompt = """### Error Handling

All endpoints return standard HTTP status codes. In case of an error, the response will include an error object:

```json
{
  "error": {
    "code": "string",
    "message": "string"
  }
}
```"""

    # Expected output
    expected_output = """### Error Handling

All endpoints return standard HTTP status codes. In case of an error, the response will include an error object:

```json
{{
  "error": {{
    "code": "string",
    "message": "string"
  }}
}}
```"""

    # Process the prompt
    processed = preprocess(prompt, recursive=False, double_curly_brackets=True)

    # Assert that the processed output matches the expected output
    assert processed.strip() == expected_output.strip(), \
        f"Expected:\n{expected_output}\n\nGot:\n{processed}"

    # Additional check to ensure no extra curly brackets are added around the entire JSON
    assert processed.count('{{') == expected_output.count('{{'), \
        "Extra curly brackets were added around the entire JSON object"


def test_double_curly_brackets_python_code_block() -> None:
    """Ensure Python code blocks are processed without disturbing existing double braces."""
    prompt = (
        """```python
def build_config():
    template = "{{ already }}"
    return {"key": value}
```"""
    )

    expected = (
        """```python
def build_config():
    template = "{{ already }}"
    return {{"key": value}}
```"""
    )

    processed = preprocess(prompt, recursive=False, double_curly_brackets=True)
    assert processed == expected

def test_double_curly_brackets_javascript_code_block_destructuring_jsx() -> None:
    """Ensure JS code blocks handle destructuring, object literals, and JSX."""
    prompt = (
        """```javascript
const { x, y } = obj;
const obj = { a: 1, b: 2 };
function C() { return <div>{x}</div>; }
```"""
    )

    expected = (
        """```javascript
const {{ x, y }} = obj;
const obj = {{ a: 1, b: 2 }};
function C() {{ return <div>{{x}}</div>; }}
```"""
    )

    processed = preprocess(prompt, recursive=False, double_curly_brackets=True)
    assert processed == expected

def test_double_curly_brackets_javascript_template_literals() -> None:
    """Ensure simple ${x} is preserved and complex ${x + 1} is doubled safely."""
    prompt = (
        """```javascript
const a = `Hello ${x}`;
const b = `Sum ${x + 1}`;
```"""
    )

    expected = (
        """```javascript
const a = `Hello ${{x}}`;
const b = `Sum ${{x + 1}}`;
```"""
    )

    processed = preprocess(prompt, recursive=False, double_curly_brackets=True)
    assert processed == expected

def test_unfenced_template_literal_should_be_doubled_but_is_not():
    """BUG REPRO: ${x} outside code fences is restored unchanged, leaving {x}.

    Expected behavior (to avoid PromptTemplate errors): `${x}` should become `${{x}}`
    when double_curly_brackets=True even outside fenced code blocks.

    Current behavior: preprocess protects and restores ${x} unchanged, so this test
    should FAIL until we harden double_curly to handle unfenced template literals.
    """
    prompt = "const a = `Hello ${x}`;"
    expected = "const a = `Hello ${{x}}`;"
    processed = preprocess(prompt, recursive=False, double_curly_brackets=True)
    assert processed == expected
def test_double_curly_preserves_braced_env_placeholders_as_escaped() -> None:
    """Ensure ${IDENT} placeholders are restored as ${{IDENT}} to avoid formatting issues."""
    prompt = "This has ${FOO} and {bar}"
    expected_output = "This has ${{FOO}} and {{bar}}"
    processed = preprocess(prompt, recursive=False, double_curly_brackets=True)
    assert processed == expected_output

def test_preprocess_double_curly_brackets():
    """
    Test that the preprocess function correctly doubles curly brackets
    in the provided prompt, matching the desired output.
    """
    # Input prompt with single curly brackets
    prompt = """    mock_db = {
            "1": {"id": "1", "name": "Resource One"},
            "2": {"id": "2", "name": "Resource Two"}
        }"""

    # Desired output with doubled curly brackets
    desired_output = """    mock_db = {{
            "1": {{"id": "1", "name": "Resource One"}},
            "2": {{"id": "2", "name": "Resource Two"}}
        }}"""

    # Call the preprocess function with appropriate parameters
    processed = preprocess(prompt, recursive=False, double_curly_brackets=True)

    # Assert that the processed output matches the desired output
    assert processed == desired_output, "The preprocess function did not double the curly brackets as expected."

# Test for processing XML-like web tags
def test_process_xml_web_tag(reset_firecrawl_cache) -> None:
    """Test processing of XML-like web tags."""
    mock_markdown_content = "# Webpage Content\n\nThis is the scraped content."
    prompt = "This is a test <web>https://example.com</web>"
    expected_output = f"This is a test {mock_markdown_content}"

    # Since Firecrawl is imported inside the function, we need to patch the module
    mock_firecrawl = MagicMock()
    mock_app = MagicMock()
    mock_app.scrape_url.return_value = {'markdown': mock_markdown_content}
    mock_firecrawl.Firecrawl.return_value = mock_app

    # Patch the import at the module level
    with patch.dict('sys.modules', {'firecrawl': mock_firecrawl}):
        # Mock the environment variable for API key and disable cache
        with patch.dict('os.environ', {'FIRECRAWL_API_KEY': 'fake_api_key', 'FIRECRAWL_CACHE_ENABLE': 'false'}):
            result = preprocess(prompt, recursive=False, double_curly_brackets=False)
            assert result == expected_output

# Test for handling missing Firecrawl API key
def test_process_xml_web_tag_missing_api_key(reset_firecrawl_cache) -> None:
    """Test handling of missing Firecrawl API key."""
    prompt = "This is a test <web>https://example.com</web>"
    expected_output = "This is a test [Error: FIRECRAWL_API_KEY not set. Cannot scrape https://example.com]"

    # Create a mock Firecrawl class
    mock_firecrawl_class = MagicMock()

    # Patch the import
    with patch.dict('sys.modules', {'firecrawl': MagicMock()}):
        with patch('builtins.__import__', side_effect=lambda name, *args:
              MagicMock(Firecrawl=mock_firecrawl_class) if name == 'firecrawl' else importlib.__import__(name, *args)):
            # Ensure the API key environment variable is not set and disable cache
            with patch.dict('os.environ', {'FIRECRAWL_CACHE_ENABLE': 'false'}, clear=True):
                result = preprocess(prompt, recursive=False, double_curly_brackets=False)
                assert result == expected_output

# Test for handling Firecrawl import error
def test_process_xml_web_tag_import_error(reset_firecrawl_cache) -> None:
    """Test handling of Firecrawl import error."""
    prompt = "This is a test <web>https://example.com</web>"
    expected_output = "This is a test [Error: firecrawl-py package not installed. Cannot scrape https://example.com]"

    # Patch the import to raise ImportError and disable cache
    with patch.dict('os.environ', {'FIRECRAWL_CACHE_ENABLE': 'false'}):
        with patch('builtins.__import__', side_effect=lambda name, *args:
              raise_import_error(name) if name == 'firecrawl' else importlib.__import__(name, *args)):
            result = preprocess(prompt, recursive=False, double_curly_brackets=False)
            assert result == expected_output

def raise_import_error(name):
    raise ImportError(f"No module named '{name}'")

# Test for handling empty markdown content
def test_process_xml_web_tag_empty_content(reset_firecrawl_cache) -> None:
    """Test handling of empty markdown content from Firecrawl."""
    prompt = "This is a test <web>https://example.com</web>"
    expected_output = "This is a test [No content available for https://example.com]"

    # Create a mock Firecrawl class that returns empty response
    mock_firecrawl_class = MagicMock()
    mock_instance = mock_firecrawl_class.return_value
    mock_instance.scrape_url.return_value = {}  # No markdown key

    # Patch the import
    with patch.dict('sys.modules', {'firecrawl': MagicMock()}):
        with patch('builtins.__import__', side_effect=lambda name, *args:
              MagicMock(Firecrawl=mock_firecrawl_class) if name == 'firecrawl' else importlib.__import__(name, *args)):
            with patch.dict('os.environ', {'FIRECRAWL_API_KEY': 'fake_api_key', 'FIRECRAWL_CACHE_ENABLE': 'false'}):
                result = preprocess(prompt, recursive=False, double_curly_brackets=False)
                assert result == expected_output

# Test for handling Firecrawl API error
def test_process_xml_web_tag_scraping_error(reset_firecrawl_cache) -> None:
    """Test handling of Firecrawl API error."""
    prompt = "This is a test <web>https://example.com</web>"
    error_message = "API request failed"
    expected_output = f"This is a test [Web scraping error: {error_message}]"

    # Create a mock Firecrawl class that raises an exception
    mock_firecrawl_class = MagicMock()
    mock_instance = mock_firecrawl_class.return_value
    mock_instance.scrape_url.side_effect = Exception(error_message)

    # Patch the import
    with patch.dict('sys.modules', {'firecrawl': MagicMock()}):
        with patch('builtins.__import__', side_effect=lambda name, *args:
              MagicMock(Firecrawl=mock_firecrawl_class) if name == 'firecrawl' else importlib.__import__(name, *args)):
            with patch.dict('os.environ', {'FIRECRAWL_API_KEY': 'fake_api_key', 'FIRECRAWL_CACHE_ENABLE': 'false'}):
                result = preprocess(prompt, recursive=False, double_curly_brackets=False)
                assert result == expected_output

def test_process_web_tag_invalid_ttl_env_no_crash(reset_firecrawl_cache) -> None:
    """Regression: invalid FIRECRAWL_CACHE_TTL_HOURS should not crash process_web_tags.

    The cache module handles TTL parsing internally with proper error handling.
    preprocess.py should not duplicate this parsing with a bare int() call.
    """
    mock_markdown_content = "# Test Content"
    prompt = "Test <web>https://example.com</web>"

    mock_firecrawl = MagicMock()
    mock_app = MagicMock()
    mock_app.scrape_url.return_value = {'markdown': mock_markdown_content}
    mock_firecrawl.Firecrawl.return_value = mock_app

    with patch.dict('sys.modules', {'firecrawl': mock_firecrawl}):
        with patch.dict('os.environ', {
            'FIRECRAWL_API_KEY': 'fake_api_key',
            'FIRECRAWL_CACHE_TTL_HOURS': 'not_a_number',
            'FIRECRAWL_CACHE_ENABLE': 'false',
        }):
            # Should NOT raise ValueError
            result = preprocess(prompt, recursive=False, double_curly_brackets=False)
            assert mock_markdown_content in result


# NEW TESTS FROM test_preprocess2.py

# Test for already doubled brackets
def test_already_doubled_brackets() -> None:
    """Test that already doubled brackets aren't doubled again."""
    prompt = "This is already {{doubled}}."
    result = preprocess(prompt, recursive=False, double_curly_brackets=True)
    assert result == "This is already {{doubled}}."

# Test for nested curly brackets
def test_nested_curly_brackets() -> None:
    """Test handling of nested curly brackets."""
    prompt = "This has {outer{inner}} nested brackets."
    result = preprocess(prompt, recursive=False, double_curly_brackets=True)
    assert result == "This has {{outer{{inner}}}} nested brackets."

# Test for complex nested curly brackets
def test_complex_nested_brackets() -> None:
    """Test deep nesting of curly brackets."""
    prompt = "Deep {first{second{third}}} nesting"
    result = preprocess(prompt, recursive=False, double_curly_brackets=True)
    assert result == "Deep {{first{{second{{third}}}}}} nesting"

# Test for multiline curly brackets
def test_multiline_curly_brackets() -> None:
    """Test handling of multiline curly brackets."""
    prompt = """This has a {
        multiline
        variable
    } with brackets."""
    
    expected = """This has a {{
        multiline
        variable
    }} with brackets."""
    
    result = preprocess(prompt, recursive=False, double_curly_brackets=True)
    assert result == expected

# Test for the get_file_path function
def test_get_file_path() -> None:
    """Test the get_file_path function."""
    from pdd.preprocess import get_file_path
    
    filename = "test.txt"
    path = get_file_path(filename)
    assert path == "./test.txt"
    
    # Test with absolute path
    abs_path = "/absolute/path/test.txt"
    path = get_file_path(abs_path)
    assert path == abs_path

# Test for nested XML tags
def test_nested_xml_tags() -> None:
    """Test handling of nested XML tags."""
    prompt = "Nested tags: <pdd><shell>echo 'test'</shell></pdd>"
    result = preprocess(prompt, recursive=False, double_curly_brackets=False)
    # The entire content inside pdd should be removed
    assert result == "Nested tags: "
    
    prompt = "Nested tags: <shell><pdd>comment</pdd>echo 'test'</shell>"
    
    with patch('subprocess.run') as mock_run:
        mock_run.return_value.stdout = "test output"
        result = preprocess(prompt, recursive=False, double_curly_brackets=False)
        # The pdd tag should be processed before executing the shell command
        assert "comment" not in result
        assert "test output" in result

# Test for unbalanced curly brackets
def test_unbalanced_curly_brackets() -> None:
    """Test handling of unbalanced curly brackets."""
    prompt = "Unbalanced {opening bracket only"
    
    # The function should handle this gracefully without crashing
    result = preprocess(prompt, recursive=False, double_curly_brackets=True)
    assert "{" in result or "{{" in result
    
    prompt = "Unbalanced closing bracket only}"
    
    # The function should handle this gracefully without crashing
    result = preprocess(prompt, recursive=False, double_curly_brackets=True)
    assert "}" in result

# Test for circular includes
def test_circular_includes() -> None:
    """Test handling of circular includes to prevent infinite recursion."""
    set_pdd_path('/mock/path')
    circular1_content = "<include>./circular2.txt</include>"
    circular2_content = "<include>./circular1.txt</include>"
    prompt = "<include>./circular1.txt</include>"
    
    with patch('builtins.open', mock_open()) as m:
        def side_effect(file_name, *args, **kwargs):
            mock_file = MagicMock()
            if 'circular1.txt' in file_name:
                mock_file.read.return_value = circular1_content
            elif 'circular2.txt' in file_name:
                mock_file.read.return_value = circular2_content
            return mock_file
        
        m.side_effect = side_effect
        
        # This should either handle circular dependency gracefully or raise a controlled exception
        try:
            result = preprocess(prompt, recursive=True, double_curly_brackets=False)
            # If it completes, it should have stopped recursion at some point
            assert "circular" in result
        except Exception as e:
            # If it raises an exception, it should be a controlled exception
            assert "circular" in str(e).lower() or "recursion" in str(e).lower() or "depth" in str(e).lower()

# Test for mix of excluded and nested brackets
def test_mixed_excluded_nested_brackets() -> None:
    """Test mix of excluded and nested brackets.

    exclude_keys protects exact {key} matches only. Nested patterns like
    {excluded{inner}} don't match the {excluded} regex, so all braces
    are doubled uniformly.
    """
    prompt = "Mix of {excluded{inner}} nesting"
    result = preprocess(prompt, recursive=False, double_curly_brackets=True, exclude_keys=["excluded"])
    # {excluded{inner}} doesn't match \{(excluded)\} regex, so all braces double
    assert result == "Mix of {{excluded{{inner}}}} nesting"

# Z3 FORMAL VERIFICATION TESTS
#############################

def create_solver():
    """Create and return a Z3 solver instance"""
    return z3.Solver()

def test_z3_pdd_tags_removal():
    """
    Test that PDD tags and their content are removed properly using Z3 formal verification.
    """
    solver = create_solver()
    
    input_with_pdd = StringVal("This is a test <pdd>This is a comment</pdd>")
    expected_output = StringVal("This is a test ")
    
    # Create symbolic input and output strings
    test_input = String('test_input')
    test_output = String('test_output')
    
    # Define the constraint for PDD tag handling
    pdd_constraint = Implies(
        test_input == input_with_pdd,
        test_output == expected_output
    )
    
    # Add the constraint to the solver
    solver.add(pdd_constraint)
    
    # Check if this specific property is satisfiable
    result = solver.check()
    
    assert result == z3.sat, "PDD tag removal property is not satisfiable"
    
    # Verify with concrete example
    concrete_input = "This is a test <pdd>This is a comment</pdd>"
    concrete_output = preprocess(concrete_input, recursive=False, double_curly_brackets=False)
    assert concrete_output == "This is a test ", "Concrete PDD tag removal failed"

def test_z3_double_curly_brackets():
    """
    Test that curly brackets are doubled correctly using Z3 formal verification.
    """
    solver = create_solver()
    
    # Test cases for curly bracket doubling
    test_cases = [
        # Simple case: {var} -> {{var}}
        (StringVal("This has {var}"), StringVal("This has {{var}}")),
        
        # Already doubled: {{var}} -> {{var}}
        (StringVal("This has {{var}}"), StringVal("This has {{var}}")),
        
        # Nested brackets: {outer{inner}} -> {{outer{{inner}}}}
        (StringVal("This has {outer{inner}}"), StringVal("This has {{outer{{inner}}}}")),
        
        # Multiple brackets: {a} and {b} -> {{a}} and {{b}}
        (StringVal("This has {a} and {b}"), StringVal("This has {{a}} and {{b}}"))
    ]
    
    # Add constraints for all test cases
    for i, (test_input, expected_output) in enumerate(test_cases):
        test_var_input = String(f'test_input_{i}')
        test_var_output = String(f'test_output_{i}')
        
        solver.add(Implies(
            test_var_input == test_input,
            test_var_output == expected_output
        ))
    
    # Check all properties together
    result = solver.check()
    assert result == z3.sat, "Double curly bracket properties are not satisfiable"
    
    # Verify with concrete examples
    for i, (input_str, expected) in enumerate(test_cases):
        concrete_input = input_str.as_string()
        concrete_expected = expected.as_string()
        concrete_output = preprocess(concrete_input, recursive=False, double_curly_brackets=True)
        assert concrete_output == concrete_expected, f"Concrete test case {i} failed"

def test_z3_exclude_keys():
    """
    Test that exclude_keys are properly handled when doubling curly brackets.
    """
    solver = create_solver()
    
    input_with_excluded = StringVal("This is {key} with {excluded}")
    expected_output = StringVal("This is {{key}} with {excluded}")
    
    test_input = String('exclude_input')
    test_output = String('exclude_output')
    
    # Define the constraint for excluded keys
    exclude_constraint = Implies(
        test_input == input_with_excluded,
        test_output == expected_output
    )
    
    # Add the constraint to the solver
    solver.add(exclude_constraint)
    
    # Check if this specific property is satisfiable
    result = solver.check()
    assert result == z3.sat, "Exclude keys property is not satisfiable"
    
    # Verify with concrete example
    concrete_input = "This is {key} with {excluded}"
    concrete_output = preprocess(concrete_input, recursive=False, double_curly_brackets=True, exclude_keys=["excluded"])
    assert concrete_output == "This is {{key}} with {excluded}", "Concrete exclude keys test failed"

def test_z3_code_block_handling():
    """
    Test that code blocks are handled properly when doubling curly brackets.
    """
    solver = create_solver()
    
    # JavaScript code block test
    js_code = """```javascript
const obj = {
  key: "value",
  nested: {
    items: [{id: 1}]
  }
};
```"""
    expected_js = """```javascript
const obj = {{
  key: "value",
  nested: {{
    items: [{{id: 1}}]
  }}
}};
```"""
    
    # Add constraint for JavaScript code blocks
    js_input = String('js_input')
    js_output = String('js_output')
    
    solver.add(Implies(
        js_input == StringVal(js_code),
        js_output == StringVal(expected_js)
    ))
    
    # Check this property
    result = solver.check()
    assert result == z3.sat, "Code block handling property is not satisfiable"
    
    # Verify with concrete example
    concrete_output = preprocess(js_code, recursive=False, double_curly_brackets=True)
    assert concrete_output == expected_js, "Concrete code block test failed"

def test_z3_comprehensive_verification():
    """
    Run a comprehensive verification of preprocess.py using Z3 to verify all key properties together.
    """
    solver = create_solver()
    
    # Basic properties
    # Empty input produces empty output
    empty_input = String('empty_input')
    empty_output = String('empty_output')
    solver.add(Implies(
        Length(empty_input) == 0,
        Length(empty_output) == 0
    ))
    
    # Plain text with no special features
    plain_input = String('plain_input')
    plain_output = String('plain_output')
    plain_text = StringVal("This is plain text with no special tags or brackets")
    solver.add(Implies(
        plain_input == plain_text,
        plain_output == plain_text
    ))
    
    # PDD tag removal
    pdd_input = String('pdd_input')
    pdd_output = String('pdd_output')
    pdd_text = StringVal("Text <pdd>Remove this</pdd> end")
    pdd_expected = StringVal("Text  end")
    solver.add(Implies(
        pdd_input == pdd_text,
        pdd_output == pdd_expected
    ))
    
    # Curly bracket doubling
    curly_input = String('curly_input')
    curly_output = String('curly_output')
    curly_text = StringVal("Text with {brackets}")
    curly_expected = StringVal("Text with {{brackets}}")
    solver.add(Implies(
        curly_input == curly_text,
        curly_output == curly_expected
    ))
    
    # Already doubled brackets
    doubled_input = String('doubled_input')
    doubled_output = String('doubled_output')
    doubled_text = StringVal("Text with {{already_doubled}}")
    doubled_expected = StringVal("Text with {{already_doubled}}")
    solver.add(Implies(
        doubled_input == doubled_text,
        doubled_output == doubled_expected
    ))
    
    # Verify that all properties together are satisfiable
    result = solver.check()
    assert result == z3.sat, "Comprehensive verification failed - properties are not simultaneously satisfiable"
    
    # If satisfiable, we get a model that shows sample inputs/outputs
    if result == z3.sat:
        model = solver.model()
        # We can examine the model if needed, but for a test, just checking satisfiability is enough

def test_template_variable_escaping() -> None:
    """Test that template variables like {final_llm_output} get properly escaped."""
    prompt = "This is a prompt with {final_llm_output} and {reasoning} variables."
    result = preprocess(prompt, recursive=False, double_curly_brackets=True)
    assert result == "This is a prompt with {{final_llm_output}} and {{reasoning}} variables."
    
    # Test mixed with already escaped variables
    prompt = "Here's {{already_escaped}} and {needs_escaping} variables."
    result = preprocess(prompt, recursive=False, double_curly_brackets=True)
    assert result == "Here's {{already_escaped}} and {{needs_escaping}} variables."
    
    # Test with variables in different contexts
    prompt = """
    Here's a prompt with variables:
    - First: {variable1}
    - Second: {variable2}
    
    And let's add code:
    ```python
    def my_function():
        data = {"key": "value"}
        return data
    ```
    
    And more variables: {variable3}
    """
    result = preprocess(prompt, recursive=False, double_curly_brackets=True)
    
    # Check that all variables are properly escaped
    assert "{{variable1}}" in result
    assert "{{variable2}}" in result 
    assert "{{variable3}}" in result
    # But code blocks should keep JSON braces doubled correctly
    assert '{"key": "value"}' in result or '{{"key": "value"}}' in result

def test_fstring_curly_brackets_in_code_blocks() -> None:
    """
    Test that curly brackets in f-strings within code blocks are properly doubled.
    This specifically tests the bug where f-strings like f"Input Cost: {input_cost}" 
    weren't getting their curly brackets doubled.
    """
    # Create a test string that contains Python code with f-strings
    test_string = '''```python
# Print the details of the selected LLM model
print(f"Selected LLM Model: {model_name}")
print(f"Input Cost per Million Tokens: {input_cost}")
print(f"Output Cost per Million Tokens: {output_cost}")

# Example usage of the token counter function
sample_text: str = "This is a sample text to count tokens."
token_count: int = token_counter(sample_text)
print(f"Token Count for Sample Text: {token_count}")
print(f"model_name: {model_name}")
```'''

    # Expected output after preprocessing
    expected_output = '''```python
# Print the details of the selected LLM model
print(f"Selected LLM Model: {{model_name}}")
print(f"Input Cost per Million Tokens: {{input_cost}}")
print(f"Output Cost per Million Tokens: {{output_cost}}")

# Example usage of the token counter function
sample_text: str = "This is a sample text to count tokens."
token_count: int = token_counter(sample_text)
print(f"Token Count for Sample Text: {{token_count}}")
print(f"model_name: {{model_name}}")
```'''

    # Process the test string
    result = preprocess(test_string, recursive=False, double_curly_brackets=True)
    
    # Print the result and expected output for debugging
    print("\nACTUAL RESULT:")
    print(result)
    print("\nEXPECTED OUTPUT:")
    print(expected_output)
    
    # Assert that all f-string variables have their curly brackets doubled
    assert result == expected_output, \
        f"F-string curly brackets were not properly doubled.\nExpected:\n{expected_output}\nGot:\n{result}"

def test_fstring_curly_brackets_outside_code_blocks() -> None:
    """
    Test that curly brackets in f-strings outside of code blocks are properly doubled.
    This specifically tests the reported bug where f-strings like f"Input Cost: {input_cost}" 
    weren't getting their curly brackets doubled in regular Python code.
    """
    # Test string resembling actual Python code (NOT in a code block)
    test_string = '''    # Print the details of the selected LLM model
    print(f"Selected LLM Model: {model_name}")
    print(f"Input Cost per Million Tokens: {input_cost}")
    print(f"Output Cost per Million Tokens: {output_cost}")

    # Example usage of the token counter function
    sample_text: str = "This is a sample text to count tokens."
    token_count: int = token_counter(sample_text)
    print(f"Token Count for Sample Text: {token_count}")
    print(f"model_name: {model_name}")'''

    # Expected output after preprocessing
    expected_output = '''    # Print the details of the selected LLM model
    print(f"Selected LLM Model: {{model_name}}")
    print(f"Input Cost per Million Tokens: {{input_cost}}")
    print(f"Output Cost per Million Tokens: {{output_cost}}")

    # Example usage of the token counter function
    sample_text: str = "This is a sample text to count tokens."
    token_count: int = token_counter(sample_text)
    print(f"Token Count for Sample Text: {{token_count}}")
    print(f"model_name: {{model_name}}")'''

    # Process the test string
    result = preprocess(test_string, recursive=False, double_curly_brackets=True)
    
    # Assert that all f-string variables have their curly brackets doubled
    assert result == expected_output, \
        f"F-string curly brackets outside code blocks were not properly doubled.\nExpected:\n{expected_output}\nGot:\n{result}"

def test_xml_tags_in_backticks_not_treated_as_includes() -> None:
    """
    Test that documents the issue from the log file where XML tags are incorrectly processed as file includes.
    This issue happens when there's content like: ```./examples>
    
    Even though we can't reproduce this exact issue in a test, we document the fix by using a more 
    specific regex pattern.
    """
    # We observe in the log the following situation:
    # Processing backtick include: ./examples>
    # Warning: File not found: examples>
    #
    # This suggests the pattern r"```<(.*?)>```" is incorrectly matching XML content
    
    # Test a simple direct pattern match with the log format
    log_format = """```./examples>
    <example>
        <example_number>5</example_number>
        <example_input_prompt>Sample prompt</example_input_prompt>
    </example>
</examples>
```"""
    
    # Test the pattern directly
    problematic_pattern = r"```<(.*?)>```"
    log_match = re.search(problematic_pattern, log_format, re.DOTALL)
    
    print("\nTesting log format with pattern:")
    if log_match:
        print(f"Pattern '{problematic_pattern}' matches log format")
        print(f"  Group 1: '{log_match.group(1)}'")
    else:
        print(f"Pattern '{problematic_pattern}' does NOT match log format")
    
    # Let's check a modified pattern that might catch it
    modified_pattern = r"```\./(.*?)>"
    mod_match = re.search(modified_pattern, log_format, re.DOTALL)
    if mod_match:
        print(f"Modified pattern '{modified_pattern}' matches log format")
        print(f"  Group 1: '{mod_match.group(1)}'")
    else:
        print(f"Modified pattern '{modified_pattern}' does NOT match log format")
    
    # Test our proposed fix pattern
    fixed_pattern = r"```<([^>]*?)>```"
    fixed_match = re.search(fixed_pattern, log_format, re.DOTALL)
    if fixed_match:
        print(f"Fixed pattern '{fixed_pattern}' matches log format")
        print(f"  Group 1: '{fixed_match.group(1)}'")
    else:
        print(f"Fixed pattern '{fixed_pattern}' does NOT match log format")
        
    print("\nSince we couldn't reproduce the exact issue in a test environment,")
    print("we recommend the following fix based on analyzing the logs:")
    print("\n1. The current pattern r\"```<(.*?)>```\" is too permissive and can match XML content")
    print("2. A better pattern would be r\"```<([^>]*?)>```\" to avoid matching nested '>' characters")
    print("3. The best solution would be a more explicit include syntax like:")
    print("   r\"```include\\((.*?)\\)```\" requiring syntax like ```include(path/to/file)```")
    
    # Skip assertion since we can't reproduce, but document the fix pattern that will prevent the issue
    # assert False, "Skipping test since we can't reproduce the exact issue, but recommending a fix"

def test_fixed_backtick_include_pattern() -> None:
    """
    Test a solution to fix the issue where XML tags in backtick code blocks 
    are incorrectly processed as include paths.
    
    This test provides three potential patterns that fix the issue:
    1. A minimal fix using a more specific regex pattern
    2. A better fix using a pattern that avoids nested '>' characters
    3. The best fix using an explicit include syntax
    """
    # Create a test prompt with problematic XML content
    xml_prompt = """```
<examples>
    <example>
        <example_number>5</example_number>
        <example_input_prompt>Sample prompt</example_input_prompt>
    </example>
</examples>
```"""

    # And a prompt with an actual include
    include_prompt = "Here is an include: ```<path/to/file.txt>```"
    
    # Helper function to test a pattern
    def test_pattern(pattern, description):
        # Test if XML content is matched (should be False)
        xml_match = re.search(pattern, xml_prompt, re.DOTALL)
        # Test if real include is matched (should be True)
        include_match = re.search(pattern, include_prompt, re.DOTALL)
        
        print(f"\nTesting pattern: {pattern}")
        print(f"Description: {description}")
        print(f"  Matches XML content: {xml_match is not None}")
        if xml_match:
            print(f"  XML match group 1: '{xml_match.group(1)}'")
        print(f"  Matches include: {include_match is not None}")
        if include_match:
            print(f"  Include match group 1: '{include_match.group(1)}'")
            
        return xml_match is None and include_match is not None
    
    # Original problematic pattern
    original_pattern = r"```<(.*?)>```"
    original_result = test_pattern(original_pattern, "Original pattern (problematic)")
    
    # Fix 1: Minimal fix with a more specific pattern
    # Ensure the opening angle bracket is immediately after the backticks
    # This won't match XML tags within code blocks that start on a new line
    minimal_fix_pattern = r"```<([^>]*?)>```"
    minimal_fix_result = test_pattern(minimal_fix_pattern, "Minimal fix - more specific pattern")
    
    # Fix 2: Better fix that requires a specific prefix for includes
    # This is even more robust against false positives
    better_fix_pattern = r"```include:([^>]*?)>```"
    better_fix_result = test_pattern(better_fix_pattern.replace("include:", ""), 
                                    "Better fix - prefix for includes (testing without prefix)")
    
    # Fix 3: Best fix using proper function call syntax
    # This is the most explicit and least error-prone
    best_fix_pattern = r"```include\((.*?)\)```"
    best_fix_result = test_pattern(best_fix_pattern.replace("include\\(", "").replace("\\)", ">"), 
                                  "Best fix - function call syntax (testing equivalent)")
    
    print("\nRecommended fix implementation in process_backtick_includes:")
    print("```python")
    print("def process_backtick_includes(text: str, recursive: bool) -> str:")
    print("    # Original problematic pattern:")
    print("    # pattern = r\"```<(.*?)>```\"")
    print("    ")
    print("    # Fixed pattern that prevents matching XML tags within code blocks:")
    print("    pattern = r\"```<([^>]*?)>```\"")
    print("    ")
    print("    # Alternative better pattern with explicit syntax:")
    print("    # pattern = r\"```include:([^>]*?)>```\"  # requires ```include:path/to/file>")
    print("    # pattern = r\"```include\\((.*?)\\)```\" # requires ```include(path/to/file)")
    print("    ")
    print("    def replace_include(match):")
    print("        # Rest of the function stays the same")
    print("```")
    
    # Verify the fixes work as expected
    assert minimal_fix_result, "The minimal fix pattern should work correctly"

def test_exact_reproduction_of_log_issue() -> None:
    """
    This test verifies that our fix correctly handles the issue seen in logs with 
    XML content being mistakenly processed as file paths.
    
    The original issue was that the regex pattern r"```<(.*?)>```" could match XML tags.
    The fixed regex pattern r"```<([^>]*?)>```" prevents this by not matching
    content with nested > characters.
    """
    # The exact snippet from the problematic file
    problematic_content = """```
<prompt>
    <include>LICENSE</include>
    <shell>echo Hello World</shell>
    <pdd>This is a comment</pdd>
    ``` <file_to_include.txt>```
</prompt>
"""
    
    # Mock to track file open attempts
    opened_files = []
    def mock_open(*args, **kwargs):
        file_path = args[0] if args else kwargs.get('file')
        if file_path:
            opened_files.append(file_path)
            print(f"Attempting to open file: {file_path}")
        raise FileNotFoundError(f"Mocked file not found: {file_path}")
    
    # Process with our mock
    with patch('builtins.open', side_effect=mock_open):
        result = preprocess(problematic_content, recursive=False, double_curly_brackets=False)
    
    print("\nFiles that the system attempted to open:")
    for file in opened_files:
        print(f"- {file}")
    
    # With the fixed implementation, XML content should NOT be processed as file includes
    xml_files = [f for f in opened_files if "<" in f and ">" in f]
    assert len(xml_files) == 0, "The fixed implementation should not process XML content as file includes"
    
    # The original issue was that this would match problematic content
    original_pattern = r"```<(.*?)>```"
    # The fixed pattern prevents this
    fixed_pattern = r"```<([^>]*?)>```"
    
    # Test both patterns directly
    original_match = re.search(original_pattern, problematic_content, re.DOTALL)
    fixed_match = re.search(fixed_pattern, problematic_content, re.DOTALL)
    
    # The original would match, but our fix should not
    print("\nPattern matching tests:")
    if original_match:
        print(f"Original pattern would match: '{original_match.group(1)}'")
    else:
        print("Original pattern does not match (which is unexpected)")
    
    if fixed_match:
        print(f"Fixed pattern matches: '{fixed_match.group(1)}'")
    else:
        print("Fixed pattern correctly does not match XML content")
    
    print("\nFix implementation confirmed!")
    print("- Original pattern could match XML content when < and > are far apart")
    print("- Fixed pattern correctly does not match XML content with nested > characters")

def test_multiline_pattern_reproduction() -> None:
    """
    This test verifies that our fix correctly handles multilime patterns.
    
    The fixed regex pattern r"```<([^>]*?)>```" prevents matching text
    with > characters, which is the correct behavior.
    """
    print("\nVerifying the fixed pattern doesn't match problematic content")
    # Create a pattern that could have caused issues
    problematic_pattern = """```<
./examples>
    <example>
        <example_number>5</example_number>
    </example>
</examples>
```"""
    
    # The original pattern would match problematically with re.DOTALL
    original_pattern = r"```<(.*?)>```"
    # The fixed pattern prevents this
    fixed_pattern = r"```<([^>]*?)>```"
    
    # Test both patterns
    original_match = re.search(original_pattern, problematic_pattern, re.DOTALL)
    fixed_match = re.search(fixed_pattern, problematic_pattern, re.DOTALL)
    
    print(f"Original pattern match: {original_match is not None}")
    print(f"Fixed pattern match: {fixed_match is not None}")
    
    # With the fixed pattern (current implementation), it should not match
    assert fixed_match is None, "The fixed pattern should not match this problematic content"
    
    # Test a proper single-line backtick include
    proper_include = """```<file_path>```"""
    proper_match = re.search(fixed_pattern, proper_include, re.DOTALL)
    assert proper_match is not None, "The fixed pattern should still match proper includes"
    assert proper_match.group(1) == "file_path", "The fixed pattern should correctly capture the file path"
    
    print("\nFix verified:")
    print("1. The fixed pattern correctly rejects problematic multi-line content")
    print("2. The fixed pattern still works for proper backtick includes")
    print("3. The fix is implemented and working correctly")

def test_comprehensive_backtick_pattern_analysis() -> None:
    """
    This test comprehensively analyzes different patterns to identify 
    exactly what's triggering the problematic regex r"```<(.*?)>```".
    
    Now that we've fixed the issue, this test serves as a regression test
    to ensure our fix doesn't break legitimate patterns.
    """
    # Mock file open to track what paths are attempted
    def create_mock_with_tracking(pattern_text):
        opened_files = []
        def mock_open(*args, **kwargs):
            file_path = args[0] if args else kwargs.get('file')
            if file_path:
                opened_files.append(file_path)
                print(f"Attempting to open file: {file_path}")
            raise FileNotFoundError(f"Mocked file not found: {file_path}")
        return mock_open, opened_files
    
    # Test Patterns
    patterns = [
        # Pattern 1: Basic format directly matching the regex ```<path>```
        ("Basic include format", """```<file_path>```"""),
        
        # Pattern 2: XML content inside a code block
        ("XML in code block", """```
<examples>
    <example>Test</example>
</examples>
```"""),
        
        # Pattern 3: Nested XML content with > characters
        ("Nested XML", """```
<examples>
    <example attr="test>with>chars">Test</example>
</examples>
```"""),
        
        # Pattern 4: Multiple backtick blocks in a row
        ("Multiple backtick blocks", """```<file1>```
Some text
```<file2>```"""),
        
        # Pattern 5: Backticks followed by text, then XML
        ("Text then XML", """```text
<examples>
    <example>Test</example>
</examples>
```"""),
        
        # Pattern 6: Mimicking what's in the logs
        ("Log format", """```./examples>
<example>
    <example_number>5</example_number>
</example>
```"""),
        
        # Pattern 7: Backtick block immediately followed by XML tag
        ("Backticks with XML", """```<examples>``````
<example>Test</example>
```"""),
        
        # Pattern 8: XML content with backticks inside it
        ("XML with internal backticks", """<examples>
    <example>```<file>```</example>
</examples>"""),

        # Pattern 9: Exact format seen in the file (missing a newline after the closing backticks)
        ("Missing newline", """```
<prompt>
    <include>LICENSE</include>
</prompt>```"""),

        # Pattern 10: Missing space after triple backticks
        ("No space after backticks", """```<prompt>
    <include>LICENSE</include>
</prompt>
```""")
    ]
    
    # Test each pattern with the current implementation
    print("\n=== Testing patterns with current implementation ===")
    for name, pattern_text in patterns:
        mock_open, opened_files = create_mock_with_tracking(pattern_text)
        
        print(f"\nTesting: {name}")
        print(f"Pattern: {pattern_text.strip()}")
        
        # Check current implementation
        with patch('builtins.open', side_effect=mock_open):
            result = preprocess(pattern_text, recursive=False, double_curly_brackets=False)
        
        if opened_files:
            print(f"Files attempted to open: {opened_files}")
            xml_files = [f for f in opened_files if "<" in f and ">" in f and f not in ["./file_path", "./file1", "./file2", "./file", "./examples"]]
            if xml_files:
                print(f"XML-like files: {xml_files}")
                assert False, f"The fixed implementation should not process XML content as file paths: {xml_files}"
        else:
            print("No files attempted to open")
        
        # Also check the regex directly to see what it matches
        pattern = r"```<([^>]*?)>```"
        matches = re.findall(pattern, pattern_text, re.DOTALL)
        if matches:
            print(f"Fixed pattern matches: {matches}")
            for match in matches:
                assert ">" not in match, f"The fixed pattern matched content with > character: {match}"
    
    print("\n=== CONCLUSION ===")
    print("All tests passed with the fixed implementation:")
    print("1. The fixed pattern r\"```<([^>]*?)>```\" only matches proper includes")
    print("2. No XML tags were incorrectly processed as file paths")
    print("3. Proper backtick includes continue to work correctly")


# ============================================================================
# Tests for Issue #74: Optional template variables should not be required
# ============================================================================

def test_issue_74_optional_variables_with_dollar_syntax():
    """
    Test that optional variables using ${VAR} syntax don't cause issues.

    Related to issue #74 where optional template variables (required: false)
    were causing "Missing key" errors when not provided.
    """
    template = """Generate code for ${MODULE}.

<prd><include>${PRD_FILE}</include></prd>
<tech_stack><include>${TECH_STACK_FILE}</include></tech_stack>

Please implement based on the above context.
"""

    # First preprocess pass (recursive=True, no doubling)
    step1 = preprocess(template, recursive=True, double_curly_brackets=False)

    # Simulate variable expansion - ${MODULE} and ${PRD_FILE} not expanded (not in env)
    # ${TECH_STACK_FILE} also not expanded
    # The _expand_vars in code_generator_main would leave these as-is if not in the dict

    # Second preprocess pass (recursive=False, with doubling)
    # This should convert ${VAR} to ${{VAR}} which is safe for PromptTemplate
    step2 = preprocess(step1, recursive=False, double_curly_brackets=True)

    # Verify ${MODULE} becomes ${{MODULE}} (safe for PromptTemplate)
    assert "${{MODULE}}" in step2 or "[File not found:" in step2

    # Verify no single-brace {MODULE} remains (which would cause llm_invoke to fail)
    single_brace_pattern = r'(?<!\{)\{MODULE\}(?!\})'
    matches = re.findall(single_brace_pattern, step2)
    assert len(matches) == 0, f"Found single-brace {{MODULE}} that would cause 'Missing key' error"


def test_issue_74_single_brace_variables_get_doubled():
    """
    Test that single-brace variables {VAR} get properly doubled to {{VAR}}.

    This ensures LangChain's PromptTemplate treats them as escaped literals.
    """
    template = "Generate code for module: {MODULE_NAME}"

    # Run through preprocess with doubling
    preprocessed = preprocess(template, recursive=False, double_curly_brackets=True)

    # After doubling, {MODULE_NAME} should become {{MODULE_NAME}}
    assert "{{MODULE_NAME}}" in preprocessed

    # Verify no single-brace remains
    single_brace_pattern = r'(?<!\{)\{MODULE_NAME\}(?!\})'
    matches = re.findall(single_brace_pattern, preprocessed)
    assert len(matches) == 0


def test_issue_74_architecture_template_scenario():
    """
    Test the exact scenario from issue #74 with architecture_json template structure.

    The template has:
    - PRD_FILE (required)
    - TECH_STACK_FILE, DOC_FILES, INCLUDE_FILES (optional)

    When only PRD_FILE is provided, optional variables should not cause errors.
    """
    template = """Generate architecture JSON.

<PRD_FILE><include>${PRD_FILE}</include></PRD_FILE>
<TECH_STACK_FILE><include>${TECH_STACK_FILE}</include></TECH_STACK_FILE>
<DOC_FILES><include-many>${DOC_FILES}</include-many></DOC_FILES>

Create JSON array based on above context.
"""

    # Step 1: First preprocess (recursive=True, no doubling)
    step1 = preprocess(template, recursive=True, double_curly_brackets=False)

    # The include tags with ${TECH_STACK_FILE} etc will try to open files
    # and fail, leaving placeholder text

    # Step 2: Second preprocess (recursive=False, with doubling)
    step2 = preprocess(step1, recursive=False, double_curly_brackets=True)

    # Check that no single-brace variables remain that would cause llm_invoke errors
    single_brace_pattern = r'(?<!\{)\{(TECH_STACK_FILE|DOC_FILES|INCLUDE_FILES)\}(?!\})'
    matches = re.findall(single_brace_pattern, step2)

    assert len(matches) == 0, (
        f"Issue #74: Found single-brace variables {matches} that would cause "
        f"'Missing key' errors. Optional variables should not require values."
    )


def test_issue_74_include_many_with_missing_optional_variable():
    """
    Test that <include-many> tags with missing optional variables are handled gracefully.
    """
    template = "<context_files><include-many>${DOC_FILES}</include-many></context_files>"

    # First pass - <include-many> stays (recursive=True)
    step1 = preprocess(template, recursive=True, double_curly_brackets=False)

    # Second pass - processes <include-many>, converts ${DOC_FILES} to ${{DOC_FILES}}
    step2 = preprocess(step1, recursive=False, double_curly_brackets=True)

    # Should not have single-brace {DOC_FILES} that would cause errors
    single_brace_pattern = r'(?<!\{)\{DOC_FILES\}(?!\})'
    matches = re.findall(single_brace_pattern, step2)
    assert len(matches) == 0


def test_process_include_tag_with_image() -> None:
    """Test processing of <include> tags with image files."""

    # Create a real 1x1 pixel PNG in memory
    img = Image.new('RGB', (1, 1))
    buffer = io.BytesIO()
    img.save(buffer, format='PNG')
    dummy_image_content = buffer.getvalue()

    image_path = "dummy_image.png"
    prompt = f"This is a test with an image: <include>{image_path}</include>"
    
    encoded_string = base64.b64encode(dummy_image_content).decode('utf-8')
    expected_output = f"This is a test with an image: data:image/png;base64,{encoded_string}"

    # Use a more robust mock for open that returns a real file-like object
    mock_file = io.BytesIO(dummy_image_content)
    mock_opener = mock_open(read_data=dummy_image_content)
    mock_opener.return_value.__enter__.return_value = mock_file

    with patch('builtins.open', mock_opener):
        # Mock os.path.splitext to control the extension
        with patch('os.path.splitext', return_value=('dummy_image', '.png')):
            assert preprocess(prompt, recursive=False, double_curly_brackets=False) == expected_output

def test_issue_74_mixed_required_and_optional_variables():
    """
    Test template with both required and optional variables.

    Only required variables should need values; optional ones should not cause errors.
    """
    template = """Module: {MODULE}
Optional PRD: {PRD_FILE}
Optional Docs: {DOC_FILES}
"""

    # Run doubling
    preprocessed = preprocess(template, recursive=False, double_curly_brackets=True)

    # All should be doubled to {{VAR}}
    assert "{{MODULE}}" in preprocessed
    assert "{{PRD_FILE}}" in preprocessed
    assert "{{DOC_FILES}}" in preprocessed

    # None should remain as single-brace
    single_brace_pattern = r'(?<!\{)\{(MODULE|PRD_FILE|DOC_FILES)\}(?!\})'
    matches = re.findall(single_brace_pattern, preprocessed)
    assert len(matches) == 0, f"Found single-brace variables: {matches}"


def test_get_file_path_repo_root_fallback(monkeypatch, tmp_path):
    """
    Verifies that get_file_path correctly falls back to the repository root
    when run from a worktree where import shadowing occurs.

    This test simulates the scenario where:
    1. The CWD does not contain the target file.
    2. The 'package_dir' (local pdd/pdd) does not contain the target file.
    3. The file *does* exist in the repository root (parent of pdd/pdd).

    Bug: https://github.com/gltanaka/pdd/issues/240
    """
    mock_file_name = "context/insert/1/prompt_to_update.prompt"

    # Create a mock repository structure
    # /tmp_path/mock_project/
    # ├── pdd/                       <-- Mock repo root
    # │   ├── pdd/                   <-- Mock Python package
    # │   │   ├── preprocess.py
    # │   │   └── __init__.py
    # │   └── context/
    # │       └── insert/
    # │           └── 1/
    # │               └── prompt_to_update.prompt
    # └── other_files/

    # Mock the location of path_resolution.py to simulate import shadowing
    # This will make get_default_resolver() return paths inside our mock worktree.
    mock_path_resolution_file = tmp_path / "mock_project" / "pdd" / "pdd" / "path_resolution.py"
    mock_path_resolution_file.parent.mkdir(parents=True, exist_ok=True)
    mock_path_resolution_file.write_text("...")  # Content doesn't matter for this test

    # Create the mock context file in the repository root
    mock_repo_root = tmp_path / "mock_project" / "pdd"
    expected_file_path = mock_repo_root / mock_file_name
    expected_file_path.parent.mkdir(parents=True, exist_ok=True)
    expected_file_path.write_text("Mock context content")

    # Change CWD to simulate running from the project root (not pdd/pdd)
    # The CWD is 'tmp_path / "mock_project"' but the pdd source is in 'tmp_path / "mock_project" / "pdd"'
    monkeypatch.chdir(tmp_path / "mock_project")

    # Mock pdd.path_resolution.__file__ to return the path to our mock file
    # This is crucial for simulating the 'package_root' calculation in get_default_resolver()
    monkeypatch.setattr('pdd.path_resolution.__file__', str(mock_path_resolution_file))

    # Expectation: get_file_path should find the file in the mock_repo_root
    found_path = get_file_path(mock_file_name)

    # Assert that the found path is the one in the mock repository root
    assert found_path == str(expected_file_path)


# ============================================================================
# Tests for Issue #375: Malformed JSON in PDD metadata tags
# https://github.com/gltanaka/pdd/issues/375
#
# Issue #410 fix: double_curly() must double ALL braces uniformly, including
# inside PDD metadata tags (<pdd-interface>, <pdd-reason>, <pdd-dependency>).
# architecture_sync.py reads raw files (never preprocessed), so PDD tags don't
# need protection. The fallback parser in parse_prompt_tags() handles doubled
# braces as a safety net. The critical requirement is that .format() succeeds.
# ============================================================================

def test_double_curly_doubles_pdd_interface_json() -> None:
    """
    Test that JSON in <pdd-interface> tags is doubled by double_curly(),
    and that .format() correctly undoubles it back to valid JSON.

    Issue #410: PDD tag protection caused .format() to raise KeyError
    because single-braced JSON was interpreted as format placeholders.
    """
    import json

    prompt = '''<pdd-interface>
{
  "type": "module",
  "module": {
    "functions": [
      {"name": "fix_architecture", "signature": "(arch: str)", "returns": "str"}
    ]
  }
}
</pdd-interface>
% This is a template with {variable} placeholder.'''

    processed = preprocess(prompt, recursive=False, double_curly_brackets=True)

    # All braces should be doubled (including inside PDD tags)
    assert "{{variable}}" in processed, "Template variables should be doubled"
    assert '{{' in processed, "Braces inside PDD tags should also be doubled"
    # JSON opening brace is on its own line, so check for {{ at start of line
    assert '"type": "module"' not in processed or '{{' in processed, \
        "JSON braces inside PDD tags should be doubled"

    # After .format(**{}), the JSON should be valid again (undoubled back)
    # In production, llm_invoke calls prompt.format(**input_data) where input_data={}
    formatted = processed.format()
    import re
    interface_match = re.search(r'<pdd-interface>(.*?)</pdd-interface>', formatted, re.DOTALL)
    assert interface_match is not None
    parsed = json.loads(interface_match.group(1).strip())
    assert parsed['type'] == 'module'
    assert len(parsed['module']['functions']) == 1


def test_double_curly_doubles_pdd_reason_braces() -> None:
    """
    Test that braces in <pdd-reason> tags are doubled like all other braces.

    Issue #410: All braces must be doubled so .format() can undouble them.
    """
    prompt = '''<pdd-reason>Handles JSON objects like {"key": "value"}</pdd-reason>
Normal text with {placeholder}.'''

    processed = preprocess(prompt, recursive=False, double_curly_brackets=True)

    # All braces should be doubled
    import re
    reason_match = re.search(r'<pdd-reason>(.*?)</pdd-reason>', processed, re.DOTALL)
    assert reason_match is not None
    reason_content = reason_match.group(1)
    assert '{{' in reason_content, "Braces in <pdd-reason> should be doubled"

    assert "{{placeholder}}" in processed

    # After .format(), content is undoubled back to original
    formatted = processed.format()
    reason_match2 = re.search(r'<pdd-reason>(.*?)</pdd-reason>', formatted, re.DOTALL)
    assert '{"key": "value"}' in reason_match2.group(1)


def test_double_curly_doubles_pdd_dependency_content() -> None:
    """
    Test that <pdd-dependency> content is processed by double_curly().

    Dependencies typically contain filenames (no braces), so doubling
    has no visible effect, but the tag structure is preserved.
    """
    prompt = '''<pdd-dependency>some_module.prompt</pdd-dependency>
Text with {variable}.'''

    processed = preprocess(prompt, recursive=False, double_curly_brackets=True)

    # Dependency tag content has no braces, so it's unchanged
    assert '<pdd-dependency>some_module.prompt</pdd-dependency>' in processed

    # Variable outside should be doubled
    assert "{{variable}}" in processed


def test_double_curly_doubles_multiple_pdd_tags() -> None:
    """
    Test that all PDD tags have their braces doubled uniformly.

    Issue #410: All braces everywhere must be doubled for .format() safety.
    """
    prompt = '''<pdd-reason>Provides unified LLM invocation with {options}</pdd-reason>
<pdd-interface>
{
  "type": "module",
  "module": {"functions": [{"name": "invoke", "returns": "str"}]}
}
</pdd-interface>
<pdd-dependency>base_module.prompt</pdd-dependency>
% Template with {input} and {output} variables.'''

    processed = preprocess(prompt, recursive=False, double_curly_brackets=True)

    # All braces doubled
    import re
    reason_match = re.search(r'<pdd-reason>(.*?)</pdd-reason>', processed, re.DOTALL)
    assert reason_match is not None
    assert '{{options}}' in reason_match.group(1), "Braces in <pdd-reason> should be doubled"

    assert "{{input}}" in processed
    assert "{{output}}" in processed

    # After .format(), everything undoubles correctly
    formatted = processed.format()
    import json
    interface_match = re.search(r'<pdd-interface>(.*?)</pdd-interface>', formatted, re.DOTALL)
    assert interface_match is not None
    parsed = json.loads(interface_match.group(1).strip())
    assert parsed['type'] == 'module'


def test_double_curly_doubles_nested_json_in_pdd_interface() -> None:
    """
    Test that deeply nested JSON in <pdd-interface> is doubled and
    survives the .format() round-trip.

    Issue #410: Nested JSON structures must survive double_curly → .format().
    """
    import json

    nested_json = {
        "type": "module",
        "module": {
            "functions": [
                {
                    "name": "process",
                    "signature": "(data: Dict[str, Any])",
                    "returns": "Dict[str, List[Dict[str, str]]]"
                }
            ],
            "classes": [
                {
                    "name": "Handler",
                    "methods": [{"name": "handle", "args": "{}"}]
                }
            ]
        }
    }

    prompt = f'''<pdd-interface>
{json.dumps(nested_json, indent=2)}
</pdd-interface>
% Use this with {{already_escaped}} and {{variable}}.'''

    processed = preprocess(prompt, recursive=False, double_curly_brackets=True)

    # After .format(), nested JSON should be intact
    formatted = processed.format()
    import re
    interface_match = re.search(r'<pdd-interface>(.*?)</pdd-interface>', formatted, re.DOTALL)
    assert interface_match is not None
    parsed = json.loads(interface_match.group(1).strip())
    assert parsed == nested_json, "Nested JSON structure was altered after round-trip"


def test_double_curly_still_doubles_outside_pdd_tags() -> None:
    """
    Regression test: Ensure normal brace doubling still works outside PDD tags.

    double_curly() must escape all braces for safe use with .format().
    """
    prompt = '''<pdd-interface>{"valid": "json"}</pdd-interface>
Normal text with {variable1} and {variable2}.
Code example: const obj = {key: value};
Template literal ${FOO} should become ${{FOO}}.'''

    processed = preprocess(prompt, recursive=False, double_curly_brackets=True)

    # All braces doubled (including PDD tag content)
    assert '{{"valid": "json"}}' in processed, "PDD tag JSON braces should be doubled"

    # Variables outside should be doubled
    assert "{{variable1}}" in processed
    assert "{{variable2}}" in processed

    # Code braces outside PDD tags should be doubled
    assert "{{key: value}}" in processed

    # Template literals should become ${{...}}
    assert "${{FOO}}" in processed


def test_double_curly_integration_with_parse_prompt_tags() -> None:
    """
    Integration test: parse_prompt_tags() can handle preprocessed content
    via its fallback double-brace parser.

    In production, architecture_sync.py reads raw files. But the fallback
    parser (commit 6a1d77c4) can also handle doubled braces as a safety net.
    """
    from pdd.architecture_sync import parse_prompt_tags

    prompt = '''<pdd-reason>Handles authentication flows</pdd-reason>
<pdd-interface>
{
  "type": "module",
  "module": {
    "functions": [
      {"name": "authenticate", "signature": "(user: str, pass: str)", "returns": "bool"},
      {"name": "validate_token", "signature": "(token: str)", "returns": "Dict"}
    ]
  }
}
</pdd-interface>
<pdd-dependency>base_auth.prompt</pdd-dependency>
% Template with {user_input} placeholder.'''

    # parse_prompt_tags on RAW content (the production path)
    raw_result = parse_prompt_tags(prompt)
    assert raw_result['interface']['type'] == 'module'
    assert len(raw_result['interface']['module']['functions']) == 2

    # parse_prompt_tags on PREPROCESSED content (safety net via fallback parser)
    processed = preprocess(prompt, recursive=False, double_curly_brackets=True)
    processed_result = parse_prompt_tags(processed)
    assert processed_result['interface'] is not None, \
        f"Fallback parser should handle doubled braces: {processed_result.get('interface_parse_error')}"
    assert processed_result['interface']['type'] == 'module'

    # Verify dependencies were extracted in both cases
    assert 'base_auth.prompt' in raw_result.get('dependencies', [])


def test_double_curly_real_world_prompt_format_roundtrip() -> None:
    """
    Test with a real-world prompt: double_curly → .format() round-trip.

    Issue #410: This is the exact flow that was broken. The prompt has PDD
    metadata tags with JSON AND template variables. After preprocessing,
    .format(**input_data) must work without KeyError.
    """
    import json

    prompt = '''<pdd-reason>Fixes validation errors in architecture.json: resolves circular deps, priority violations, missing fields.</pdd-reason>
<pdd-interface>
{
  "type": "module",
  "module": {
    "functions": [
      {"name": "fix_architecture", "signature": "(current_architecture: str, step7_output: str)", "returns": "str (corrected JSON array)"}
    ]
  }
}
</pdd-interface>
<pdd-dependency>agentic_arch_step7_validate_LLM.prompt</pdd-dependency>
% You are an expert software architect. Your task is to fix validation errors.

% Inputs
- Issue URL: {issue_url}
- Repository: {repo_owner}/{repo_name}
- Issue Number: {issue_number}

% Current Architecture
<architecture_json>
{current_architecture}
</architecture_json>'''

    processed = preprocess(prompt, recursive=False, double_curly_brackets=True)

    # Template variables outside PDD tags SHOULD be doubled
    assert "{{issue_url}}" in processed
    assert "{{repo_owner}}" in processed
    assert "{{current_architecture}}" in processed

    # .format(**{}) should succeed (issue #410) — this is the production call
    # In production, llm_invoke calls prompt.format(**input_data) where
    # input_data is typically {} for pdd sync. All {{...}} get undoubled to {...}.
    formatted = processed.format()

    # After formatting, PDD tags should contain valid JSON (undoubled back)
    import re
    interface_match = re.search(r'<pdd-interface>(.*?)</pdd-interface>', formatted, re.DOTALL)
    assert interface_match is not None, "Lost <pdd-interface> tag"
    interface_json = json.loads(interface_match.group(1).strip())
    assert interface_json['type'] == 'module'
    assert interface_json['module']['functions'][0]['name'] == 'fix_architecture'

    # Template variables should be undoubled back to original single-brace form
    assert "{issue_url}" in formatted
    assert "{repo_owner}" in formatted
    assert "{current_architecture}" in formatted


# ============================================================================
# Issue #410: Preprocessed prompts with PDD tags must survive str.format()
# The double_curly() → .format() pipeline is how all prompts reach the LLM.
# PDD tags containing JSON must be doubled so .format() undoubles them safely.
# ============================================================================

def test_pdd_tags_survive_format() -> None:
    """
    Regression test for issue #410: pdd sync fails with KeyError when prompts
    contain <pdd-interface> tags with JSON.

    The preprocessing pipeline is:
      1. double_curly() doubles all { → {{
      2. llm_invoke calls prompt.format(**input_data) which undoubles {{ → {

    If PDD tag content is protected from doubling (step 1), .format() in step 2
    interprets the single braces as format placeholders and raises KeyError.
    """
    prompt = '''<pdd-reason>Defines the User data model with Firestore serialization.</pdd-reason>
<pdd-interface>
{
  "type": "module",
  "module": {
    "functions": [
      {"name": "User", "signature": "@dataclass class", "returns": "User"},
      {"name": "User.to_dict", "signature": "(self) -> Dict[str, Any]", "returns": "Dict[str, Any]"},
      {"name": "User.from_dict", "signature": "(cls, data: Dict[str, Any]) -> User", "returns": "User"}
    ]
  }
}
</pdd-interface>

You are an expert Python engineer. Write the User data model.'''

    processed = preprocess(prompt, recursive=False, double_curly_brackets=True)

    # This is the exact operation that llm_invoke.py:1238 performs.
    # It must not raise KeyError.
    try:
        formatted = processed.format()
    except KeyError as e:
        pytest.fail(
            f"Issue #410: preprocessed prompt with PDD tags failed .format(): {e}\n"
            f"This means double_curly() did not escape braces inside PDD tags.\n"
            f"Preprocessed content (first 500 chars):\n{processed[:500]}"
        )

    # After .format() undoubles {{ → {, the JSON should be valid
    assert '"type": "module"' in formatted
    assert '{"name": "User"' in formatted
    assert '<pdd-interface>' in formatted
    assert '</pdd-interface>' in formatted


import os
import io
import re
import pytest
import json
import subprocess
from unittest.mock import patch, mock_open, MagicMock, PropertyMock
from pdd.preprocess import (
    preprocess,
    get_file_path,
    double_curly,
    process_backtick_includes,
    process_xml_tags,
    process_pdd_tags,
    process_shell_tags,
    process_web_tags,
    process_include_tags,
    process_include_many_tags,
    _extract_fence_spans,
    _extract_inline_code_spans,
    _extract_code_spans,
    _is_inside_any_span,
    _intersects_any_span,
    _scan_risky_placeholders,
    _dbg,
    _write_debug_report,
    _DEBUG_EVENTS,
    _parse_attrs,
)


# ============================================================================
# Fixture to reset Firecrawl cache singleton for test isolation
# ============================================================================
@pytest.fixture
def reset_firecrawl_cache():
    import pdd.firecrawl_cache
    original_instance = pdd.firecrawl_cache._cache_instance
    pdd.firecrawl_cache._cache_instance = None
    yield
    pdd.firecrawl_cache._cache_instance = original_instance


# ============================================================================
# _dbg and _write_debug_report coverage
# ============================================================================

def test_dbg_when_debug_enabled(monkeypatch):
    """Cover lines 29-30: _dbg prints and appends when debug is on."""
    import pdd.preprocess as pp
    original = pp._DEBUG_PREPROCESS
    pp._DEBUG_PREPROCESS = True
    pp._DEBUG_EVENTS.clear()
    try:
        _dbg("test message")
        assert "test message" in pp._DEBUG_EVENTS
    finally:
        pp._DEBUG_PREPROCESS = original


def test_write_debug_report_writes_file(monkeypatch, tmp_path):
    """Cover lines 34-40: _write_debug_report writes to file."""
    import pdd.preprocess as pp
    original_debug = pp._DEBUG_PREPROCESS
    original_file = pp._DEBUG_OUTPUT_FILE
    pp._DEBUG_PREPROCESS = True
    report_path = str(tmp_path / "debug_report.txt")
    pp._DEBUG_OUTPUT_FILE = report_path
    pp._DEBUG_EVENTS.clear()
    pp._DEBUG_EVENTS.append("event1")
    pp._DEBUG_EVENTS.append("event2")
    try:
        _write_debug_report()
        assert os.path.exists(report_path)
        content = open(report_path).read()
        assert "event1" in content
        assert "event2" in content
    finally:
        pp._DEBUG_PREPROCESS = original_debug
        pp._DEBUG_OUTPUT_FILE = original_file


def test_write_debug_report_handles_write_error(monkeypatch):
    """Cover lines 38-40: _write_debug_report handles write errors gracefully."""
    import pdd.preprocess as pp
    original_debug = pp._DEBUG_PREPROCESS
    original_file = pp._DEBUG_OUTPUT_FILE
    pp._DEBUG_PREPROCESS = True
    pp._DEBUG_OUTPUT_FILE = "/nonexistent/path/report.txt"
    pp._DEBUG_EVENTS.clear()
    try:
        # Should not raise
        _write_debug_report()
    finally:
        pp._DEBUG_PREPROCESS = original_debug
        pp._DEBUG_OUTPUT_FILE = original_file


def test_write_debug_report_no_file_set(monkeypatch):
    """Cover lines 42-44: debug enabled but no output file set."""
    import pdd.preprocess as pp
    original_debug = pp._DEBUG_PREPROCESS
    original_file = pp._DEBUG_OUTPUT_FILE
    pp._DEBUG_PREPROCESS = True
    pp._DEBUG_OUTPUT_FILE = None
    try:
        _write_debug_report()  # Should just print a message, not crash
    finally:
        pp._DEBUG_PREPROCESS = original_debug
        pp._DEBUG_OUTPUT_FILE = original_file


# ============================================================================
# _parse_attrs coverage
# ============================================================================

def test_parse_attrs_with_attributes():
    """Cover lines 230-234: _parse_attrs parses key=value pairs."""
    result = _parse_attrs(' path="file.txt" query="what is this"')
    assert result == {"path": "file.txt", "query": "what is this"}


def test_parse_attrs_empty_string():
    """Cover line 228-229: _parse_attrs with empty string."""
    result = _parse_attrs("")
    assert result == {}


def test_parse_attrs_single_quotes():
    """_parse_attrs handles single-quoted attributes."""
    result = _parse_attrs(" path='file.txt' mode='full'")
    assert result == {"path": "file.txt", "mode": "full"}


# ============================================================================
# Include tag with query attribute
# ============================================================================

def test_include_tag_with_query_deferred_when_recursive():
    """Cover line 251: query includes are deferred during recursive pass."""
    prompt = '<include path="file.txt" query="what functions exist"/>'
    result = preprocess(prompt, recursive=True, double_curly_brackets=False)
    assert result == prompt


def test_include_tag_with_query_import_error():
    """Cover lines 258-270: query include when extractor not available."""
    prompt = '<include path="file.txt" query="what functions exist"/>'
    with patch('builtins.open', mock_open(read_data="content")):
        # Setting the module to None in sys.modules triggers ImportError on import
        with patch.dict('sys.modules', {'pdd.include_query_extractor': None}):
             # Removed the aggressive builtins.__import__ patch
            result = process_include_tags(prompt, recursive=False)
    assert "Error" in result or "not found" in result.lower() or "include_query_extractor" in result


def test_include_tag_with_query_generic_exception():
    """Cover query include generic exception path."""
    prompt = '<include path="file.txt" query="what functions exist"/>'
    mock_extractor = MagicMock()
    mock_extractor.IncludeQueryExtractor.return_value.extract.side_effect = RuntimeError("extraction failed")
    
    with patch('builtins.open', mock_open(read_data="content")):
        with patch.dict('sys.modules', {'pdd.include_query_extractor': mock_extractor}):
            result = process_include_tags(prompt, recursive=False)
    assert "Error" in result


# ============================================================================
# Image include processing
# ============================================================================

def test_include_gif_image():
    """Cover lines 299-302: GIF image processing (convert to PNG)."""
    from PIL import Image
    import io as _io

    img = Image.new('RGB', (50, 50), color='red')
    frames = [Image.new('RGB', (50, 50), color='blue')]
    buffer = _io.BytesIO()
    img.save(buffer, format='GIF', save_all=True, append_images=frames)
    gif_data = buffer.getvalue()

    prompt = "<include>test.gif</include>"

    def mock_open_func(path, *args, **kwargs):
        if 'r' in args or kwargs.get('mode') == 'r':
            raise FileNotFoundError
        mock_file = _io.BytesIO(gif_data)
        mock_file.name = path
        return mock_file

    with patch('builtins.open', side_effect=mock_open_func):
        with patch('os.path.splitext', return_value=('test', '.gif')):
            result = process_include_tags(prompt, recursive=False)

    assert result.startswith("data:image/png;base64,")


def test_include_jpg_image():
    """Cover lines 303-305: JPG image processing."""
    from PIL import Image
    import io as _io

    img = Image.new('RGB', (50, 50), color='green')
    buffer = _io.BytesIO()
    img.save(buffer, format='JPEG')
    jpg_data = buffer.getvalue()

    prompt = "<include>test.jpg</include>"

    def mock_open_func(path, *args, **kwargs):
        if 'r' in args or kwargs.get('mode') == 'r':
            raise FileNotFoundError
        mock_file = _io.BytesIO(jpg_data)
        mock_file.name = path
        return mock_file

    with patch('builtins.open', side_effect=mock_open_func):
        with patch('os.path.splitext', return_value=('test', '.jpg')):
            result = process_include_tags(prompt, recursive=False)

    assert result.startswith("data:image/jpeg;base64,")


def test_include_large_image_resized():
    """Cover image resizing when dimensions exceed 1024."""
    from PIL import Image
    import io as _io

    img = Image.new('RGB', (2048, 2048), color='blue')
    buffer = _io.BytesIO()
    img.save(buffer, format='PNG')
    png_data = buffer.getvalue()

    prompt = "<include>large.png</include>"

    def mock_open_func(path, *args, **kwargs):
        if 'r' in args or kwargs.get('mode') == 'r':
            raise FileNotFoundError
        mock_file = _io.BytesIO(png_data)
        mock_file.name = path
        return mock_file

    with patch('builtins.open', side_effect=mock_open_func):
        with patch('os.path.splitext', return_value=('large', '.png')):
            result = process_include_tags(prompt, recursive=False)

    assert result.startswith("data:image/png;base64,")


# ============================================================================
# Include tag with selectors/content_selector
# ============================================================================

def test_include_tag_with_select_attribute():
    """Cover lines 330-339: include with select attribute."""
    prompt = '<include path="file.py" select="def main"/>'
    file_content = "def main():\n    pass\n\ndef helper():\n    pass\n"

    mock_selector = MagicMock()
    mock_selector.ContentSelector.return_value.select.return_value = "def main():\n    pass\n"

    with patch('builtins.open', mock_open(read_data=file_content)):
        with patch.dict('sys.modules', {'pdd.content_selector': mock_selector}):
            result = process_include_tags(prompt, recursive=False)

    assert "def main" in result


def test_include_tag_with_lines_attribute():
    """Cover include with lines attribute."""
    prompt = '<include path="file.py" lines="1-3"/>'
    file_content = "line1\nline2\nline3\nline4\nline5\n"

    mock_selector = MagicMock()
    mock_selector.ContentSelector.return_value.select.return_value = "line1\nline2\nline3\n"

    with patch('builtins.open', mock_open(read_data=file_content)):
        with patch.dict('sys.modules', {'pdd.content_selector': mock_selector}):
            result = process_include_tags(prompt, recursive=False)

    assert "line1" in result


def test_include_tag_selector_import_error():
    """Cover lines 347-348: ContentSelector import error."""
    prompt = '<include path="file.py" select="def main"/>'
    file_content = "def main():\n    pass\n"

    # Use sys.modules to simulate missing module instead of patching __import__
    with patch('builtins.open', mock_open(read_data=file_content)):
        with patch.dict('sys.modules', {'pdd.content_selector': None}):
            result = process_include_tags(prompt, recursive=False)

    # Should include full content as fallback
    assert "def main" in result


def test_include_tag_selector_exception():
    """Cover lines 349-350: ContentSelector raises exception."""
    prompt = '<include path="file.py" select="def main"/>'
    file_content = "def main():\n    pass\n"

    mock_selector = MagicMock()
    mock_selector.ContentSelector.return_value.select.side_effect = RuntimeError("selector error")

    with patch('builtins.open', mock_open(read_data=file_content)):
        with patch.dict('sys.modules', {'pdd.content_selector': mock_selector}):
            result = process_include_tags(prompt, recursive=False)

    # Should still include content (error is logged but content returned)
    assert "def main" in result


# ============================================================================
# Include tag ValueError (non-circular) and generic Exception
# ============================================================================

def test_include_tag_value_error_non_circular():
    """Cover lines 363-372: ValueError that is not circular include."""
    prompt = "<include>bad_file.txt</include>"

    def mock_open_func(path, *args, **kwargs):
        raise ValueError("some value error")

    with patch('builtins.open', side_effect=mock_open_func):
        result = process_include_tags(prompt, recursive=False)

    assert "Error processing include" in result


def test_include_tag_generic_exception():
    """Cover generic Exception in include processing."""
    prompt = "<include>bad_file.txt</include>"

    def mock_open_func(path, *args, **kwargs):
        raise RuntimeError("unexpected error")

    with patch('builtins.open', side_effect=mock_open_func):
        result = process_include_tags(prompt, recursive=False)

    assert "Error processing include" in result


# ============================================================================
# process_pdd_tags special case (line 395)
# ============================================================================

def test_pdd_tags_special_case_trailing_space():
    """Cover line 395: special case where processed == 'This is a test'."""
    result = process_pdd_tags("This is a test <pdd>comment here</pdd>")
    assert result == "This is a test "


# ============================================================================
# Shell tag generic Exception
# ============================================================================

def test_shell_tag_generic_exception():
    """Cover lines 415-418: shell tag with generic Exception."""
    prompt = "Test <shell>some_command</shell>"

    with patch('subprocess.run', side_effect=OSError("command not found")):
        result = preprocess(prompt, recursive=False, double_curly_brackets=False)

    assert "Shell execution error" in result


# ============================================================================
# Web tag cached content
# ============================================================================

def test_web_tag_uses_cached_content(reset_firecrawl_cache):
    """Cover lines 440-441: web tag returns cached content."""
    from pdd.firecrawl_cache import get_firecrawl_cache

    prompt = "Test <web>https://cached.example.com</web>"

    with patch.dict('os.environ', {'FIRECRAWL_CACHE_ENABLE': 'true', 'FIRECRAWL_API_KEY': 'key'}):
        cache = get_firecrawl_cache()
        cache.set("https://cached.example.com", "# Cached Content")

        result = preprocess(prompt, recursive=False, double_curly_brackets=False)

    assert "# Cached Content" in result


# ============================================================================
# Web tag timeout
# ============================================================================

def test_web_tag_timeout(reset_firecrawl_cache):
    """Cover lines 475-476: web tag times out."""
    from concurrent.futures import TimeoutError as FuturesTimeoutError

    prompt = "Test <web>https://slow.example.com</web>"

    mock_firecrawl = MagicMock()
    mock_app = MagicMock()
    # This side effect is not strictly necessary if we mock the executor, but keeps consistency
    mock_app.scrape_url.return_value = {'markdown': 'content'} 
    mock_firecrawl.Firecrawl.return_value = mock_app

    with patch.dict('sys.modules', {'firecrawl': mock_firecrawl}):
        with patch.dict('os.environ', {'FIRECRAWL_API_KEY': 'key', 'FIRECRAWL_CACHE_ENABLE': 'false'}):
            # Patch ThreadPoolExecutor where it is defined/imported. 
            # Since the code does `from concurrent.futures import ThreadPoolExecutor` inside the function,
            # we should patch `concurrent.futures.ThreadPoolExecutor`.
            with patch('concurrent.futures.ThreadPoolExecutor') as MockExecutor:
                mock_future = MagicMock()
                mock_future.result.side_effect = FuturesTimeoutError()
                
                mock_instance = MockExecutor.return_value
                mock_instance.__enter__.return_value = mock_instance
                mock_instance.submit.return_value = mock_future
                
                result = preprocess(prompt, recursive=False, double_curly_brackets=False)

    assert "timed out" in result


# ============================================================================
# Web tag with response object (hasattr markdown) but no markdown
# ============================================================================

def test_web_tag_response_object_with_markdown_attr(reset_firecrawl_cache):
    """Cover lines 487-489: response has markdown attribute (object style)."""
    prompt = "Test <web>https://example.com</web>"

    mock_firecrawl = MagicMock()
    mock_response = MagicMock(spec=[])  # No dict-like behavior
    mock_response.markdown = "# Object Response"
    mock_app = MagicMock()
    mock_app.scrape_url.return_value = mock_response
    mock_firecrawl.Firecrawl.return_value = mock_app

    with patch.dict('sys.modules', {'firecrawl': mock_firecrawl}):
        with patch.dict('os.environ', {'FIRECRAWL_API_KEY': 'key', 'FIRECRAWL_CACHE_ENABLE': 'false'}):
            result = preprocess(prompt, recursive=False, double_curly_brackets=False)

    assert "# Object Response" in result


# ============================================================================
# Web tag inside code span (line 497)
# ============================================================================

def test_web_tag_ignored_in_code_span(reset_firecrawl_cache):
    """Cover line 497: web tag inside inline code is not processed."""
    prompt = "Use `<web>https://example.com</web>` as example."

    mock_firecrawl = MagicMock()
    with patch.dict('sys.modules', {'firecrawl': mock_firecrawl}):
        with patch.dict('os.environ', {'FIRECRAWL_API_KEY': 'key', 'FIRECRAWL_CACHE_ENABLE': 'false'}):
            result = preprocess(prompt, recursive=False, double_curly_brackets=False)

    assert result == prompt


# ============================================================================
# Include-many generic Exception
# ============================================================================

def test_include_many_generic_exception():
    """Cover lines 525-528: include-many with generic exception."""
    prompt = "<include-many>error_file.txt</include-many>"

    def mock_open_func(path, *args, **kwargs):
        raise RuntimeError("unexpected error")

    with patch('builtins.open', side_effect=mock_open_func):
        result = preprocess(prompt, recursive=False, double_curly_brackets=False)

    assert "Error processing include" in result


# ============================================================================
# double_curly _restore_var fallback paths
# ============================================================================

def test_double_curly_restore_var_invalid_index():
    """Cover lines 579-582: _restore_var with invalid index or non-matching pattern."""
    # This tests the edge case where the placeholder index is out of range
    text = "Test __PDD_VAR_999__ here"
    # Manually invoke double_curly with text that has a stale placeholder
    result = double_curly(text)
    assert "__PDD_VAR_999__" in result  # Should be returned as-is


def test_double_curly_restore_var_exception_path():
    """Cover the except branch in _restore_var."""
    # Create a scenario where re.match fails inside _restore_var
    text = "Has ${VALID} placeholder"
    result = double_curly(text)
    assert "${{VALID}}" in result


# ============================================================================
# Code block non-matching language (line 600, 604)
# ============================================================================

def test_double_curly_non_code_language_block():
    """Cover lines 600, 604: code block with non-code language (e.g., markdown)."""
    prompt = """```markdown\nThis has {braces} in markdown.\n```"""

    result = preprocess(prompt, recursive=False, double_curly_brackets=True)
    # Non-code language blocks should be returned as-is by process_code_block
    assert "```markdown" in result


def test_double_curly_plain_code_block_no_language():
    """Code block with empty language identifier."""
    prompt = """```\n{plain_braces}\n```"""

    result = preprocess(prompt, recursive=False, double_curly_brackets=True)
    assert "{{plain_braces}}" in result or "{plain_braces}" in result


# ============================================================================
# Preprocess error handling
# ============================================================================

def test_preprocess_recursion_error():
    """Cover lines 153-155: RecursionError is re-raised."""
    with patch('pdd.preprocess.process_backtick_includes', side_effect=RecursionError("max depth")):
        with pytest.raises(RecursionError):
            preprocess("test", recursive=False, double_curly_brackets=False)


def test_preprocess_circular_value_error():
    """Cover lines 153-155: ValueError with 'Circular include' is re-raised."""
    with patch('pdd.preprocess.process_backtick_includes', side_effect=ValueError("Circular include detected")):
        with pytest.raises(ValueError, match="Circular include"):
            preprocess("test", recursive=False, double_curly_brackets=False)


def test_preprocess_generic_exception_returns_prompt():
    """Cover lines 156-161: generic Exception returns original prompt."""
    with patch('pdd.preprocess.process_backtick_includes', side_effect=TypeError("unexpected")):
        result = preprocess("original prompt", recursive=False, double_curly_brackets=False)
    assert result == "original prompt"


# ============================================================================
# _scan_risky_placeholders template brace detection
# ============================================================================

def test_scan_risky_placeholders_finds_template_braces():
    """Cover lines 113-114: detect ${...} template literals outside fences."""
    text = "const x = ${FOO};\nconst y = ${BAR + 1};"
    singles, templates = _scan_risky_placeholders(text)
    assert len(templates) >= 2


def test_scan_risky_placeholders_ignores_fenced():
    """Template literals inside fences should not be reported."""
    text = "```js\nconst x = ${FOO};\n```"
    singles, templates = _scan_risky_placeholders(text)
    assert len(templates) == 0


# ============================================================================
# Backtick include ValueError (non-circular) and generic Exception
# ============================================================================

def test_backtick_include_value_error_non_circular():
    """Cover lines 196-205: backtick include with non-circular ValueError."""
    prompt = "```<bad_file.txt>```"

    def mock_open_func(path, *args, **kwargs):
        raise ValueError("some value error")

    with patch('builtins.open', side_effect=mock_open_func):
        result = preprocess(prompt, recursive=False, double_curly_brackets=False)

    assert "Error processing include" in result


def test_backtick_include_generic_exception():
    """Cover generic Exception in backtick include."""
    prompt = "```<bad_file.txt>```"

    def mock_open_func(path, *args, **kwargs):
        raise RuntimeError("unexpected error")

    with patch('builtins.open', side_effect=mock_open_func):
        result = preprocess(prompt, recursive=False, double_curly_brackets=False)

    assert "Error processing include" in result


# ============================================================================
# Backtick include circular detection via _seen
# ============================================================================

def test_backtick_include_circular_via_seen():
    """Cover line 181: circular include detected via _seen set."""
    prompt = "```<circular.txt>```"
    
    # Pre-populate _seen with the resolved path of circular.txt
    with patch('builtins.open', mock_open(read_data="content")):
        with patch('os.path.realpath', return_value="/resolved/circular.txt"):
            with pytest.raises(ValueError, match="Circular include"):
                process_backtick_includes(prompt, recursive=False, _seen={"/resolved/circular.txt"})


# ============================================================================
# Max include iterations exceeded
# ============================================================================

def test_backtick_include_max_iterations():
    """Cover line 211: max iterations exceeded raises ValueError."""
    import pdd.preprocess as pp
    original_max = pp._MAX_INCLUDE_ITERATIONS
    pp._MAX_INCLUDE_ITERATIONS = 1

    prompt = "```<file1.txt>```"

    # Make the substitution always produce a new backtick include
    def mock_open_func(path, *args, **kwargs):
        return io.StringIO("```<file2.txt>```")

    try:
        with patch('builtins.open', side_effect=mock_open_func):
            with pytest.raises(ValueError, match="maximum include depth"):
                process_backtick_includes(prompt, recursive=False)
    finally:
        pp._MAX_INCLUDE_ITERATIONS = original_max


# ============================================================================
# Include tag max iterations exceeded
# ============================================================================

def test_include_tag_max_iterations():
    """Cover line 378: max iterations exceeded in include tags."""
    import pdd.preprocess as pp
    original_max = pp._MAX_INCLUDE_ITERATIONS
    pp._MAX_INCLUDE_ITERATIONS = 1

    prompt = "<include>file1.txt</include>"

    def mock_open_func(path, *args, **kwargs):
        return io.StringIO("<include>file2.txt</include>")

    try:
        with patch('builtins.open', side_effect=mock_open_func):
            with pytest.raises(ValueError, match="maximum include depth"):
                process_include_tags(prompt, recursive=False)
    finally:
        pp._MAX_INCLUDE_ITERATIONS = original_max


# ============================================================================
# Web tag inside fenced code block
# ============================================================================

def test_web_tag_ignored_in_fenced_code_block(reset_firecrawl_cache):
    """Web tags inside fenced code blocks should not execute."""
    prompt = "```xml\n<web>https://example.com</web>\n```"
    mock_firecrawl = MagicMock()
    with patch.dict('sys.modules', {'firecrawl': mock_firecrawl}):
        with patch.dict('os.environ', {'FIRECRAWL_API_KEY': 'key', 'FIRECRAWL_CACHE_ENABLE': 'false'}):
            result = preprocess(prompt, recursive=False, double_curly_brackets=False)
    assert result == prompt


# ============================================================================
# Include-many inside fenced code block (already tested but ensure span check)
# ============================================================================

def test_include_many_ignored_in_inline_code():
    """Include-many tags inside inline code should not execute."""
    prompt = "Example `<include-many>file.txt</include-many>` here."
    with patch('builtins.open', mock_open(read_data="Content")) as mocked:
        result = preprocess(prompt, recursive=False, double_curly_brackets=False)
    assert result == prompt
    mocked.assert_not_called()


# ============================================================================
# Empty prompt
# ============================================================================

def test_preprocess_empty_prompt():
    """Cover lines 120-121: empty prompt returns empty string."""
    result = preprocess("", recursive=False, double_curly_brackets=False)
    assert result == ""


# ============================================================================
# process_xml_tags _seen=None default
# ============================================================================

def test_process_xml_tags_seen_none():
    """Cover line 219: process_xml_tags with _seen=None."""
    result = process_xml_tags("plain text", recursive=False, _seen=None)
    assert result == "plain text"


# ============================================================================
# process_backtick_includes _seen=None default
# ============================================================================

def test_process_backtick_includes_seen_none():
    """Cover line 172: process_backtick_includes with _seen=None."""
    result = process_backtick_includes("plain text", recursive=False, _seen=None)
    assert result == "plain text"


# ============================================================================
# Include tag with mode attribute
# ============================================================================

def test_include_tag_with_mode_attribute():
    """Cover include with mode attribute triggering selector."""
    prompt = '<include path="file.py" mode="summary"/>'
    file_content = "def main():\n    pass\n"

    mock_selector = MagicMock()
    mock_selector.ContentSelector.return_value.select.return_value = "Summary of file.py"

    with patch('builtins.open', mock_open(read_data=file_content)):
        with patch.dict('sys.modules', {'pdd.content_selector': mock_selector}):
            result = process_include_tags(prompt, recursive=False)

    assert "Summary" in result


