import os
import pytest
from unittest.mock import patch, mock_open
from pdd.preprocess import preprocess
import subprocess
import importlib
from unittest.mock import MagicMock

# Helper function to mock environment variable
def set_pdd_path(path: str) -> None:
    """Set the PDD_PATH environment variable to the specified path."""
    os.environ['PDD_PATH'] = path

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

# Test for doubling curly brackets
def test_double_curly_brackets() -> None:
    """Test doubling of curly brackets."""
    prompt = "This is a test {key}"
    expected_output = "This is a test {{key}}"

    assert preprocess(prompt, recursive=False, double_curly_brackets=True) == expected_output

# Test for excluding keys from doubling curly brackets
def test_exclude_keys_from_doubling() -> None:
    """Test excluding specific keys from doubling curly brackets."""
    prompt = "This is a test {key} and {exclude} {}"
    expected_output = "This is a test {{key}} and {exclude} {{}}"

    assert preprocess(prompt, recursive=False, double_curly_brackets=True, exclude_keys=['exclude']) == expected_output

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

# Test for handling file not found
def test_file_not_found() -> None:
    """Test handling of file not found error."""
    set_pdd_path('/mock/path')
    prompt = "This is a test ```<missing_file.txt>```"
    expected_output = "This is a test ```<missing_file.txt>```"

    with patch('builtins.open', side_effect=FileNotFoundError):
        assert preprocess(prompt, recursive=False, double_curly_brackets=False) == expected_output

# Test for handling shell command error
def test_shell_command_error() -> None:
    """Test handling of shell command error."""
    prompt = "This is a test <shell>invalid_command</shell>"
    expected_output = "This is a test Error: Command 'invalid_command' returned non-zero exit status 1."

    with patch('subprocess.run', side_effect=subprocess.CalledProcessError(1, 'invalid_command')):
        assert preprocess(prompt, recursive=False, double_curly_brackets=False) == expected_output

# Ensure to clean up the environment variable after tests
def teardown_module(module) -> None:
    """Clean up the environment variable after tests."""
    if 'PDD_PATH' in os.environ:
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
def test_process_xml_web_tag() -> None:
    """Test processing of XML-like web tags."""
    mock_markdown_content = "# Webpage Content\n\nThis is the scraped content."
    prompt = "This is a test <web>https://example.com</web>"
    expected_output = f"This is a test {mock_markdown_content}"

    # Create a mock FirecrawlApp class
    mock_firecrawl_app = MagicMock()
    mock_instance = mock_firecrawl_app.return_value
    mock_instance.scrape_url.return_value = {'markdown': mock_markdown_content}
    
    # Patch the import
    with patch.dict('sys.modules', {'firecrawl': MagicMock()}):
        with patch('builtins.__import__', side_effect=lambda name, *args: 
              MagicMock(FirecrawlApp=mock_firecrawl_app) if name == 'firecrawl' else importlib.__import__(name, *args)):
            # Mock the environment variable for API key
            with patch.dict('os.environ', {'FIRECRAWL_API_KEY': 'fake_api_key'}):
                result = preprocess(prompt, recursive=False, double_curly_brackets=False)
                assert result == expected_output

# Test for handling missing Firecrawl API key
def test_process_xml_web_tag_missing_api_key() -> None:
    """Test handling of missing Firecrawl API key."""
    prompt = "This is a test <web>https://example.com</web>"
    expected_output = "This is a test [Error: FIRECRAWL_API_KEY not set. Cannot scrape https://example.com]"

    # Create a mock FirecrawlApp class
    mock_firecrawl_app = MagicMock()
    
    # Patch the import
    with patch.dict('sys.modules', {'firecrawl': MagicMock()}):
        with patch('builtins.__import__', side_effect=lambda name, *args: 
              MagicMock(FirecrawlApp=mock_firecrawl_app) if name == 'firecrawl' else importlib.__import__(name, *args)):
            # Ensure the API key environment variable is not set
            with patch.dict('os.environ', {}, clear=True):
                result = preprocess(prompt, recursive=False, double_curly_brackets=False)
                assert result == expected_output

# Test for handling Firecrawl import error
def test_process_xml_web_tag_import_error() -> None:
    """Test handling of Firecrawl import error."""
    prompt = "This is a test <web>https://example.com</web>"
    expected_output = "This is a test [Error: firecrawl-py package not installed. Cannot scrape https://example.com]"

    # Patch the import to raise ImportError
    with patch('builtins.__import__', side_effect=lambda name, *args: 
          raise_import_error(name) if name == 'firecrawl' else importlib.__import__(name, *args)):
        result = preprocess(prompt, recursive=False, double_curly_brackets=False)
        assert result == expected_output

def raise_import_error(name):
    raise ImportError(f"No module named '{name}'")

# Test for handling empty markdown content
def test_process_xml_web_tag_empty_content() -> None:
    """Test handling of empty markdown content from Firecrawl."""
    prompt = "This is a test <web>https://example.com</web>"
    expected_output = "This is a test [No content available for https://example.com]"

    # Create a mock FirecrawlApp class that returns empty response
    mock_firecrawl_app = MagicMock()
    mock_instance = mock_firecrawl_app.return_value
    mock_instance.scrape_url.return_value = {}  # No markdown key
    
    # Patch the import
    with patch.dict('sys.modules', {'firecrawl': MagicMock()}):
        with patch('builtins.__import__', side_effect=lambda name, *args: 
              MagicMock(FirecrawlApp=mock_firecrawl_app) if name == 'firecrawl' else importlib.__import__(name, *args)):
            with patch.dict('os.environ', {'FIRECRAWL_API_KEY': 'fake_api_key'}):
                result = preprocess(prompt, recursive=False, double_curly_brackets=False)
                assert result == expected_output

# Test for handling Firecrawl API error
def test_process_xml_web_tag_scraping_error() -> None:
    """Test handling of Firecrawl API error."""
    prompt = "This is a test <web>https://example.com</web>"
    error_message = "API request failed"
    expected_output = f"This is a test [Web scraping error: {error_message}]"

    # Create a mock FirecrawlApp class that raises an exception
    mock_firecrawl_app = MagicMock()
    mock_instance = mock_firecrawl_app.return_value
    mock_instance.scrape_url.side_effect = Exception(error_message)
    
    # Patch the import
    with patch.dict('sys.modules', {'firecrawl': MagicMock()}):
        with patch('builtins.__import__', side_effect=lambda name, *args: 
              MagicMock(FirecrawlApp=mock_firecrawl_app) if name == 'firecrawl' else importlib.__import__(name, *args)):
            with patch.dict('os.environ', {'FIRECRAWL_API_KEY': 'fake_api_key'}):
                result = preprocess(prompt, recursive=False, double_curly_brackets=False)
                assert result == expected_output

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
    """Test mix of excluded and nested brackets."""
    prompt = "Mix of {excluded{inner}} nesting"
    result = preprocess(prompt, recursive=False, double_curly_brackets=True, exclude_keys=["excluded"])
    assert result == "Mix of {excluded{{inner}}} nesting"
