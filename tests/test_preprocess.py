import pytest
from unittest.mock import patch, mock_open
from pdd.preprocess import preprocess, process_backtick_includes, process_xml_tags, double_curly
from bs4 import BeautifulSoup
import subprocess

@pytest.fixture
def sample_prompt() -> str:
    """Fixture providing a sample prompt for testing."""
    return """
    Here's an include: ```<sample.txt>```
    <include>another_file.txt</include>
    <pdd>This is a comment that will be removed</pdd>
    <shell>echo "Hello, World!"</shell>
    This is a {variable} that will be doubled.
    """

@patch('builtins.open', new_callable=mock_open, read_data="Included content")
@patch('subprocess.run')
def test_preprocess(mock_subprocess_run, mock_file, sample_prompt: str) -> None:
    """Test the preprocess function with a sample prompt."""
    mock_subprocess_run.return_value.stdout = "Hello, World!"

    result = preprocess(sample_prompt)

    assert "```Included content```" in result
    assert "Included content" in result  # For XML include
    assert "This is a comment that will be removed" not in result
    assert "Hello, World!" in result
    assert "This is a {{variable}} that will be doubled." in result

def test_process_backtick_includes() -> None:
    """Test processing of backtick includes."""
    text = "Test ```<file.txt>``` content"
    with patch('builtins.open', new_callable=mock_open, read_data="Included text"):
        result = process_backtick_includes(text, False)
    assert result == "Test ```Included text``` content"

def test_process_xml_tags() -> None:
    """Test processing of XML tags."""
    xml = "<include>file.txt</include><pdd>Comment</pdd><shell>echo 'Test'</shell>"
    soup = BeautifulSoup(xml, 'html.parser')
    
    with patch('builtins.open', new_callable=mock_open, read_data="Included content"):
        with patch('subprocess.run') as mock_run:
            mock_run.return_value.stdout = "Test output"
            result = process_xml_tags(soup, False)

    assert "Included content" in result
    assert "Comment" not in result
    assert "Test output" in result

def test_double_curly() -> None:
    """Test doubling of curly brackets."""
    text = "This is a {test} with {curly} brackets"
    result = double_curly(text)
    assert result == "This is a {{test}} with {{curly}} brackets"

def test_recursive_processing() -> None:
    """Test recursive processing of includes."""
    nested_prompt = "```<outer.txt>```"
    outer_content = "Outer content ```<inner.txt>```"
    inner_content = "Inner content"

    with patch('builtins.open') as mock_open:
        mock_open.side_effect = [
            mock_open(read_data=outer_content).return_value,
            mock_open(read_data=inner_content).return_value
        ]
        result = preprocess(nested_prompt, recursive=True)

    assert "Outer content ```Inner content```" in result

def test_non_recursive_processing() -> None:
    """Test non-recursive processing of includes."""
    nested_prompt = "```<outer.txt>```"
    outer_content = "Outer content ```<inner.txt>```"

    with patch('builtins.open', new_callable=mock_open, read_data=outer_content):
        result = preprocess(nested_prompt, recursive=False)

    assert "Outer content ```<inner.txt>```" in result

def test_no_double_curly_brackets() -> None:
    """Test processing without doubling curly brackets."""
    prompt = "This is a {test} prompt"
    result = preprocess(prompt, double_curly_brackets=False)
    assert result == "This is a {test} prompt"

def test_file_not_found() -> None:
    """Test handling of file not found error."""
    prompt = "```<nonexistent.txt>```"
    with pytest.raises(FileNotFoundError):
        preprocess(prompt)

def test_shell_command_error() -> None:
    """Test handling of shell command error."""
    prompt = "<shell>invalid_command</shell>"
    with patch('subprocess.run', side_effect=subprocess.CalledProcessError(1, 'invalid_command')):
        with pytest.raises(subprocess.CalledProcessError):
            preprocess(prompt)
