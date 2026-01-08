import re
import os
from pathlib import Path
from typing import List, Optional, Pattern

# =============================================================================
# Constants & Regex Patterns
# =============================================================================

# Pre-compiled regex patterns for performance
# Matches <tag>content</tag> or <tag ...>content</tag>
# Uses non-greedy matching (.*?) for content to handle multiple tags on one line/file
TAG_PATTERN_TEMPLATE = r"<{tag}(?:\s+[^>]*)?>(.*?)</{tag}>"

# Specific PDD tag names
TAG_INCLUDE = "include"
TAG_WEB = "web"
TAG_SHELL = "shell"

# Heuristic patterns for code detection
# Matches lines starting with common keywords or significant indentation
# Added \b to ensure we don't match words like "form" (for) or "classy" (class)
CODE_LINE_PATTERN = re.compile(
    r"^\s*(?:(?:def|class|import|from|var|const|let|function|return|if|else|elif|for|while|try|except|finally|switch|case|public|private|protected)\b|@|{|}|<script|<style)",
    re.MULTILINE
)

# Matches lines that look like standard natural language (Start with Capital, end with punctuation)
TEXT_LINE_PATTERN = re.compile(
    r"^\s*[A-Z].*[.?!:]\s*$",
    re.MULTILINE
)


# =============================================================================
# File I/O
# =============================================================================

def read_file_content(path: str) -> str:
    """
    Reads the content of a file, normalizing line endings and handling encoding.

    Args:
        path (str): The file path to read.

    Returns:
        str: The content of the file.

    Raises:
        FileNotFoundError: If the file does not exist.
        PermissionError: If the file cannot be accessed.
        IOError: For other I/O related errors.
    """
    file_path = Path(path)
    
    if not file_path.exists():
        raise FileNotFoundError(f"The file at {path} was not found.")
    
    if not file_path.is_file():
        raise IOError(f"The path {path} exists but is not a file.")

    # Open with utf-8, replacing errors to prevent crashing on binary snippets
    with open(file_path, mode='r', encoding='utf-8', errors='replace') as f:
        content = f.read()

    return normalize_text(content)


# =============================================================================
# Text Normalization
# =============================================================================

def normalize_text(text: str) -> str:
    """
    Normalizes text by unifying newline characters and stripping trailing whitespace
    from individual lines.

    Args:
        text (str): The raw input text.

    Returns:
        str: The normalized text.

    """
    # Unify newlines to \n
    text = text.replace('\r\n', '\n').replace('\r', '\n')
    
    # Strip trailing whitespace from each line
    lines = [line.rstrip() for line in text.split('\n')]
    
    return '\n'.join(lines)


# =============================================================================
# Tag Detection & Extraction
# =============================================================================

def _get_tag_regex(tag_name: str) -> Pattern:
    """
    Generates and compiles a regex pattern for a specific XML-like tag.
    Flags: DOTALL (dot matches newline) and IGNORECASE.
    """
    pattern_str = TAG_PATTERN_TEMPLATE.format(tag=re.escape(tag_name))
    return re.compile(pattern_str, re.DOTALL | re.IGNORECASE)


def extract_tag_content(text: str, tag_name: str) -> List[str]:
    """
    Extracts the inner content of all occurrences of a specific tag.

    Args:
        text (str): The text to search.
        tag_name (str): The name of the tag (e.g., 'include', 'web').

    Returns:
        List[str]: A list of strings found inside the tags.
    """
    pattern = _get_tag_regex(tag_name)
    matches = pattern.findall(text)
    # Strip whitespace from extracted content for cleanliness
    return [m.strip() for m in matches]


def count_tags(text: str, tag_name: str) -> int:
    """
    Counts the number of occurrences of a specific tag pair.

    Args:
        text (str): The text to search.
        tag_name (str): The name of the tag.

    Returns:
        int: The count of tags found.
    """
    pattern = _get_tag_regex(tag_name)
    # findall is generally efficient enough for counting in this context
    return len(pattern.findall(text))


# =============================================================================
# Heuristics & Ratios
# =============================================================================

def calculate_code_ratio(text: str) -> float:
    """
    Calculates the ratio of "code-like" lines to total non-empty lines.
    
    This is a heuristic used to detect if a prompt is overly implementation-heavy
    rather than natural language instructions.

    Heuristic:
    - Code lines: Start with keywords (def, class, var), symbols ({, }), or heavy indentation.
    - Text lines: Start with capital letters, end with punctuation.
    
    Args:
        text (str): The content to analyze.

    Returns:
        float: A value between 0.0 (all text) and 1.0 (all code). Returns 0.0 for empty text.
    """
    lines = [line for line in text.split('\n') if line.strip()]
    
    if not lines:
        return 0.0

    code_score = 0
    
    for line in lines:
        # Check for explicit code patterns
        if CODE_LINE_PATTERN.match(line):
            code_score += 1
            continue
            
        # Check for indentation heuristic (4 spaces or 1 tab often implies code block in markdown/text)
        # But we must be careful not to flag standard indented lists as code.
        # We check if it starts with whitespace but NOT a list marker (-, *, 1.)
        stripped = line.lstrip()
        indentation = len(line) - len(stripped)
        is_list_item = stripped.startswith(('-', '*', '+')) or (stripped[:1].isdigit() and stripped[1:2] == '.')
        
        if indentation >= 4 and not is_list_item:
            code_score += 1

    return round(code_score / len(lines), 2)

def find_line_number(text: str, index: int) -> int:
    """
    Calculates the line number (1-based) for a given character index.

    Args:
        text (str): The full text.
        index (int): The 0-based character index.

    Returns:
        int: The 1-based line number.
    """
    return text.count('\n', 0, index) + 1