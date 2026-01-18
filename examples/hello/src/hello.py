from __future__ import annotations

def hello() -> None:
    """Print a friendly greeting to stdout."""
    print("hello")

if __name__ == "__main__":
    hello()

# Test Suite
import io
import sys
import pytest
from unittest.mock import patch

def test_hello_prints_correct_greeting(capsys):
    """
    Verify that the hello function prints exactly "hello" followed by a newline.
    Using pytest's capsys fixture to capture stdout.
    """
    # Act
    hello()
    
    # Assert
    captured = capsys.readouterr()
    assert captured.out == "hello\n"
    assert captured.err == ""

def test_hello_return_value():
    """
    Verify that the hello function returns None (implicit return).
    """
    # Act
    result = hello()
    
    # Assert
    assert result is None

def test_hello_multiple_calls(capsys):
    """
    Verify that calling the function multiple times produces the expected output multiple times.
    """
    # Act
    hello()
    hello()
    
    # Assert
    captured = capsys.readouterr()
    assert captured.out == "hello\nhello\n"