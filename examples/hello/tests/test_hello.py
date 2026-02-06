"""Tests for hello module.

Verifies behavior defined in hello_python.prompt:
- A python function 'hello' that prints "hello"
"""

from io import StringIO
from unittest.mock import patch

import sys
import os

sys.path.insert(0, os.path.join(os.path.dirname(__file__), "..", "src"))

from hello import hello


def test_hello_prints_hello():
    """Test that hello() prints exactly 'hello'."""
    with patch("sys.stdout", new_callable=StringIO) as mock_stdout:
        hello()
    assert mock_stdout.getvalue() == "hello\n"


def test_hello_returns_none():
    """Test that hello() returns None."""
    result = hello()
    assert result is None
