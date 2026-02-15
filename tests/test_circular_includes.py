"""
Tests for circular <include> detection in pdd/preprocess.py (Issue #521).

The preprocessor has no cycle detection — circular includes recurse ~82 times
until Python's recursion limit, then the broad `except Exception` swallows
the RecursionError and returns corrupted output with exit code 0.

These tests verify that circular includes produce an error (exception or
error marker in output), NOT silently corrupted content.
"""

import os
import pytest
from unittest.mock import patch, mock_open, MagicMock
from pdd.preprocess import preprocess

# Store original so we can restore
_original_pdd_path = os.environ.get('PDD_PATH')


def set_pdd_path(path: str) -> None:
    os.environ['PDD_PATH'] = path


def _make_mock_open(file_map: dict):
    """Create a mock open that returns content based on filename."""
    def side_effect(file_name, *args, **kwargs):
        mock_file = MagicMock()
        for key, content in file_map.items():
            if key in str(file_name):
                mock_file.read.return_value = content
                mock_file.__enter__ = lambda s: s
                mock_file.__exit__ = MagicMock(return_value=False)
                return mock_file
        raise FileNotFoundError(f"No mock for {file_name}")
    return side_effect


class TestCircularIncludes:
    """Issue #521: Circular <include> tags must be detected, not silently expanded."""

    def setup_method(self):
        set_pdd_path('/mock/path')

    def teardown_method(self):
        if _original_pdd_path is not None:
            os.environ['PDD_PATH'] = _original_pdd_path
        elif 'PDD_PATH' in os.environ:
            del os.environ['PDD_PATH']

    def test_circular_xml_includes_must_error(self):
        """A→B→A circular include must raise or return error, not silently corrupt."""
        file_map = {
            'a.txt': 'Hello\n<include>b.txt</include>',
            'b.txt': 'World\n<include>a.txt</include>',
        }
        with patch('builtins.open', mock_open()) as m:
            m.side_effect = _make_mock_open(file_map)

            # The bug: preprocess silently returns corrupted output with
            # "Hello" repeated ~82 times. A correct implementation must
            # either raise an error OR return output containing an error marker.
            try:
                result = preprocess(
                    '<include>a.txt</include>',
                    recursive=True,
                    double_curly_brackets=False,
                )
            except (RecursionError, ValueError, RuntimeError):
                # Any of these exceptions is acceptable — cycle was detected
                return

            # If no exception, the output must NOT contain duplicated content.
            # The buggy behavior produces "Hello" 82+ times.
            hello_count = result.count('Hello')
            world_count = result.count('World')
            assert hello_count <= 2 and world_count <= 2, (
                f"Circular include silently produced corrupted output: "
                f"'Hello' appeared {hello_count} times, 'World' appeared {world_count} times. "
                f"Expected an error or at most 2 occurrences each."
            )

    def test_circular_backtick_includes_must_error(self):
        """Circular backtick-style includes must also be detected."""
        file_map = {
            'x.txt': 'Foo\n```<y.txt>```',
            'y.txt': 'Bar\n```<x.txt>```',
        }
        with patch('builtins.open', mock_open()) as m:
            m.side_effect = _make_mock_open(file_map)

            try:
                result = preprocess(
                    '```<x.txt>```',
                    recursive=True,
                    double_curly_brackets=False,
                )
            except (RecursionError, ValueError, RuntimeError):
                return

            foo_count = result.count('Foo')
            bar_count = result.count('Bar')
            assert foo_count <= 2 and bar_count <= 2, (
                f"Circular backtick include silently produced corrupted output: "
                f"'Foo' appeared {foo_count} times, 'Bar' appeared {bar_count} times."
            )

    def test_self_referencing_include_must_error(self):
        """A file that includes itself must be detected as circular."""
        file_map = {
            'self.txt': 'Content\n<include>self.txt</include>',
        }
        with patch('builtins.open', mock_open()) as m:
            m.side_effect = _make_mock_open(file_map)

            try:
                result = preprocess(
                    '<include>self.txt</include>',
                    recursive=True,
                    double_curly_brackets=False,
                )
            except (RecursionError, ValueError, RuntimeError):
                return

            content_count = result.count('Content')
            assert content_count <= 2, (
                f"Self-referencing include silently produced corrupted output: "
                f"'Content' appeared {content_count} times."
            )

    def test_three_file_cycle_must_error(self):
        """A→B→C→A three-file cycle must be detected."""
        file_map = {
            'a.txt': 'AAA\n<include>b.txt</include>',
            'b.txt': 'BBB\n<include>c.txt</include>',
            'c.txt': 'CCC\n<include>a.txt</include>',
        }
        with patch('builtins.open', mock_open()) as m:
            m.side_effect = _make_mock_open(file_map)

            try:
                result = preprocess(
                    '<include>a.txt</include>',
                    recursive=True,
                    double_curly_brackets=False,
                )
            except (RecursionError, ValueError, RuntimeError):
                return

            aaa_count = result.count('AAA')
            assert aaa_count <= 2, (
                f"Three-file circular include silently produced corrupted output: "
                f"'AAA' appeared {aaa_count} times."
            )

    def test_non_circular_recursive_includes_still_work(self):
        """Non-circular recursive includes (A→B→C, no cycle) must still work."""
        file_map = {
            'top.txt': 'Top\n<include>mid.txt</include>',
            'mid.txt': 'Mid\n<include>leaf.txt</include>',
            'leaf.txt': 'Leaf',
        }
        with patch('builtins.open', mock_open()) as m:
            m.side_effect = _make_mock_open(file_map)

            result = preprocess(
                '<include>top.txt</include>',
                recursive=True,
                double_curly_brackets=False,
            )

            assert 'Top' in result
            assert 'Mid' in result
            assert 'Leaf' in result

    def test_diamond_includes_not_falsely_flagged(self):
        """Diamond pattern (A→B, A→C, B→D, C→D) is NOT circular and must work."""
        file_map = {
            'a.txt': '<include>b.txt</include>\n<include>c.txt</include>',
            'b.txt': 'B\n<include>d.txt</include>',
            'c.txt': 'C\n<include>d.txt</include>',
            'd.txt': 'Shared',
        }
        with patch('builtins.open', mock_open()) as m:
            m.side_effect = _make_mock_open(file_map)

            result = preprocess(
                '<include>a.txt</include>',
                recursive=True,
                double_curly_brackets=False,
            )

            assert 'B' in result
            assert 'C' in result
            # D is included twice (via B and via C) — that's fine, not circular
            assert result.count('Shared') == 2
