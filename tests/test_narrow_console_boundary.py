"""
Tests for narrow console boundary bug (Issue #220).

This test file specifically tests the off-by-one boundary error in
sync_animation.py's _draw_connecting_lines_and_arrows() function.

The bug occurs when console_width is narrow enough that box position
calculations result in max_x >= console_width, causing an IndexError
when accessing line_parts[2][i] at line 340.

Root cause:
- Line 331 creates arrays with `console_width` elements (valid indices 0 to console_width-1)
- Lines 288-290 calculate box positions that can reach or exceed `console_width`
- Line 339's loop `for i in range(min_x, max_x + 1)` includes `max_x` in the range
- When `max_x >= console_width`, the loop tries to access an out-of-bounds index

These tests are expected to FAIL until the bug is fixed by clamping
min_x and max_x to valid array bounds:
    min_x = max(min(all_branch_xs), 0)
    max_x = min(max(all_branch_xs), console_width - 1)
"""

import pytest
from unittest.mock import MagicMock

from pdd.sync_animation import (
    AnimationState,
    _draw_connecting_lines_and_arrows,
)


@pytest.fixture
def base_animation_state():
    """Create a basic AnimationState for testing."""
    state = AnimationState(basename="test_module", budget=10.0)
    state.current_function_name = "generate"
    state.frame_count = 0
    return state


class TestNarrowConsoleBoundary:
    """Tests for the narrow console boundary bug (#220)."""

    def test_narrow_console_no_index_error(self, base_animation_state):
        """
        Test that console_width=44 does not cause IndexError.

        This is the primary reproduction case from issue #220.
        With console_width=44, tests_x can reach 44, causing an IndexError
        when accessing line_parts[2][44] (max valid index is 43).
        """
        state = base_animation_state
        console_width = 44

        # This should NOT raise IndexError
        result = _draw_connecting_lines_and_arrows(state, console_width)

        assert result is not None
        assert len(result) == 6  # Should return 6 Text lines
        # Each line should have exactly console_width characters
        for line in result:
            assert len(str(line)) <= console_width

    def test_very_narrow_console_boundary(self, base_animation_state):
        """
        Test that very narrow console (30 columns) does not crash.

        Edge case with even narrower console width.
        """
        state = base_animation_state
        console_width = 30

        # This should NOT raise IndexError
        result = _draw_connecting_lines_and_arrows(state, console_width)

        assert result is not None
        assert len(result) == 6

    def test_minimum_console_width(self, base_animation_state):
        """
        Test extreme minimum console width (20 columns).

        Tests the absolute minimum viable console width.
        """
        state = base_animation_state
        console_width = 20

        # This should NOT raise IndexError
        result = _draw_connecting_lines_and_arrows(state, console_width)

        assert result is not None
        assert len(result) == 6

    def test_exact_boundary_console_width(self, base_animation_state):
        """
        Test console_width=45, which is right at the boundary.

        This tests the threshold where the bug starts to appear.
        """
        state = base_animation_state
        console_width = 45

        # This should NOT raise IndexError
        result = _draw_connecting_lines_and_arrows(state, console_width)

        assert result is not None
        assert len(result) == 6

    def test_standard_console_widths_no_regression(self, base_animation_state):
        """
        Test standard console widths (80, 120, 160) still work.

        Regression test to ensure the fix doesn't break normal widths.
        """
        state = base_animation_state

        for console_width in [80, 120, 160]:
            result = _draw_connecting_lines_and_arrows(state, console_width)
            assert result is not None
            assert len(result) == 6

    def test_all_commands_narrow_console(self, base_animation_state):
        """
        Test all animation commands with narrow console.

        Different commands have different waypoint paths, so all need testing.
        """
        state = base_animation_state
        console_width = 40

        commands = ["generate", "example", "test", "update", "crash", "verify", "fix", "auto-deps", "checking"]

        for cmd in commands:
            state.current_function_name = cmd
            state.frame_count = 0

            # This should NOT raise IndexError for any command
            result = _draw_connecting_lines_and_arrows(state, console_width)
            assert result is not None, f"Command '{cmd}' returned None"
            assert len(result) == 6, f"Command '{cmd}' returned wrong number of lines"

    def test_negative_table_start_scenario(self, base_animation_state):
        """
        Test the specific math scenario that causes the bug.

        With console_width=44 and box_width=20:
        - total_table_width = 64 (exceeds console width)
        - table_start = (44 - 64) // 2 = -10
        - tests_x = -10 + 2*20 + 4 + 10 = 44 (out of bounds)
        """
        state = base_animation_state
        console_width = 44

        # Force specific path_box_content_width to trigger the calculation
        state.path_box_content_width = 16  # This affects box_width calculation

        # This should NOT raise IndexError
        result = _draw_connecting_lines_and_arrows(state, console_width)

        assert result is not None
        assert len(result) == 6

    def test_bidirectional_animation_narrow_console(self, base_animation_state):
        """
        Test bidirectional commands (crash, verify, fix) at narrow width.

        These commands reverse direction based on frame count, testing
        both forward and backward waypoint paths.
        """
        state = base_animation_state
        console_width = 42

        bidirectional_commands = ["crash", "verify", "fix"]

        for cmd in bidirectional_commands:
            state.current_function_name = cmd

            # Test both animation directions
            for frame in [0, 60]:  # frame 0 = forward, frame 60 = reverse
                state.frame_count = frame

                # This should NOT raise IndexError
                result = _draw_connecting_lines_and_arrows(state, console_width)
                assert result is not None, f"Command '{cmd}' at frame {frame} returned None"
                assert len(result) == 6, f"Command '{cmd}' at frame {frame} returned wrong line count"
