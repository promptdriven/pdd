"""
Tests for ThreadSafeRedirector and TUIStdoutWrapper in sync_tui.py.

These tests verify:
1. TUIStdoutWrapper.isatty() returns True (so Rich uses \r mode)
2. ThreadSafeRedirector properly handles \r for progress bar suppression
3. Normal newline behavior is preserved
"""
from typing import List
from unittest.mock import MagicMock

import pytest
from rich.console import Console

import pdd.sync_tui as sync_tui
from pdd.sync_tui import ThreadSafeRedirector, TUIStdoutWrapper


class MockRichLog:
    """Mock RichLog widget that captures written content."""

    def __init__(self):
        self.written_lines: List[str] = []
        self.written_texts: List[object] = []

    def write(self, text):
        """Capture the plain text content."""
        if hasattr(text, 'plain'):
            self.written_texts.append(text)
            self.written_lines.append(text.plain)
        else:
            self.written_lines.append(str(text))


class MockApp:
    """Mock Textual App that executes callbacks immediately."""

    def call_from_thread(self, callback, *args, **kwargs):
        """Execute callback immediately instead of scheduling."""
        callback(*args, **kwargs)


@pytest.fixture
def mock_log():
    """Create a mock RichLog widget."""
    return MockRichLog()


@pytest.fixture
def mock_app():
    """Create a mock Textual App."""
    return MockApp()


@pytest.fixture
def redirector(mock_app, mock_log):
    """Create a ThreadSafeRedirector with mocked dependencies."""
    return ThreadSafeRedirector(mock_app, mock_log)


@pytest.fixture
def captured_lines(mock_log):
    """Return the captured lines from the mock log."""
    return mock_log.written_lines


@pytest.fixture
def captured_texts(mock_log):
    """Return the captured Rich Text objects from the mock log."""
    return mock_log.written_texts


# =============================================================================
# Test 1: TUIStdoutWrapper.isatty() returns False (default behavior)
# =============================================================================

def test_tui_stdout_wrapper_isatty():
    """TUIStdoutWrapper.isatty() should return False (default from io.TextIOBase).

    We no longer need isatty() to return True because:
    1. Progress is shown via Textual's native ProgressBar widget
    2. Rich's track() is disabled in TUI context via COLUMNS env var check
    """
    mock_redirector = MagicMock()
    mock_stdin = MagicMock()

    wrapper = TUIStdoutWrapper(mock_redirector, mock_stdin)

    # Default behavior from io.TextIOBase is False
    assert wrapper.isatty() == False


# =============================================================================
# Test 2: Carriage return handling - suppress intermediate updates
# =============================================================================

def test_carriage_return_suppresses_intermediate(redirector, captured_lines):
    """Progress updates using \\r should be suppressed until final \\n."""
    # Simulate progress bar output: "Progress: 1/3\r" then "Progress: 2/3\r" then "Progress: 3/3\n"
    redirector.write("Progress: 1/3\r")
    redirector.write("Progress: 2/3\r")
    redirector.write("Progress: 3/3\n")

    # Should only output ONE line (the final one), not three
    assert len(captured_lines) == 1
    # Must be EXACTLY "Progress: 3/3", not containing earlier updates
    assert captured_lines[0] == "Progress: 3/3"
    assert "1/3" not in captured_lines[0]
    assert "2/3" not in captured_lines[0]


# =============================================================================
# Test 3: Normal newline behavior should be unchanged
# =============================================================================

def test_newline_outputs_line(redirector, captured_lines):
    """Normal output with newlines should work as before."""
    redirector.write("Line 1\n")
    redirector.write("Line 2\n")

    assert len(captured_lines) == 2
    assert "Line 1" in captured_lines[0]
    assert "Line 2" in captured_lines[1]


# =============================================================================
# Test 4: Mixed \r and \n output
# =============================================================================

def test_mixed_cr_and_newline(redirector, captured_lines):
    """Test output with both \\r and \\n."""
    redirector.write("Starting...\n")
    redirector.write("Progress: 1/2\r")
    redirector.write("Progress: 2/2\n")
    redirector.write("Done!\n")

    assert len(captured_lines) == 3
    assert "Starting" in captured_lines[0]
    assert "Progress: 2/2" in captured_lines[1]
    assert "Done" in captured_lines[2]


# =============================================================================
# Test 5: \r within a line (edge case)
# =============================================================================

def test_cr_within_line(redirector, captured_lines):
    """Content before \\r in same line should be discarded."""
    redirector.write("Old text\rNew text\n")

    assert len(captured_lines) == 1
    assert captured_lines[0] == "New text"
    assert "Old text" not in captured_lines[0]


# =============================================================================
# Test 6: Multiple \r in same write
# =============================================================================

def test_multiple_cr_in_single_write(redirector, captured_lines):
    """Multiple \\r characters in a single write should keep only last segment."""
    redirector.write("First\rSecond\rThird\n")

    assert len(captured_lines) == 1
    assert captured_lines[0] == "Third"


# =============================================================================
# Test 7: Empty writes should be handled gracefully
# =============================================================================

def test_empty_write(redirector, captured_lines):
    """Empty writes should not cause errors."""
    result = redirector.write("")
    assert result == 0
    assert len(captured_lines) == 0


def test_none_like_empty(redirector, captured_lines):
    """Write should handle empty string."""
    redirector.write("")
    redirector.write("Hello\n")
    assert len(captured_lines) == 1
    assert captured_lines[0] == "Hello"


# =============================================================================
# Test 8: Partial writes (buffering)
# =============================================================================

def test_partial_writes_buffered(redirector, captured_lines):
    """Partial writes without newline should be buffered."""
    redirector.write("Hello ")
    redirector.write("World")
    assert len(captured_lines) == 0  # Nothing output yet

    redirector.write("!\n")
    assert len(captured_lines) == 1
    assert captured_lines[0] == "Hello World!"


# =============================================================================
# Test 9: ANSI codes should be preserved
# =============================================================================

def test_ansi_codes_preserved(redirector, captured_lines):
    """ANSI escape codes should be processed (converted to Rich Text)."""
    # Write text with ANSI color codes
    redirector.write("\x1b[32mGreen text\x1b[0m\n")

    assert len(captured_lines) == 1
    # The ANSI codes get converted to Rich Text, plain text should be just "Green text"
    assert "Green text" in captured_lines[0]


def test_rich_printed_ansi_output_does_not_show_escape_fragments(redirector, captured_lines):
    """ANSI output printed through Rich should not display raw escape fragments."""
    console = Console(
        file=redirector,
        force_terminal=True,
        color_system="standard",
        highlight=True,
        width=80,
    )

    console.print("\x1b[90mhello\x1b[0m")
    console.print("\x1b[36m\x1b[1mcyan-bold\x1b[39;49;00m")

    assert captured_lines == ["hello", "cyan-bold"]


def test_rich_printed_ansi_preserves_existing_rich_styles(redirector, captured_texts):
    """Reparsing highlighted ANSI should keep non-ANSI Rich styles on the line."""
    console = Console(
        file=redirector,
        force_terminal=True,
        color_system="standard",
        highlight=True,
        width=80,
    )

    console.print("[bold]prefix[/bold] \x1b[90mhello\x1b[0m")

    text = captured_texts[0]
    assert text.plain == "prefix hello"
    assert any(
        span.start <= 0 and span.end >= len("prefix") and span.style.bold
        for span in text.spans
    )
    assert any(
        span.start <= len("prefix ") and span.end >= len("prefix hello")
        and getattr(span.style.color, "number", None) == 8
        for span in text.spans
    )


def test_rich_printed_ansi_reset_preserves_outer_suffix_style(
    redirector,
    captured_texts,
):
    """Nested ANSI reset should not truncate an outer Rich style span."""
    console = Console(
        file=redirector,
        force_terminal=True,
        color_system="standard",
        highlight=True,
        width=80,
    )

    console.print("[dim]\x1b[31mFAIL\x1b[0m after[/dim]")

    text = captured_texts[0]
    assert text.plain == "FAIL after"
    assert any(
        span.start <= len("FAIL ") and span.end >= len("FAIL after")
        and span.style.dim
        for span in text.spans
    )


def test_rich_highlighter_style_not_replayed_for_256_color_csi(
    redirector,
    captured_texts,
):
    """Rich highlighter SGR should not become part of restored CSI style."""
    console = Console(
        file=redirector,
        force_terminal=True,
        color_system="standard",
        highlight=True,
        width=80,
    )

    console.print("\x1b[38;5;196mRED\x1b[0m after")

    text = captured_texts[0]
    assert text.plain == "RED after"
    assert any(
        span.start <= 0 and span.end >= len("RED")
        and getattr(span.style.color, "number", None) == 196
        for span in text.spans
    )
    assert not any(span.style.bold for span in text.spans)


def test_rich_highlighter_style_not_replayed_after_osc_title(
    redirector,
    captured_texts,
):
    """Restoring highlighted OSC should not style following visible text."""
    console = Console(
        file=redirector,
        force_terminal=True,
        color_system="standard",
        highlight=True,
        width=80,
    )

    console.print("pre\x1b]0;title\x1b\\post after")

    text = captured_texts[0]
    assert text.plain == "prepost after"
    assert not any(
        span.start < len("prepost after")
        and span.end > len("pre")
        and (span.style.bold or span.style.underline)
        for span in text.spans
    )


def test_rich_printed_osc_and_csi_preserve_styles(redirector, captured_texts):
    """OSC hyperlinks and CSI color should not leak or drop existing Rich styles."""
    console = Console(
        file=redirector,
        force_terminal=True,
        color_system="standard",
        highlight=True,
        width=80,
    )
    osc_link = "\x1b]8;;https://example.com\x1b\\link\x1b]8;;\x1b\\"

    console.print("[bold]prefix[/bold] " + osc_link + " \x1b[90mhello\x1b[0m")

    text = captured_texts[0]
    assert text.plain == "prefix link hello"
    assert any(
        span.start <= 0 and span.end >= len("prefix") and span.style.bold
        for span in text.spans
    )
    assert any(
        span.start <= len("prefix ") and span.end >= len("prefix link")
        and span.style.link == "https://example.com"
        for span in text.spans
    )
    assert any(
        span.start <= len("prefix link ") and span.end >= len("prefix link hello")
        and getattr(span.style.color, "number", None) == 8
        for span in text.spans
    )


def test_direct_bel_terminated_osc_does_not_leak_payload(redirector, captured_lines):
    """BEL-terminated OSC sequences should be stripped from direct output."""
    redirector.write("pre\x1b]0;mytitle\x07post\n")

    assert captured_lines == ["prepost"]


@pytest.mark.parametrize(
    "sequence",
    [
        "pre\x1bP1;payload\x1b\\post",
        "pre\x1bXpayload\x1b\\post",
        "pre\x1b^payload\x1b\\post",
        "pre\x1b_payload\x1b\\post",
        "pre\x90payload\x9cpost",
    ],
    ids=[
        "esc-dcs",
        "esc-sos",
        "esc-pm",
        "esc-apc",
        "c1-dcs",
    ],
)
def test_string_control_payloads_do_not_leak(sequence, redirector, captured_lines):
    """DCS/SOS/PM/APC and C1 string-control payloads should be stripped."""
    redirector.write(sequence + "\n")

    assert captured_lines == ["prepost"]


@pytest.mark.parametrize(
    "sequence",
    [
        "pre\x1bcpost",
        "pre\x1b#8post",
        "pre\x1b%Gpost",
        "pre\x1b Fpost",
        "pre\x1b Gpost",
        "pre\x9b?25lpost",
    ],
    ids=[
        "esc-ris",
        "esc-screen-alignment",
        "esc-utf8-designate",
        "esc-sp-f",
        "esc-sp-g",
        "c1-csi",
    ],
)
def test_ecma48_controls_do_not_leak(sequence, redirector, captured_lines):
    """Valid ESC/C1 controls should not reach the log as raw text."""
    redirector.write(sequence + "\n")

    assert captured_lines == ["prepost"]


@pytest.mark.parametrize(
    "sequence",
    [
        "pre\x1b]0;payload\x1b[31mRED\x1b[0mpost",
        "pre\x1bPpayload\x1b[31mRED\x1b[0mpost",
    ],
    ids=["osc-interrupted-by-csi", "dcs-interrupted-by-csi"],
)
def test_interrupted_string_control_payloads_do_not_leak(
    sequence,
    redirector,
    captured_lines,
):
    """String-control payload before an interrupting ESC should be stripped."""
    redirector.write(sequence + "\n")

    assert captured_lines == ["preREDpost"]


@pytest.mark.parametrize(
    ("start", "end"),
    [
        ("\x1b]0;title", "\x1b\\"),
        ("\x1bPpayload", "\x1b\\"),
        ("\x90payload", "\x9c"),
    ],
    ids=["osc-st", "dcs-st", "c1-dcs-st"],
)
def test_string_control_payloads_can_span_newlines(
    start,
    end,
    redirector,
    captured_lines,
):
    """Newlines inside string controls should not flush hidden payload."""
    redirector.write("pre" + start + "\n")
    assert captured_lines == []

    redirector.write("more" + end + "post\n")

    assert captured_lines == ["prepost"]


def test_rich_printed_non_csi_escape_preserves_styles(redirector, captured_texts):
    """Non-CSI escape controls should be stripped without dropping Rich styles."""
    console = Console(
        file=redirector,
        force_terminal=True,
        color_system="standard",
        highlight=True,
        width=80,
    )

    console.print("[bold]prefix[/bold] \x1b(Btail")

    text = captured_texts[0]
    assert text.plain == "prefix tail"
    assert any(
        span.start <= 0 and span.end >= len("prefix") and span.style.bold
        for span in text.spans
    )


def test_rich_printed_charset_selector_sibling_preserves_styles(redirector, captured_texts):
    """Charset selector siblings such as ESC)0 should not leak raw escape text."""
    console = Console(
        file=redirector,
        force_terminal=True,
        color_system="standard",
        highlight=True,
        width=80,
    )

    console.print("[bold]prefix[/bold] \x1b)0tail")

    text = captured_texts[0]
    assert text.plain == "prefix tail"
    assert any(
        span.start <= 0 and span.end >= len("prefix") and span.style.bold
        for span in text.spans
    )


def test_malformed_highlighted_ansi_restore_advances_linearly(monkeypatch):
    """Malformed highlighted OSC/CSI candidates should not rescan suffixes."""
    malformed_osc = "\x1b\x1b[1m]\x1b[0m8;;unterminated"
    malformed_csi = "\x1b\x1b[1m[\x1b[0m999"
    repeat_count = 20
    malformed = (malformed_osc + malformed_csi) * repeat_count
    calls = 0
    original_skip = sync_tui._skip_sgr_sequences

    def counting_skip(text, start):
        nonlocal calls
        calls += 1
        return original_skip(text, start)

    monkeypatch.setattr(sync_tui, "_skip_sgr_sequences", counting_skip)

    sync_tui._restore_rich_highlighted_ansi(malformed)

    assert calls <= repeat_count * 20


def test_malformed_osc_span_mapping_avoids_regex_rescan(monkeypatch):
    """Fallback span mapping should scan malformed OSC fragments once."""
    malformed = "\x1b]8;;unterminated"
    repeat_count = 20
    plain = "prefix " + malformed * repeat_count + " suffix"
    original = sync_tui.Text(plain)
    reparsed = sync_tui.Text(plain)
    calls = 0
    original_scan = sync_tui._scan_ansi_token

    def counting_scan(text, start):
        nonlocal calls
        calls += 1
        return original_scan(text, start)

    monkeypatch.setattr(sync_tui, "_scan_ansi_token", counting_scan)

    merged = sync_tui._merge_reparsed_ansi_spans(original, reparsed)

    assert merged.plain == plain
    assert calls <= repeat_count * 2
