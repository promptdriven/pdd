"""Context-compression reporting for CLI execution summaries (issue #877)."""

from __future__ import annotations

import os
from typing import Any

_FALLBACK_EVENTS: list[str] = []


class CompressionFallbackError(Exception):
    """Raised when selector/compression fails and ``compression_fallback`` is ``error``."""


def clear_compression_fallback_events() -> None:
    """Reset per-invocation fallback events (call at CLI entry)."""
    _FALLBACK_EVENTS.clear()


def record_compression_fallback(message: str) -> None:
    """Record a selector/compression fallback for the execution summary."""
    if message and message not in _FALLBACK_EVENTS:
        _FALLBACK_EVENTS.append(message)


def read_active_compression_settings() -> dict[str, Any]:
    """Read effective compression flags from process environment."""
    context_compression = os.environ.get("PDD_CONTEXT_COMPRESSION", "") or "off"
    return {
        "context_compression": context_compression,
        "compress_examples": os.environ.get("PDD_COMPRESS_EXAMPLES") == "1",
        "compress_test_context": os.environ.get("PDD_COMPRESS_TEST_CONTEXT") == "1",
        "compression_fallback": os.environ.get("PDD_COMPRESSION_FALLBACK", "full") or "full",
    }


def format_compression_summary_lines() -> list[str]:
    """Lines for the command execution summary."""
    settings = read_active_compression_settings()
    lines: list[str] = []

    active_parts: list[str] = []
    mode = str(settings["context_compression"])
    if mode.lower() not in ("", "off"):
        active_parts.append(f"context-compression={mode}")
    if settings["compress_examples"]:
        active_parts.append("compress-examples")
    if settings["compress_test_context"]:
        active_parts.append("compress-test-context")

    if active_parts:
        lines.append(
            "  Context compression active: "
            f"{', '.join(active_parts)}; fallback policy: {settings['compression_fallback']}"
        )
    else:
        lines.append(
            f"  Context compression: off; fallback policy: {settings['compression_fallback']}"
        )

    for event in _FALLBACK_EVENTS:
        lines.append(f"  Compression fallback triggered: {event}")

    return lines
