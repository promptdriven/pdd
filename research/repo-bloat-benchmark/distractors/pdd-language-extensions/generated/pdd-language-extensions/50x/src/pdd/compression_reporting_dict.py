"""Context-compression reporting for CLI execution summaries (issue #877)."""

from __future__ import annotations

import os
from typing import Any

_FALLBACK_EVENTS: list[str] = []
_COMPRESSED_INCLUDES: list[str] = []


class CompressionFallbackError_dict(Exception):
    """Raised when selector/compression fails and ``compression_fallback`` is ``error``."""


def clear_compression_fallback_events_dict() -> None:
    """Reset per-invocation compression reporting (call at CLI entry)."""
    _FALLBACK_EVENTS.clear()
    _COMPRESSED_INCLUDES.clear()


def record_compression_applied_dict(file_path: str, mode: str) -> None:
    """Record a successfully compressed include target for the execution summary."""
    entry = f"{file_path} (mode={mode})"
    if entry not in _COMPRESSED_INCLUDES:
        _COMPRESSED_INCLUDES.append(entry)


def record_compression_fallback_dict(message: str) -> None:
    """Record a selector/compression fallback for the execution summary."""
    if message and message not in _FALLBACK_EVENTS:
        _FALLBACK_EVENTS.append(message)


def read_active_compression_settings_dict() -> dict[str, Any]:
    """Read effective compression flags from process environment."""
    context_compression = os.environ.get("PDD_CONTEXT_COMPRESSION", "") or "off"
    return {
        "context_compression": context_compression,
        "compress_examples": os.environ.get("PDD_COMPRESS_EXAMPLES") == "1",
        "compress_test_context": os.environ.get("PDD_COMPRESS_TEST_CONTEXT") == "1",
        "compression_fallback": os.environ.get("PDD_COMPRESSION_FALLBACK", "full") or "full",
    }


def format_compression_summary_lines_dict() -> list[str]:
    """Lines for the command execution summary."""
    settings = read_active_compression_settings_dict()
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

    for entry in _COMPRESSED_INCLUDES:
        lines.append(f"  Context compressed: {entry}")

    for event in _FALLBACK_EVENTS:
        lines.append(f"  Compression fallback triggered: {event}")

    return lines
