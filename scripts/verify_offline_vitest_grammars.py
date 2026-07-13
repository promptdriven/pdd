"""Verify an installed pdd wheel can parse Vitest support code offline."""

from __future__ import annotations

import importlib.metadata
import socket
from pathlib import Path

import pdd
from pdd.sync_core.runner import VITEST_GRAMMAR_VERSIONS, _vitest_parser


class _DeniedSocket(socket.socket):
    """Raise if protected parser initialization attempts network access."""

    def connect(self, _address) -> None:
        raise AssertionError("Vitest grammar initialization attempted network access")

    def connect_ex(self, _address) -> int:
        raise AssertionError("Vitest grammar initialization attempted network access")


def main() -> None:
    """Check wheel provenance, exact grammar versions, and both parsers."""
    if "site-packages" not in str(Path(pdd.__file__).resolve()):
        raise SystemExit(f"pdd imported outside isolated wheel: {pdd.__file__}")
    for distribution, expected in VITEST_GRAMMAR_VERSIONS.items():
        actual = importlib.metadata.version(distribution)
        if actual != expected:
            raise SystemExit(f"{distribution}: expected {expected}, found {actual}")
    socket.socket = _DeniedSocket
    javascript = _vitest_parser("javascript")
    typescript = _vitest_parser("typescript")
    if javascript.parse(b"const value = 1;").root_node.has_error:
        raise SystemExit("packaged JavaScript grammar failed to parse")
    if typescript.parse(b"const value: number = 1;").root_node.has_error:
        raise SystemExit("packaged TypeScript grammar failed to parse")


if __name__ == "__main__":
    main()
