"""Trusted pytest plugin that captures node IDs before repository hooks mutate them."""

from __future__ import annotations

import json
from pathlib import Path

import pytest


_OUTPUT_PATH: str | None = None


@pytest.hookimpl(wrapper=True, tryfirst=True)
def pytest_collection_modifyitems(items):
    """Persist the pre-mutation collection after all inner hooks complete."""
    protected_node_ids = tuple(item.nodeid for item in items)
    try:
        return (yield)
    finally:
        output = _OUTPUT_PATH
        if output:
            Path(output).write_text(
                json.dumps(protected_node_ids, separators=(",", ":")),
                encoding="utf-8",
            )
