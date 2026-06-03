"""Shared parsing for comma-separated PDD include ``select`` attribute values."""

from __future__ import annotations

import re


def parse_selectors_string(selectors_str: str) -> list[str]:
    """Split selector strings without breaking ``kind:value,more`` continuations."""
    raw_parts = [s.strip() for s in selectors_str.split(",") if s.strip()]
    selectors: list[str] = []
    for part in raw_parts:
        if re.match(r"^\w+:", part) or not selectors:
            selectors.append(part)
        else:
            selectors[-1] += "," + part
    return selectors
