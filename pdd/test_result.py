"""Shared return type for test generation commands (#1072)."""
from __future__ import annotations

from typing import NamedTuple, Optional


class TestResult(NamedTuple):
    """Return type for cmd_test_main and run_agentic_test_generate.

    Using a NamedTuple prevents the class of bug where callers use
    wrong positional indexes (the original cause of #1072).
    """

    content: str
    cost: float
    model: str
    agentic_success: Optional[bool]
    error_message: str = ""
