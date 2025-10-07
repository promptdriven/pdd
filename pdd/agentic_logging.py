from __future__ import annotations
import os
from rich.console import Console

console = Console()

_env_level = os.getenv("PDD_AGENTIC_LOGLEVEL")
if _env_level is None and os.getenv("PYTEST_CURRENT_TEST"):
    _env_level = "quiet"
_LOGLEVEL = (_env_level or "normal").strip().lower()
IS_QUIET = _LOGLEVEL == "quiet"
IS_VERBOSE = _LOGLEVEL == "verbose"

AGENT_COST_PER_CALL = float(os.getenv("PDD_AGENTIC_COST_PER_CALL", "0.02"))
AGENT_CALL_TIMEOUT = int(os.getenv("PDD_AGENTIC_TIMEOUT", "240"))
VERIFY_TIMEOUT = int(os.getenv("PDD_AGENTIC_VERIFY_TIMEOUT", "120"))
MAX_LOG_LINES = int(os.getenv("PDD_AGENTIC_MAX_LOG_LINES", "200"))

def _print(msg: str, *, force: bool = False) -> None:
    if not IS_QUIET or force:
        console.print(msg)

def info(msg: str) -> None:
    _print(msg)

def always(msg: str) -> None:
    _print(msg)

def verbose(msg: str) -> None:
    if IS_VERBOSE:
        console.print(msg)

def print_head(label: str, text: str, max_lines: int = MAX_LOG_LINES) -> None:
    if not IS_VERBOSE:
        return
    lines = (text or "").splitlines()
    head = "\n".join(lines[:max_lines])
    tail = "" if len(lines) <= max_lines else f"\n... (truncated, total {len(lines)} lines)"
    console.print(f"[bold cyan]{label}[/bold cyan]\n{head}{tail}")
