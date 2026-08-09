"""Example: capture Rich/ANSI worker output in the sync Textual TUI.

Run this from a real terminal. The worker emits ANSI sequences that Rich may
highlight before they reach the TUI redirector; SyncApp captures the output
without showing raw escape fragments in the RichLog.
"""

from __future__ import annotations

import sys
import threading
from typing import Any

from rich.console import Console

from pdd.sync_tui import SyncApp


def worker() -> dict[str, Any]:
    """Emit representative worker output and return a sync-like result."""
    console = Console(
        file=sys.stdout,
        force_terminal=True,
        color_system="standard",
        highlight=True,
        width=80,
    )
    console.print("\x1b[90mchecking prompt drift\x1b[0m")
    console.print("pre\x1b]0;hidden-title\x1b[31mRED\x1b[0mpost")
    console.print("done")
    return {
        "success": True,
        "total_cost": 0.0,
        "model_name": "example",
        "operations_completed": ["example"],
        "errors": [],
    }


def main() -> dict[str, Any]:
    """Run the TUI with a small worker that writes ANSI-rich output."""
    app = SyncApp(
        basename="sync_tui_example",
        budget=0.01,
        worker_func=worker,
        function_name_ref=["example"],
        cost_ref=[0.0],
        prompt_path_ref=["prompts/sync_tui_python.prompt"],
        code_path_ref=["pdd/sync_tui.py"],
        example_path_ref=["context/sync_tui_example.py"],
        tests_path_ref=["tests/test_sync_tui.py"],
        prompt_color_ref=["blue"],
        code_color_ref=["cyan"],
        example_color_ref=["green"],
        tests_color_ref=["yellow"],
        stop_event=threading.Event(),
        no_steer=True,
    )
    return app.run()


if __name__ == "__main__":
    main()
