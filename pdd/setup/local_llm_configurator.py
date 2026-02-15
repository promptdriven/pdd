"""Local LLM configurator for PDD.

Guides users through configuring local LLM tools (Ollama, LM Studio, custom endpoints).
Local models need a base_url and model name, not API keys.
"""

from __future__ import annotations

import csv
import io
import logging
import os
import shutil
import tempfile
from pathlib import Path
from typing import Any, Dict, List, Optional, Tuple
from urllib.parse import urlparse

from rich.console import Console
from rich.table import Table

logger = logging.getLogger("pdd.setup.local_llm_configurator")
console = Console()

# CSV header for ~/.pdd/llm_model.csv
CSV_COLUMNS: List[str] = [
    "provider",
    "model",
    "input",
    "output",
    "coding_arena_elo",
    "base_url",
    "api_key",
    "max_reasoning_tokens",
    "structured_output",
    "reasoning_type",
    "location",
]

DEFAULT_LM_STUDIO_BASE_URL = "http://localhost:1234/v1"
DEFAULT_OLLAMA_BASE_URL = "http://localhost:11434"
DEFAULT_OLLAMA_API_URL = "http://localhost:11434/api/tags"


def _get_user_csv_path() -> Path:
    """Return the path to the user's ~/.pdd/llm_model.csv."""
    return Path.home() / ".pdd" / "llm_model.csv"


def _validate_base_url(url: str) -> bool:
    """Validate that a base URL has http or https scheme and a netloc."""
    try:
        parsed = urlparse(url.strip())
        return parsed.scheme in ("http", "https") and bool(parsed.netloc)
    except Exception:
        return False


def _build_model_row(
    provider: str,
    model: str,
    base_url: str,
    coding_arena_elo: int = 1000,
    structured_output: bool = True,
    reasoning_type: str = "none",
) -> Dict[str, Any]:
    """Build a CSV row dict for a local model."""
    return {
        "provider": provider,
        "model": model,
        "input": 0,
        "output": 0,
        "coding_arena_elo": coding_arena_elo,
        "base_url": base_url,
        "api_key": "",
        "max_reasoning_tokens": 0,
        "structured_output": structured_output,
        "reasoning_type": reasoning_type,
        "location": "",
    }


def _read_existing_csv(csv_path: Path) -> List[Dict[str, str]]:
    """Read existing rows from the user CSV, returning list of dicts."""
    rows: List[Dict[str, str]] = []
    if not csv_path.exists():
        return rows
    try:
        with open(csv_path, "r", newline="", encoding="utf-8") as f:
            reader = csv.DictReader(f)
            for row in reader:
                rows.append(row)
    except Exception as e:
        logger.warning(f"Failed to read existing CSV at {csv_path}: {e}")
    return rows


def _write_csv_atomic(csv_path: Path, rows: List[Dict[str, Any]]) -> None:
    """Atomically write rows to the user CSV.

    Writes to a temporary file first, then moves it into place to avoid
    partial writes corrupting the file.
    """
    csv_path.parent.mkdir(parents=True, exist_ok=True)

    # Write to a temp file in the same directory for atomic rename
    fd, tmp_path_str = tempfile.mkstemp(
        dir=str(csv_path.parent), suffix=".csv.tmp"
    )
    tmp_path = Path(tmp_path_str)
    try:
        with os.fdopen(fd, "w", newline="", encoding="utf-8") as f:
            writer = csv.DictWriter(f, fieldnames=CSV_COLUMNS, extrasaction="ignore")
            writer.writeheader()
            for row in rows:
                writer.writerow(row)
        # Atomic move
        shutil.move(str(tmp_path), str(csv_path))
    except Exception:
        # Clean up temp file on failure
        try:
            tmp_path.unlink(missing_ok=True)
        except Exception:
            pass
        raise


def _append_rows_to_csv(csv_path: Path, new_rows: List[Dict[str, Any]]) -> None:
    """Append new model rows to the user CSV, creating it if needed."""
    existing = _read_existing_csv(csv_path)
    # Convert existing rows to have consistent types
    combined = list(existing) + new_rows
    _write_csv_atomic(csv_path, combined)


def _discover_ollama_models(base_url: str) -> Optional[List[str]]:
    """Query Ollama API for available models.

    Returns a list of model names, or None if the API is unreachable.
    """
    import urllib.request
    import json

    api_url = base_url.rstrip("/") + "/api/tags"
    try:
        req = urllib.request.Request(api_url, method="GET")
        with urllib.request.urlopen(req, timeout=5) as resp:
            data = json.loads(resp.read().decode("utf-8"))
            models = data.get("models", [])
            return [m.get("name", "") for m in models if m.get("name")]
    except Exception as e:
        logger.debug(f"Failed to query Ollama at {api_url}: {e}")
        return None


def _prompt_input(prompt_text: str, default: str = "") -> str:
    """Prompt user for input with optional default. Returns stripped input."""
    try:
        if default:
            raw = input(f"{prompt_text} [{default}]: ").strip()
            return raw if raw else default
        else:
            return input(f"{prompt_text}: ").strip()
    except (EOFError, KeyboardInterrupt):
        return ""


def _configure_lm_studio() -> List[Dict[str, Any]]:
    """Configure LM Studio models interactively."""
    rows: List[Dict[str, Any]] = []

    console.print("\n[bold cyan]LM Studio Configuration[/bold cyan]")
    console.print(f"Default base URL: {DEFAULT_LM_STUDIO_BASE_URL}")

    base_url = _prompt_input("Base URL", DEFAULT_LM_STUDIO_BASE_URL)
    if not base_url:
        console.print("[yellow]Cancelled.[/yellow]")
        return rows

    if not _validate_base_url(base_url):
        console.print("[red]Invalid URL. Must start with http:// or https://[/red]")
        return rows

    while True:
        model_name = _prompt_input("Model name (empty to finish)")
        if not model_name:
            break

        # Add lm_studio/ prefix if not present
        litellm_model = model_name
        if not litellm_model.startswith("lm_studio/"):
            litellm_model = f"lm_studio/{model_name}"

        row = _build_model_row(
            provider="lm_studio",
            model=litellm_model,
            base_url=base_url,
        )
        rows.append(row)
        console.print(f"  [green]✓[/green] Added: {litellm_model}")

    return rows


def _configure_ollama() -> List[Dict[str, Any]]:
    """Configure Ollama models interactively with auto-detection."""
    rows: List[Dict[str, Any]] = []

    console.print("\n[bold cyan]Ollama Configuration[/bold cyan]")
    console.print(f"Default base URL: {DEFAULT_OLLAMA_BASE_URL}")

    base_url = _prompt_input("Base URL", DEFAULT_OLLAMA_BASE_URL)
    if not base_url:
        console.print("[yellow]Cancelled.[/yellow]")
        return rows

    if not _validate_base_url(base_url):
        console.print("[red]Invalid URL. Must start with http:// or https://[/red]")
        return rows

    # Try auto-detection
    console.print("[dim]Checking for running Ollama instance...[/dim]")
    discovered = _discover_ollama_models(base_url)

    if discovered:
        console.print(f"[green]Found {len(discovered)} model(s):[/green]")

        table = Table(show_header=True, header_style="bold")
        table.add_column("#", style="dim", width=4)
        table.add_column("Model Name")
        for idx, name in enumerate(discovered, 1):
            table.add_row(str(idx), name)
        console.print(table)

        selection = _prompt_input(
            "Select models to add (comma-separated numbers, 'all', or empty to skip)"
        )
        if not selection:
            console.print("[yellow]No models selected.[/yellow]")
        elif selection.strip().lower() == "all":
            for name in discovered:
                litellm_model = f"ollama_chat/{name}"
                row = _build_model_row(
                    provider="Ollama",
                    model=litellm_model,
                    base_url=base_url,
                )
                rows.append(row)
                console.print(f"  [green]✓[/green] Added: {litellm_model}")
        else:
            # Parse comma-separated indices
            for part in selection.split(","):
                part = part.strip()
                try:
                    idx = int(part)
                    if 1 <= idx <= len(discovered):
                        name = discovered[idx - 1]
                        litellm_model = f"ollama_chat/{name}"
                        row = _build_model_row(
                            provider="Ollama",
                            model=litellm_model,
                            base_url=base_url,
                        )
                        rows.append(row)
                        console.print(f"  [green]✓[/green] Added: {litellm_model}")
                    else:
                        console.print(f"  [yellow]Skipping invalid index: {idx}[/yellow]")
                except ValueError:
                    console.print(f"  [yellow]Skipping invalid input: '{part}'[/yellow]")
    else:
        console.print(
            "[yellow]Could not connect to Ollama. Falling back to manual entry.[/yellow]"
        )
        while True:
            model_name = _prompt_input("Model name (empty to finish)")
            if not model_name:
                break

            litellm_model = model_name
            if not litellm_model.startswith("ollama_chat/"):
                litellm_model = f"ollama_chat/{model_name}"

            row = _build_model_row(
                provider="Ollama",
                model=litellm_model,
                base_url=base_url,
            )
            rows.append(row)
            console.print(f"  [green]✓[/green] Added: {litellm_model}")

    return rows


def _configure_custom() -> List[Dict[str, Any]]:
    """Configure a custom local LLM endpoint interactively."""
    rows: List[Dict[str, Any]] = []

    console.print("\n[bold cyan]Custom Local LLM Configuration[/bold cyan]")

    base_url = _prompt_input("Base URL (e.g., http://localhost:8080/v1)")
    if not base_url:
        console.print("[yellow]Cancelled.[/yellow]")
        return rows

    if not _validate_base_url(base_url):
        console.print("[red]Invalid URL. Must start with http:// or https://[/red]")
        return rows

    provider_name = _prompt_input("Provider name", "custom")

    while True:
        model_name = _prompt_input("Model name (empty to finish)")
        if not model_name:
            break

        row = _build_model_row(
            provider=provider_name,
            model=model_name,
            base_url=base_url,
        )
        rows.append(row)
        console.print(f"  [green]✓[/green] Added: {model_name}")

    return rows


def configure_local_llm() -> bool:
    """Interactive setup for local LLM providers.

    Guides the user through selecting a local LLM provider (LM Studio, Ollama,
    or custom), discovering available models, and appending them to the user's
    ``~/.pdd/llm_model.csv``.

    Returns:
        True if any models were added, False otherwise.
    """
    console.print("\n[bold]Local LLM Setup[/bold]")
    console.print("Configure local LLM tools for use with PDD.\n")
    console.print("Select a provider:")
    console.print("  [bold]1[/bold]. LM Studio  (default: localhost:1234)")
    console.print("  [bold]2[/bold]. Ollama     (default: localhost:11434)")
    console.print("  [bold]3[/bold]. Other      (custom endpoint)")
    console.print()

    choice = _prompt_input("Choice (1/2/3, empty to cancel)")
    if not choice:
        console.print("[yellow]Cancelled.[/yellow]")
        return False

    new_rows: List[Dict[str, Any]] = []

    if choice == "1":
        new_rows = _configure_lm_studio()
    elif choice == "2":
        new_rows = _configure_ollama()
    elif choice == "3":
        new_rows = _configure_custom()
    else:
        console.print(f"[red]Invalid choice: '{choice}'. Please enter 1, 2, or 3.[/red]")
        return False

    if not new_rows:
        console.print("[yellow]No models were added.[/yellow]")
        return False

    # Write to user CSV
    csv_path = _get_user_csv_path()
    try:
        _append_rows_to_csv(csv_path, new_rows)
        console.print(
            f"\n[green]Successfully added {len(new_rows)} model(s) to {csv_path}[/green]"
        )
        return True
    except Exception as e:
        console.print(f"[red]Failed to write to {csv_path}: {e}[/red]")
        logger.error(f"Failed to write CSV: {e}", exc_info=True)
        return False