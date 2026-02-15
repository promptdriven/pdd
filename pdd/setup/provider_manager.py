from __future__ import annotations

import csv
import io
import os
import re
import tempfile
import shutil
from datetime import datetime
from pathlib import Path
from typing import Dict, List, Optional, Tuple

from rich.console import Console
from rich.table import Table
from rich.prompt import Prompt, Confirm

from pdd.setup.api_key_scanner import KeyInfo

console = Console()

# CSV column schema
CSV_FIELDNAMES = [
    "provider", "model", "input", "output", "coding_arena_elo",
    "base_url", "api_key", "max_reasoning_tokens", "structured_output",
    "reasoning_type", "location",
]

# ---------------------------------------------------------------------------
# Path helpers
# ---------------------------------------------------------------------------

def _get_shell_name() -> str:
    """Detect shell from SHELL env var, default to bash."""
    shell_path = os.environ.get("SHELL", "/bin/bash")
    shell = Path(shell_path).name
    # Normalise common shells
    if shell in ("bash", "zsh", "fish", "sh", "ksh", "csh", "tcsh"):
        return shell
    return "bash"


def _get_pdd_dir() -> Path:
    """Return ~/.pdd, creating it if necessary."""
    pdd_dir = Path.home() / ".pdd"
    pdd_dir.mkdir(parents=True, exist_ok=True)
    return pdd_dir


def _get_api_env_path() -> Path:
    """Return path to ~/.pdd/api-env.{shell}."""
    shell = _get_shell_name()
    return _get_pdd_dir() / f"api-env.{shell}"


def _get_user_csv_path() -> Path:
    """Return path to ~/.pdd/llm_model.csv."""
    return _get_pdd_dir() / "llm_model.csv"


def _get_master_csv_path() -> Path:
    """Return path to pdd/data/llm_model.csv (shipped with the package)."""
    return Path(__file__).resolve().parent.parent / "data" / "llm_model.csv"


# ---------------------------------------------------------------------------
# CSV I/O helpers
# ---------------------------------------------------------------------------

def _read_csv(path: Path) -> List[Dict[str, str]]:
    """Read a CSV file and return list of row dicts. Returns [] if missing."""
    if not path.exists():
        return []
    with open(path, "r", encoding="utf-8", newline="") as f:
        reader = csv.DictReader(f)
        return list(reader)


def _write_csv_atomic(path: Path, rows: List[Dict[str, str]]) -> None:
    """Atomically write rows to a CSV file (temp file + rename)."""
    path.parent.mkdir(parents=True, exist_ok=True)
    fd, tmp_path = tempfile.mkstemp(
        dir=str(path.parent), suffix=".tmp", prefix=".llm_model_"
    )
    try:
        with os.fdopen(fd, "w", encoding="utf-8", newline="") as f:
            writer = csv.DictWriter(f, fieldnames=CSV_FIELDNAMES)
            writer.writeheader()
            for row in rows:
                # Ensure every field is present
                clean = {k: row.get(k, "") for k in CSV_FIELDNAMES}
                writer.writerow(clean)
        shutil.move(tmp_path, str(path))
    except Exception:
        # Clean up temp file on failure
        if os.path.exists(tmp_path):
            os.unlink(tmp_path)
        raise


# ---------------------------------------------------------------------------
# api-env file helpers
# ---------------------------------------------------------------------------

def _read_api_env_lines(path: Path) -> List[str]:
    """Read api-env file lines. Returns [] if missing."""
    if not path.exists():
        return []
    with open(path, "r", encoding="utf-8") as f:
        return f.readlines()


def _write_api_env_atomic(path: Path, lines: List[str]) -> None:
    """Atomically write lines to api-env file."""
    path.parent.mkdir(parents=True, exist_ok=True)
    fd, tmp_path = tempfile.mkstemp(
        dir=str(path.parent), suffix=".tmp", prefix=".api-env_"
    )
    try:
        with os.fdopen(fd, "w", encoding="utf-8") as f:
            f.writelines(lines)
        shutil.move(tmp_path, str(path))
    except Exception:
        if os.path.exists(tmp_path):
            os.unlink(tmp_path)
        raise


def _save_key_to_api_env(key_name: str, key_value: str) -> None:
    """
    Add or update an export line in the api-env file.
    If the key already exists (even commented out), replace it.
    """
    env_path = _get_api_env_path()
    lines = _read_api_env_lines(env_path)

    export_line = f'export {key_name}="{key_value}"\n'

    # Pattern to match existing line (commented or not)
    pattern = re.compile(
        r"^(?:#\s*)?export\s+" + re.escape(key_name) + r"\s*=", re.MULTILINE
    )

    found = False
    new_lines: List[str] = []
    for line in lines:
        if pattern.match(line.strip()):
            new_lines.append(export_line)
            found = True
        else:
            new_lines.append(line)

    if not found:
        # Ensure trailing newline before appending
        if new_lines and not new_lines[-1].endswith("\n"):
            new_lines[-1] += "\n"
        new_lines.append(export_line)

    _write_api_env_atomic(env_path, new_lines)


def _comment_out_key_in_api_env(key_name: str) -> None:
    """
    Comment out (never delete) a key in the api-env file.
    Adds a comment with the date.
    """
    env_path = _get_api_env_path()
    lines = _read_api_env_lines(env_path)

    pattern = re.compile(
        r"^export\s+" + re.escape(key_name) + r"\s*=", re.MULTILINE
    )

    today = datetime.now().strftime("%Y-%m-%d")
    new_lines: List[str] = []
    for line in lines:
        stripped = line.strip()
        if pattern.match(stripped):
            comment = f"# Commented out by pdd setup on {today}\n"
            new_lines.append(comment)
            new_lines.append(f"# {stripped}\n")
        else:
            new_lines.append(line)

    _write_api_env_atomic(env_path, new_lines)


def _get_master_rows_for_key(api_key_name: str) -> List[Dict[str, str]]:
    """Return all rows from master CSV whose api_key column matches."""
    master_rows = _read_csv(_get_master_csv_path())
    return [r for r in master_rows if r.get("api_key", "").strip() == api_key_name]


# ---------------------------------------------------------------------------
# Public API
# ---------------------------------------------------------------------------

def add_api_key(scan_results: Dict[str, KeyInfo]) -> bool:
    """
    Show missing keys from scan_results, prompt user for one, save to
    api-env file, then copy ALL matching rows from master CSV into user CSV.

    Returns True if a key was added/updated, False if cancelled.
    """
    # Separate missing and found keys
    missing_keys = {k: v for k, v in scan_results.items() if not v.is_set}
    found_keys = {k: v for k, v in scan_results.items() if v.is_set}

    if not missing_keys:
        console.print("[green]All known API keys are already configured.[/green]")
        return False

    # Display missing keys
    console.print("\n[bold]Missing API keys:[/bold]")
    sorted_missing = sorted(missing_keys.keys())
    for idx, key_name in enumerate(sorted_missing, 1):
        console.print(f"  {idx}. {key_name}")

    # Prompt user to select one
    selection = Prompt.ask(
        "\nEnter the number of the key to add (or press Enter to cancel)"
    )
    if not selection.strip():
        console.print("[dim]Cancelled.[/dim]")
        return False

    try:
        choice = int(selection.strip())
        if choice < 1 or choice > len(sorted_missing):
            console.print("[red]Invalid selection.[/red]")
            return False
    except ValueError:
        console.print("[red]Invalid input.[/red]")
        return False

    selected_key = sorted_missing[choice - 1]

    # Check if key is already in environment (shouldn't be since it's in missing, but guard)
    if os.environ.get(selected_key):
        console.print(
            f"[yellow]{selected_key} is already set in the current environment. Skipping.[/yellow]"
        )
        return False

    # Check if master CSV has rows for this key
    master_rows = _get_master_rows_for_key(selected_key)
    if not master_rows:
        console.print(
            f"[yellow]No models found in master CSV for '{selected_key}'.[/yellow]\n"
            f"[yellow]Please use 'Add a custom provider' instead.[/yellow]"
        )
        return False

    # Prompt for the actual key value
    key_value = Prompt.ask(f"Enter the value for {selected_key}")
    if not key_value.strip():
        console.print("[dim]Cancelled.[/dim]")
        return False
    key_value = key_value.strip()

    # Save key to api-env file
    _save_key_to_api_env(selected_key, key_value)
    console.print(f"[green]Saved {selected_key} to {_get_api_env_path()}[/green]")

    # Copy matching rows from master CSV into user CSV
    user_csv_path = _get_user_csv_path()
    existing_user_rows = _read_csv(user_csv_path)

    # Build set of existing model identifiers to avoid duplicates
    existing_models = {
        (r.get("provider", ""), r.get("model", ""))
        for r in existing_user_rows
    }

    added_count = 0
    for row in master_rows:
        model_id = (row.get("provider", ""), row.get("model", ""))
        if model_id not in existing_models:
            existing_user_rows.append(row)
            existing_models.add(model_id)
            added_count += 1

    _write_csv_atomic(user_csv_path, existing_user_rows)
    console.print(
        f"[green]Added {added_count} model(s) for {selected_key} to {user_csv_path}[/green]"
    )

    return True


def add_custom_provider() -> bool:
    """
    Prompt for custom provider details and append a row to user CSV.

    Returns True if a provider was added, False if cancelled.
    """
    console.print("\n[bold]Add a Custom LiteLLM-Compatible Provider[/bold]\n")

    # Provider prefix (e.g. "openai", "anthropic", "ollama", etc.)
    provider = Prompt.ask("Provider prefix (e.g. openai, ollama, together_ai)")
    if not provider.strip():
        console.print("[dim]Cancelled.[/dim]")
        return False
    provider = provider.strip()

    # Model name
    model_name = Prompt.ask("Model name (e.g. my-model-v1)")
    if not model_name.strip():
        console.print("[dim]Cancelled.[/dim]")
        return False
    model_name = model_name.strip()

    # Full model string for LiteLLM: provider/model
    full_model = f"{provider}/{model_name}"

    # API key env var name
    api_key_var = Prompt.ask("API key environment variable name (e.g. OPENAI_API_KEY)")
    if not api_key_var.strip():
        console.print("[dim]Cancelled.[/dim]")
        return False
    api_key_var = api_key_var.strip()

    # Base URL (optional)
    base_url = Prompt.ask("Base URL (optional, press Enter to skip)", default="")
    base_url = base_url.strip()

    # Costs (optional)
    input_cost = Prompt.ask("Input cost per 1M tokens (optional, press Enter for 0.0)", default="0.0")
    output_cost = Prompt.ask("Output cost per 1M tokens (optional, press Enter for 0.0)", default="0.0")

    try:
        input_cost_val = str(float(input_cost.strip()))
    except ValueError:
        input_cost_val = "0.0"

    try:
        output_cost_val = str(float(output_cost.strip()))
    except ValueError:
        output_cost_val = "0.0"

    # Ask if user wants to provide the actual API key value now
    provide_key = Confirm.ask(
        f"Do you want to enter the value for {api_key_var} now?", default=True
    )
    if provide_key:
        key_value = Prompt.ask(f"Enter the value for {api_key_var}")
        if key_value.strip():
            _save_key_to_api_env(api_key_var, key_value.strip())
            console.print(
                f"[green]Saved {api_key_var} to {_get_api_env_path()}[/green]"
            )

    # Build the row with sensible defaults
    new_row: Dict[str, str] = {
        "provider": provider,
        "model": full_model,
        "input": input_cost_val,
        "output": output_cost_val,
        "coding_arena_elo": "1000",
        "base_url": base_url,
        "api_key": api_key_var,
        "max_reasoning_tokens": "0",
        "structured_output": "True",
        "reasoning_type": "",
        "location": "",
    }

    # Append to user CSV
    user_csv_path = _get_user_csv_path()
    existing_rows = _read_csv(user_csv_path)
    existing_rows.append(new_row)
    _write_csv_atomic(user_csv_path, existing_rows)

    console.print(
        f"[green]Added custom model '{full_model}' to {user_csv_path}[/green]"
    )
    return True


def remove_models_by_provider() -> bool:
    """
    Group user CSV models by api_key, show numbered list with counts,
    remove all rows for selected provider. Comment out the key in api-env.

    Returns True if models were removed, False if cancelled.
    """
    user_csv_path = _get_user_csv_path()
    rows = _read_csv(user_csv_path)

    if not rows:
        console.print("[yellow]No models configured in user CSV.[/yellow]")
        return False

    # Group by api_key
    provider_groups: Dict[str, List[Dict[str, str]]] = {}
    for row in rows:
        key = row.get("api_key", "").strip()
        if not key:
            key = "(no api_key)"
        provider_groups.setdefault(key, []).append(row)

    sorted_providers = sorted(provider_groups.keys())

    # Display table
    table = Table(title="Configured Providers")
    table.add_column("#", style="bold")
    table.add_column("API Key Variable")
    table.add_column("Model Count", justify="right")
    table.add_column("Sample Models")

    for idx, prov_key in enumerate(sorted_providers, 1):
        prov_rows = provider_groups[prov_key]
        sample = ", ".join(
            r.get("model", "?") for r in prov_rows[:3]
        )
        if len(prov_rows) > 3:
            sample += ", ..."
        table.add_row(str(idx), prov_key, str(len(prov_rows)), sample)

    console.print(table)

    selection = Prompt.ask(
        "\nEnter the number of the provider to remove (or press Enter to cancel)"
    )
    if not selection.strip():
        console.print("[dim]Cancelled.[/dim]")
        return False

    try:
        choice = int(selection.strip())
        if choice < 1 or choice > len(sorted_providers):
            console.print("[red]Invalid selection.[/red]")
            return False
    except ValueError:
        console.print("[red]Invalid input.[/red]")
        return False

    selected_provider_key = sorted_providers[choice - 1]
    remove_count = len(provider_groups[selected_provider_key])

    # Confirm
    if not Confirm.ask(
        f"Remove all {remove_count} model(s) for '{selected_provider_key}'?"
    ):
        console.print("[dim]Cancelled.[/dim]")
        return False

    # Filter out the selected provider's rows
    remaining_rows = [
        r for r in rows
        if (r.get("api_key", "").strip() or "(no api_key)") != selected_provider_key
    ]

    _write_csv_atomic(user_csv_path, remaining_rows)
    console.print(
        f"[green]Removed {remove_count} model(s) for '{selected_provider_key}'.[/green]"
    )

    # Comment out the key in api-env (only if it's a real key name)
    if selected_provider_key != "(no api_key)":
        _comment_out_key_in_api_env(selected_provider_key)
        console.print(
            f"[green]Commented out {selected_provider_key} in {_get_api_env_path()}[/green]"
        )

    return True


def remove_individual_models() -> bool:
    """
    List all models from user CSV, let user select by comma-separated numbers,
    remove selected rows.

    Returns True if models were removed, False if cancelled.
    """
    user_csv_path = _get_user_csv_path()
    rows = _read_csv(user_csv_path)

    if not rows:
        console.print("[yellow]No models configured in user CSV.[/yellow]")
        return False

    # Display all models
    table = Table(title="Configured Models")
    table.add_column("#", style="bold")
    table.add_column("Provider")
    table.add_column("Model")
    table.add_column("API Key")

    for idx, row in enumerate(rows, 1):
        table.add_row(
            str(idx),
            row.get("provider", ""),
            row.get("model", ""),
            row.get("api_key", ""),
        )

    console.print(table)

    selection = Prompt.ask(
        "\nEnter model numbers to remove (comma-separated, or press Enter to cancel)"
    )
    if not selection.strip():
        console.print("[dim]Cancelled.[/dim]")
        return False

    # Parse comma-separated numbers
    indices_to_remove: set[int] = set()
    for part in selection.split(","):
        part = part.strip()
        if not part:
            continue
        try:
            num = int(part)
            if 1 <= num <= len(rows):
                indices_to_remove.add(num)
            else:
                console.print(f"[yellow]Skipping invalid number: {num}[/yellow]")
        except ValueError:
            console.print(f"[yellow]Skipping invalid input: '{part}'[/yellow]")

    if not indices_to_remove:
        console.print("[dim]No valid selections. Cancelled.[/dim]")
        return False

    # Show what will be removed
    console.print("\n[bold]Models to remove:[/bold]")
    for idx in sorted(indices_to_remove):
        row = rows[idx - 1]
        console.print(f"  {idx}. {row.get('model', '?')} ({row.get('api_key', '')})")

    if not Confirm.ask(f"Remove {len(indices_to_remove)} model(s)?"):
        console.print("[dim]Cancelled.[/dim]")
        return False

    # Filter out selected rows (convert to 0-based)
    remaining_rows = [
        row for idx, row in enumerate(rows, 1)
        if idx not in indices_to_remove
    ]

    _write_csv_atomic(user_csv_path, remaining_rows)
    console.print(
        f"[green]Removed {len(indices_to_remove)} model(s) from {user_csv_path}[/green]"
    )

    return True