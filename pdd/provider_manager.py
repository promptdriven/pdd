from __future__ import annotations

import csv
import io
import os
import re
import shlex
import shutil
import tempfile
from datetime import datetime
from pathlib import Path
from typing import Dict, List, Optional

from rich.console import Console
from rich.table import Table
from rich.prompt import Prompt, Confirm

from pdd.litellm_registry import (
    is_litellm_available,
    get_top_providers,
    search_providers,
    get_models_for_provider,
    get_api_key_env_var,
    ProviderInfo,
    ModelInfo,
)

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


def _get_shell_rc_path() -> Optional[Path]:
    """Return the shell RC file path (~/.zshrc, ~/.bashrc, etc.)."""
    shell = _get_shell_name()
    home = Path.home()
    shell_files = {
        "zsh": home / ".zshrc",
        "bash": home / ".bashrc",
        "fish": home / ".config" / "fish" / "config.fish",
        "csh": home / ".cshrc",
        "tcsh": home / ".tcshrc",
        "ksh": home / ".kshrc",
        "sh": home / ".profile",
    }
    return shell_files.get(shell)


def _get_source_line_for_shell(api_env_path: Path) -> str:
    """Return the appropriate source line syntax for the current shell."""
    shell = _get_shell_name()
    path_str = str(api_env_path)

    if shell == "fish":
        return f'test -f "{path_str}"; and source "{path_str}"'
    elif shell in ("csh", "tcsh"):
        return f'if ( -f "{path_str}" ) source "{path_str}"'
    elif shell == "sh":
        # sh uses . instead of source
        return f'[ -f "{path_str}" ] && . "{path_str}"'
    else:
        # bash, zsh, ksh and others
        return f'[ -f "{path_str}" ] && source "{path_str}"'


def _ensure_api_env_sourced_in_rc() -> bool:
    """
    Ensure the api-env file is sourced in the user's shell RC file.

    Adds a shell-appropriate source line to ~/.zshrc (or equivalent) if not
    already present. This ensures new terminal sessions automatically have
    the API keys available.

    Returns True if the line was added, False if already present or unsupported.
    """
    rc_path = _get_shell_rc_path()
    if rc_path is None:
        return False

    api_env_path = _get_api_env_path()

    # Ensure parent directory exists (important for fish: ~/.config/fish/)
    rc_path.parent.mkdir(parents=True, exist_ok=True)

    # Check if api-env path is already referenced in the RC file
    if rc_path.exists():
        content = rc_path.read_text(encoding="utf-8")
        # Check if the api-env file path is already mentioned (covers any syntax)
        if str(api_env_path) in content:
            return False
    else:
        content = ""

    # Build shell-appropriate source line
    source_line = _get_source_line_for_shell(api_env_path)

    # Append the source line
    with open(rc_path, "a", encoding="utf-8") as f:
        f.write(f"\n# PDD API keys\n{source_line}\n")

    return True


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


def _build_env_export_line(key_name: str, key_value: str) -> str:
    """Build a shell-appropriate export line for the given key/value."""
    shell = _get_shell_name()
    # Use shlex.quote() for proper shell escaping of special characters
    # This handles $, ", ', `, \, spaces, and other problematic chars
    quoted_value = shlex.quote(key_value)

    if shell == "fish":
        return f"set -gx {key_name} {quoted_value}\n"
    elif shell in ("csh", "tcsh"):
        return f"setenv {key_name} {quoted_value}\n"
    else:
        # bash, zsh, ksh, sh and others
        return f"export {key_name}={quoted_value}\n"


def _build_env_key_pattern(key_name: str) -> re.Pattern:
    """Build a regex pattern to match any shell syntax for the given key."""
    # Match: export KEY=, setenv KEY , set -gx KEY  (with optional comment prefix)
    escaped_key = re.escape(key_name)
    return re.compile(
        rf"^(?:#\s*)?(?:export\s+{escaped_key}\s*=|setenv\s+{escaped_key}\s|set\s+-gx\s+{escaped_key}\s)",
        re.MULTILINE,
    )


def _save_key_to_api_env(key_name: str, key_value: str) -> None:
    """
    Add or update an export line in the api-env file.
    If the key already exists (even commented out), replace it.

    Uses shell-appropriate syntax (export for bash/zsh, set -gx for fish,
    setenv for csh/tcsh).

    Also sets the key in os.environ so it's immediately available
    in the current session without requiring the user to source their shell.
    """
    # Set in current process environment for immediate availability
    os.environ[key_name] = key_value

    env_path = _get_api_env_path()
    lines = _read_api_env_lines(env_path)

    export_line = _build_env_export_line(key_name, key_value)
    pattern = _build_env_key_pattern(key_name)

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
    Adds a comment with the date. Handles all shell syntaxes.
    """
    env_path = _get_api_env_path()
    lines = _read_api_env_lines(env_path)

    # Match uncommented lines only (export, setenv, set -gx)
    escaped_key = re.escape(key_name)
    pattern = re.compile(
        rf"^(?:export\s+{escaped_key}\s*=|setenv\s+{escaped_key}\s|set\s+-gx\s+{escaped_key}\s)",
        re.MULTILINE,
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


# ---------------------------------------------------------------------------
# Key-existence check (used by add_provider_from_registry)
# ---------------------------------------------------------------------------

def _is_key_set(key_name: str) -> Optional[str]:
    """Return the source label if *key_name* is set, else ``None``.

    Checks .env (via python-dotenv), shell environment, and api-env file.
    """
    try:
        from dotenv import dotenv_values  # type: ignore
        dotenv_vals = dotenv_values()
        if key_name in dotenv_vals and dotenv_vals[key_name] is not None:
            return ".env file"
    except Exception:
        pass

    if os.environ.get(key_name):
        return "shell environment"

    env_path = _get_api_env_path()
    if env_path.exists():
        from pdd.api_key_scanner import _parse_api_env_file
        api_env_vals = _parse_api_env_file(env_path)
        if key_name in api_env_vals:
            return f"~/.pdd/{env_path.name}"

    return None


# ---------------------------------------------------------------------------
# Public API
# ---------------------------------------------------------------------------

def add_provider_from_registry() -> bool:
    """
    Search/browse LiteLLM's model registry, let the user pick a provider
    and specific models, handle the API key, and save to user CSV.

    Returns True if any models were added, False if cancelled.
    """
    if not is_litellm_available():
        console.print(
            "[red]litellm is required but not installed or has no model data.[/red]\n"
            "[yellow]Run: pip install litellm[/yellow]\n"
            "[yellow]Or use 'Add a custom provider' instead.[/yellow]"
        )
        return False

    # ── Step 1: Browse / Search providers ──────────────────────────────

    top = get_top_providers()

    console.print("\n[bold]Search providers[/bold]\n")
    console.print("  Top providers:")
    for idx, p in enumerate(top, 1):
        console.print(
            f"    {idx:>2}. {p.display_name:20s}  ({p.model_count} chat models)"
        )
    console.print()

    selection = Prompt.ask(
        "Enter number, or type to search (empty to cancel)"
    )
    if not selection.strip():
        console.print("[dim]Cancelled.[/dim]")
        return False

    selected_provider: Optional[ProviderInfo] = None

    # Try as a number first (direct selection from top list)
    try:
        choice = int(selection.strip())
        if 1 <= choice <= len(top):
            selected_provider = top[choice - 1]
    except ValueError:
        pass

    # If not a valid number, treat as search query
    if selected_provider is None:
        results = search_providers(selection.strip())
        if not results:
            console.print(
                f"[yellow]No providers matching '{selection.strip()}'.[/yellow]\n"
                "[yellow]Try a different search, or use 'Add a custom provider'.[/yellow]"
            )
            return False

        if len(results) == 1:
            selected_provider = results[0]
        else:
            console.print(f"\n  Found {len(results)} provider(s):")
            for idx, p in enumerate(results, 1):
                console.print(
                    f"    {idx:>2}. {p.display_name:20s}  ({p.model_count} chat models)"
                )
            console.print()

            pick = Prompt.ask("Select provider number (empty to cancel)")
            if not pick.strip():
                console.print("[dim]Cancelled.[/dim]")
                return False
            try:
                pick_idx = int(pick.strip())
                if 1 <= pick_idx <= len(results):
                    selected_provider = results[pick_idx - 1]
                else:
                    console.print("[red]Invalid selection.[/red]")
                    return False
            except ValueError:
                console.print("[red]Invalid input.[/red]")
                return False

    assert selected_provider is not None

    # ── Step 2: Model selection ────────────────────────────────────────

    models = get_models_for_provider(selected_provider.name)
    if not models:
        console.print(
            f"[yellow]No chat models found for {selected_provider.display_name} "
            f"in litellm's registry.[/yellow]\n"
            "[yellow]Use 'Add a custom provider' instead.[/yellow]"
        )
        return False

    table = Table(title=f"Chat models for {selected_provider.display_name}")
    table.add_column("#", style="bold", width=4)
    table.add_column("Model")
    table.add_column("Input $/M", justify="right")
    table.add_column("Output $/M", justify="right")
    table.add_column("Max Input", justify="right")

    for idx, m in enumerate(models, 1):
        input_cost = f"${m.input_cost_per_million:.2f}" if m.input_cost_per_million else "$0.00"
        output_cost = f"${m.output_cost_per_million:.2f}" if m.output_cost_per_million else "$0.00"
        max_input = f"{m.max_input_tokens:,}" if m.max_input_tokens else "—"
        table.add_row(str(idx), m.litellm_id, input_cost, output_cost, max_input)

    console.print(table)
    console.print()

    model_selection = Prompt.ask(
        "Select models (comma-separated numbers, 'all', or empty to cancel)"
    )
    if not model_selection.strip():
        console.print("[dim]Cancelled.[/dim]")
        return False

    selected_models: List[ModelInfo] = []

    if model_selection.strip().lower() == "all":
        selected_models = list(models)
    else:
        for part in model_selection.split(","):
            part = part.strip()
            if not part:
                continue
            try:
                num = int(part)
                if 1 <= num <= len(models):
                    selected_models.append(models[num - 1])
                else:
                    console.print(f"[yellow]Skipping invalid number: {num}[/yellow]")
            except ValueError:
                console.print(f"[yellow]Skipping invalid input: '{part}'[/yellow]")

    if not selected_models:
        console.print("[dim]No valid selections. Cancelled.[/dim]")
        return False

    # ── Step 3: API key ────────────────────────────────────────────────

    api_key_var = selected_provider.api_key_env_var

    if api_key_var is None:
        # Provider not in our known mapping — ask the user
        api_key_var = Prompt.ask(
            f"API key env var for {selected_provider.display_name} "
            "(e.g. PROVIDER_API_KEY, or empty to skip)"
        ).strip() or None

    if api_key_var:
        existing_source = _is_key_set(api_key_var)
        if existing_source:
            console.print(
                f"  [green]{api_key_var} is already set ({existing_source}).[/green]"
            )
            if Confirm.ask("Update the key?", default=False):
                key_value = Prompt.ask(f"Enter new value for {api_key_var}")
                if key_value.strip():
                    _save_key_to_api_env(api_key_var, key_value.strip())
                    console.print(
                        f"[green]Updated {api_key_var} in {_get_api_env_path()}[/green]"
                    )
                    rc_updated = _ensure_api_env_sourced_in_rc()
                    if rc_updated:
                        console.print(
                            f"[green]Added source line to {_get_shell_rc_path()}[/green]"
                        )
                    console.print(
                        "[dim]Key is available now for this session.[/dim]"
                    )
        else:
            key_value = Prompt.ask(f"Enter the value for {api_key_var}")
            if key_value.strip():
                _save_key_to_api_env(api_key_var, key_value.strip())
                console.print(
                    f"[green]Saved {api_key_var} to {_get_api_env_path()}[/green]"
                )
                rc_updated = _ensure_api_env_sourced_in_rc()
                if rc_updated:
                    console.print(
                        f"[green]Added source line to {_get_shell_rc_path()}[/green]"
                    )
                console.print(
                    "[dim]Key is available now for this session.[/dim]"
                )

    # ── Step 4: Write to user CSV ──────────────────────────────────────

    user_csv_path = _get_user_csv_path()
    existing_rows = _read_csv(user_csv_path)

    # Build set of existing model identifiers to avoid duplicates
    existing_model_ids = {
        (r.get("provider", ""), r.get("model", ""))
        for r in existing_rows
    }

    added_count = 0
    for m in selected_models:
        # Build the litellm model ID with provider prefix convention
        csv_model = m.litellm_id

        new_row: Dict[str, str] = {
            "provider": selected_provider.display_name,
            "model": csv_model,
            "input": str(m.input_cost_per_million),
            "output": str(m.output_cost_per_million),
            "coding_arena_elo": "1000",
            "base_url": "",
            "api_key": api_key_var or "",
            "max_reasoning_tokens": "0",
            "structured_output": str(m.supports_function_calling),
            "reasoning_type": "",
            "location": "",
        }

        model_id = (new_row["provider"], new_row["model"])
        if model_id not in existing_model_ids:
            existing_rows.append(new_row)
            existing_model_ids.add(model_id)
            added_count += 1
        else:
            console.print(f"  [dim]Skipping duplicate: {csv_model}[/dim]")

    if added_count > 0:
        _write_csv_atomic(user_csv_path, existing_rows)
        console.print(
            f"[green]Added {added_count} model(s) to {user_csv_path}[/green]"
        )
    else:
        console.print("[yellow]No new models were added (all already configured).[/yellow]")

    return added_count > 0


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
            rc_updated = _ensure_api_env_sourced_in_rc()
            if rc_updated:
                console.print(
                    f"[green]Added source line to {_get_shell_rc_path()}[/green]"
                )
            console.print(
                "[dim]Key is available now for this session.[/dim]"
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