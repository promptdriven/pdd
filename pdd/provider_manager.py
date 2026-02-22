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
from typing import Any, Dict, List, Optional

from rich.console import Console
from rich.table import Table
from rich.prompt import Prompt, Confirm


console = Console()

# CSV column schema
CSV_FIELDNAMES = [
    "provider", "model", "input", "output", "coding_arena_elo",
    "base_url", "api_key", "max_reasoning_tokens", "structured_output",
    "reasoning_type", "location",
]

# ---------------------------------------------------------------------------
# Pipe-delimited api_key helpers
# ---------------------------------------------------------------------------
# The CSV api_key column can contain multiple env var names separated by "|".
# Single var → pass as api_key= to litellm.  Multi-var → litellm reads from
# os.environ automatically (Bedrock, Azure, Vertex AI).  Empty → device flow
# or local model (GitHub Copilot, Ollama).


def parse_api_key_vars(api_key_field: str) -> List[str]:
    """Split the pipe-delimited api_key CSV field into individual env var names.

    Returns an empty list if the field is empty/blank.
    """
    if not api_key_field or not api_key_field.strip():
        return []
    return [v.strip() for v in api_key_field.split("|") if v.strip()]


def is_multi_credential(api_key_field: str) -> bool:
    """Return True if the api_key field contains multiple env vars (pipe-delimited)."""
    return "|" in (api_key_field or "")


# ---------------------------------------------------------------------------
# Complex provider authentication registry
# ---------------------------------------------------------------------------
# Providers that require multi-variable auth (not just a single API key).
# Maps provider display name (as in CSV) -> list of env var configs.
# Used by _setup_complex_provider() for interactive credential prompting.

COMPLEX_AUTH_PROVIDERS: Dict[str, List[Dict[str, Any]]] = {
    "Google Vertex AI": [
        {
            "env_var": "GOOGLE_APPLICATION_CREDENTIALS",
            "label": "Credentials",
            "required": True,
            "default": None,
            "hint": "Path to GCP service account JSON (or 'adc' for Application Default Credentials)",
        },
        {
            "env_var": "VERTEXAI_PROJECT",
            "label": "GCP Project",
            "required": True,
            "default": None,
            "hint": "Google Cloud project ID",
        },
        {
            "env_var": "VERTEXAI_LOCATION",
            "label": "Location",
            "required": True,
            "default": "us-central1",
            "hint": "GCP region (e.g. us-central1)",
        },
    ],
    "AWS Bedrock": [
        {
            "env_var": "AWS_ACCESS_KEY_ID",
            "label": "Access Key ID",
            "required": True,
            "default": None,
            "hint": "AWS IAM access key ID",
        },
        {
            "env_var": "AWS_SECRET_ACCESS_KEY",
            "label": "Secret Key",
            "required": True,
            "default": None,
            "hint": "AWS IAM secret access key",
        },
        {
            "env_var": "AWS_REGION_NAME",
            "label": "Region",
            "required": True,
            "default": "us-east-1",
            "hint": "AWS region (e.g. us-east-1)",
        },
    ],
    "Azure OpenAI": [
        {
            "env_var": "AZURE_API_KEY",
            "label": "API Key",
            "required": True,
            "default": None,
            "hint": "Azure OpenAI resource key",
        },
        {
            "env_var": "AZURE_API_BASE",
            "label": "Endpoint",
            "required": True,
            "default": None,
            "hint": "Azure OpenAI endpoint URL (e.g. https://myresource.openai.azure.com/)",
        },
        {
            "env_var": "AZURE_API_VERSION",
            "label": "API Version",
            "required": True,
            "default": "2024-10-21",
            "hint": "Azure API version string",
        },
    ],
    "Azure AI": [
        {
            "env_var": "AZURE_AI_API_KEY",
            "label": "API Key",
            "required": True,
            "default": None,
            "hint": "Azure AI Foundry API key",
        },
        {
            "env_var": "AZURE_AI_API_BASE",
            "label": "Endpoint",
            "required": False,
            "default": None,
            "hint": "Optional: Azure AI endpoint URL",
        },
    ],
    "Github Copilot": [
        {
            "env_var": "GITHUB_COPILOT_API_KEY",
            "label": "API Key",
            "required": False,
            "default": None,
            "hint": "Optional: GitHub Copilot uses device flow auth at runtime",
        },
    ],
}

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


def _quote_for_shell(value: str, shell: str) -> str:
    """Quote a value for the given shell, handling shell-specific edge cases.

    - POSIX shells (bash/zsh/sh/ksh): shlex.quote() is fully correct.
    - fish: single quotes treat \\\\ and \\' as escape sequences (unlike POSIX),
      so we must escape backslashes and single quotes within single quotes.
    - csh/tcsh: single quotes DO prevent $ expansion, but ! (history expansion)
      is never suppressed by any quoting. We backslash-escape ! outside quotes.
    """
    if shell == "fish":
        # fish single quotes recognise \\' and \\\\ as escapes
        escaped = value.replace("\\", "\\\\").replace("'", "\\'")
        return f"'{escaped}'"
    elif shell in ("csh", "tcsh"):
        # csh single quotes are mostly POSIX-like, but ! is never suppressed.
        # Strategy: use shlex.quote() for the base quoting, then break out
        # any ! characters so they can be backslash-escaped outside quotes.
        if "!" not in value:
            return shlex.quote(value)
        # Split on !, quote each segment, rejoin with escaped !
        parts = value.split("!")
        quoted_parts = [shlex.quote(p) for p in parts]
        return "\\!".join(quoted_parts)
    else:
        # bash, zsh, ksh, sh — shlex.quote() is fully correct
        return shlex.quote(value)


def _build_env_export_line(key_name: str, key_value: str) -> str:
    """Build a shell-appropriate export line for the given key/value."""
    shell = _get_shell_name()
    quoted_value = _quote_for_shell(key_value, shell)

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

def _get_ref_csv_path() -> Path:
    """Return path to the bundled reference CSV."""
    return Path(__file__).parent / "data" / "llm_model.csv"


def _setup_complex_provider(provider_name: str) -> bool:
    """Run interactive auth setup for a complex (multi-variable) provider.

    Prompts for each required env var and saves to api-env.
    Returns True if at least one credential was configured, False if all skipped.
    """
    var_configs = COMPLEX_AUTH_PROVIDERS.get(provider_name)
    if not var_configs:
        return False

    required_names = [c["label"] for c in var_configs if c["required"]]
    optional_names = [c["label"] for c in var_configs if not c["required"]]
    print()
    console.print(f"  [bold]{provider_name} Setup[/bold]")
    if required_names:
        console.print(f"  Required: {', '.join(required_names)}")
    if optional_names:
        console.print(f"  Optional: {', '.join(optional_names)}")

    # GitHub Copilot: trigger interactive OAuth device flow via litellm
    if provider_name == "Github Copilot":
        console.print(
            "\n  [dim]GitHub Copilot authenticates via OAuth device flow.\n"
            "  This will open a browser to authenticate with GitHub.[/dim]\n"
        )
        if Confirm.ask("  Authenticate now?", default=True):
            try:
                import litellm
                console.print("  [dim]Starting device flow authentication...[/dim]")
                # A simple completion call triggers litellm's GitHub Copilot
                # OAuth device flow, which prompts the user to visit a URL
                # and enter a code.  The resulting token is cached by litellm
                # at ~/.config/litellm/github_copilot/api-key.json.
                litellm.completion(
                    model="github_copilot/gpt-4o",
                    messages=[{"role": "user", "content": "Say OK"}],
                    timeout=120,
                )
                console.print("  [green]✓ GitHub Copilot authenticated successfully![/green]")
                return True
            except KeyboardInterrupt:
                console.print("\n  [yellow]Authentication cancelled.[/yellow]")
                return False
            except Exception as e:
                console.print(f"  [red]Authentication failed: {e}[/red]")
                console.print("  [dim]You can try again later with 'pdd setup'.[/dim]")
                return False
        else:
            console.print("  [dim]Skipped. You can authenticate later with 'pdd setup'.[/dim]")
            return False
    print()

    any_saved = False
    for cfg in var_configs:
        env_var = cfg["env_var"]
        label = cfg["label"]
        required = cfg["required"]
        default = cfg["default"]
        hint = cfg["hint"]

        existing_source = _is_key_set(env_var)
        if existing_source:
            console.print(f"  [green]✓[/green] {label} already set ({existing_source})")
            if not Confirm.ask("    Update?", default=False):
                continue

        opt_tag = " [dim](optional)[/dim]" if not required else ""
        if default:
            value = Prompt.ask(f"  {label}{opt_tag} [dim]{hint}[/dim]", default=default)
        else:
            value = Prompt.ask(f"  {label}{opt_tag} [dim]{hint}[/dim]", default="")

        value = value.strip()
        if not value:
            if not required:
                continue
            console.print(f"    [yellow]Skipped[/yellow]")
            continue

        # Vertex AI: special handling for credentials path
        if env_var == "GOOGLE_APPLICATION_CREDENTIALS":
            if value.lower() == "adc":
                console.print(
                    "    [dim]Using Application Default Credentials.\n"
                    "    Make sure you've run: gcloud auth application-default login[/dim]"
                )
                continue
            if not Path(value).exists():
                console.print(f"    [yellow]Warning: file not found at {value}[/yellow]")

        _save_key_to_api_env(env_var, value)
        console.print(f"    [green]✓ Saved[/green]")
        any_saved = True

    if any_saved:
        _ensure_api_env_sourced_in_rc()
        console.print("\n  [dim]Credentials available for this session.[/dim]")

    return any_saved


def add_provider_from_registry() -> bool:
    """
    Browse providers from the reference CSV, let the user pick one,
    handle the API key, and add its models to the user CSV.

    Returns True if any models were added, False if cancelled.
    """
    # ── Step 1: List providers from reference CSV ─────────────────────

    ref_rows = _read_csv(_get_ref_csv_path())
    if not ref_rows:
        console.print("[yellow]No models found in reference CSV.[/yellow]")
        return False

    # Build unique provider list with model counts and api_key
    provider_info: Dict[str, Dict[str, object]] = {}
    for row in ref_rows:
        provider = row.get("provider", "").strip()
        api_key = row.get("api_key", "").strip()
        if not provider:
            continue
        if provider not in provider_info:
            provider_info[provider] = {"api_key": api_key, "count": 0}
        provider_info[provider]["count"] = int(provider_info[provider]["count"]) + 1

    sorted_providers = sorted(provider_info.keys())

    console.print("\n[bold]Add a provider[/bold]\n")
    for idx, prov in enumerate(sorted_providers, 1):
        info = provider_info[prov]
        count = info["count"]
        s = "s" if count != 1 else ""
        console.print(f"  {idx:>2}. {prov:25s}  ({count} model{s})")
    console.print()

    selection = Prompt.ask("Enter number (empty to cancel)")
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

    selected_provider = sorted_providers[choice - 1]
    api_key_var = str(provider_info[selected_provider]["api_key"]) or None

    # ── Step 2: Provider authentication ──────────────────────────────

    if selected_provider in COMPLEX_AUTH_PROVIDERS:
        _setup_complex_provider(selected_provider)
    elif api_key_var:
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
            key_value = Prompt.ask(
                f"Enter your {selected_provider} API key (or press Enter to skip)",
                default="",
            )
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
            else:
                console.print(
                    f"[yellow]Note: No API key configured for {selected_provider}. "
                    f"The LLM may have limited capability.[/yellow]"
                )

    # ── Step 3: Add all models for this provider to user CSV ──────────

    provider_rows = [
        row for row in ref_rows
        if row.get("provider", "").strip() == selected_provider
    ]

    user_csv_path = _get_user_csv_path()
    existing_rows = _read_csv(user_csv_path)
    existing_models = {r.get("model", "").strip() for r in existing_rows}

    added_count = 0
    for row in provider_rows:
        model = row.get("model", "").strip()
        if model and model not in existing_models:
            existing_rows.append(row)
            existing_models.add(model)
            added_count += 1

    if added_count > 0:
        _write_csv_atomic(user_csv_path, existing_rows)
        console.print(
            f"[green]Added {added_count} model(s) for {selected_provider} to {user_csv_path}[/green]"
        )
    else:
        console.print("[yellow]All models for this provider are already configured.[/yellow]")

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