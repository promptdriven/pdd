from __future__ import annotations

import os
import sys
import threading
import time as time_module
from pathlib import Path
from typing import Any, Dict, List, Optional, Tuple

import pandas as pd
from rich.console import Console

from rich.table import Table

console = Console()


def _load_user_csv() -> Optional[pd.DataFrame]:
    """Load the user's LLM model CSV from ~/.pdd/llm_model.csv.

    Returns:
        DataFrame with model data, or None if file doesn't exist or is empty.
    """
    csv_path = Path.home() / ".pdd" / "llm_model.csv"
    if not csv_path.is_file():
        return None

    try:
        df = pd.read_csv(csv_path)
    except Exception as e:
        console.print(f"[red]Failed to read {csv_path}: {e}[/red]")
        return None

    if df.empty:
        return None

    # Ensure expected columns exist
    required_cols = {"provider", "model", "api_key"}
    missing = required_cols - set(df.columns)
    if missing:
        console.print(f"[red]CSV is missing required columns: {missing}[/red]")
        return None

    # Normalise nullable string columns
    for col in ("api_key", "base_url", "location"):
        if col in df.columns:
            df[col] = df[col].fillna("").astype(str)

    # Normalise numeric cost columns
    for col in ("input", "output"):
        if col in df.columns:
            df[col] = pd.to_numeric(df[col], errors="coerce").fillna(0.0)

    return df


def _resolve_api_key(row: Dict[str, Any]) -> Tuple[Optional[str], str]:
    """Resolve the API key for a model row.

    Returns:
        (key_value_or_none, status_string)
        status_string is a human-readable description like '✓ Found (OPENAI_API_KEY)'.
    """
    key_name: str = str(row.get("api_key", "")).strip()

    # No env var configured — litellm will use its own defaults
    if not key_name:
        return None, "(no key configured)"

    # Check environment
    key_value = os.getenv(key_name, "")
    if key_value:
        return key_value.strip(), f"✓ Found ({key_name})"

    # Check if a .env file might have it (dotenv may not be loaded yet)
    try:
        from dotenv import dotenv_values

        env_path = Path.home() / ".pdd" / ".env"
        if not env_path.is_file():
            env_path = Path.cwd() / ".env"
        if env_path.is_file():
            vals = dotenv_values(env_path)
            val = vals.get(key_name, "")
            if val:
                return val.strip(), f"✓ Found ({key_name} via .env)"
    except ImportError:
        pass

    return None, f"✗ Not found ({key_name})"


def _resolve_base_url(row: Dict[str, Any]) -> Optional[str]:
    """Return the base_url for the model, if any."""
    base_url: str = str(row.get("base_url", "")).strip()
    if base_url:
        return base_url

    # LM Studio convention
    model_name = str(row.get("model", "")).lower()
    provider = str(row.get("provider", "")).lower()
    if model_name.startswith("lm_studio/") or provider == "lm_studio":
        return os.getenv("LM_STUDIO_API_BASE", "http://localhost:1234/v1")

    return None


def _resolve_provider_auth(row: Dict[str, Any]) -> List[Tuple[str, str, bool]]:
    """Resolve all auth-related env vars for a model row.

    Returns a list of (label, status_string, is_ok) tuples.
    Driven by the CSV api_key field (pipe-delimited for multi-credential providers).
    """
    from pdd.provider_manager import parse_api_key_vars

    api_key_field = str(row.get("api_key", "")).strip()
    env_vars = parse_api_key_vars(api_key_field)

    if not env_vars:
        # Empty api_key — device flow (e.g. GitHub Copilot) or local model
        return [("Auth", "Device flow / no key needed", True)]

    results: List[Tuple[str, str, bool]] = []
    for var in env_vars:
        value = os.getenv(var, "")
        if value:
            # Extra validation for credential file paths
            if var == "GOOGLE_APPLICATION_CREDENTIALS" and not Path(value).is_file():
                results.append((var, f"⚠ Path set but file not found ({var})", False))
            else:
                results.append((var, f"✓ Found ({var})", True))
        else:
            results.append((var, f"✗ Not found ({var})", False))

    return results


def _calculate_cost(
    prompt_tokens: int,
    completion_tokens: int,
    input_price_per_m: float,
    output_price_per_m: float,
) -> float:
    """Calculate cost from token counts and per-million-token prices."""
    return (prompt_tokens * input_price_per_m + completion_tokens * output_price_per_m) / 1_000_000.0


def _classify_error(exc: Exception) -> str:
    """Return a concise, user-friendly error description."""
    msg = str(exc).lower()
    exc_type = type(exc).__name__

    # Authentication errors
    if "authentication" in msg or "401" in msg or "403" in msg or "invalid api key" in msg:
        return f"Authentication error — check your API key ({exc_type})"

    # Connection refused (typically local servers)
    if "connection refused" in msg or "connect" in msg and "refused" in msg:
        return f"Connection refused — is the local server running? ({exc_type})"

    # Model not found
    if "not found" in msg or "404" in msg or "does not exist" in msg:
        return f"Model not found — check the model name ({exc_type})"

    # Timeout
    if "timeout" in msg or "timed out" in msg:
        return f"Request timed out ({exc_type})"

    # Rate limit
    if "rate" in msg and "limit" in msg or "429" in msg:
        return f"Rate limited — try again later ({exc_type})"

    # Generic
    return f"{exc_type}: {exc}"


def _run_test(row: Dict[str, Any]) -> Dict[str, Any]:
    """Run a single litellm.completion() test against the given model row.

    Returns a dict with keys: success, duration_s, cost, error, tokens.
    """
    import litellm
    from pdd.provider_manager import parse_api_key_vars

    model_name: str = str(row.get("model", ""))
    base_url = _resolve_base_url(row)

    kwargs: Dict[str, Any] = {
        "model": model_name,
        "messages": [{"role": "user", "content": "Say OK"}],
        "timeout": 8,
    }

    # Resolve API key using the pipe-delimited convention:
    #   Single var  → pass as api_key=
    #   Multi var   → litellm reads from os.environ (don't pass api_key=)
    #   Empty       → device flow / local (don't pass api_key=)
    api_key_field = str(row.get("api_key", "")).strip()
    env_vars = parse_api_key_vars(api_key_field)

    if len(env_vars) == 1:
        key_value = os.getenv(env_vars[0], "")
        if key_value:
            kwargs["api_key"] = key_value.strip()
    # Multi-var and empty: litellm reads env vars automatically

    if base_url:
        kwargs["base_url"] = base_url
        kwargs["api_base"] = base_url

    start = time_module.time()
    try:
        response = litellm.completion(**kwargs)
        duration = time_module.time() - start

        # Extract token usage
        usage = getattr(response, "usage", None)
        prompt_tokens = getattr(usage, "prompt_tokens", 0) or 0
        completion_tokens = getattr(usage, "completion_tokens", 0) or 0

        input_price = float(row.get("input", 0.0))
        output_price = float(row.get("output", 0.0))
        cost = _calculate_cost(prompt_tokens, completion_tokens, input_price, output_price)

        return {
            "success": True,
            "duration_s": duration,
            "cost": cost,
            "error": None,
            "tokens": {"prompt": prompt_tokens, "completion": completion_tokens},
        }

    except Exception as exc:
        duration = time_module.time() - start
        return {
            "success": False,
            "duration_s": duration,
            "cost": 0.0,
            "error": _classify_error(exc),
            "tokens": None,
        }


def _display_model_list(
    df: pd.DataFrame,
    results: Dict[int, Dict[str, Any]],
) -> None:
    """Display the model list as a rich table with any persisted test results."""
    table = Table(title="Available Models", show_lines=False, pad_edge=True)
    table.add_column("#", style="bold cyan", justify="right", width=4)
    table.add_column("Provider", style="white", min_width=10)
    table.add_column("Model", style="bright_white", min_width=30)
    table.add_column("Input $/M", justify="right", min_width=8)
    table.add_column("Output $/M", justify="right", min_width=8)
    table.add_column("ELO", justify="right", min_width=6)
    table.add_column("Last Test", min_width=25)

    for idx, row in df.iterrows():
        i = int(idx)
        provider = str(row.get("provider", ""))
        model = str(row.get("model", ""))
        input_cost = row.get("input", 0.0)
        output_cost = row.get("output", 0.0)
        elo = row.get("coding_arena_elo", "")

        # Format costs
        input_str = f"${float(input_cost):.2f}" if pd.notna(input_cost) else "—"
        output_str = f"${float(output_cost):.2f}" if pd.notna(output_cost) else "—"
        elo_str = str(int(elo)) if pd.notna(elo) and elo else "—"

        # Test result
        if i in results:
            r = results[i]
            if r["success"]:
                test_str = f"[green]✓ OK ({r['duration_s']:.1f}s, ${r['cost']:.4f})[/green]"
            else:
                # Truncate error for table display
                err = r["error"] or "Unknown error"
                if len(err) > 40:
                    err = err[:37] + "..."
                test_str = f"[red]✗ {err}[/red]"
        else:
            test_str = "—"

        table.add_row(
            str(i + 1),
            provider,
            model,
            input_str,
            output_str,
            elo_str,
            test_str,
        )

    console.print(table)


def test_model_interactive() -> None:
    """Interactive model tester.

    Shows models from ~/.pdd/llm_model.csv, lets the user pick one to test,
    runs a minimal litellm.completion() call, and displays diagnostics.
    Loops until the user enters empty input or 'q'.
    """
    df = _load_user_csv()
    if df is None:
        console.print(
            "[yellow]No user model CSV found at ~/.pdd/llm_model.csv or it is empty.[/yellow]"
        )
        console.print(
            "[dim]Run [bold]pdd setup[/bold] to configure your models first.[/dim]"
        )
        return

    # Session-persisted test results: index -> result dict
    results: Dict[int, Dict[str, Any]] = {}

    while True:
        console.print()
        _display_model_list(df, results)
        console.print()

        try:
            choice = console.input(
                "[bold cyan]Enter model number to test (or empty to quit): [/bold cyan]"
            ).strip()
        except (EOFError, KeyboardInterrupt):
            console.print("\n[dim]Exiting model tester.[/dim]")
            return

        if not choice or choice.lower() == "q":
            console.print("[dim]Exiting model tester.[/dim]")
            return

        # Parse selection
        try:
            idx = int(choice) - 1
        except ValueError:
            console.print(f"[red]Invalid input: '{choice}'. Enter a number or 'q'.[/red]")
            continue

        if idx < 0 or idx >= len(df):
            console.print(f"[red]Invalid selection. Choose 1–{len(df)}.[/red]")
            continue

        row = df.iloc[idx].to_dict()
        model_name = str(row.get("model", ""))
        provider = str(row.get("provider", ""))

        console.print()
        console.print(f"[bold]Testing: [bright_white]{model_name}[/bright_white] ({provider})[/bold]")
        console.print("─" * 50)

        # Diagnostics: provider authentication
        auth_checks = _resolve_provider_auth(row)
        for label, status_str, is_ok in auth_checks:
            color = "green" if is_ok else "red"
            console.print(f"  {label + ':':<13s}[{color}]{status_str}[/{color}]")

        # Diagnostics: base URL
        base_url = _resolve_base_url(row)
        if base_url:
            console.print(f"  Base URL:  [dim]{base_url}[/dim]")

        console.print()
        sys.stdout.write("  Sending test prompt...")
        sys.stdout.flush()

        # Run the test in a thread, printing dots while waiting
        test_result_holder: List[Optional[Dict[str, Any]]] = [None]

        def _do_test() -> None:
            test_result_holder[0] = _run_test(row)

        t = threading.Thread(target=_do_test, daemon=True)
        t.start()

        elapsed = 0.0
        while t.is_alive() and elapsed < 8.0:
            t.join(timeout=1.0)
            if t.is_alive():
                sys.stdout.write(".")
                sys.stdout.flush()
                elapsed += 1.0

        if t.is_alive():
            # Timeout — thread is still running; don't wait further
            sys.stdout.write("\n")
            result = {
                "success": False,
                "duration_s": elapsed,
                "cost": 0.0,
                "error": "Request timed out (8s)",
                "tokens": None,
            }
        else:
            sys.stdout.write("\n")
            result = test_result_holder[0] or {
                "success": False,
                "duration_s": 0.0,
                "cost": 0.0,
                "error": "Unknown error",
                "tokens": None,
            }

        results[idx] = result

        if result["success"]:
            tokens = result.get("tokens") or {}
            token_info = ""
            if tokens:
                token_info = f", {tokens.get('prompt', 0)}+{tokens.get('completion', 0)} tokens"
            console.print(
                f"  LLM call   [green]✓ OK[/green] "
                f"({result['duration_s']:.1f}s, ${result['cost']:.4f}{token_info})"
            )
        else:
            console.print(f"  LLM call   [red]✗ {result['error']}[/red]")

        console.print()