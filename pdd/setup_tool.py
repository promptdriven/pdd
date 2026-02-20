"""
Main orchestrator for `pdd setup`.

Implements a two-phase flow designed for minimal user friction:
  Phase 1 — Interactive CLI bootstrap (0–2 user inputs)
  Phase 2 — Deterministic auto-configuration (pure Python, no LLM calls)
"""
from __future__ import annotations

import getpass
import os
import sys
from pathlib import Path
from typing import Dict, List, Optional, Tuple

from rich.console import Console as _RichConsole
_console = _RichConsole(highlight=False)

# ANSI escape codes for coloring (works without rich)
CYAN = "\033[36m"
WHITE = "\033[37m"
BOLD = "\033[1m"
RESET = "\033[0m"
LIGHT_HORIZONTAL = "\u2500"

# Top providers shown when prompting for an API key (order = display order)
_PROMPT_PROVIDERS = [
    ("anthropic", "Anthropic", "ANTHROPIC_API_KEY"),
    ("gemini", "Google Gemini", "GEMINI_API_KEY"),
    ("openai", "OpenAI", "OPENAI_API_KEY"),
    ("deepseek", "DeepSeek", "DEEPSEEK_API_KEY"),
]


def _print_pdd_logo() -> None:
    """Print the PDD logo in ASCII art with ANSI colors."""
    logo = "\n".join(
        [
            "  +xxxxxxxxxxxxxxx+",
            "xxxxxxxxxxxxxxxxxxxxx+",
            "xxx                 +xx+            PROMPT",
            "xxx      x+           xx+           DRIVEN",
            "xxx        x+         xxx           DEVELOPMENT\u00a9",
            "xxx         x+        xx+",
            "xxx        x+         xx+           COMMAND LINE INTERFACE",
            "xxx      x+          xxx",
            "xxx                +xx+ ",
            "xxx     +xxxxxxxxxxx+",
            "xxx   +xx+",
            "xxx  +xx+",
            "xxx+xx+                             WWW.PROMPTDRIVEN.AI",
            "xxxx+",
            "xx+",
        ]
    )
    print(f"{CYAN}{logo}{RESET}")
    print()
    print(f"{BOLD}{WHITE}Let's get set up quickly with a solid basic configuration!{RESET}")
    print()


def run_setup() -> None:
    """Main entry point for pdd setup. Two-phase flow with post-setup menu."""
    from pdd.cli_detector import detect_and_bootstrap_cli, CliBootstrapResult

    # ── Banner ────────────────────────────────────────────────────────────
    _print_pdd_logo()

    try:
        # ── Phase 1 — CLI Bootstrap (interactive, 0–2 user inputs) ────────
        results: list[CliBootstrapResult] = detect_and_bootstrap_cli()

        for result in results:
            if result.skipped:
                pass
            elif not result.api_key_configured:
                _console.print(
                    f"[yellow]Note: No API key configured for {result.cli_name or 'the CLI'}. "
                    "The agent may have limited capability.[/yellow]"
                )

        # ── Phase 2 — Deterministic Auto-Configuration ────────────────────
        auto_result = _run_auto_phase(results)

        if auto_result:
            found_keys, _model_summary = auto_result
            # Offer post-setup menu before final summary
            try:
                choice = input(
                    "\n  Press Enter to finish, or 'm' for more options: "
                ).strip()
            except (EOFError, KeyboardInterrupt):
                choice = ""

            if choice:
                _run_options_menu()
        else:
            found_keys: list[tuple[str, str]] = []
            _console.print("\n  [yellow]Setup incomplete. Use the menu to configure manually.[/yellow]")
            _run_options_menu()

        # ── Final summary (after menu, so it reflects any changes) ────────
        _print_exit_summary(found_keys, results)

    except KeyboardInterrupt:
        print("\nSetup interrupted — exiting.")
        return


# ---------------------------------------------------------------------------
# Phase 2 — Deterministic auto-configuration
# ---------------------------------------------------------------------------

def _print_step_banner(title: str) -> None:
    """Print a cyan banner for a setup step."""
    print(f"\n{CYAN}{LIGHT_HORIZONTAL * 40}{RESET}")
    print(f"{CYAN}{BOLD}{title}{RESET}")
    print(f"{CYAN}{LIGHT_HORIZONTAL * 40}{RESET}")


def _run_auto_phase(cli_results=None) -> Optional[Tuple[List[Tuple[str, str]], Dict[str, int]]]:
    """Run 3 deterministic setup steps.

    Returns (found_keys, model_summary) on success, or None on failure.
    """
    try:
        # Step 1: Scan API keys
        _print_step_banner("Scanning for API keys...")
        found_keys = _step1_scan_keys()
        print()
        _console.print("[blue]Press Enter to continue to the next step...[/blue]", end="")
        input()

        # Step 2: Configure models + .pddrc
        _print_step_banner("Configuring models...")
        model_summary = _step2_configure_models_and_pddrc(found_keys)
        print()
        _console.print("[blue]Press Enter to continue to the next step...[/blue]", end="")
        input()

        # Step 3: Test + summary
        _print_step_banner("Testing and summarizing...")
        _step3_test_and_summary(found_keys, model_summary, cli_results)

        return (found_keys, model_summary)

    except Exception as exc:
        _console.print(f"\n[yellow]Auto-configuration failed: {exc}[/yellow]")
        return None


# ---------------------------------------------------------------------------
# Step 1 — Scan for API keys
# ---------------------------------------------------------------------------

def _step1_scan_keys() -> List[Tuple[str, str]]:
    """Scan API key env vars referenced in the reference CSV across all sources.

    Returns list of (key_name, source_label) for keys that were found.
    Multi-credential providers (pipe-delimited api_key) are displayed as
    grouped provider lines; single-var providers as individual lines.
    """
    from pdd.provider_manager import _read_csv, parse_api_key_vars
    from pdd.api_key_scanner import _parse_api_env_file, _detect_shell

    # Ensure ~/.pdd exists
    pdd_dir = Path.home() / ".pdd"
    pdd_dir.mkdir(parents=True, exist_ok=True)

    # Gather unique api_key field values from the reference CSV
    ref_path = Path(__file__).parent / "data" / "llm_model.csv"
    ref_rows = _read_csv(ref_path)

    # Build two sets: single-var keys and multi-var provider groups
    single_var_keys: set = set()             # e.g. {"ANTHROPIC_API_KEY", "OPENAI_API_KEY"}
    multi_var_providers: Dict[str, List[str]] = {}  # provider_name -> [var1, var2, ...]
    all_individual_vars: set = set()         # every individual var across all providers

    for row in ref_rows:
        api_key_field = row.get("api_key", "").strip()
        if not api_key_field:
            continue
        env_vars = parse_api_key_vars(api_key_field)
        if len(env_vars) == 1:
            single_var_keys.add(env_vars[0])
            all_individual_vars.add(env_vars[0])
        elif len(env_vars) > 1:
            provider = row.get("provider", "").strip() or api_key_field
            if provider not in multi_var_providers:
                multi_var_providers[provider] = env_vars
            for v in env_vars:
                all_individual_vars.add(v)

    # Load all credential sources once
    dotenv_vals: Dict[str, str] = {}
    try:
        from dotenv import dotenv_values
        for env_path in [Path.cwd() / ".env", Path.home() / ".env"]:
            if env_path.is_file():
                vals = dotenv_values(env_path)
                for k, v in vals.items():
                    if v is not None and k not in dotenv_vals:
                        dotenv_vals[k] = v
    except ImportError:
        pass

    shell_name = _detect_shell()
    api_env_vals: Dict[str, str] = {}
    api_env_label = ""
    if shell_name:
        api_env_path = pdd_dir / f"api-env.{shell_name}"
        api_env_vals = _parse_api_env_file(api_env_path)
        api_env_label = f"~/.pdd/api-env.{shell_name}"

    def _find_source(var: str) -> Optional[str]:
        if var in os.environ:
            return "shell environment"
        if var in api_env_vals:
            return api_env_label
        if var in dotenv_vals:
            return ".env file"
        return None

    found_keys: List[Tuple[str, str]] = []

    # --- Multi-var providers: grouped display ---
    for provider_name, env_vars in sorted(multi_var_providers.items()):
        found_vars = []
        missing_vars = []
        for var in env_vars:
            source = _find_source(var)
            if source:
                found_vars.append(var)
                found_keys.append((var, source))
            else:
                missing_vars.append(var)

        if not found_vars and not missing_vars:
            continue

        total = len(env_vars)
        found_count = len(found_vars)
        if found_count == total:
            _console.print(f"  [green]✓[/green] {provider_name}: {found_count}/{total} vars set")
        elif found_count > 0:
            missing_str = ", ".join(missing_vars)
            _console.print(
                f"  [yellow]![/yellow] {provider_name}: {found_count}/{total} vars set"
                f" (missing: {missing_str})"
            )
        # If found_count == 0, skip — nothing to show for this provider

    # --- Single-var providers: individual display ---
    sorted_single = sorted(single_var_keys)
    max_name_len = max((len(k) for k in sorted_single), default=20) if sorted_single else 20
    for key_name in sorted_single:
        source = _find_source(key_name)
        if source:
            found_keys.append((key_name, source))
            _console.print(f"  [green]✓[/green] {key_name:<{max_name_len}s}   {source}")

    if not found_keys:
        _console.print("  [yellow]✗ No API keys found.[/yellow]\n")
        found_keys = _prompt_for_api_key()

    print(f"\n  {len(found_keys)} API key(s) found.")

    api_env_path = pdd_dir / f"api-env.{shell_name}" if shell_name else pdd_dir / "api-env.bash"
    _console.print(f"  [dim]You can edit your global API keys in {api_env_path}[/dim]")

    return found_keys


def _prompt_for_api_key() -> List[Tuple[str, str]]:
    """Interactively ask the user to add at least one API key.

    Called when no keys are found during scanning. Saves the key to
    ~/.pdd/api-env.{shell} and loads it into the current session.
    Returns list of (key_name, source_label) for newly added keys.
    """
    from pdd.provider_manager import _read_csv, _save_key_to_api_env

    added_keys: List[Tuple[str, str]] = []
    api_env_label = f"~/.pdd/api-env.{os.path.basename(os.environ.get('SHELL', 'bash'))}"

    # Build provider list from reference CSV
    ref_path = Path(__file__).parent / "data" / "llm_model.csv"
    ref_rows = _read_csv(ref_path)
    # Collect unique (provider_display, api_key_env_var) pairs
    seen = set()
    all_providers: List[Tuple[str, str]] = []
    for row in ref_rows:
        provider = row.get("provider", "").strip()
        api_key = row.get("api_key", "").strip()
        if provider and api_key and (provider, api_key) not in seen:
            seen.add((provider, api_key))
            all_providers.append((provider, api_key))
    all_providers.sort(key=lambda x: x[0])

    while True:
        print("  To continue setup, add at least one API key.")
        print("  Providers:")
        for i, (display, env_var) in enumerate(all_providers, 1):
            print(f"    {i}) {display:<25s} ({env_var})")
        skip_idx = len(all_providers) + 1
        print(f"    {skip_idx}) Skip (continue without keys)")

        try:
            choice = input(f"\n  Select provider [1-{skip_idx}]: ").strip()
        except (EOFError, KeyboardInterrupt):
            print()
            break

        # Parse choice
        try:
            choice_num = int(choice)
        except ValueError:
            _console.print(f"  [yellow]Invalid input. Enter a number 1-{skip_idx}.[/yellow]\n")
            continue

        if choice_num == skip_idx:
            break

        if 1 <= choice_num <= len(all_providers):
            display, env_var = all_providers[choice_num - 1]
        else:
            _console.print(f"  [yellow]Invalid input. Enter a number 1-{skip_idx}.[/yellow]\n")
            continue

        # Prompt for the key value (masked)
        try:
            key_value = getpass.getpass(f"  Paste your {env_var}: ").strip()
        except (EOFError, KeyboardInterrupt):
            print()
            break

        if not key_value:
            _console.print("  [yellow]No key entered, skipping.[/yellow]\n")
            continue

        # Save to api-env file and load into current session
        _save_key_to_api_env(env_var, key_value)
        added_keys.append((env_var, api_env_label))
        _console.print(f"  [green]✓[/green] {env_var} saved to {api_env_label}")
        _console.print(f"  [green]✓[/green] Loaded into current session\n")

        # Ask if they want to add another
        try:
            another = input("  Add another key? [y/N]: ").strip().lower()
        except (EOFError, KeyboardInterrupt):
            print()
            break

        if another not in ("y", "yes"):
            break
        print()

    return added_keys


# ---------------------------------------------------------------------------
# Step 2 — Configure models + .pddrc
# ---------------------------------------------------------------------------

def _step2_configure_models_and_pddrc(
    found_keys: List[Tuple[str, str]],
) -> Dict[str, int]:
    """Match found API keys to reference models, write user CSV, and ensure .pddrc.

    Returns {provider_display_name: model_count} for the summary.
    """
    from pdd.provider_manager import (
        _read_csv,
        _write_csv_atomic,
        _get_user_csv_path,
    )
    from pdd.pddrc_initializer import _detect_language, _build_pddrc_content

    found_key_names = {k for k, _ in found_keys}

    # Read reference CSV
    ref_path = Path(__file__).parent / "data" / "llm_model.csv"
    ref_rows = _read_csv(ref_path)

    # Filter reference rows to those whose api_key env vars are all found.
    # Supports pipe-delimited multi-var fields (e.g. "VAR1|VAR2|VAR3").
    # Empty api_key (device flow / local) matches automatically.
    # Skip local-only rows (lm_studio, ollama, localhost base_url).
    from pdd.provider_manager import parse_api_key_vars

    matching_rows: List[Dict[str, str]] = []
    for row in ref_rows:
        api_key_col = row.get("api_key", "").strip()
        provider = row.get("provider", "").strip().lower()
        base_url = row.get("base_url", "").strip()

        # Skip local models
        if provider in ("lm_studio", "ollama"):
            continue
        if base_url and ("localhost" in base_url or "127.0.0.1" in base_url):
            continue

        # Match: all individual env vars must be in found_key_names
        env_vars = parse_api_key_vars(api_key_col)
        if not env_vars:
            # Empty api_key = device flow (e.g. GitHub Copilot) — always match
            matching_rows.append(row)
        elif all(v in found_key_names for v in env_vars):
            matching_rows.append(row)

    # Read existing user CSV and deduplicate (create if missing)
    user_csv_path = _get_user_csv_path()
    user_csv_path.parent.mkdir(parents=True, exist_ok=True)
    existing_rows = _read_csv(user_csv_path)
    existing_models = {r.get("model", "").strip() for r in existing_rows}

    new_rows: List[Dict[str, str]] = []
    for row in matching_rows:
        if row.get("model", "").strip() not in existing_models:
            new_rows.append(row)

    # Count by provider for display
    provider_counts: Dict[str, int] = {}
    all_rows = existing_rows + new_rows
    for row in all_rows:
        provider = row.get("provider", "Unknown").strip()
        if row.get("api_key", "").strip():
            provider_counts[provider] = provider_counts.get(provider, 0) + 1

    # Write merged result
    if new_rows:
        _write_csv_atomic(user_csv_path, all_rows)
        _console.print(f"  [green]✓[/green] {len(new_rows)} new model(s) added to {user_csv_path}")
    else:
        _console.print(f"  [green]✓[/green] All matching models already lodaed in {user_csv_path}")

    total = sum(provider_counts.values())
    _console.print(f"  [green]✓[/green] {total} model(s) configured")
    for provider, count in sorted(provider_counts.items()):
        s = "s" if count != 1 else ""
        print(f"      {provider}: {count} model{s}")

    # ── Check .pddrc ─────────────────────────────────────────────────────
    cwd = Path.cwd()
    pddrc_path = cwd / ".pddrc"
    if pddrc_path.exists():
        _console.print(f"  [green]✓[/green] .pddrc detected at {pddrc_path}")
    else:
        print()
        _console.print("  [bold].pddrc[/bold] configures where PDD puts generated code, tests, and examples.")
        _console.print("  It lives in your project root and lets you define contexts for different")
        _console.print("  parts of your codebase (e.g. frontend vs backend).")
        print()
        try:
            answer = input("  Create .pddrc in this project? [y/Enter to skip] ").strip().lower()
        except (EOFError, KeyboardInterrupt):
            answer = ""

        if answer in ("y", "yes"):
            language = _detect_language(cwd) or "python"
            content = _build_pddrc_content(language)
            try:
                pddrc_path.write_text(content, encoding="utf-8")
                _console.print(f"  [green]✓[/green] Created .pddrc at {pddrc_path} (detected: {language})")
            except OSError as exc:
                _console.print(f"  [yellow]✗ Failed to create .pddrc: {exc}[/yellow]")
        else:
            _console.print("  [dim]Skipped .pddrc creation. You can create one later with pdd setup.")

    return provider_counts


# ---------------------------------------------------------------------------
# Step 3 — Test one model + print summary
# ---------------------------------------------------------------------------

def _step3_test_and_summary(
    found_keys: List[Tuple[str, str]],
    model_summary: Dict[str, int],
    cli_results=None,
) -> None:
    """Test the first available cloud model and print the final summary."""
    from pdd.provider_manager import _read_csv, _get_user_csv_path, parse_api_key_vars

    user_csv_path = _get_user_csv_path()
    rows = _read_csv(user_csv_path)
    test_result = "Skipped (no models configured)"

    # Pick first cloud model that has all auth configured.
    # Uses the pipe-delimited api_key convention: check every env var is set.
    cloud_row = None
    for row in rows:
        api_key_field = row.get("api_key", "").strip()
        env_vars = parse_api_key_vars(api_key_field)
        if not env_vars:
            # Empty = device flow (e.g. GitHub Copilot) — pick it
            cloud_row = row
            break
        if all(os.getenv(v, "") for v in env_vars):
            cloud_row = row
            break

    if cloud_row:
        test_model = cloud_row.get("model", "")
        try:
            import litellm  # noqa: F401
            from pdd.model_tester import _run_test
            import threading
            import time as time_module

            sys.stdout.write(f"  Testing {test_model}...")
            sys.stdout.flush()

            # Run in a thread so we can print dots while waiting
            test_result_holder: list = [None]

            def _do_test() -> None:
                test_result_holder[0] = _run_test(cloud_row)

            t = threading.Thread(target=_do_test, daemon=True)
            t.start()

            elapsed = 0.0
            while t.is_alive() and elapsed < 8.0:
                t.join(timeout=1.0)
                if t.is_alive():
                    sys.stdout.write(".")
                    sys.stdout.flush()
                    elapsed += 1.0

            sys.stdout.write("\n")
            if t.is_alive():
                result = {
                    "success": False,
                    "duration_s": elapsed,
                    "cost": 0.0,
                    "error": "Request timed out (8s)",
                    "tokens": None,
                }
            else:
                result = test_result_holder[0] or {
                    "success": False,
                    "duration_s": 0.0,
                    "cost": 0.0,
                    "error": "Unknown error",
                    "tokens": None,
                }

            if result["success"]:
                test_result = f"[green]✓[/green] {test_model} responded OK ({result['duration_s']:.1f}s)"
            else:
                test_result = f"[yellow]✗ {test_model} failed: {result['error']}[/yellow]"
        except ImportError:
            test_result = "[yellow]Skipped (litellm not installed)[/yellow]"
    _console.print(f"  {test_result}")

    # ── Summary ───────────────────────────────────────────────────────────
    print()
    _console.print("  [bold green]PDD Setup Complete![/bold green]")
    print()

    # CLIs
    if cli_results:
        configured = [r for r in cli_results if not r.skipped and r.cli_name]
        skipped = [r for r in cli_results if r.skipped]
        if configured:
            names = ", ".join(r.cli_name for r in configured)
            no_key = [r for r in configured if not r.api_key_configured]
            if no_key:
                no_key_names = ", ".join(r.cli_name for r in no_key)
                _console.print(f"    CLI:       [green]✓[/green] {names} configured ([yellow]{no_key_names} missing API key[/yellow])")
            else:
                _console.print(f"    CLI:       [green]✓[/green] {names} configured")
        elif skipped:
            _console.print("    CLI:       [yellow]✗[/yellow] skipped")
        else:
            _console.print("    CLI:       [dim]not configured[/dim]")
    else:
        _console.print("    CLI:       [dim]not configured[/dim]")

    # API Keys
    if found_keys:
        _console.print(f"    API Keys:  [green]\u2713[/green] {len(found_keys)} found")
    else:
        _console.print("    API Keys:  [red]\u2717[/red] 0 found")

    # Models
    total_models = sum(model_summary.values())
    parts = ", ".join(f"{p}: {c}" for p, c in sorted(model_summary.items()))
    if parts:
        print(f"    Models:    {total_models} configured ({parts}) in {_get_user_csv_path()}")
    else:
        print(f"    Models:    {total_models} configured in {_get_user_csv_path()}")

    # .pddrc
    pddrc_path = Path.cwd() / ".pddrc"
    if pddrc_path.exists():
        _console.print("    .pddrc:    [green]\u2713[/green] exists")
    else:
        _console.print("    .pddrc:    [red]\u2717[/red] not created")

    # Test
    _console.print(f"    Test:      {test_result}")

    # Exit summary is handled by run_setup after the options menu


# ---------------------------------------------------------------------------
# Exit summary — files, quick start, tips
# ---------------------------------------------------------------------------

_FAT_DIVIDER = "\u2501" * 80   # ━
_THIN_DIVIDER = "\u2500" * 80  # ─
_BULLET = "\u2022"             # •

_SUCCESS_PYTHON_TEMPLATE = """\
Write a python script to print "You did it, <Username>!!!" to the console.
Do not write anything except that message.
Capitalize the username."""


def _create_sample_prompt() -> str:
    """Create the sample prompt file if it doesn't exist. Returns the filename."""
    prompt_file = Path("success_python.prompt")
    if not prompt_file.exists():
        prompt_file.write_text(_SUCCESS_PYTHON_TEMPLATE)
    return str(prompt_file)


def _print_exit_summary(found_keys: List[Tuple[str, str]], cli_results=None) -> None:
    """Write PDD-SETUP-SUMMARY.txt and print QUICK START + LEARN MORE to terminal."""
    from pdd.api_key_scanner import _detect_shell

    shell = _detect_shell() or "bash"
    pdd_dir = Path.home() / ".pdd"
    api_env_path = pdd_dir / f"api-env.{shell}"
    user_csv_path = pdd_dir / "llm_model.csv"
    sample_prompt = _create_sample_prompt()

    # Build valid_keys dict: key_name -> actual value
    valid_keys: Dict[str, str] = {}
    for key_name, _source in found_keys:
        val = os.environ.get(key_name, "")
        if val.strip():
            valid_keys[key_name] = val

    # Determine which files were created/configured
    saved_files: List[str] = []
    if api_env_path.exists():
        saved_files.append(str(api_env_path))
    if user_csv_path.exists():
        saved_files.append(str(user_csv_path))

    created_pdd_dir = pdd_dir.exists()

    # Check if shell init file was updated
    from pdd.provider_manager import _get_shell_rc_path
    rc_path = _get_shell_rc_path()
    init_file_updated: Optional[str] = None
    if rc_path and rc_path.exists():
        rc_content = rc_path.read_text(encoding="utf-8")
        if "api-env" in rc_content:
            init_file_updated = str(rc_path)

    # Source command
    if shell == "sh":
        source_cmd = f". {api_env_path}"
    else:
        source_cmd = f"source {api_env_path}"

    # ── Build full summary (saved to file) ───────────────────────────────
    lines: List[str] = []
    lines.append("")
    lines.append("")
    lines.append(_FAT_DIVIDER)
    lines.append("PDD Setup Complete!")
    lines.append(_FAT_DIVIDER)
    lines.append("")

    # CLIs configured
    lines.append("CLIs Configured:")
    lines.append("")
    if cli_results:
        configured = [r for r in cli_results if not r.skipped and r.cli_name]
        if configured:
            for r in configured:
                key_status = "API key set" if r.api_key_configured else "no API key"
                lines.append(f"  {r.cli_name} ({r.provider}) — {key_status}")
        else:
            lines.append("  None")
    else:
        lines.append("  None")
    lines.append("")

    # API Keys configured
    lines.append("API Keys Configured:")
    lines.append("")
    if valid_keys:
        for kn, kv in valid_keys.items():
            masked = f"{kv[:8]}...{kv[-4:]}" if len(kv) > 12 else "***"
            lines.append(f"  {kn}: {masked}")
    else:
        lines.append("  None")
    lines.append("")

    # Files created
    lines.append("Files created and configured:")
    lines.append("")

    file_descriptions: List[Tuple[str, str]] = []
    if created_pdd_dir:
        file_descriptions.append(("~/.pdd/", "PDD configuration directory"))
    for fp in saved_files:
        if "api-env." in fp:
            file_descriptions.append((fp, f"API environment variables ({shell} shell)"))
        elif "llm_model.csv" in fp:
            file_descriptions.append((fp, "LLM model configuration"))
    file_descriptions.append((sample_prompt, "Sample prompt for testing"))
    if init_file_updated:
        file_descriptions.append((init_file_updated, "Shell startup file (updated to source API environment)"))
    file_descriptions.append(("PDD-SETUP-SUMMARY.txt", "This summary"))

    max_path_len = max(len(p) for p, _ in file_descriptions) if file_descriptions else 0
    for fp, desc in file_descriptions:
        lines.append(f"{fp:<{max_path_len + 2}}{desc}")

    lines.append("")
    lines.append(_THIN_DIVIDER)
    lines.append("")
    lines.append("QUICK START:")
    lines.append("")
    lines.append("1. Generate code from the sample prompt:")
    lines.append("   pdd generate success_python.prompt")
    lines.append("")
    lines.append(_THIN_DIVIDER)
    lines.append("")
    lines.append("LEARN MORE:")
    lines.append("")
    lines.append(f"{_BULLET} PDD documentation: pdd --help")
    lines.append(f"{_BULLET} PDD website: https://promptdriven.ai/")
    lines.append(f"{_BULLET} Discord community: https://discord.gg/Yp4RTh8bG7")
    lines.append("")
    lines.append("TIPS:")
    lines.append("")
    lines.append(f"{_BULLET} Start with simple prompts and gradually increase complexity")
    lines.append(f"{_BULLET} Try out 'pdd test' with your prompt+code to create test(s) pdd can use to automatically verify and fix your output code")
    lines.append(f"{_BULLET} Try out 'pdd example' with your prompt+code to create examples which help pdd do better")
    lines.append("")
    lines.append(f"{_BULLET} As you get comfortable, learn configuration settings, including the .pddrc file, PDD_GENERATE_OUTPUT_PATH, and PDD_TEST_OUTPUT_PATH")
    lines.append(f"{_BULLET} For larger projects, use Makefiles and/or 'pdd sync'")
    lines.append(f"{_BULLET} For ongoing substantial projects, learn about llm_model.csv and the --strength,")
    lines.append(f"  --temperature, and --time options to optimize model cost, latency, and output quality")
    lines.append("")
    lines.append(f"{_BULLET} Use 'pdd --help' to explore all available commands")
    lines.append("")
    lines.append(f"Problems? Shout out on our Discord for help! https://discord.gg/Yp4RTh8bG7")

    if api_env_path.exists():
        lines.append("")
        lines.append(_THIN_DIVIDER)
        lines.append("")
        lines.append("IMPORTANT: To use your API keys in this terminal session, run:")
        lines.append(f"    {source_cmd}")
        lines.append("")
        lines.append("New terminal windows will load keys automatically.")

    summary_text = "\n".join(lines)

    # Write PDD-SETUP-SUMMARY.txt
    summary_path = Path("PDD-SETUP-SUMMARY.txt")
    summary_path.write_text(summary_text, encoding="utf-8")

    # ── Print only QUICK START + LEARN MORE to terminal ──────────────────
    print()
    print()
    _console.print("[bold green]Completed setup.[/bold green]")
    print()
    print(_THIN_DIVIDER)
    print()
    print("QUICK START:")
    print()
    print("1. Generate code from the sample prompt:")
    print("   pdd generate success_python.prompt")
    print()
    print(_THIN_DIVIDER)
    print()
    print("LEARN MORE:")
    print()
    print(f"{_BULLET} PDD documentation: pdd --help")
    print(f"{_BULLET} PDD website: https://promptdriven.ai/")
    print(f"{_BULLET} Discord community: https://discord.gg/Yp4RTh8bG7")
    print()
    _console.print(f"[dim]Full summary saved to PDD-SETUP-SUMMARY.txt[/dim]")
    print()
    if api_env_path.exists():
        _console.print(
            f"[bold yellow]Important:[/bold yellow] For updates to API keys in this terminal session, run:\n"
            f"\n    {source_cmd}\n\n"
            f"[dim]New terminal windows will load updated keys automatically.[/dim]"
        )
        print()


# ---------------------------------------------------------------------------
# Options menu (post-setup or fallback)
# ---------------------------------------------------------------------------

def _run_options_menu() -> None:
    """Menu loop for manual configuration options."""
    print()

    from pdd.provider_manager import add_provider_from_registry
    from pdd.model_tester import test_model_interactive

    while True:
        print("  Options:")
        print("    1. Add a provider")
        print("    2. Test a model")
        print()

        try:
            choice = input("  Select an option (Enter to finish): ").strip()
        except (EOFError, KeyboardInterrupt):
            print()
            break

        if not choice:
            break

        if choice == "1":
            try:
                add_provider_from_registry()
            except Exception as exc:
                print(f"  Error adding provider: {exc}")
        elif choice == "2":
            try:
                test_model_interactive()
            except Exception as exc:
                print(f"  Error testing model: {exc}")
        else:
            _console.print("  [yellow]Invalid option. Please enter 1 or 2.[/yellow]")

        print()


if __name__ == "__main__":
    run_setup()
