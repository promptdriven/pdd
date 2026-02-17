"""
Main orchestrator for `pdd setup`.

Implements a two-phase flow designed for minimal user friction:
  Phase 1 — Interactive CLI bootstrap (0–2 user inputs)
  Phase 2 — Deterministic auto-configuration (pure Python, no LLM calls)
"""
from __future__ import annotations

import getpass
import json
import os
import urllib.error
import urllib.request
from pathlib import Path
from typing import Dict, List, Optional, Tuple

from rich.console import Console as _RichConsole
_console = _RichConsole()

# Top providers shown when prompting for an API key (order = display order)
_PROMPT_PROVIDERS = [
    ("anthropic", "Anthropic", "ANTHROPIC_API_KEY"),
    ("gemini", "Google Gemini", "GEMINI_API_KEY"),
    ("openai", "OpenAI", "OPENAI_API_KEY"),
    ("deepseek", "DeepSeek", "DEEPSEEK_API_KEY"),
]


def run_setup() -> None:
    """Main entry point for pdd setup. Two-phase flow with fallback."""
    from pdd.cli_detector import detect_and_bootstrap_cli, CliBootstrapResult

    # ── Banner ────────────────────────────────────────────────────────────
    print()
    print("  ╭──────────────────────────────╮")
    print("  │        pdd setup             │")
    print("  ╰──────────────────────────────╯")
    print()

    try:
        # ── Phase 1 — CLI Bootstrap (interactive, 0–2 user inputs) ────────
        result: CliBootstrapResult = detect_and_bootstrap_cli()

        if result.cli_name == "":
            print(
                "Agentic features require at least one CLI tool. "
                "Run `pdd setup` again when ready."
            )
            return

        if not result.api_key_configured:
            print(
                "Note: No API key configured. "
                "The agent may have limited capability."
            )

        # ── Phase 2 — Deterministic Auto-Configuration ────────────────────
        auto_success = _run_auto_phase()

        if not auto_success:
            _run_fallback_menu()

        print()
        _console.print("[green]Setup complete. Happy prompting![/green]")
        print()

    except KeyboardInterrupt:
        print("\nSetup interrupted — exiting.")
        return


# ---------------------------------------------------------------------------
# Phase 2 — Deterministic auto-configuration
# ---------------------------------------------------------------------------

def _run_auto_phase() -> bool:
    """Run 4 deterministic setup steps. Returns True on success."""
    try:
        # Step 1: Scan API keys
        print("\n[Step 1/4] Scanning for API keys...")
        found_keys = _step1_scan_keys()
        input("\nPress Enter to continue to the next step...")

        # Step 2: Configure models
        print("\n[Step 2/4] Configuring models...")
        model_summary = _step2_configure_models(found_keys)
        input("\nPress Enter to continue to the next step...")

        # Step 3: Local LLMs + .pddrc
        print("\n[Step 3/4] Checking local LLMs and .pddrc...")
        local_summary = _step3_local_llms_and_pddrc()
        input("\nPress Enter to continue to the next step...")

        # Step 4: Test + summary
        print("\n[Step 4/4] Testing and summarizing...")
        _step4_test_and_summary(found_keys, model_summary, local_summary)

        return True

    except Exception as exc:
        print(f"\nAuto-configuration failed: {exc}")
        print("Falling back to manual setup...")
        return False


# ---------------------------------------------------------------------------
# Step 1 — Scan for API keys
# ---------------------------------------------------------------------------

def _step1_scan_keys() -> List[Tuple[str, str]]:
    """Scan all known API key env vars across all sources.

    Returns list of (key_name, source_label) for keys that were found.
    """
    from pdd.litellm_registry import PROVIDER_API_KEY_MAP
    from pdd.api_key_scanner import _parse_api_env_file, _detect_shell

    # Ensure ~/.pdd exists
    pdd_dir = Path.home() / ".pdd"
    pdd_dir.mkdir(parents=True, exist_ok=True)

    # Gather all unique env var names to check
    all_key_names = sorted(set(PROVIDER_API_KEY_MAP.values()))

    # Load sources once
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

    # Scan each key
    found_keys: List[Tuple[str, str]] = []
    max_name_len = max(len(k) for k in all_key_names) if all_key_names else 20

    for key_name in all_key_names:
        if key_name in os.environ:
            source = "shell environment"
            found_keys.append((key_name, source))
            print(f"  ✓ {key_name:<{max_name_len}s}   {source}")
        elif key_name in api_env_vals:
            source = api_env_label
            found_keys.append((key_name, source))
            print(f"  ✓ {key_name:<{max_name_len}s}   {source}")
        elif key_name in dotenv_vals:
            source = ".env file"
            found_keys.append((key_name, source))
            print(f"  ✓ {key_name:<{max_name_len}s}   {source}")

    if not found_keys:
        print("  ✗ No API keys found.\n")
        found_keys = _prompt_for_api_key()

    print(f"\n  {len(found_keys)} API key(s) found.")
    return found_keys


def _prompt_for_api_key() -> List[Tuple[str, str]]:
    """Interactively ask the user to add at least one API key.

    Called when no keys are found during scanning. Saves the key to
    ~/.pdd/api-env.{shell} and loads it into the current session.
    Returns list of (key_name, source_label) for newly added keys.
    """
    from pdd.litellm_registry import PROVIDER_API_KEY_MAP, PROVIDER_DISPLAY_NAMES
    from pdd.provider_manager import _save_key_to_api_env, _get_api_env_path

    added_keys: List[Tuple[str, str]] = []
    api_env_label = f"~/.pdd/api-env.{os.path.basename(os.environ.get('SHELL', 'bash'))}"

    while True:
        print("  To continue setup, add at least one API key.")
        print("  Popular providers:")
        for i, (_, display, env_var) in enumerate(_PROMPT_PROVIDERS, 1):
            print(f"    {i}) {display:<20s} ({env_var})")
        other_idx = len(_PROMPT_PROVIDERS) + 1
        skip_idx = other_idx + 1
        print(f"    {other_idx}) Other provider")
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
            print(f"  Invalid input. Enter a number 1-{skip_idx}.\n")
            continue

        if choice_num == skip_idx:
            break

        if choice_num == other_idx:
            # Show all providers
            all_providers = sorted(
                PROVIDER_API_KEY_MAP.items(),
                key=lambda x: PROVIDER_DISPLAY_NAMES.get(x[0], x[0]),
            )
            print("\n  All providers:")
            for i, (pid, env_var) in enumerate(all_providers, 1):
                display = PROVIDER_DISPLAY_NAMES.get(pid, pid)
                print(f"    {i}) {display:<25s} ({env_var})")
            try:
                sub_choice = input(f"\n  Select provider [1-{len(all_providers)}]: ").strip()
                sub_num = int(sub_choice)
                if 1 <= sub_num <= len(all_providers):
                    _, env_var = all_providers[sub_num - 1]
                    display = PROVIDER_DISPLAY_NAMES.get(
                        all_providers[sub_num - 1][0],
                        all_providers[sub_num - 1][0],
                    )
                else:
                    print("  Invalid selection.\n")
                    continue
            except (ValueError, EOFError, KeyboardInterrupt):
                print()
                continue
        elif 1 <= choice_num <= len(_PROMPT_PROVIDERS):
            _, display, env_var = _PROMPT_PROVIDERS[choice_num - 1]
        else:
            print(f"  Invalid input. Enter a number 1-{skip_idx}.\n")
            continue

        # Prompt for the key value (masked)
        try:
            key_value = getpass.getpass(f"  Paste your {env_var}: ").strip()
        except (EOFError, KeyboardInterrupt):
            print()
            break

        if not key_value:
            print("  No key entered, skipping.\n")
            continue

        # Save to api-env file and load into current session
        _save_key_to_api_env(env_var, key_value)
        added_keys.append((env_var, api_env_label))
        print(f"  ✓ {env_var} saved to {api_env_label}")
        print(f"  ✓ Loaded into current session\n")

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
# Step 2 — Configure models from reference CSV
# ---------------------------------------------------------------------------

def _step2_configure_models(
    found_keys: List[Tuple[str, str]],
) -> Dict[str, int]:
    """Match found API keys to reference models and write user CSV.

    Returns {provider_display_name: model_count} for the summary.
    """
    from pdd.provider_manager import (
        _read_csv,
        _write_csv_atomic,
        _get_user_csv_path,
    )

    found_key_names = {k for k, _ in found_keys}

    # Read reference CSV
    ref_path = Path(__file__).parent / "data" / "llm_model.csv"
    ref_rows = _read_csv(ref_path)

    # Filter reference rows to those whose api_key matches a found key
    # Skip local-only rows (lm_studio, ollama — handled in step 3)
    matching_rows: List[Dict[str, str]] = []
    for row in ref_rows:
        api_key_col = row.get("api_key", "").strip()
        provider = row.get("provider", "").strip().lower()
        base_url = row.get("base_url", "").strip()

        # Skip local models
        if provider in ("lm_studio", "ollama"):
            continue
        # Skip rows with base_url pointing to localhost (local models)
        if base_url and ("localhost" in base_url or "127.0.0.1" in base_url):
            continue
        # Match on api_key
        if api_key_col and api_key_col in found_key_names:
            matching_rows.append(row)

    # Read existing user CSV and deduplicate
    user_csv_path = _get_user_csv_path()
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
        # Only count cloud models (with api_key)
        if row.get("api_key", "").strip():
            provider_counts[provider] = provider_counts.get(provider, 0) + 1

    # Write merged result
    if new_rows:
        _write_csv_atomic(user_csv_path, all_rows)
        print(f"  ✓ {len(new_rows)} new model(s) added to {user_csv_path}")
    else:
        print(f"  ✓ All matching models already in {user_csv_path}")

    total = sum(provider_counts.values())
    print(f"  ✓ {total} cloud model(s) configured")
    for provider, count in sorted(provider_counts.items()):
        s = "s" if count != 1 else ""
        print(f"    {provider}: {count} model{s}")

    return provider_counts


# ---------------------------------------------------------------------------
# Step 3 — Local LLMs + .pddrc
# ---------------------------------------------------------------------------

def _step3_local_llms_and_pddrc() -> Dict[str, List[str]]:
    """Check local LLMs and ensure .pddrc exists.

    Returns {provider: [model_names]} for local LLMs found.
    """
    from pdd.pddrc_initializer import _detect_language, _build_pddrc_content

    local_summary: Dict[str, List[str]] = {}

    # ── Check Ollama ──────────────────────────────────────────────────────
    ollama_models = _query_local_server(
        url="http://localhost:11434/api/tags",
        extract_models=_extract_ollama_models,
    )
    if ollama_models is not None:
        local_summary["Ollama"] = ollama_models
        if ollama_models:
            names = ", ".join(ollama_models)
            print(f"  ✓ Ollama running — found {names}")
            _append_local_models_to_csv(
                ollama_models, provider="Ollama", prefix="ollama_chat/",
                base_url="http://localhost:11434",
            )
        else:
            print("  ✓ Ollama running — no models installed")
    else:
        print("  ✗ Ollama not running (skip)")

    # ── Check LM Studio ──────────────────────────────────────────────────
    lm_models = _query_local_server(
        url="http://localhost:1234/v1/models",
        extract_models=_extract_lm_studio_models,
    )
    if lm_models is not None:
        local_summary["LM Studio"] = lm_models
        if lm_models:
            names = ", ".join(lm_models)
            print(f"  ✓ LM Studio running — found {names}")
            _append_local_models_to_csv(
                lm_models, provider="lm_studio", prefix="lm_studio/",
                base_url="http://localhost:1234/v1",
            )
        else:
            print("  ✓ LM Studio running — no models loaded")
    else:
        print("  ✗ LM Studio not running (skip)")

    # ── Check .pddrc ─────────────────────────────────────────────────────
    cwd = Path.cwd()
    pddrc_path = cwd / ".pddrc"
    if pddrc_path.exists():
        print(f"  ✓ .pddrc already exists at {pddrc_path}")
    else:
        language = _detect_language(cwd) or "python"
        content = _build_pddrc_content(language)
        try:
            pddrc_path.write_text(content, encoding="utf-8")
            print(f"  ✓ Created .pddrc at {pddrc_path} (detected: {language})")
        except OSError as exc:
            print(f"  ✗ Failed to create .pddrc: {exc}")

    return local_summary


def _query_local_server(
    url: str,
    extract_models,
    timeout: float = 3.0,
) -> Optional[List[str]]:
    """Query a local LLM server. Returns model list or None if unreachable."""
    try:
        req = urllib.request.Request(url)
        with urllib.request.urlopen(req, timeout=timeout) as resp:
            data = json.loads(resp.read().decode("utf-8"))
            return extract_models(data)
    except (urllib.error.URLError, OSError, json.JSONDecodeError, KeyError):
        return None


def _extract_ollama_models(data: dict) -> List[str]:
    """Extract model names from Ollama /api/tags response."""
    models = data.get("models", [])
    return [m.get("name", "") for m in models if m.get("name")]


def _extract_lm_studio_models(data: dict) -> List[str]:
    """Extract model names from LM Studio /v1/models response."""
    models = data.get("data", [])
    return [m.get("id", "") for m in models if m.get("id")]


def _append_local_models_to_csv(
    model_names: List[str],
    provider: str,
    prefix: str,
    base_url: str,
) -> None:
    """Append local models to user CSV, skipping duplicates."""
    from pdd.provider_manager import (
        _read_csv,
        _write_csv_atomic,
        _get_user_csv_path,
    )

    user_csv_path = _get_user_csv_path()
    existing_rows = _read_csv(user_csv_path)
    existing_models = {r.get("model", "").strip() for r in existing_rows}

    new_rows = []
    for name in model_names:
        model_id = f"{prefix}{name}"
        if model_id not in existing_models:
            new_rows.append({
                "provider": provider,
                "model": model_id,
                "input": "0",
                "output": "0",
                "coding_arena_elo": "1000",
                "base_url": base_url,
                "api_key": "",
                "max_reasoning_tokens": "0",
                "structured_output": "True",
                "reasoning_type": "none",
                "location": "",
            })

    if new_rows:
        _write_csv_atomic(user_csv_path, existing_rows + new_rows)


# ---------------------------------------------------------------------------
# Step 4 — Test one model + print summary
# ---------------------------------------------------------------------------

def _step4_test_and_summary(
    found_keys: List[Tuple[str, str]],
    model_summary: Dict[str, int],
    local_summary: Dict[str, List[str]],
) -> None:
    """Test the first available cloud model and print the final summary."""
    from pdd.provider_manager import _read_csv, _get_user_csv_path

    # Pick first cloud model
    user_csv_path = _get_user_csv_path()
    rows = _read_csv(user_csv_path)
    test_result = "Skipped (no models configured)"

    cloud_row = None
    for row in rows:
        if row.get("api_key", "").strip():
            cloud_row = row
            break

    if cloud_row:
        test_model = cloud_row.get("model", "")
        try:
            import litellm  # noqa: F401
            from pdd.model_tester import _run_test

            print(f"  Testing {test_model}...")
            result = _run_test(cloud_row)
            if result["success"]:
                test_result = f"✓ {test_model} responded OK ({result['duration_s']:.1f}s)"
            else:
                test_result = f"✗ {test_model} failed: {result['error']}"
        except ImportError:
            test_result = "Skipped (litellm not installed)"
    print(f"  {test_result}")

    # ── Summary ───────────────────────────────────────────────────────────
    print()
    print("  ═══════════════════════════════════════════════")
    print("    PDD Setup Complete")
    print("  ═══════════════════════════════════════════════")
    print()

    # API Keys
    print(f"    API Keys:  {len(found_keys)} found")

    # Models
    total_models = sum(model_summary.values())
    parts = ", ".join(f"{p}: {c}" for p, c in sorted(model_summary.items()))
    if parts:
        print(f"    Models:    {total_models} configured ({parts})")
    else:
        print(f"    Models:    {total_models} configured")

    # Local LLMs
    if local_summary:
        local_parts = []
        for provider, models in local_summary.items():
            if models:
                local_parts.append(f"{provider} — {', '.join(models)}")
            else:
                local_parts.append(f"{provider} (no models)")
        print(f"    Local:     {'; '.join(local_parts)}")
    else:
        print("    Local:     none found")

    # .pddrc
    pddrc_path = Path.cwd() / ".pddrc"
    if pddrc_path.exists():
        print("    .pddrc:    exists")
    else:
        print("    .pddrc:    not created")

    # Test
    print(f"    Test:      {test_result}")

    print()
    print("  ═══════════════════════════════════════════════")
    print("    Run 'pdd generate' or 'pdd sync' to start.")
    print("  ═══════════════════════════════════════════════")


# ---------------------------------------------------------------------------
# Fallback manual menu
# ---------------------------------------------------------------------------

def _run_fallback_menu() -> None:
    """Simplified manual menu loop when auto-phase fails."""
    print()

    from pdd.provider_manager import add_provider_from_registry
    from pdd.model_tester import test_model_interactive
    from pdd.pddrc_initializer import offer_pddrc_init

    while True:
        print("Manual setup options:")
        print("  1. Add a provider")
        print("  2. Test a model")
        print("  3. Initialize .pddrc")
        print("  4. Done")

        try:
            choice = input("Select an option [1-4]: ").strip()
        except (EOFError, KeyboardInterrupt):
            print("\nSetup interrupted — exiting.")
            return

        if choice == "1":
            try:
                add_provider_from_registry()
            except Exception as exc:
                print(f"Error adding provider: {exc}")
        elif choice == "2":
            try:
                test_model_interactive()
            except Exception as exc:
                print(f"Error testing model: {exc}")
        elif choice == "3":
            try:
                offer_pddrc_init()
            except Exception as exc:
                print(f"Error initializing .pddrc: {exc}")
        elif choice == "4":
            break
        else:
            print("Invalid option. Please enter 1, 2, 3, or 4.")

        print()


if __name__ == "__main__":
    run_setup()
