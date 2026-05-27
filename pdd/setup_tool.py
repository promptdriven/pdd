"""
Orchestrates pdd setup with OpenCode- and Antigravity-aware CLI bootstrap and
deterministic model configuration.
"""

from __future__ import annotations

import getpass
import os
import sys
import threading
import time
from pathlib import Path
from typing import Any, Dict, List, Optional, Tuple

from rich.console import Console

from pdd.cli_branding import PDD_FULL_TAGLINE, PDD_POSITIONING

_console = Console(highlight=False)

# ANSI escape codes (the spec mandates these literal sequences)
CYAN = "\033[36m"
WHITE = "\033[37m"
BOLD = "\033[1m"
RESET = "\033[0m"
YELLOW = "\033[33m"
GREEN = "\033[32m"
RED = "\033[31m"
DIM = "\033[2m"

LIGHT_HORIZONTAL = "\u2500"


# ---------------------------------------------------------------------------
# Banner
# ---------------------------------------------------------------------------

def _print_pdd_logo() -> None:
    """Print the PDD ASCII art logo, tagline, positioning, and setup intro."""
    logo_lines = [
        "",
        "    ____  ____  ____",
        "   / __ \\/ __ \\/ __ \\",
        "  / /_/ / / / / / / /",
        " / ____/ /_/ / /_/ /",
        "/_/   /_____/_____/",
        "",
        "       THE LAST",
        " PROGRAMMING LANGUAGE",
        "",
    ]
    for line in logo_lines:
        print(f"{CYAN}{line}{RESET}")
    print(f"{BOLD}{WHITE}{PDD_FULL_TAGLINE}{RESET}")
    print(f"{WHITE}{PDD_POSITIONING}{RESET}")
    print()
    print(f"{BOLD}{WHITE}Let's get set up quickly with a solid basic configuration!{RESET}")
    print()


def _print_step_banner(title: str) -> None:
    """Print a cyan banner above a step heading."""
    line = LIGHT_HORIZONTAL * 60
    print()
    print(f"{CYAN}{line}{RESET}")
    print(f"{CYAN}{title}{RESET}")
    print(f"{CYAN}{line}{RESET}")


# ---------------------------------------------------------------------------
# Filesystem / source-finding helpers
# ---------------------------------------------------------------------------

def _ref_csv_path() -> Path:
    """Path to the reference llm_model.csv that ships with the package."""
    return Path(__file__).resolve().parent / "data" / "llm_model.csv"


def _scan_for_api_keys_quiet() -> List[Tuple[str, str]]:
    """Silently rescan for API keys after the menu may have added some.

    Mirrors the source-finding logic of step 1 (env → ~/.pdd/api-env.<shell>
    → project/home .env) but emits no console output, so the post-menu
    refresh doesn't double-print the per-key listing already shown in step 1.

    Returns:
        List of (key_name, source_label) tuples. Only includes keys whose
        VALUE is non-empty after .strip() (Issue #813 round-10).
    """
    from pdd.provider_manager import expand_api_key_vars, _read_csv
    from pdd.api_key_scanner import _parse_api_env_file, _detect_shell

    ref_csv = _ref_csv_path()
    if not ref_csv.exists():
        return []

    rows = _read_csv(ref_csv)
    candidates: set = set()
    for r in rows:
        api_key_field = r.get("api_key", "")
        if api_key_field:
            candidates.update(expand_api_key_vars(api_key_field))

    shell = _detect_shell() or "bash"
    api_env_path = Path.home() / ".pdd" / f"api-env.{shell}"
    env_file_vars: Dict[str, str] = {}
    if api_env_path.exists():
        try:
            env_file_vars = _parse_api_env_file(api_env_path) or {}
        except Exception:
            env_file_vars = {}

    dotenv_vals: Dict[str, str] = {}
    try:
        import dotenv  # type: ignore
        for p in [Path.cwd() / ".env", Path.home() / ".env"]:
            if p.exists():
                vals = dotenv.dotenv_values(p) or {}
                # Last one wins; only override with non-empty
                for k, v in vals.items():
                    if v is not None:
                        dotenv_vals[k] = v
    except ImportError:
        pass

    found: List[Tuple[str, str]] = []
    for var in sorted(candidates):
        val_os = os.environ.get(var)
        if val_os and val_os.strip():
            found.append((var, "shell environment"))
            continue

        val_env_file = env_file_vars.get(var)
        if val_env_file and str(val_env_file).strip():
            found.append((var, f"~/.pdd/api-env.{shell}"))
            continue

        val_dotenv = dotenv_vals.get(var)
        if val_dotenv and str(val_dotenv).strip():
            found.append((var, ".env file"))

    return found


# ---------------------------------------------------------------------------
# Step 1 — Scan for API keys
# ---------------------------------------------------------------------------

def _prompt_for_api_key() -> List[Tuple[str, str]]:
    """Interactively prompt the user to add one or more API keys.

    Returns:
        List of (key_name, source_label) for newly added keys.
    """
    from pdd.provider_manager import (
        _read_csv,
        _save_key_to_api_env,
        preferred_api_key_name,
    )

    print("To continue setup, add at least one API key.")
    ref_csv = _ref_csv_path()
    if not ref_csv.exists():
        return []

    rows = _read_csv(ref_csv)
    pairs: Dict[Tuple[str, str], None] = {}
    for r in rows:
        provider = (r.get("provider") or "").strip()
        api_key = (r.get("api_key") or "").strip()
        # Only single-var providers via this quick-add flow
        if provider and api_key and "|" not in api_key:
            pairs[(provider, preferred_api_key_name(api_key))] = None

    prov_list = sorted(pairs.keys(), key=lambda x: x[0].lower())
    added: List[Tuple[str, str]] = []

    while True:
        print()
        print("Select a provider to configure:")
        for i, (prov, key_name) in enumerate(prov_list, 1):
            print(f"  {i}. {prov} ({key_name})")
        skip_num = len(prov_list) + 1
        print(f"  {skip_num}. Skip")

        choice = input("Enter number (Enter to skip): ").strip()
        if not choice:
            break
        try:
            idx = int(choice) - 1
        except ValueError:
            print("Invalid choice.")
            continue
        if idx == len(prov_list):
            break
        if not (0 <= idx < len(prov_list)):
            print("Invalid choice.")
            continue
        prov, key_name = prov_list[idx]
        val = getpass.getpass(f"{key_name}: ").strip()
        if val:
            try:
                _save_key_to_api_env(key_name, val)
            except Exception as e:
                print(f"Warning: failed to persist key: {e}")
            os.environ[key_name] = val
            added.append((key_name, "just added"))
            print(f"{GREEN}✓ Saved {key_name}{RESET}")
        else:
            print("Skipped (empty).")

        again = input("Add another key? [y/N]: ").strip().lower()
        if again != "y":
            break

    return added


def _step1_scan_keys(cli_results: Optional[List[Any]] = None) -> List[Tuple[str, str]]:
    """Step 1 — scan for API keys; print summary; optionally prompt the user."""
    _print_step_banner("Step 1: Scanning for API keys")

    pdd_dir = Path.home() / ".pdd"
    pdd_dir.mkdir(parents=True, exist_ok=True)

    from pdd.provider_manager import expand_api_key_vars, _read_csv
    from pdd.api_key_scanner import _parse_api_env_file, _detect_shell

    shell = _detect_shell() or "bash"
    ref_csv = _ref_csv_path()
    if not ref_csv.exists():
        print("Reference model CSV not found; cannot scan for API keys.")
        return []

    ref_rows = _read_csv(ref_csv)

    # Group by provider so multi-var providers can be displayed together
    provider_vars: Dict[str, List[str]] = {}
    provider_api_field: Dict[str, str] = {}
    for r in ref_rows:
        provider = (r.get("provider") or "").strip() or "unknown"
        api_field = (r.get("api_key") or "").strip()
        if not api_field:
            continue
        vars_ = expand_api_key_vars(api_field)
        if not vars_:
            continue
        provider_vars.setdefault(provider, [])
        for v in vars_:
            if v not in provider_vars[provider]:
                provider_vars[provider].append(v)
        provider_api_field[provider] = api_field

    api_env_path = Path.home() / ".pdd" / f"api-env.{shell}"
    env_file_vars: Dict[str, str] = {}
    if api_env_path.exists():
        try:
            env_file_vars = _parse_api_env_file(api_env_path) or {}
        except Exception:
            env_file_vars = {}

    dotenv_vals: Dict[str, str] = {}
    try:
        import dotenv  # type: ignore
        for p in [Path.cwd() / ".env", Path.home() / ".env"]:
            if p.exists():
                vals = dotenv.dotenv_values(p) or {}
                for k, v in vals.items():
                    if v is not None:
                        dotenv_vals[k] = v
    except ImportError:
        pass

    def _source_for(var: str) -> Optional[str]:
        val_os = os.environ.get(var)
        if val_os and val_os.strip():
            return "shell environment"
        val_env_file = env_file_vars.get(var)
        if val_env_file and str(val_env_file).strip():
            return f"~/.pdd/api-env.{shell}"
        val_dotenv = dotenv_vals.get(var)
        if val_dotenv and str(val_dotenv).strip():
            return ".env file"
        return None

    found: List[Tuple[str, str]] = []
    # Iterate providers in a stable order
    for provider in sorted(provider_vars.keys(), key=lambda s: s.lower()):
        vars_ = provider_vars[provider]
        if "|" in provider_api_field.get(provider, ""):
            # Multi-var provider — grouped display
            present_pairs: List[Tuple[str, str]] = []
            missing: List[str] = []
            for v in vars_:
                src = _source_for(v)
                if src is not None:
                    present_pairs.append((v, src))
                else:
                    missing.append(v)
            if not present_pairs:
                continue  # Skip providers with 0 found
            total = len(vars_)
            n_set = len(present_pairs)
            if missing:
                print(f"  {YELLOW}! {provider}: {n_set}/{total} vars set "
                      f"(missing {len(missing)}){RESET}")
            else:
                print(f"  {GREEN}✓ {provider}: {n_set}/{total} vars set{RESET}")
            found.extend(present_pairs)
        else:
            # Single-var provider — aligned individual lines
            for v in vars_:
                src = _source_for(v)
                if src is not None:
                    print(f"  {GREEN}✓ {provider:<28}{RESET} ({src})")
                    found.append((v, src))

    print()
    print(f"  {len(found)} API key(s) found.")

    if not found:
        # Decide whether to prompt based on whether any CLI has OAuth.
        from pdd.cli_detector import _has_cli_oauth
        oauth_providers: List[str] = []
        if cli_results:
            for r in cli_results:
                if getattr(r, "skipped", False):
                    continue
                cli_name = getattr(r, "cli_name", None)
                if cli_name and _has_cli_oauth(cli_name):
                    oauth_providers.append(getattr(r, "provider", cli_name))

        if oauth_providers:
            count = len(set(oauth_providers))
            print(f"{GREEN}✓ stored OAuth/subscription/config credentials detected "
                  f"for {count} provider(s). No API key needed for the agentic CLI.{RESET}")
            print(f"{DIM}Hint: re-run `pdd setup` later to add an API key "
                  f"for direct litellm-backed commands.{RESET}")
        else:
            print("No API keys found.")
            added = _prompt_for_api_key()
            found.extend(added)

    print(f"{DIM}You can edit your global API keys in ~/.pdd/api-env.{shell}{RESET}")

    return found


# ---------------------------------------------------------------------------
# Step 2 — Configure Models + .pddrc
# ---------------------------------------------------------------------------

def _normalize_row_for_configured_keys(
    row: Dict[str, str],
    found_key_names: List[str],
) -> Dict[str, str]:
    """Return a row whose api_key field matches the configured Google alias."""
    normalized = dict(row)
    if (
        (normalized.get("api_key") or "").strip() == "GEMINI_API_KEY"
        and "GOOGLE_API_KEY" in set(found_key_names)
    ):
        normalized["api_key"] = "GOOGLE_API_KEY"
    return normalized


def _step2_configure_models_and_pddrc(found_key_names: List[str]) -> Dict[str, int]:
    """Filter reference CSV → user CSV; offer to create .pddrc."""
    _print_step_banner("Step 2: Configuring models and .pddrc")

    from pdd.provider_manager import (
        _read_csv,
        _write_csv_atomic,
        _get_user_csv_path,
        api_key_requirements_satisfied,
    )
    from pdd.pddrc_initializer import _detect_language, _build_pddrc_content

    ref_csv = _ref_csv_path()
    configured_models: List[Dict[str, str]] = []
    if ref_csv.exists():
        rows = _read_csv(ref_csv)
        for r in rows:
            api_key = (r.get("api_key") or "").strip()
            provider = (r.get("provider") or "").strip()
            base_url = (r.get("base_url") or "").strip()
            # Skip local
            if provider in ("lm_studio", "ollama"):
                continue
            if "127.0.0.1" in base_url or "localhost" in base_url:
                continue
            if not api_key:
                # Device flow — always include
                configured_models.append(r)
            else:
                if api_key_requirements_satisfied(api_key, found_key_names):
                    configured_models.append(
                        _normalize_row_for_configured_keys(r, found_key_names)
                    )

    user_csv = _get_user_csv_path()
    existing: List[Dict[str, str]] = []
    if user_csv.exists():
        try:
                existing = [
                    _normalize_row_for_configured_keys(row, found_key_names)
                    for row in _read_csv(user_csv)
                ]
        except Exception:
            existing = []

    existing_models = {(r.get("model") or "").strip() for r in existing}
    new_rows = []
    for r in configured_models:
        m = (r.get("model") or "").strip()
        if m and m not in existing_models:
            new_rows.append(r)
            existing_models.add(m)

    combined = existing + new_rows
    try:
        _write_csv_atomic(user_csv, combined)
    except Exception as e:
        print(f"Warning: failed to write user CSV: {e}")

    provider_counts: Dict[str, int] = {}
    for r in combined:
        p = (r.get("provider") or "unknown").strip()
        provider_counts[p] = provider_counts.get(p, 0) + 1

    if new_rows:
        print(f"  {GREEN}✓ {len(new_rows)} new model(s) added to {user_csv}{RESET}")
    else:
        if combined:
            print(f"  All matching models already present in {user_csv}.")
        else:
            print(f"  No matching cloud models for the configured keys.")

    print(f"  {GREEN}✓ {len(combined)} model(s) configured total{RESET}")
    for p, c in sorted(provider_counts.items()):
        print(f"    {p}: {c} model(s)")

    print()
    pddrc_path = Path.cwd() / ".pddrc"
    if pddrc_path.exists():
        print(f"  {GREEN}✓ .pddrc detected at {pddrc_path}{RESET}")
    else:
        print("  No .pddrc found in this project.")
        print(f"  {DIM}A .pddrc tells pdd which language to default to and "
              f"where to look for prompts/code.{RESET}")
        ans = input("Create .pddrc in this project? [y/Enter to skip]: ").strip().lower()
        if ans == "y":
            lang = _detect_language(Path.cwd()) or "python"
            try:
                content = _build_pddrc_content(lang)
                pddrc_path.write_text(content, encoding="utf-8")
                print(f"  {GREEN}✓ Created .pddrc for {lang}.{RESET}")
            except Exception as e:
                print(f"  Could not create .pddrc: {e}")
        else:
            print(f"  {DIM}Skipped .pddrc creation.{RESET}")

    return provider_counts


# ---------------------------------------------------------------------------
# Step 3 — Test + summary
# ---------------------------------------------------------------------------

def _step3_test_and_summary(found_key_names: List[str],
                            provider_counts: Dict[str, int]) -> Dict[str, Any]:
    """Pick a cloud model, test it with a timeout, then print a summary."""
    _print_step_banner("Step 3: Testing and summarizing")

    from pdd.provider_manager import (
        _read_csv,
        _get_user_csv_path,
        api_key_requirements_satisfied,
    )

    user_csv = _get_user_csv_path()
    test_row: Optional[Dict[str, str]] = None
    if user_csv.exists():
        for r in _read_csv(user_csv):
            api_key = (r.get("api_key") or "").strip()
            provider = (r.get("provider") or "").strip()
            base_url = (r.get("base_url") or "").strip()
            if provider in ("lm_studio", "ollama"):
                continue
            if "127.0.0.1" in base_url or "localhost" in base_url:
                continue
            if not api_key:
                test_row = r
                break
            if api_key_requirements_satisfied(api_key, found_key_names):
                test_row = r
                break

    test_summary: Dict[str, Any] = {
        "ran": False,
        "success": False,
        "message": "",
        "model": None,
    }

    if not test_row:
        print("  No cloud model with all credentials set; skipping live test.")
        test_summary["message"] = "no eligible model"
    else:
        try:
            import litellm  # type: ignore # noqa: F401
            has_litellm = True
        except ImportError:
            has_litellm = False

        if not has_litellm:
            print("  litellm not installed; skipping live test.")
            test_summary["message"] = "litellm not installed"
        else:
            model_name = test_row.get("model") or "(unknown)"
            test_summary["model"] = model_name
            print(f"  Testing {model_name}", end="", flush=True)

            from pdd.model_tester import _run_test
            result_container: Dict[str, Any] = {}
            stop_event = threading.Event()

            def spinner() -> None:
                while not stop_event.is_set():
                    if stop_event.wait(1.0):
                        return
                    if not stop_event.is_set():
                        try:
                            sys.stdout.write(".")
                            sys.stdout.flush()
                        except Exception:
                            pass

            spinner_thread = threading.Thread(target=spinner, daemon=True)
            spinner_thread.start()

            def worker() -> None:
                try:
                    result_container["result"] = _run_test(test_row)
                except Exception as e:  # pragma: no cover
                    result_container["result"] = {
                        "success": False, "duration_s": 0.0, "cost": 0.0,
                        "error": str(e), "tokens": None,
                    }

            wt = threading.Thread(target=worker, daemon=True)
            wt.start()
            wt.join(timeout=8.0)

            stop_event.set()
            spinner_thread.join(timeout=1.0)
            print()

            if wt.is_alive():
                print(f"  {RED}✗ Test timed out after 8s.{RESET}")
                test_summary["ran"] = True
                test_summary["success"] = False
                test_summary["message"] = "timed out"
            else:
                result = result_container.get("result") or {}
                test_summary["ran"] = True
                if result.get("success"):
                    dur = result.get("duration_s", 0.0)
                    print(f"  {GREEN}✓ {model_name} responded OK "
                          f"({dur:.1f}s){RESET}")
                    test_summary["success"] = True
                    test_summary["message"] = (
                        f"{model_name} responded OK ({dur:.1f}s)"
                    )
                else:
                    err = result.get("error") or "Unknown error"
                    print(f"  {RED}✗ {model_name} test failed: {err}{RESET}")
                    test_summary["message"] = err

    return test_summary


# ---------------------------------------------------------------------------
# Auto phase + menu
# ---------------------------------------------------------------------------

def _run_auto_phase(cli_results: List[Any]) -> Optional[Dict[str, Any]]:
    """Run the 3 deterministic steps with Press-Enter pauses. Returns context
    dict on success, or None on failure."""
    try:
        found_keys = _step1_scan_keys(cli_results)
        found_key_names = [k for k, _ in found_keys]

        input("\nPress Enter to continue to the next step...")
        provider_counts = _step2_configure_models_and_pddrc(found_key_names)

        input("\nPress Enter to continue to the next step...")
        test_summary = _step3_test_and_summary(found_key_names, provider_counts)

        print()
        print(f"{BOLD}{GREEN}PDD Setup Complete!{RESET}")
        print()
        return {
            "found_keys": found_keys,
            "provider_counts": provider_counts,
            "test_summary": test_summary,
        }
    except KeyboardInterrupt:
        raise
    except Exception as e:
        print(f"{RED}Error during auto-configuration: {e}{RESET}")
        return None


def _run_options_menu() -> None:
    """Two-item options menu. Press Enter to finish."""
    from pdd.provider_manager import add_provider_from_registry
    from pdd.model_tester import test_model_interactive

    while True:
        print()
        print(f"{BOLD}Options:{RESET}")
        print("  1. Add a provider")
        print("  2. Test a model")
        choice = input("Select an option (Enter to finish): ").strip()
        if not choice:
            break
        try:
            if choice == "1":
                add_provider_from_registry()
            elif choice == "2":
                test_model_interactive()
            else:
                print(f"  {YELLOW}Invalid option.{RESET}")
        except Exception as e:
            print(f"  Error: {e}")


# ---------------------------------------------------------------------------
# Exit summary
# ---------------------------------------------------------------------------

def _mask_key(key_name: str) -> str:
    """Return a masked label (we never have the value here)."""
    return key_name


def _cli_credential_label(r: Any) -> str:
    """Return the per-CLI credential label.

    Priority (Issue #813 round-10):
        1. api_key_configured == True            → "API key set"
        2. _has_cli_oauth(cli_name) == True      → "OAuth/subscription/config credential configured"
        3. neither                                → "no credentials"
    """
    from pdd.cli_detector import _has_cli_oauth
    if getattr(r, "api_key_configured", False):
        return "API key set"
    cli_name = getattr(r, "cli_name", None)
    if cli_name and _has_cli_oauth(cli_name):
        return "OAuth/subscription/config credential configured"
    return "no credentials"


def _build_quick_start_lines(oauth_only_setup: bool) -> List[str]:
    """Build the quick-start text as a list of strings, used in both the
    summary file and the terminal print so the two views stay in sync."""
    if oauth_only_setup:
        return [
            "Setup detected an OAuth/subscription/config-backed agentic CLI but no API key was "
            "found in your environment.",
            "",
            "1) Issue-driven agentic commands (work NOW with OAuth):",
            "   These dispatch through the configured agentic CLI",
            "   (claude/codex/agy/gemini/opencode) as a subprocess and use its",
            "   stored OAuth/subscription/config credential. No API key required.",
            "     pdd generate <issue-url>",
            "     pdd change   <issue-url>",
            "     pdd bug      <issue-url>",
            "     pdd fix      <issue-url>",
            "     pdd test     <issue-url>",
            "     pdd checkup  <issue-url>",
            "",
            "2) Direct prompt commands (require an env-var API key):",
            "   These call litellm directly and need ANTHROPIC_API_KEY /",
            "   OPENAI_API_KEY / GEMINI_API_KEY (etc.) to be set.",
            "     pdd generate <prompt-file>",
            "     pdd test     <prompt>",
            "     pdd fix      <prompt>",
            "     pdd sync     <prompt-or-issue>",
            "   To enable these, re-run `pdd setup` and add an API key",
            "   (or use the post-setup options menu's \"Add a provider\").",
        ]
    return [
        "Generate code from the sample prompt:",
        "  pdd generate success_python.prompt",
    ]


def _print_exit_summary(found_keys: List[Tuple[str, str]],
                        cli_results: Optional[List[Any]] = None) -> None:
    """Write PDD-SETUP-SUMMARY.txt and print a condensed terminal summary."""
    cli_results = cli_results or []

    # Create the sample success_python.prompt if absent
    sample_file = Path.cwd() / "success_python.prompt"
    if not sample_file.exists():
        try:
            sample_file.write_text(
                "% Sample PDD prompt\n"
                "Write a Python script that prints \"Hello from PDD!\".\n",
                encoding="utf-8",
            )
        except Exception:
            pass

    # OAuth-only branch detection — based on the full found_keys scan
    # (env + ~/.pdd/api-env + .env), NOT on os.environ alone. See spec
    # round-10 / P4 review.
    has_oauth_cli = False
    for r in cli_results:
        if getattr(r, "skipped", False):
            continue
        try:
            from pdd.cli_detector import _has_cli_oauth
            cli_name = getattr(r, "cli_name", None)
            if cli_name and _has_cli_oauth(cli_name):
                has_oauth_cli = True
                break
        except Exception:
            pass

    oauth_only_setup = (not found_keys) and has_oauth_cli

    quick_start_lines = _build_quick_start_lines(oauth_only_setup)

    # ---- Write PDD-SETUP-SUMMARY.txt ----
    summary_path = Path.cwd() / "PDD-SETUP-SUMMARY.txt"
    lines: List[str] = []
    lines.append("PDD Setup Complete")
    lines.append("==================")
    lines.append("")
    lines.append("CLIs Configured:")
    if not cli_results or all(getattr(r, "skipped", False) for r in cli_results):
        lines.append("  (none)")
    else:
        for r in cli_results:
            if getattr(r, "skipped", False):
                continue
            label = _cli_credential_label(r)
            name = getattr(r, "cli_name", "?") or "?"
            lines.append(f"  - {name}: {label}")
    lines.append("")
    lines.append("API Keys Configured:")
    if not found_keys:
        lines.append("  (none)")
    else:
        for k, s in found_keys:
            lines.append(f"  - {_mask_key(k)}  ({s})")
    lines.append("")
    lines.append("Files Created / Updated:")
    lines.append(f"  - {sample_file}")
    lines.append(f"  - {summary_path}")
    lines.append("")
    lines.append("QUICK START")
    lines.append("-----------")
    for q in quick_start_lines:
        lines.append(q)
    lines.append("")
    lines.append("Learn More:")
    lines.append("  - pdd --help")
    lines.append("  - https://promptdriven.ai/")
    lines.append("  - Discord: https://discord.gg/Yp4RTh8bG7")
    lines.append("")

    # api-env reminder, included in BOTH file and terminal
    try:
        from pdd.api_key_scanner import _detect_shell
        shell = _detect_shell() or "bash"
    except Exception:
        shell = "bash"
    api_env_path = Path.home() / ".pdd" / f"api-env.{shell}"
    if api_env_path.exists():
        lines.append("Important:")
        lines.append(f"  Run `source ~/.pdd/api-env.{shell}` for the keys to "
                     "take effect in this terminal.")
        lines.append("  (New terminal windows will load them automatically.)")
        lines.append("")

    try:
        summary_path.write_text("\n".join(lines) + "\n", encoding="utf-8")
    except Exception as e:
        print(f"Could not write summary file: {e}")

    # ---- Print condensed terminal summary ----
    print()
    print(f"{BOLD}{CYAN}{LIGHT_HORIZONTAL * 60}{RESET}")
    print(f"{BOLD}QUICK START:{RESET}")
    for q in quick_start_lines:
        print(q)
    print(f"{BOLD}{CYAN}{LIGHT_HORIZONTAL * 60}{RESET}")

    print()
    print(f"{BOLD}LEARN MORE:{RESET}")
    print("  - pdd --help")
    print("  - https://promptdriven.ai/")
    print("  - Discord: https://discord.gg/Yp4RTh8bG7")

    if api_env_path.exists():
        print()
        print(f"{BOLD}{YELLOW}Important:{RESET} "
              f"run `source ~/.pdd/api-env.{shell}` for keys to take effect "
              f"in this terminal session.")
        print(f"{DIM}(New terminal windows will load keys automatically.){RESET}")

    print()
    print(f"{DIM}Full summary saved to {summary_path}{RESET}")


# ---------------------------------------------------------------------------
# Public entry point
# ---------------------------------------------------------------------------

def run_setup() -> None:
    """Main entry point for `pdd setup`."""
    try:
        _print_pdd_logo()

        from pdd.cli_detector import detect_and_bootstrap_cli, _has_cli_oauth

        _print_step_banner("Phase 1: Agentic CLI Bootstrap")
        cli_results = detect_and_bootstrap_cli()

        # CLI bootstrap warnings (yellow) only when BOTH api_key and OAuth absent
        for r in cli_results or []:
            if getattr(r, "skipped", False):
                continue
            api_key_ok = bool(getattr(r, "api_key_configured", False))
            cli_name_r = getattr(r, "cli_name", None)
            oauth_ok = False
            try:
                oauth_ok = bool(cli_name_r and _has_cli_oauth(cli_name_r))
            except Exception:
                oauth_ok = False
            if not api_key_ok and not oauth_ok:
                name = cli_name_r or "?"
                print(f"{YELLOW}No credentials configured for {name}: "
                      f"set an API key or sign in via the CLI.{RESET}")

        context = _run_auto_phase(cli_results)

        if context is None:
            # Failure path — fall back to options menu
            msg = "Setup incomplete. Use the menu to configure manually."
            _console.print(f"[yellow]{msg}[/yellow]")
            print(f"{YELLOW}{msg}{RESET}")
            _run_options_menu()
            found_keys = _scan_for_api_keys_quiet()
        else:
            found_keys = context.get("found_keys", [])
            ans = input("Press Enter to finish, or 'm' for more options: ").strip()
            if ans:
                _run_options_menu()
                # Refresh: menu may have added a key
                found_keys = _scan_for_api_keys_quiet()

        _print_exit_summary(found_keys, cli_results)
    except KeyboardInterrupt:
        print()
        print("Setup interrupted — exiting.")
        return


if __name__ == "__main__":
    run_setup()
