"""pdd setup orchestrator.

Two-phase setup:
  Phase 1: interactive CLI bootstrap (delegates to pdd.cli_detector).
  Phase 2: deterministic auto-configuration (no LLM calls):
    Step 1: scan API keys
    Step 2: configure models in user CSV + optional .pddrc
    Step 3: test a model + print summary

Designed for minimal user interaction — the happy path requires only a few
Enter presses.
"""
from __future__ import annotations

import os
import sys
import getpass
import builtins as _builtins
import threading
from pathlib import Path
from typing import Any, Dict, List, Optional, Tuple

try:
    from rich.console import Console
except ImportError:  # pragma: no cover - rich is an application dependency.
    Console = None  # type: ignore[assignment]


if Console is not None:
    _console = Console(highlight=False)
else:
    class _FallbackConsole:
        def print(self, *args: object, **kwargs: object) -> None:
            _builtins.print(*args, **kwargs)

    _console = _FallbackConsole()

_DEFAULT_CONSOLE = _console
_DEFAULT_BUILTIN_PRINT = _builtins.print

# ---- ANSI / formatting helpers ---------------------------------------------

CYAN = "\033[36m"
WHITE = "\033[37m"
YELLOW = "\033[33m"
RED = "\033[31m"
GREEN = "\033[32m"
DIM = "\033[2m"
BOLD = "\033[1m"
RESET = "\033[0m"

LIGHT_HORIZONTAL = "\u2500"

PDD_LOGO = r"""
  ____  ____  ____
 |  _ \|  _ \|  _ \
 | |_) | | | | | | |
 |  __/| |_| | |_| |
 |_|   |____/|____/
"""


def _print_pdd_logo() -> None:
    _print(f"{CYAN}{PDD_LOGO}{RESET}")
    _print(f"{BOLD}{WHITE}Let's get set up quickly with a solid basic configuration!{RESET}")
    _print()


def _print_step_banner(title: str) -> None:
    line = LIGHT_HORIZONTAL * max(4, len(title) + 4)
    _print()
    _print(f"{CYAN}{line}{RESET}")
    _print(f"{CYAN}{title}{RESET}")
    _print(f"{CYAN}{line}{RESET}")


def _mask_key(value: str) -> str:
    if not value:
        return ""
    if len(value) <= 8:
        return "*" * len(value)
    return f"{value[:4]}...{value[-4:]}"


def _print(*args: object, **kwargs: object) -> None:
    """Print through Rich normally, while preserving patched print capture."""
    if _console is not _DEFAULT_CONSOLE:
        _console.print(*args, **kwargs)
        if _builtins.print is not _DEFAULT_BUILTIN_PRINT:
            _builtins.print(*args, **kwargs)
    elif _builtins.print is not _DEFAULT_BUILTIN_PRINT:
        _builtins.print(*args, **kwargs)
    else:
        _console.print(*args, **kwargs)


# ---- Reference CSV path -----------------------------------------------------

def _reference_csv_path() -> Path:
    return Path(__file__).resolve().parent / "data" / "llm_model.csv"


def _is_local_row(row: Dict[str, str]) -> bool:
    provider = (row.get("provider") or "").strip().lower()
    base_url = (row.get("base_url") or "").strip().lower()
    if provider in {"lm_studio", "ollama"}:
        return True
    if "localhost" in base_url or "127.0.0.1" in base_url:
        return True
    return False


# ============================================================================
# Step 1: Scan for API keys
# ============================================================================

def _scan_dotenv_files() -> Dict[str, Tuple[str, str]]:
    """Scan common .env files in the current directory."""
    found: Dict[str, Tuple[str, str]] = {}
    try:
        from dotenv import dotenv_values  # type: ignore
    except ImportError:
        return found

    cwd = Path.cwd()
    for name in (".env", ".env.local"):
        path = cwd / name
        if path.exists():
            try:
                values = dotenv_values(str(path))
                for k, v in values.items():
                    if v and k not in found:
                        found[k] = (str(v), f".env ({path.name})")
            except Exception:
                continue
    return found


def _scan_api_env_file() -> Tuple[Dict[str, str], Optional[Path], Optional[str]]:
    """Returns (vars, file_path, shell_name)."""
    from pdd.api_key_scanner import _parse_api_env_file, _detect_shell

    shell = _detect_shell() or "sh"
    home = Path.home()
    api_env_file = home / ".pdd" / f"api-env.{shell}"
    if api_env_file.exists():
        try:
            vars_ = _parse_api_env_file(api_env_file)
            return vars_, api_env_file, shell
        except Exception:
            return {}, api_env_file, shell
    return {}, api_env_file, shell


def _step1_scan_keys() -> List[Tuple[str, str]]:
    """Scan for API keys. Returns list of (key_name, source_label)."""
    from pdd.provider_manager import _read_csv, parse_api_key_vars

    # Ensure ~/.pdd
    pdd_dir = Path.home() / ".pdd"
    pdd_dir.mkdir(parents=True, exist_ok=True)

    # Read reference CSV → discover all known API key vars per provider
    ref_csv = _reference_csv_path()
    try:
        rows = _read_csv(ref_csv)
    except Exception as e:
        _print(f"{RED}Could not read reference CSV at {ref_csv}: {e}{RESET}")
        rows = []

    # Build per-provider mapping: provider -> set(vars)
    provider_vars: Dict[str, List[str]] = {}
    for row in rows:
        provider = (row.get("provider") or "").strip()
        api_key_field = (row.get("api_key") or "").strip()
        if not provider:
            continue
        if _is_local_row(row):
            continue
        if not api_key_field:
            # device flow — no env var to scan
            continue
        vars_list = parse_api_key_vars(api_key_field)
        existing = provider_vars.setdefault(provider, [])
        for v in vars_list:
            if v not in existing:
                existing.append(v)

    # Scan sources
    api_env_vars, api_env_path, shell = _scan_api_env_file()
    dotenv_vars = _scan_dotenv_files()

    def _lookup(var: str) -> Optional[str]:
        """Return source label if var is set, else None."""
        if os.environ.get(var):
            return "shell environment"
        if var in api_env_vars:
            os.environ.setdefault(var, api_env_vars[var])
            return f"~/.pdd/api-env.{shell}"
        if var in dotenv_vars:
            value, label = dotenv_vars[var]
            os.environ.setdefault(var, value)
            return label
        return None

    found: List[Tuple[str, str]] = []
    found_names: set = set()

    # Display per-provider grouped results
    _print()
    multi_providers: List[str] = []
    single_providers: List[str] = []
    for provider, vars_list in provider_vars.items():
        if len(vars_list) > 1:
            multi_providers.append(provider)
        else:
            single_providers.append(provider)

    # Single-var providers — render aligned
    single_lines: List[Tuple[str, str, Optional[str]]] = []
    for provider in sorted(single_providers, key=str.lower):
        var = provider_vars[provider][0]
        src = _lookup(var)
        single_lines.append((provider, var, src))

    if single_lines:
        max_var = max(len(v) for _, v, _ in single_lines)
        for provider, var, src in single_lines:
            if src:
                if var not in found_names:
                    found.append((var, src))
                    found_names.add(var)
                _print(f"  {GREEN}✓{RESET} {var:<{max_var}}  {DIM}({src}){RESET}")
            else:
                _print(f"  {DIM}-{RESET} {var:<{max_var}}  {DIM}(not set){RESET}")

    # Multi-var providers — grouped summary
    for provider in sorted(multi_providers, key=str.lower):
        vars_list = provider_vars[provider]
        present = []
        missing = []
        for var in vars_list:
            src = _lookup(var)
            if src:
                present.append((var, src))
            else:
                missing.append(var)
        total = len(vars_list)
        if not present:
            continue  # skip providers with 0 found
        for var, src in present:
            if var not in found_names:
                found.append((var, src))
                found_names.add(var)
        if not missing:
            _print(f"  {GREEN}✓{RESET} {provider}: {len(present)}/{total} vars set")
        else:
            _print(
                f"  {YELLOW}!{RESET} {provider}: {len(present)}/{total} vars set "
                f"{DIM}(missing: {', '.join(missing)}){RESET}"
            )

    # If none found, prompt to add one
    if not found:
        _print()
        _print(f"{YELLOW}No API keys detected.{RESET}")
        added = _prompt_for_api_key()
        for k, src in added:
            if k not in found_names:
                found.append((k, src))
                found_names.add(k)

    _print()
    _print(f"{BOLD}Found {len(found)} API key(s).{RESET}")
    if api_env_path is not None:
        _print(f"{DIM}You can edit your global API keys in {api_env_path}{RESET}")
    return found


def _prompt_for_api_key() -> List[Tuple[str, str]]:
    """Interactive: pick provider, enter key, save. Returns list of (var, source)."""
    from pdd.provider_manager import _read_csv, _save_key_to_api_env, parse_api_key_vars

    added: List[Tuple[str, str]] = []
    try:
        rows = _read_csv(_reference_csv_path())
    except Exception as e:
        _print(f"{RED}Could not load provider list: {e}{RESET}")
        return added

    # Build unique (provider, api_key_field) pairs
    seen: set = set()
    pairs: List[Tuple[str, str]] = []
    for row in rows:
        provider = (row.get("provider") or "").strip()
        api_key_field = (row.get("api_key") or "").strip()
        if not provider or not api_key_field:
            continue
        if _is_local_row(row):
            continue
        key = (provider, api_key_field)
        if key in seen:
            continue
        seen.add(key)
        pairs.append(key)

    pairs.sort(key=lambda p: p[0].lower())

    while True:
        _print()
        _print(f"{BOLD}Choose a provider to add a key for:{RESET}")
        for i, (prov, field) in enumerate(pairs, 1):
            vars_ = parse_api_key_vars(field)
            label = ", ".join(vars_) if len(vars_) > 1 else vars_[0]
            _print(f"  {i:>2}. {prov:<24} {DIM}({label}){RESET}")
        skip_idx = len(pairs) + 1
        _print(f"  {skip_idx:>2}. Skip")

        try:
            choice = input("Enter number: ").strip()
        except EOFError:
            return added
        if not choice:
            return added
        try:
            idx = int(choice)
        except ValueError:
            _print(f"{RED}Invalid selection.{RESET}")
            continue
        if idx == skip_idx or idx < 1 or idx > len(pairs):
            return added

        provider, field = pairs[idx - 1]
        vars_ = parse_api_key_vars(field)
        # For multi-var, prompt each
        for var in vars_:
            try:
                value = getpass.getpass(f"{var}: ").strip()
            except (EOFError, KeyboardInterrupt):
                _print()
                return added
            if not value:
                _print(f"{DIM}Skipped {var}{RESET}")
                continue
            try:
                _save_key_to_api_env(var, value)
                # Make available to current process
                os.environ[var] = value
                from pdd.api_key_scanner import _detect_shell
                shell = _detect_shell() or "sh"
                src = f"~/.pdd/api-env.{shell}"
                added.append((var, src))
                _print(f"{GREEN}✓ Saved {var}{RESET}")
            except Exception as e:
                _print(f"{RED}Failed to save {var}: {e}{RESET}")

        try:
            again = input("Add another key? [y/N]: ").strip().lower()
        except EOFError:
            return added
        if again != "y":
            return added


# ============================================================================
# Step 2: Configure models + .pddrc
# ============================================================================

def _step2_configure_models_and_pddrc(
    found_keys: List[Tuple[str, str]]
) -> Dict[str, int]:
    """Auto-add models matching found keys to user CSV. Returns provider→count."""
    from pdd.provider_manager import (
        _read_csv,
        _write_csv_atomic,
        _get_user_csv_path,
        parse_api_key_vars,
    )

    found_names = {k for k, _ in found_keys}

    # Read reference
    try:
        ref_rows = _read_csv(_reference_csv_path())
    except Exception as e:
        _print(f"{RED}Could not read reference CSV: {e}{RESET}")
        return {}

    # Filter eligible
    eligible: List[Dict[str, str]] = []
    for row in ref_rows:
        if _is_local_row(row):
            continue
        api_key_field = (row.get("api_key") or "").strip()
        if not api_key_field:
            # device flow — include
            eligible.append(row)
            continue
        vars_ = parse_api_key_vars(api_key_field)
        if all(v in found_names for v in vars_):
            eligible.append(row)

    # User CSV
    user_csv = _get_user_csv_path()
    user_csv.parent.mkdir(parents=True, exist_ok=True)

    existing_rows: List[Dict[str, str]] = []
    if user_csv.exists():
        try:
            existing_rows = _read_csv(user_csv)
        except Exception:
            existing_rows = []

    existing_models = {(r.get("model") or "").strip() for r in existing_rows}

    added_rows: List[Dict[str, str]] = []
    for row in eligible:
        model = (row.get("model") or "").strip()
        if not model or model in existing_models:
            continue
        existing_models.add(model)
        added_rows.append(row)

    if added_rows:
        all_rows = existing_rows + added_rows
        try:
            _write_csv_atomic(user_csv, all_rows)
            _print(f"{GREEN}✓ Added {len(added_rows)} new model(s) to {user_csv}{RESET}")
        except Exception as e:
            _print(f"{RED}Failed to write user CSV: {e}{RESET}")
    else:
        _print(f"{DIM}No new models to add (already configured).{RESET}")

    # Provider breakdown over the entire user CSV
    breakdown: Dict[str, int] = {}
    try:
        final_rows = _read_csv(user_csv) if user_csv.exists() else existing_rows + added_rows
    except Exception:
        final_rows = existing_rows + added_rows
    for r in final_rows:
        prov = (r.get("provider") or "unknown").strip() or "unknown"
        breakdown[prov] = breakdown.get(prov, 0) + 1

    if breakdown:
        _print()
        _print(f"{BOLD}Configured models:{RESET}")
        for prov in sorted(breakdown, key=str.lower):
            _print(f"  {prov:<24} {breakdown[prov]} model(s)")

    # .pddrc handling
    _print()
    pddrc_path = Path.cwd() / ".pddrc"
    if pddrc_path.exists():
        _print(f"{GREEN}✓ .pddrc detected in this project at {pddrc_path}{RESET}")
    else:
        _print(f"{BOLD}.pddrc{RESET} is a per-project config file that pins your default")
        _print("model strength, output paths, and other PDD preferences for this project.")
        try:
            answer = input("Create .pddrc in this project? [y/Enter to skip]: ").strip().lower()
        except EOFError:
            answer = ""
        if answer == "y":
            from pdd.pddrc_initializer import _detect_language, _build_pddrc_content
            lang = _detect_language(Path.cwd()) or "python"
            try:
                content = _build_pddrc_content(lang)
                pddrc_path.write_text(content, encoding="utf-8")
                _print(f"{GREEN}✓ Created {pddrc_path} (language: {lang}){RESET}")
            except Exception as e:
                _print(f"{RED}Failed to create .pddrc: {e}{RESET}")
        else:
            _print(f"{DIM}Skipped .pddrc creation.{RESET}")

    return breakdown


# ============================================================================
# Step 3: Test + summary
# ============================================================================

def _animated_run(target, args=(), timeout: float = 8.0) -> Tuple[bool, Any]:
    """Run target in background thread with dot animation. Returns (completed, result)."""
    result_box: Dict[str, Any] = {}

    def _wrapped():
        try:
            result_box["value"] = target(*args)
        except Exception as e:
            result_box["error"] = e

    t = threading.Thread(target=_wrapped, daemon=True)
    t.start()
    elapsed = 0.0
    sys.stdout.write("  Testing")
    sys.stdout.flush()
    while t.is_alive() and elapsed < timeout:
        t.join(timeout=1.0)
        elapsed += 1.0
        if t.is_alive():
            sys.stdout.write(".")
            sys.stdout.flush()
    sys.stdout.write("\n")
    sys.stdout.flush()

    if t.is_alive():
        return False, None
    if "error" in result_box:
        return True, {"success": False, "error": str(result_box["error"]),
                      "duration_s": 0.0, "cost": 0.0, "tokens": None}
    return True, result_box.get("value")


def _step3_test_and_summary(
    cli_results: List[Any],
    found_keys: List[Tuple[str, str]],
    model_breakdown: Dict[str, int],
) -> Dict[str, Any]:
    """Pick a cloud model, test it, print summary. Returns test result dict."""
    from pdd.provider_manager import _read_csv, _get_user_csv_path, parse_api_key_vars

    user_csv = _get_user_csv_path()
    rows: List[Dict[str, str]] = []
    if user_csv.exists():
        try:
            rows = _read_csv(user_csv)
        except Exception:
            rows = []

    found_names = {k for k, _ in found_keys}

    # Pick first cloud model with all keys present
    chosen: Optional[Dict[str, str]] = None
    for row in rows:
        if _is_local_row(row):
            continue
        api_key_field = (row.get("api_key") or "").strip()
        if not api_key_field:
            chosen = row
            break
        vars_ = parse_api_key_vars(api_key_field)
        if all(v in found_names or os.environ.get(v) for v in vars_):
            chosen = row
            break

    test_result: Dict[str, Any] = {"success": False, "error": "Not run", "skipped": False}

    if chosen is None:
        _print(f"{YELLOW}No cloud model available to test.{RESET}")
        test_result = {"success": False, "skipped": True, "error": "No model"}
    else:
        try:
            import litellm  # noqa: F401
            litellm_ok = True
        except ImportError:
            litellm_ok = False

        if not litellm_ok:
            _print(f"{YELLOW}litellm not installed — skipping live model test.{RESET}")
            test_result = {"success": False, "skipped": True,
                           "error": "litellm not installed"}
        else:
            model_name = (chosen.get("model") or "").strip()
            _print(f"{BOLD}Testing model:{RESET} {model_name}")
            from pdd.model_tester import _run_test
            completed, result = _animated_run(_run_test, args=(chosen,), timeout=8.0)
            if not completed:
                _print(f"{RED}✗ Test timed out after 8s.{RESET}")
                test_result = {"success": False, "skipped": False,
                               "error": "Timed out", "model": model_name}
            elif result is None:
                test_result = {"success": False, "skipped": False,
                               "error": "Unknown error", "model": model_name}
            else:
                test_result = dict(result)
                test_result["model"] = model_name
                if result.get("success"):
                    dur = result.get("duration_s", 0.0) or 0.0
                    cost = result.get("cost", 0.0) or 0.0
                    _print(
                        f"  {GREEN}✓ {model_name} responded OK{RESET} "
                        f"({dur:.2f}s, ${cost:.4f})"
                    )
                else:
                    err = result.get("error") or "failed"
                    _print(f"  {RED}✗ {err}{RESET}")

    # ---- Summary block ----
    _print()
    _print(f"{BOLD}PDD Setup Complete!{RESET}")
    _print(f"{BOLD}Summary{RESET}")
    _print(f"{CYAN}{LIGHT_HORIZONTAL * 40}{RESET}")

    # CLIs
    cli_names = []
    for r in cli_results or []:
        try:
            if getattr(r, "skipped", False):
                continue
            name = getattr(r, "cli_name", None) or getattr(r, "name", None)
            if not name:
                continue
            if not getattr(r, "api_key_configured", True):
                cli_names.append(f"{name} {YELLOW}(no API key){RESET}")
            else:
                cli_names.append(name)
        except Exception:
            continue
    if cli_names:
        _print(f"  {GREEN}✓{RESET} CLI:        {', '.join(cli_names)}")
    else:
        _print(f"  {DIM}-{RESET} CLI:        not configured")

    # Keys
    if found_keys:
        _print(f"  {GREEN}✓{RESET} API Keys:   {len(found_keys)} found")
    else:
        _print(f"  {RED}✗{RESET} API Keys:   none found")

    # Models
    total_models = sum(model_breakdown.values())
    if total_models:
        provs = ", ".join(
            f"{p} ({c})" for p, c in sorted(model_breakdown.items(), key=lambda x: x[0].lower())
        )
        _print(f"  {GREEN}✓{RESET} Models:     {total_models} configured — {provs}")
        _print(f"               {DIM}{user_csv}{RESET}")
    else:
        _print(f"  {RED}✗{RESET} Models:     none configured")

    # .pddrc
    pddrc_path = Path.cwd() / ".pddrc"
    if pddrc_path.exists():
        _print(f"  {GREEN}✓{RESET} .pddrc:     {pddrc_path}")
    else:
        _print(f"  {DIM}-{RESET} .pddrc:     not created")

    # Test
    if test_result.get("skipped"):
        _print(f"  {YELLOW}-{RESET} Test:       skipped ({test_result.get('error')})")
    elif test_result.get("success"):
        _print(f"  {GREEN}✓{RESET} Test:       passed ({test_result.get('model', '')})")
    else:
        _print(f"  {RED}✗{RESET} Test:       failed — {test_result.get('error', 'unknown')}")

    return test_result


# ============================================================================
# Exit summary
# ============================================================================

def _create_sample_prompt() -> Optional[Path]:
    sample = Path.cwd() / "success_python.prompt"
    if sample.exists():
        return sample
    try:
        sample.write_text(
            "% Write a tiny Python script that prints \"Hello from PDD!\" exactly once.\n"
            "% The function should be named `main` and take no arguments.\n",
            encoding="utf-8",
        )
        return sample
    except Exception:
        return None


def _api_env_path() -> Optional[Path]:
    from pdd.api_key_scanner import _detect_shell
    shell = _detect_shell() or "sh"
    p = Path.home() / ".pdd" / f"api-env.{shell}"
    return p if p.exists() else None


def _print_exit_summary(found_keys: List[Tuple[str, str]], cli_results: List[Any]) -> None:
    sample = _create_sample_prompt()
    api_env = _api_env_path()

    cli_names = []
    for r in cli_results or []:
        try:
            if getattr(r, "skipped", False):
                continue
            n = getattr(r, "cli_name", None) or getattr(r, "name", None)
            if n:
                cli_names.append(n)
        except Exception:
            continue

    summary_path = Path.cwd() / "PDD-SETUP-SUMMARY.txt"
    lines = []
    lines.append("PDD Setup Complete")
    lines.append("=" * 40)
    lines.append("")
    lines.append("Configured CLIs:")
    if cli_names:
        for n in cli_names:
            lines.append(f"  - {n}")
    else:
        lines.append("  (none)")
    lines.append("")
    lines.append("API Keys (masked):")
    for var, src in found_keys:
        val = os.environ.get(var, "")
        lines.append(f"  - {var} = {_mask_key(val)}  (from {src})")
    lines.append("")
    lines.append("Files Created / Updated:")
    user_csv = Path.home() / ".pdd" / "llm_model.csv"
    if user_csv.exists():
        lines.append(f"  - {user_csv}")
    if api_env:
        lines.append(f"  - {api_env}")
    pddrc = Path.cwd() / ".pddrc"
    if pddrc.exists():
        lines.append(f"  - {pddrc}")
    if sample:
        lines.append(f"  - {sample}")
    lines.append("")
    lines.append("QUICK START:")
    if sample:
        lines.append(f"  pdd generate {sample.name}")
    else:
        lines.append("  pdd generate <your_prompt_file>.prompt")
    lines.append("")
    lines.append("LEARN MORE:")
    lines.append("  pdd --help")
    lines.append("  https://promptdriven.ai")
    lines.append("  Discord: https://discord.gg/Yp4RTh8bG7")
    lines.append("")
    if api_env:
        lines.append("Important:")
        lines.append("  To load your API keys into this terminal session, run:")
        lines.append(f"    source {api_env}")
        lines.append("  New terminal windows will load keys automatically.")
        lines.append("")

    try:
        summary_path.write_text("\n".join(lines), encoding="utf-8")
    except Exception:
        pass

    # Terminal output
    _print()
    _print(f"{BOLD}{CYAN}QUICK START{RESET}")
    if sample:
        _print(f"  pdd generate {sample.name}")
    else:
        _print("  pdd generate <your_prompt_file>.prompt")
    _print()
    _print(f"{BOLD}{CYAN}LEARN MORE{RESET}")
    _print(f"  pdd --help")
    _print(f"  https://promptdriven.ai")
    _print(f"  Discord: https://discord.gg/Yp4RTh8bG7")
    _print()
    _print(f"{DIM}Saved full summary to {summary_path}{RESET}")

    if api_env:
        _print()
        _print(f"{BOLD}{YELLOW}Important:{RESET} {BOLD}To load your API keys in this terminal session, run:{RESET}")
        _print(f"  {BOLD}source {api_env}{RESET}")
        _print(f"{DIM}New terminal windows will load these keys automatically.{RESET}")


# ============================================================================
# Options menu
# ============================================================================

def _run_options_menu() -> None:
    from pdd.provider_manager import add_provider_from_registry
    from pdd.model_tester import test_model_interactive

    while True:
        _print()
        _print(f"{BOLD}Options{RESET}")
        _print("  1. Add a provider")
        _print("  2. Test a model")
        _print(f"  {DIM}(press Enter to exit){RESET}")
        try:
            choice = input("Choice: ").strip()
        except EOFError:
            return
        if not choice:
            return
        try:
            if choice == "1":
                add_provider_from_registry()
            elif choice == "2":
                test_model_interactive()
            else:
                _print(f"{YELLOW}Invalid option.{RESET}")
        except KeyboardInterrupt:
            _print()
            return
        except Exception as e:
            _print(f"{RED}Action failed: {e}{RESET}")


# ============================================================================
# Auto phase orchestration
# ============================================================================

def _run_auto_phase(cli_results: List[Any]) -> Tuple[List[Tuple[str, str]], Dict[str, int], Dict[str, Any]]:
    _print_step_banner("Step 1 of 3: Scan for API keys")
    found_keys = _step1_scan_keys()

    try:
        input("\nPress Enter to continue to the next step...")
    except EOFError:
        pass

    _print_step_banner("Step 2 of 3: Configure models and .pddrc")
    breakdown = _step2_configure_models_and_pddrc(found_keys)

    try:
        input("\nPress Enter to continue to the next step...")
    except EOFError:
        pass

    _print_step_banner("Step 3 of 3: Test a model and summary")
    test_result = _step3_test_and_summary(cli_results, found_keys, breakdown)

    return found_keys, breakdown, test_result


# ============================================================================
# Public entry point
# ============================================================================

def run_setup() -> None:
    """Main entry point for `pdd setup`."""
    try:
        _print_pdd_logo()

        # ---- Phase 1: CLI bootstrap ----
        cli_results: List[Any] = []
        try:
            from pdd.cli_detector import detect_and_bootstrap_cli
            cli_results = detect_and_bootstrap_cli() or []
        except KeyboardInterrupt:
            _print(f"\n{YELLOW}Setup interrupted — exiting.{RESET}")
            return
        except Exception as e:
            _print(f"{YELLOW}CLI bootstrap encountered an issue: {e}{RESET}")
            cli_results = []

        # Warn about CLIs without API keys
        for r in cli_results:
            try:
                if getattr(r, "skipped", False):
                    continue
                name = getattr(r, "cli_name", None) or getattr(r, "name", None) or "CLI"
                if not getattr(r, "api_key_configured", True):
                    _print(
                        f"{YELLOW}No API key configured for {name}; "
                        f"its capability may be limited.{RESET}"
                    )
            except Exception:
                continue

        # ---- Phase 2: auto-config ----
        found_keys: List[Tuple[str, str]] = []
        try:
            auto_result = _run_auto_phase(cli_results)
            if not auto_result:
                raise RuntimeError("Auto-configuration did not complete")
            found_keys, _breakdown, _test = auto_result
        except KeyboardInterrupt:
            _print(f"\n{YELLOW}Setup interrupted — exiting.{RESET}")
            return
        except Exception as e:
            error_message = f"{RED}Auto-configuration failed: {e}{RESET}"
            incomplete_message = (
                f"{YELLOW}Setup incomplete. Use the menu to configure manually.{RESET}"
            )
            _print(error_message)
            _print(incomplete_message)
            try:
                _run_options_menu()
            except KeyboardInterrupt:
                _print()
            _print_exit_summary(found_keys, cli_results)
            return

        # ---- Optional menu ----
        try:
            answer = input(
                "\nPress Enter to finish, or 'm' for more options: "
            ).strip()
        except EOFError:
            answer = ""
        except KeyboardInterrupt:
            _print(f"\n{YELLOW}Setup interrupted — exiting.{RESET}")
            return

        if answer:
            try:
                _run_options_menu()
            except KeyboardInterrupt:
                _print()

        _print_exit_summary(found_keys, cli_results)

    except KeyboardInterrupt:
        _print(f"\n{YELLOW}Setup interrupted — exiting.{RESET}")
        return


if __name__ == "__main__":
    run_setup()
