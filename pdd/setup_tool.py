"""pdd setup orchestrator.

Two-phase setup flow:
  Phase 1 — Interactive CLI bootstrap (delegates to cli_detector).
  Phase 2 — Deterministic auto-configuration:
            (a) scan API keys, (b) configure models + .pddrc, (c) test + summary.

All heavy imports are deferred inside functions to keep startup fast and to
avoid hard dependencies when the user only needs a subset of features.
"""

from __future__ import annotations

import getpass
import os
import sys
import threading
from pathlib import Path
from typing import Any, Dict, List, Optional, Tuple

# ANSI escape codes
CYAN = "\033[36m"
WHITE = "\033[37m"
YELLOW = "\033[33m"
GREEN = "\033[32m"
RED = "\033[31m"
DIM = "\033[2m"
BOLD = "\033[1m"
RESET = "\033[0m"

LIGHT_HORIZONTAL = "\u2500"

_console = None


# ---------------------------------------------------------------------------
# Console helpers
# ---------------------------------------------------------------------------

def _get_console():
    if _console is not None:
        return _console
    try:
        from rich.console import Console
        return Console(highlight=False)
    except Exception:  # pragma: no cover - rich is a hard dep but be safe
        return None


def _print(msg: str = "") -> None:
    import builtins

    if getattr(builtins.print, "__module__", "builtins") != "builtins":
        builtins.print(msg)
        return

    console = _get_console()
    if console is not None:
        console.print(msg)
    else:
        builtins.print(msg)


def _print_pdd_logo() -> None:
    logo = r"""
   ____  ____  ____
  |  _ \|  _ \|  _ \
  | |_) | | | | | | |
  |  __/| |_| | |_| |
  |_|   |____/|____/
"""
    _print(f"{CYAN}{logo}{RESET}")
    _print(f"{BOLD}{WHITE}Let's get set up quickly with a solid basic configuration!{RESET}\n")


def _print_step_banner(title: str) -> None:
    line = LIGHT_HORIZONTAL * max(8, len(title) + 4)
    _print()
    _print(f"{CYAN}{line}{RESET}")
    _print(f"{CYAN}{BOLD}  {title}{RESET}")
    _print(f"{CYAN}{line}{RESET}")
    _print()


def _mask_key(value: str) -> str:
    if not value:
        return ""
    if len(value) <= 8:
        return "*" * len(value)
    return f"{value[:4]}...{value[-4:]}"


# ---------------------------------------------------------------------------
# Reference CSV helpers
# ---------------------------------------------------------------------------

def _reference_csv_path() -> Path:
    return Path(__file__).resolve().parent / "data" / "llm_model.csv"


def _read_reference_rows() -> List[Dict[str, str]]:
    from pdd.provider_manager import _read_csv
    path = _reference_csv_path()
    if not path.exists():
        return []
    return _read_csv(path)


def _is_local_row(row: Dict[str, str]) -> bool:
    provider = (row.get("provider") or "").strip().lower()
    base_url = (row.get("base_url") or "").strip().lower()
    if provider in {"lm_studio", "ollama"}:
        return True
    if "localhost" in base_url or "127.0.0.1" in base_url:
        return True
    return False


# ---------------------------------------------------------------------------
# Phase 2 / Step 1 — Scan API keys
# ---------------------------------------------------------------------------

def _scan_environment_for_keys(key_names: List[str]) -> Dict[str, Tuple[str, str]]:
    """Return map: key_name -> (value, source_label) for keys that are found."""
    from pdd.api_key_scanner import _parse_api_env_file, _detect_shell

    found: Dict[str, Tuple[str, str]] = {}

    # 1. process environment
    for name in key_names:
        val = os.environ.get(name)
        if val:
            found[name] = (val, "shell environment")

    # 2. ~/.pdd/api-env.{shell}
    shell = _detect_shell()
    if shell:
        api_env = Path.home() / ".pdd" / f"api-env.{shell}"
        if api_env.exists():
            try:
                parsed = _parse_api_env_file(api_env)
            except Exception:
                parsed = {}
            for name in key_names:
                if name in parsed and name not in found:
                    found[name] = (parsed[name], f"~/.pdd/api-env.{shell}")

    # 3. .env files in cwd / parents (use python-dotenv if available)
    try:
        from dotenv import dotenv_values  # type: ignore
        candidates = []
        cwd = Path.cwd()
        candidates.append(cwd / ".env")
        candidates.append(cwd / ".env.local")
        for parent in cwd.parents:
            candidates.append(parent / ".env")
        seen: set = set()
        for path in candidates:
            try:
                rp = path.resolve()
            except Exception:
                continue
            if rp in seen or not path.exists():
                continue
            seen.add(rp)
            try:
                values = dotenv_values(str(path))
            except Exception:
                continue
            for name in key_names:
                v = values.get(name)
                if v and name not in found:
                    found[name] = (v, f".env ({path})")
    except Exception:
        pass

    return found


def _lookup_key_value(key_name: str) -> str:
    """Best-effort value lookup for masked setup summaries."""
    if os.environ.get(key_name):
        return os.environ[key_name]

    try:
        from pdd.api_key_scanner import _parse_api_env_file, _detect_shell

        shell = _detect_shell()
        if shell:
            api_env = Path.home() / ".pdd" / f"api-env.{shell}"
            value = _parse_api_env_file(api_env).get(key_name, "")
            if value:
                return value
    except Exception:
        pass

    try:
        from dotenv import dotenv_values  # type: ignore

        candidates = [Path.cwd() / ".env", Path.cwd() / ".env.local"]
        candidates.extend(parent / ".env" for parent in Path.cwd().parents)
        seen: set = set()
        for path in candidates:
            try:
                resolved = path.resolve()
            except Exception:
                continue
            if resolved in seen or not path.exists():
                continue
            seen.add(resolved)
            value = dotenv_values(str(path)).get(key_name)
            if value:
                return value
    except Exception:
        pass

    return ""


def _prompt_for_api_key() -> List[Tuple[str, str]]:
    """Interactively prompt user to add one or more API keys."""
    from pdd.provider_manager import _save_key_to_api_env

    rows = _read_reference_rows()
    # unique (provider, api_key) pairs, skip empty api_key (device flow) and locals
    pairs = []
    seen = set()
    for row in rows:
        if _is_local_row(row):
            continue
        provider = (row.get("provider") or "").strip()
        api_key = (row.get("api_key") or "").strip()
        if not provider or not api_key:
            continue
        key = (provider, api_key)
        if key in seen:
            continue
        seen.add(key)
        pairs.append(key)
    pairs.sort(key=lambda p: p[0].lower())

    added: List[Tuple[str, str]] = []

    while True:
        _print()
        _print(f"{BOLD}Add an API key{RESET}")
        _print()
        for i, (prov, _) in enumerate(pairs, start=1):
            _print(f"  {i:>2}. {prov}")
        skip_idx = len(pairs) + 1
        _print(f"  {skip_idx:>2}. Skip")
        _print()

        try:
            choice = input("Enter number (empty to skip): ").strip()
        except EOFError:
            return added
        if not choice or choice == str(skip_idx):
            return added
        try:
            idx = int(choice)
            if idx < 1 or idx > len(pairs):
                _print(f"{YELLOW}Invalid selection.{RESET}")
                continue
        except ValueError:
            _print(f"{YELLOW}Invalid input.{RESET}")
            continue

        provider, api_key_field = pairs[idx - 1]
        # Use first var of multi-credential
        from pdd.provider_manager import parse_api_key_vars
        vars_needed = parse_api_key_vars(api_key_field)

        for var in vars_needed:
            try:
                value = getpass.getpass(f"{var}: ").strip()
            except (EOFError, KeyboardInterrupt):
                _print()
                return added
            if not value:
                _print(f"{YELLOW}Skipped {var}.{RESET}")
                continue
            try:
                _save_key_to_api_env(var, value)
                os.environ[var] = value
                added.append((var, "~/.pdd/api-env"))
                _print(f"{GREEN}✓ Saved {var}{RESET}")
            except Exception as e:
                _print(f"{RED}✗ Failed to save {var}: {e}{RESET}")

        try:
            again = input("Add another key? [y/N]: ").strip().lower()
        except EOFError:
            return added
        if again != "y":
            return added


def _step1_scan_keys() -> List[Tuple[str, str]]:
    from pdd.provider_manager import parse_api_key_vars
    from pdd.api_key_scanner import _detect_shell

    pdd_dir = Path.home() / ".pdd"
    pdd_dir.mkdir(parents=True, exist_ok=True)

    rows = _read_reference_rows()

    # Build provider -> list of var names mapping (preserves grouping)
    provider_vars: Dict[str, List[str]] = {}
    all_vars: List[str] = []
    seen_vars: set = set()
    provider_is_multi: Dict[str, bool] = {}

    for row in rows:
        provider = (row.get("provider") or "").strip()
        api_key_field = (row.get("api_key") or "").strip()
        if not provider or not api_key_field:
            continue
        if _is_local_row(row):
            continue
        vars_list = parse_api_key_vars(api_key_field)
        if not vars_list:
            continue
        if provider not in provider_vars:
            provider_vars[provider] = []
            provider_is_multi[provider] = len(vars_list) > 1
        for v in vars_list:
            if v not in provider_vars[provider]:
                provider_vars[provider].append(v)
            if v not in seen_vars:
                seen_vars.add(v)
                all_vars.append(v)

    found_map = _scan_environment_for_keys(all_vars)

    # Display
    _print(f"{BOLD}Scanning for API keys...{RESET}")
    _print()

    # Multi-credential providers grouped
    for provider, vars_list in sorted(provider_vars.items(), key=lambda p: p[0].lower()):
        if not provider_is_multi.get(provider):
            continue
        present = [v for v in vars_list if v in found_map]
        if not present:
            continue
        total = len(vars_list)
        if len(present) == total:
            _print(f"  {GREEN}✓{RESET} {provider}: {len(present)}/{total} vars set")
        else:
            missing = [v for v in vars_list if v not in found_map]
            _print(f"  {YELLOW}!{RESET} {provider}: {len(present)}/{total} vars set "
                  f"{DIM}(missing: {', '.join(missing)}){RESET}")

    # Single-credential providers, individual lines
    single_lines: List[Tuple[str, str, str]] = []  # (var, provider, source)
    for provider, vars_list in provider_vars.items():
        if provider_is_multi.get(provider):
            continue
        for v in vars_list:
            if v in found_map:
                _, source = found_map[v]
                single_lines.append((v, provider, source))

    if single_lines:
        max_var = max(len(t[0]) for t in single_lines)
        for var, provider, source in sorted(single_lines, key=lambda t: t[0]):
            _print(f"  {GREEN}✓{RESET} {var.ljust(max_var)}  {DIM}({source}){RESET}")

    if not found_map:
        _print(f"  {YELLOW}No API keys found.{RESET}")
        _print()
        _print("You'll need at least one API key to use pdd with cloud models.")
        added = _prompt_for_api_key()
        # Re-scan after additions
        if added:
            found_map = _scan_environment_for_keys(all_vars)

    _print()
    _print(f"{BOLD}Found {len(found_map)} API key(s).{RESET}")

    shell = _detect_shell() or "sh"
    _print(f"{DIM}You can edit your global API keys in ~/.pdd/api-env.{shell}{RESET}")

    return [(name, source) for name, (_, source) in found_map.items()]


# ---------------------------------------------------------------------------
# Phase 2 / Step 2 — Configure models + .pddrc
# ---------------------------------------------------------------------------

def _step2_configure_models_and_pddrc(found_keys: List[Tuple[str, str]]) -> Dict[str, int]:
    from pdd.provider_manager import (
        _read_csv,
        _write_csv_atomic,
        _get_user_csv_path,
        parse_api_key_vars,
    )
    from pdd.pddrc_initializer import _detect_language, _build_pddrc_content

    found_names = {name for name, _ in found_keys}
    reference_rows = _read_reference_rows()

    eligible: List[Dict[str, str]] = []
    for row in reference_rows:
        if _is_local_row(row):
            continue
        api_key_field = (row.get("api_key") or "").strip()
        if api_key_field == "":
            # device flow / no key required (e.g. github copilot) — include
            eligible.append(row)
            continue
        vars_needed = parse_api_key_vars(api_key_field)
        if vars_needed and all(v in found_names for v in vars_needed):
            eligible.append(row)

    user_csv_path = _get_user_csv_path()
    user_csv_path.parent.mkdir(parents=True, exist_ok=True)

    existing_rows: List[Dict[str, str]] = []
    if user_csv_path.exists():
        try:
            existing_rows = _read_csv(user_csv_path)
        except Exception:
            existing_rows = []

    existing_models = {(r.get("model") or "").strip() for r in existing_rows}

    new_rows = []
    for row in eligible:
        model = (row.get("model") or "").strip()
        if not model or model in existing_models:
            continue
        new_rows.append(row)
        existing_models.add(model)

    if new_rows or not user_csv_path.exists():
        all_rows = existing_rows + new_rows
        try:
            _write_csv_atomic(user_csv_path, all_rows)
        except Exception as e:
            _print(f"{RED}✗ Failed to write {user_csv_path}: {e}{RESET}")

    # Per-provider counts (over all rows in user CSV that match eligibility,
    # i.e., final state)
    final_rows = existing_rows + new_rows
    by_provider: Dict[str, int] = {}
    for row in final_rows:
        provider = (row.get("provider") or "").strip() or "unknown"
        by_provider[provider] = by_provider.get(provider, 0) + 1

    _print(f"{BOLD}Configuring models...{RESET}")
    _print()
    if new_rows:
        _print(f"  {GREEN}✓{RESET} Added {len(new_rows)} new model(s) to {user_csv_path}")
    else:
        _print(f"  {DIM}All matching models are already configured.{RESET}")
    _print()
    _print(f"{BOLD}Total: {len(final_rows)} model(s) configured{RESET}")
    for prov, count in sorted(by_provider.items(), key=lambda p: -p[1]):
        _print(f"  {DIM}•{RESET} {prov}: {count}")

    # .pddrc
    _print()
    pddrc_path = Path.cwd() / ".pddrc"
    if pddrc_path.exists():
        _print(f"  {GREEN}✓{RESET} .pddrc detected in this project")
    else:
        _print(f"{BOLD}.pddrc{RESET}: A project-level config file that tells pdd about your")
        _print(f"        language, source/test/example layout, and defaults.")
        _print()
        try:
            answer = input("Create .pddrc in this project? [y/Enter to skip]: ").strip().lower()
        except EOFError:
            answer = ""
        if answer == "y":
            language = _detect_language(Path.cwd()) or "python"
            try:
                content = _build_pddrc_content(language)
                pddrc_path.write_text(content, encoding="utf-8")
                _print(f"  {GREEN}✓{RESET} Created .pddrc (language: {language})")
            except Exception as e:
                _print(f"  {RED}✗ Failed to create .pddrc: {e}{RESET}")
        else:
            _print(f"  {DIM}Skipped .pddrc creation.{RESET}")

    return by_provider


# ---------------------------------------------------------------------------
# Phase 2 / Step 3 — Test + summary
# ---------------------------------------------------------------------------

def _pick_test_model(found_keys: List[Tuple[str, str]]) -> Optional[Dict[str, Any]]:
    from pdd.provider_manager import _read_csv, _get_user_csv_path, parse_api_key_vars

    user_csv_path = _get_user_csv_path()
    if not user_csv_path.exists():
        return None
    try:
        rows = _read_csv(user_csv_path)
    except Exception:
        return None

    found_names = {name for name, _ in found_keys}
    for row in rows:
        if _is_local_row(row):
            continue
        api_key_field = (row.get("api_key") or "").strip()
        if api_key_field == "":
            return row  # device flow eligible
        vars_needed = parse_api_key_vars(api_key_field)
        if vars_needed and all(v in found_names for v in vars_needed):
            return row
    return None


def _run_test_with_animation(row: Dict[str, Any], timeout: float = 8.0) -> Dict[str, Any]:
    from pdd.model_tester import _run_test
    import time

    result_holder: Dict[str, Any] = {}

    def worker():
        try:
            result_holder["result"] = _run_test(row)
        except Exception as e:
            result_holder["result"] = {"success": False, "error": str(e),
                                       "duration_s": 0.0, "cost": 0.0, "tokens": None}

    thread = threading.Thread(target=worker, daemon=True)
    thread.start()

    start = time.time()
    sys.stdout.write("  Testing")
    sys.stdout.flush()
    while thread.is_alive() and (time.time() - start) < timeout:
        time.sleep(1.0)
        sys.stdout.write(".")
        sys.stdout.flush()
    sys.stdout.write("\n")
    sys.stdout.flush()

    if thread.is_alive():
        return {"success": False, "error": f"timeout after {timeout}s",
                "duration_s": timeout, "cost": 0.0, "tokens": None}

    return result_holder.get(
        "result",
        {"success": False, "error": "no result", "duration_s": 0.0, "cost": 0.0, "tokens": None},
    )


def _step3_test_and_summary(
    found_keys: List[Tuple[str, str]],
    by_provider: Dict[str, int],
    cli_results: List[Any],
) -> Dict[str, Any]:
    _print(f"{BOLD}Testing a configured model...{RESET}")
    _print()

    test_result: Dict[str, Any] = {"ran": False}

    try:
        import litellm  # type: ignore  # noqa: F401
        litellm_available = True
    except Exception:
        litellm_available = False

    if not litellm_available:
        _print(f"  {YELLOW}litellm not available — skipping test.{RESET}")
        test_result = {"ran": False, "skipped": True, "reason": "litellm not installed"}
    else:
        row = _pick_test_model(found_keys)
        if row is None:
            _print(f"  {YELLOW}No cloud model with all required keys — skipping test.{RESET}")
            test_result = {"ran": False, "skipped": True, "reason": "no eligible model"}
        else:
            model_name = row.get("model", "?")
            _print(f"  Selected model: {BOLD}{model_name}{RESET}")
            res = _run_test_with_animation(row)
            test_result = {"ran": True, "model": model_name, **res}
            if res.get("success"):
                dur = res.get("duration_s", 0.0)
                cost = res.get("cost", 0.0)
                _print(f"  {GREEN}✓ {model_name} responded OK{RESET} ({dur:.1f}s, ${cost:.4f})")
            else:
                err = res.get("error") or "unknown error"
                _print(f"  {RED}✗ Failed:{RESET} {err}")

    # Summary
    _print()
    _print(f"{BOLD}PDD Setup Complete!{RESET}")
    _print()

    # CLIs
    cli_label = "not configured"
    cli_color = YELLOW
    if cli_results:
        configured = [r for r in cli_results if not getattr(r, "skipped", False) and getattr(r, "cli_name", None)]
        if configured:
            parts = []
            for r in configured:
                name = getattr(r, "cli_name", "?")
                if not getattr(r, "api_key_configured", True):
                    parts.append(f"{name} {YELLOW}(no key){RESET}")
                else:
                    parts.append(name)
            cli_label = ", ".join(parts)
            cli_color = GREEN
    marker = f"{cli_color}{'✓' if cli_color == GREEN else '!'}{RESET}"
    _print(f"  {marker} CLI: {cli_label}")

    # API Keys
    if found_keys:
        _print(f"  {GREEN}✓{RESET} API Keys: {len(found_keys)} found")
    else:
        _print(f"  {YELLOW}!{RESET} API Keys: none found")

    # Models
    total_models = sum(by_provider.values())
    if total_models:
        from pdd.provider_manager import _get_user_csv_path
        path = _get_user_csv_path()
        breakdown = ", ".join(f"{p}: {c}" for p, c in sorted(by_provider.items(), key=lambda x: -x[1]))
        _print(f"  {GREEN}✓{RESET} Models: {total_models} ({breakdown})")
        _print(f"      {DIM}{path}{RESET}")
    else:
        _print(f"  {YELLOW}!{RESET} Models: none configured")

    # .pddrc
    pddrc_path = Path.cwd() / ".pddrc"
    if pddrc_path.exists():
        _print(f"  {GREEN}✓{RESET} .pddrc: exists")
    else:
        _print(f"  {YELLOW}!{RESET} .pddrc: not created")

    # Test
    if test_result.get("ran"):
        if test_result.get("success"):
            _print(f"  {GREEN}✓{RESET} Test: {test_result.get('model')} OK")
        else:
            _print(f"  {RED}✗{RESET} Test: {test_result.get('model')} failed")
    else:
        reason = test_result.get("reason", "skipped")
        _print(f"  {YELLOW}!{RESET} Test: skipped ({reason})")

    return test_result


# ---------------------------------------------------------------------------
# Options menu (fallback / \"more options\")
# ---------------------------------------------------------------------------

def _run_options_menu() -> None:
    from pdd.provider_manager import add_provider_from_registry
    from pdd.model_tester import test_model_interactive

    while True:
        _print()
        _print(f"{BOLD}Options{RESET}")
        _print()
        _print("  1. Add a provider")
        _print("  2. Test a model")
        _print()
        try:
            choice = input("Choose (Enter to exit): ").strip()
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
                _print(f"{YELLOW}Invalid choice.{RESET}")
        except KeyboardInterrupt:
            _print()
            return
        except Exception as e:
            _print(f"{RED}Error: {e}{RESET}")


# ---------------------------------------------------------------------------
# Exit summary
# ---------------------------------------------------------------------------

def _ensure_sample_prompt() -> Path:
    sample_path = Path.cwd() / "success_python.prompt"
    if not sample_path.exists():
        try:
            sample_path.write_text(
                "% Write a Python program that prints \"Hello from pdd!\" to standard output.\n"
                "% Define a function `main()` that performs the print.\n"
                "% Call `main()` from an `if __name__ == \"__main__\":` block.\n",
                encoding="utf-8",
            )
        except Exception:
            pass
    return sample_path


def _print_exit_summary(found_keys: List[Tuple[str, str]], cli_results: List[Any]) -> None:
    from pdd.api_key_scanner import _detect_shell
    from pdd.provider_manager import _get_shell_rc_path

    sample_path = _ensure_sample_prompt()
    shell = _detect_shell() or "sh"
    api_env_path = Path.home() / ".pdd" / f"api-env.{shell}"
    summary_path = Path.cwd() / "PDD-SETUP-SUMMARY.txt"
    rc_path = _get_shell_rc_path()

    # Build summary file content
    lines: List[str] = []
    lines.append("PDD Setup Complete")
    lines.append("==================")
    lines.append("")
    lines.append("CLIs configured:")
    if cli_results:
        for r in cli_results:
            if getattr(r, "skipped", False):
                continue
            name = getattr(r, "cli_name", None) or "(none)"
            path = getattr(r, "cli_path", "") or ""
            keyok = getattr(r, "api_key_configured", True)
            lines.append(f"  - {name} ({path}) "
                         f"{'[OK]' if keyok else '[no API key configured]'}")
    else:
        lines.append("  (none)")
    lines.append("")

    lines.append("API keys found:")
    if found_keys:
        for name, source in found_keys:
            val = _lookup_key_value(name)
            masked = _mask_key(val) if val else "(value not in env)"
            lines.append(f"  - {name} = {masked}  [{source}]")
    else:
        lines.append("  (none)")
    lines.append("")

    lines.append("Files created / managed:")
    lines.append(f"  - ~/.pdd/llm_model.csv  (configured models)")
    if api_env_path.exists():
        lines.append(f"  - {api_env_path}  (API keys)")
    if (Path.cwd() / ".pddrc").exists():
        lines.append(f"  - {(Path.cwd() / '.pddrc')}  (project config)")
    if rc_path and rc_path.exists():
        try:
            if str(api_env_path) in rc_path.read_text(encoding="utf-8"):
                lines.append(f"  - {rc_path}  (loads API keys in new terminals)")
        except Exception:
            pass
    lines.append(f"  - {sample_path}  (sample prompt)")
    lines.append("")

    lines.append("QUICK START:")
    lines.append(f"  pdd generate {sample_path.name}")
    lines.append("")

    if api_env_path.exists():
        lines.append("IMPORTANT: To load your API keys in this terminal session, run:")
        lines.append(f"  source {api_env_path}")
        lines.append("(New terminal windows will load these keys automatically.)")
        lines.append("")

    lines.append("LEARN MORE:")
    lines.append("  - pdd --help")
    lines.append("  - https://promptdriven.ai")
    lines.append("  - Discord: https://discord.gg/Yp4RTh8bG7")
    lines.append("")

    try:
        summary_path.write_text("\n".join(lines), encoding="utf-8")
    except Exception:
        pass

    # Terminal output (condensed)
    _print()
    _print(f"{BOLD}{CYAN}QUICK START{RESET}")
    _print(f"  {BOLD}pdd generate {sample_path.name}{RESET}")
    _print()
    _print(f"{BOLD}{CYAN}LEARN MORE{RESET}")
    _print(f"  • {BOLD}pdd --help{RESET}")
    _print(f"  • https://promptdriven.ai")
    _print(f"  • Discord: https://discord.gg/Yp4RTh8bG7")
    _print()

    if api_env_path.exists():
        _print(f"{BOLD}{YELLOW}Important:{RESET} {BOLD}To load your API keys into this terminal "
              f"session, run:{RESET}")
        _print(f"  {BOLD}source {api_env_path}{RESET}")
        _print(f"{DIM}New terminal windows will load these keys automatically.{RESET}")
        _print()

    _print(f"{DIM}Full summary saved to: {summary_path}{RESET}")


# ---------------------------------------------------------------------------
# Phase orchestration
# ---------------------------------------------------------------------------

def _run_auto_phase(cli_results: List[Any]) -> Tuple[List[Tuple[str, str]], Dict[str, int], Dict[str, Any]]:
    _print_step_banner("Step 1 of 3: Scan for API keys")
    found_keys = _step1_scan_keys()

    _print()
    try:
        input("Press Enter to continue to the next step...")
    except EOFError:
        pass

    _print_step_banner("Step 2 of 3: Configure models and .pddrc")
    by_provider = _step2_configure_models_and_pddrc(found_keys)

    _print()
    try:
        input("Press Enter to continue to the next step...")
    except EOFError:
        pass

    _print_step_banner("Step 3 of 3: Test a model and summarize")
    test_result = _step3_test_and_summary(found_keys, by_provider, cli_results)

    return found_keys, by_provider, test_result


def run_setup() -> None:
    """Main entry point for `pdd setup`."""
    try:
        _print_pdd_logo()

        # Phase 1: CLI bootstrap
        cli_results: List[Any] = []
        try:
            from pdd.cli_detector import CliBootstrapResult, detect_and_bootstrap_cli
            _ = CliBootstrapResult
            cli_results = detect_and_bootstrap_cli() or []
        except KeyboardInterrupt:
            raise
        except Exception as e:
            _print(f"{YELLOW}CLI detection skipped: {e}{RESET}")
            cli_results = []

        for r in cli_results:
            if getattr(r, "skipped", False):
                continue
            name = getattr(r, "cli_name", None)
            if name and not getattr(r, "api_key_configured", True):
                _print(f"{YELLOW}No API key configured for {name}; "
                      f"some capabilities may be limited.{RESET}")

        # Phase 2: deterministic auto-config
        found_keys: List[Tuple[str, str]] = []
        try:
            found_keys, _by_provider, _test = _run_auto_phase(cli_results)
        except KeyboardInterrupt:
            raise
        except Exception as e:
            _print()
            _print(f"{RED}Error during auto-configuration: {e}{RESET}")
            _print(f"{YELLOW}Setup incomplete. Use the menu to configure manually.{RESET}")
            _run_options_menu()
            _print_exit_summary(found_keys, cli_results)
            return

        # Post-setup prompt
        _print()
        try:
            choice = input("Press Enter to finish, or 'm' for more options: ").strip()
        except EOFError:
            choice = ""
        if choice:
            _run_options_menu()

        _print_exit_summary(found_keys, cli_results)

    except KeyboardInterrupt:
        _print()
        _print(f"{YELLOW}Setup interrupted — exiting.{RESET}")
        return


if __name__ == "__main__":
    run_setup()
