"""
Orchestrates pdd setup with OpenCode- and Antigravity-aware CLI bootstrap and
deterministic model configuration.
"""

from __future__ import annotations

import getpass
import json
import os
import re
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


def _is_local_row(row: Dict[str, str]) -> bool:
    """A locally-served model (Ollama / LM Studio / localhost endpoint). These
    are never curated — they don't compete in cloud `--local` provider routing
    and must not be offered for removal (mirrors Step 2's local-model skip)."""
    provider = (row.get("provider") or "").strip().lower()
    base_url = (row.get("base_url") or "").strip().lower()
    return (
        provider in ("lm_studio", "ollama")
        or "127.0.0.1" in base_url
        or "localhost" in base_url
    )


def _provider_pref_path() -> Path:
    """Sidecar storing the user's primary-provider selection, next to the user
    CSV. Used so re-running `pdd setup` doesn't silently re-add providers the
    user previously dropped (issue #1202)."""
    from pdd.provider_manager import _get_user_csv_path
    return _get_user_csv_path().parent / "setup_preferences.json"


def _load_selected_providers() -> Optional[List[str]]:
    """Return the saved primary-provider selection, or None if unset/unreadable.

    A missing or corrupt file is treated as "no preference" — never fatal."""
    path = _provider_pref_path()
    if not path.exists():
        return None
    try:
        # errors="replace" so invalid bytes never raise UnicodeDecodeError;
        # any resulting non-JSON content is handled by the ValueError branch.
        data = json.loads(path.read_text(encoding="utf-8", errors="replace"))
    except (OSError, ValueError):
        return None
    selected = data.get("selected_providers") if isinstance(data, dict) else None
    if isinstance(selected, list) and all(isinstance(p, str) for p in selected):
        return [p.strip() for p in selected if p.strip()]
    return None


def _save_selected_providers(providers: List[str]) -> None:
    """Persist the primary-provider selection. Best-effort; a write failure is
    logged but does not abort setup (the selection still applies this run)."""
    path = _provider_pref_path()
    try:
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text(
            json.dumps({"selected_providers": sorted(providers)}, indent=2) + "\n",
            encoding="utf-8",
        )
    except OSError as exc:
        print(f"  {DIM}(could not save provider preference: {exc}){RESET}")


def _keyed_providers_in_csv() -> set:
    """Return the set of providers in the user CSV that have at least one row
    whose api_key requirements are ACTUALLY satisfied in the environment (a real,
    usable credential — not merely a non-empty api_key column naming an env var
    that isn't set). Used to detect what the options menu actually configured.

    Checking real availability (rather than just a non-empty api_key field)
    matters because the menu's add-provider path appends a provider's rows even
    when the user skips entering the key; such a provider is NOT credentialed and
    must not be unioned into the saved selection (#1202 review)."""
    from pdd.provider_manager import (
        _read_csv, _get_user_csv_path, api_key_requirements_satisfied,
    )
    user_csv = _get_user_csv_path()
    if not user_csv.exists():
        return set()
    try:
        rows = _read_csv(user_csv)
    except Exception:
        return set()
    found_key_names = [name for name, _ in _scan_for_api_keys_quiet()]
    by_provider: Dict[str, List[Dict[str, str]]] = {}
    for r in rows:
        prov = (r.get("provider") or "").strip()
        if prov:
            by_provider.setdefault(prov, []).append(r)
    return {
        prov for prov, prs in by_provider.items()
        if any(
            (r.get("api_key") or "").strip()
            and api_key_requirements_satisfied(r.get("api_key") or "", found_key_names)
            for r in prs
        )
    }


def _union_providers_into_pref(added: set) -> None:
    """Union newly-added keyed providers into an EXISTING saved selection so the
    options menu's "Add a provider" path isn't undone by curation on the next
    `pdd setup` run (#1202 review). Only the providers `added` during the menu
    are unioned — preserved hand-edited rows and rows kept after a declined
    removal are NOT re-absorbed (that would reopen multi-provider routing the
    user curated away). Device-login providers are excluded by construction
    (``added`` comes from `_keyed_providers_in_csv`). No-op when nothing was
    added or no sidecar exists (never creates a policy the user didn't opt
    into)."""
    if not added:
        return
    saved = _load_selected_providers()
    if saved is None:
        return
    updated = sorted(set(saved) | set(added))
    if updated != sorted(saved):
        _save_selected_providers(updated)


def _select_providers_to_keep(
    rows: List[Dict[str, str]],
    curatable: List[str],
) -> Optional[List[str]]:
    """When the auto-configured models span more than one provider, ask the user
    which provider(s) `pdd --local` should use, and return the chosen provider
    names. Returns None when there is no choice to make (<2 curatable providers),
    leaving the row set untouched.

    Only ``curatable`` providers (those derived from the bundled reference CSV
    for which the user has credentials) are offered. Rows for any NON-curatable
    provider — local models (ollama/lm_studio) and foreign providers the user
    has no reference row or credential for — are not listed and preserved by the
    caller. Of an unselected curatable provider's rows, the caller auto-removes
    only PDD-managed ones (bundled reference models + device-login rows with no
    api_key, the free-login case #1202 targets) after an explicit confirmation +
    backup; hand-edited KEYED custom rows under that provider are preserved (and
    the user is warned they may still be used), so curation never deletes a
    user's own additions.

    Rationale (issue #1202): `pdd --local` auto-selects across every provider in
    the CSV by cost/ELO, so leaving several providers in the file silently
    routes a user who configured (say) a Gemini key to a higher-ranked or
    free device-login provider (e.g. GitHub Copilot). Curating the CSV down to
    the user's chosen provider(s) is the reliable fix — reordering rows does
    not change selection.
    """
    providers = sorted({p.strip() for p in curatable if p.strip()})
    if len(providers) < 2:
        return None

    # A provider is "device-login" (e.g. GitHub Copilot) when none of its rows
    # carry an api_key. Those are excluded from the default selection so a free
    # login does not silently outrank a key the user deliberately configured.
    device_providers = {
        p for p in providers
        if all(
            not (r.get("api_key") or "").strip()
            for r in rows
            if (r.get("provider") or "").strip() == p
        )
    }
    non_device = [p for p in providers if p not in device_providers]

    def _best_elo(prov: str) -> float:
        best = 0.0
        for r in rows:
            if (r.get("provider") or "").strip() == prov:
                try:
                    best = max(best, float(r.get("coding_arena_elo") or 0))
                except (TypeError, ValueError):
                    pass
        return best

    # First-time default is a SINGLE provider — the highest-ELO non-device one
    # (a free device login must never be the default over a configured key).
    # A single-provider default means accepting it (Enter) yields an
    # unambiguous pin, so `pdd --local` cannot cost/ELO-route across providers
    # (issue #1202). A user who genuinely wants several selects them explicitly;
    # that explicit multi-provider choice is saved and honored as the default on
    # re-run (so we don't override a deliberate multi-provider setup).
    single_default = [max(non_device, key=_best_elo)] if non_device else providers[:1]
    saved = _load_selected_providers()
    default = [p for p in providers if p in saved] if saved else list(single_default)
    # A stale/foreign saved selection (no overlap with the current providers)
    # falls back to the single non-device default — never to a multi/all set
    # that could reopen cross-provider routing.
    if not default:
        default = single_default

    row_counts = {
        p: sum(1 for r in rows if (r.get("provider") or "").strip() == p)
        for p in providers
    }

    print()
    print("Multiple providers are configured. Which should `pdd --local` use?")
    print(f"  {DIM}(--local picks across all listed providers by cost/ranking, "
          f"so keep only the one(s) you want. Rows for providers you don't "
          f"select are removed from your CSV — a backup is saved first.){RESET}")
    for idx, prov in enumerate(providers, 1):
        n = row_counts.get(prov, 0)
        plural = "s" if n != 1 else ""
        tag = f"  {DIM}(device login, no API key){RESET}" if prov in device_providers else ""
        marker = "*" if prov in default else " "
        print(f"   {marker} {idx}. {prov}  ({n} model{plural}){tag}")
    print(f"  {DIM}Enter numbers (e.g. 1,2), 'a' for all, or press Enter for "
          f"default [{', '.join(default)}].{RESET}")

    # Re-prompt on unrecognized input so a typo never silently falls back to the
    # default and drops a provider the user meant to keep. Only an empty line or
    # EOF (non-interactive stdin) means "accept the default".
    max_attempts = 3
    for attempt in range(max_attempts):
        try:
            raw = input("Provider selection: ").strip()
        except EOFError:
            chosen = default
            break
        if not raw:
            chosen = default
            break
        if raw.lower() in ("a", "all"):
            chosen = list(providers)
            break
        picked: List[str] = []
        for tok in re.split(r"[,\s]+", raw):
            if tok.isdigit() and 1 <= int(tok) <= len(providers):
                picked.append(providers[int(tok) - 1])
        picked = list(dict.fromkeys(picked))  # dedupe, preserve order
        if picked:
            chosen = picked
            break
        if attempt < max_attempts - 1:
            print(f"  {YELLOW}Didn't recognize '{raw}'. Enter the number(s) from "
                  f"the list, 'a' for all, or press Enter for the default.{RESET}")
    else:
        # Exhausted attempts with only invalid input — apply the safe default.
        print(f"  {DIM}No valid selection entered; using default "
              f"[{', '.join(default)}].{RESET}")
        chosen = default

    _save_selected_providers(chosen)
    return chosen


def _apply_provider_curation(
    rows: List[Dict[str, str]],
    curatable: List[str],
    user_csv: Path,
) -> List[Dict[str, str]]:
    """Prompt for provider selection (when >1 curatable) and return ``rows`` with
    the unselected providers' PDD-managed rows removed. Device-login rows and
    PRISTINE bundled rows (matching the shipped reference, ignoring the
    normalization-only ``api_key`` field) are auto-removed after an explicit
    confirmation + timestamped backup; hand-edited or user-added rows are
    preserved and the user is warned they may still be used. Returns ``rows``
    unchanged when there is no choice to make (<2 curatable providers) or the
    user declines removal. Reused by both `_step2_configure_models_and_pddrc`
    and the post-menu curation pass."""
    from pdd.provider_manager import _read_csv
    selected = _select_providers_to_keep(rows, curatable)
    if selected is None:
        return rows
    selected_set = set(selected)
    curatable_set = set(curatable)

    # Identify PDD-managed rows by ROUTING identity: a row is auto-removable only
    # if it routes to the same place as a bundled model — same model name and the
    # same routing fields (base_url, api_key, location). Tuning metadata (ELO,
    # costs, structured_output, reasoning_type, …) is allowed to drift between
    # bundled-CSV versions, so a stale-but-untouched row (incl. a device-login
    # Copilot row whose ELO changed) is still removable. But any row the user
    # RE-POINTED (changed base_url / api_key / location) or ADDED (a model not in
    # the reference) is preserved and warned — covering custom fine-tunes,
    # OpenAI-compatible proxies, and edited Copilot rows alike.
    ref_by_model: Dict[str, Dict[str, str]] = {}
    ref_csv = _ref_csv_path()
    if ref_csv.exists():
        try:
            for r in _read_csv(ref_csv):
                m = (r.get("model") or "").strip()
                if m:
                    ref_by_model[m] = r
        except Exception:
            ref_by_model = {}
    _gemini_aliases = {"GEMINI_API_KEY", "GOOGLE_API_KEY"}
    # Routing fields determine where a request goes and which credential it uses.
    _routing_fields = ["base_url", "location"]

    def _api_key_pristine(row_key: str, ref_key: str) -> bool:
        row_key, ref_key = (row_key or "").strip(), (ref_key or "").strip()
        if row_key == ref_key:
            return True
        # setup normalizes GEMINI_API_KEY→GOOGLE_API_KEY; treat as untouched.
        return bool(row_key) and bool(ref_key) \
            and {row_key, ref_key} <= _gemini_aliases

    def _unselected_curatable(row: Dict[str, str]) -> bool:
        prov = (row.get("provider") or "").strip()
        return prov in curatable_set and prov not in selected_set

    def _is_pdd_managed_row(row: Dict[str, str]) -> bool:
        ref = ref_by_model.get((row.get("model") or "").strip())
        if ref is None:
            return False  # a model the user added themselves
        if not _api_key_pristine(row.get("api_key", ""), ref.get("api_key", "")):
            return False  # re-pointed to a different credential
        return all(
            (row.get(f) or "").strip() == (ref.get(f) or "").strip()
            for f in _routing_fields
        )

    # Auto-remove ONLY PDD-managed rows (routing-identical to a bundled model)
    # under an unselected provider. Anything the user re-pointed or added is
    # preserved and the user is warned.
    to_remove, kept_custom = [], []
    for r in rows:
        if not _unselected_curatable(r):
            continue
        if _is_pdd_managed_row(r):
            to_remove.append(r)
        else:
            kept_custom.append(r)

    if kept_custom:
        print()
        print(f"  {YELLOW}Keeping {len(kept_custom)} hand-edited row(s) under "
              f"providers you didn't select:{RESET}")
        for r in kept_custom:
            print(f"    - {(r.get('provider') or '').strip()} / "
                  f"{(r.get('model') or '').strip()}")
        print(f"  {DIM}(these are your own custom entries; `pdd --local` may "
              f"still use them. Remove them by editing {user_csv.name}.){RESET}")

    if not to_remove:
        return rows

    print()
    print(f"  {YELLOW}The following {len(to_remove)} model row(s) for "
          f"unselected provider(s) will be removed from {user_csv}:{RESET}")
    for r in to_remove:
        print(f"    - {(r.get('provider') or '').strip()} / "
              f"{(r.get('model') or '').strip()}")
    print(f"  {DIM}(a timestamped backup is saved first, so this is "
          f"reversible){RESET}")
    try:
        ans = input("Remove these rows? [Y/n]: ").strip().lower()
    except EOFError:
        ans = ""
    if ans in ("n", "no"):
        print(f"  {DIM}Keeping all rows. Note: `pdd --local` may still "
              f"auto-select across providers by cost/ranking.{RESET}")
        return rows

    if user_csv.exists():
        try:
            base = f"{user_csv.name}.backup.{int(time.time())}"
            backup = user_csv.with_name(base)
            # Avoid clobbering a backup written in the same second.
            suffix = 1
            while backup.exists():
                backup = user_csv.with_name(f"{base}-{suffix}")
                suffix += 1
            backup.write_bytes(user_csv.read_bytes())
            print(f"  {DIM}(previous model list backed up to {backup.name}){RESET}")
        except OSError:
            pass  # backup is best-effort; never block the write
    # Remove by identity so a preserved hand-edited row that happens to share a
    # model name with a removed row is never dropped.
    remove_ids = {id(r) for r in to_remove}
    return [r for r in rows if id(r) not in remove_ids]


def _reference_providers() -> set:
    """Distinct provider names present in the bundled reference CSV — the only
    providers `pdd setup` manages/curates. Custom or foreign providers the user
    hand-added are never curated."""
    ref_csv = _ref_csv_path()
    if not ref_csv.exists():
        return set()
    try:
        from pdd.provider_manager import _read_csv
        return {
            (r.get("provider") or "").strip()
            for r in _read_csv(ref_csv)
            if (r.get("provider") or "").strip()
        }
    except Exception:
        return set()


def _usable_providers_in_csv() -> set:
    """Reference-derived providers `pdd --local` could actually use from the user
    CSV: credential-satisfied or device-login. Local models (Ollama / LM Studio /
    localhost) and any custom/foreign provider NOT in the bundled reference CSV
    are excluded — setup only curates the providers it manages."""
    from pdd.provider_manager import (
        _read_csv, _get_user_csv_path, api_key_requirements_satisfied,
    )
    user_csv = _get_user_csv_path()
    if not user_csv.exists():
        return set()
    try:
        rows = _read_csv(user_csv)
    except Exception:
        return set()
    ref_providers = _reference_providers()
    found = [name for name, _ in _scan_for_api_keys_quiet()]
    return {
        (r.get("provider") or "").strip()
        for r in rows
        if (r.get("provider") or "").strip() in ref_providers
        and not _is_local_row(r)
        and (
            not (r.get("api_key") or "").strip()
            or api_key_requirements_satisfied(r.get("api_key") or "", found)
        )
    }


def _curate_after_menu(before_usable: set) -> None:
    """Re-curate the user CSV after the options menu added a usable provider the
    keyed-only union path doesn't cover. ``before_usable`` is the set of usable
    providers (from `_usable_providers_in_csv`) captured BEFORE the menu ran;
    only providers the menu actually ADDED (``after - before``) trigger this.

    Two gaps it closes (both gated on a real menu addition, so it never
    re-prompts when nothing changed — e.g. the user only tested a model):
      * setup finished with one provider (no prompt, no `setup_preferences.json`)
        and the menu added a second; and
      * a curated user authenticated a DEVICE-login provider (e.g. Copilot) via
        the menu — which the keyed-only union deliberately ignores, so it would
        otherwise re-enter `--local` routing uncurated.
    No-op when nothing usable was added, fewer than 2 usable providers remain,
    or everything added is already in the saved selection (keyed adds the union
    path already folded in)."""
    after_usable = _usable_providers_in_csv()
    added = after_usable - set(before_usable)
    if not added or len(after_usable) < 2:
        return
    saved = _load_selected_providers()
    if saved is not None and added <= set(saved):
        return
    from pdd.provider_manager import _read_csv, _write_csv_atomic, _get_user_csv_path
    user_csv = _get_user_csv_path()
    try:
        rows = _read_csv(user_csv)
    except Exception:
        return
    curated = _apply_provider_curation(rows, sorted(after_usable), user_csv)
    if curated is not rows:
        try:
            _write_csv_atomic(user_csv, curated)
        except Exception as e:
            print(f"Warning: failed to write user CSV: {e}")


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
    # Issue #1202: when several providers are configured, ask which the user
    # actually wants `pdd --local` to use and curate the CSV down to those.
    # Leaving every provider in the file lets cost/ELO auto-selection route to
    # an unintended (often free device-login) provider. Only the reference-CSV
    # providers the user has credentials for are curatable; local models and
    # hand-edited custom rows are preserved untouched.
    curatable = sorted({
        (r.get("provider") or "").strip()
        for r in configured_models
        if (r.get("provider") or "").strip()
    })
    combined = _apply_provider_curation(combined, curatable, user_csv)
    try:
        _write_csv_atomic(user_csv, combined)
    except Exception as e:
        print(f"Warning: failed to write user CSV: {e}")

    provider_counts: Dict[str, int] = {}
    for r in combined:
        p = (r.get("provider") or "unknown").strip()
        provider_counts[p] = provider_counts.get(p, 0) + 1

    # Count only the rows that actually survived curation, so the summary does
    # not claim "N new model(s) added" for rows filtered out before the write.
    written_models = {(r.get("model") or "").strip() for r in combined}
    added_rows = [r for r in new_rows
                  if (r.get("model") or "").strip() in written_models]
    if added_rows:
        print(f"  {GREEN}✓ {len(added_rows)} new model(s) added to {user_csv}{RESET}")
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
            _before_keyed = _keyed_providers_in_csv()
            _before_usable = _usable_providers_in_csv()
            _run_options_menu()
            # Keep a curated selection in sync with providers ADDED via the menu
            # (delta only), so a later run won't drop them — without re-absorbing
            # providers the user curated away.
            _union_providers_into_pref(_keyed_providers_in_csv() - _before_keyed)
            # Re-curate only if the menu actually added a usable provider that
            # would otherwise reopen cross-provider routing.
            _curate_after_menu(_before_usable)
            found_keys = _scan_for_api_keys_quiet()
        else:
            found_keys = context.get("found_keys", [])
            ans = input("Press Enter to finish, or 'm' for more options: ").strip()
            if ans:
                _before_keyed = _keyed_providers_in_csv()
                _before_usable = _usable_providers_in_csv()
                _run_options_menu()
                _union_providers_into_pref(_keyed_providers_in_csv() - _before_keyed)
                _curate_after_menu(_before_usable)
                # Refresh: menu may have added a key
                found_keys = _scan_for_api_keys_quiet()

        _print_exit_summary(found_keys, cli_results)
    except KeyboardInterrupt:
        print()
        print("Setup interrupted — exiting.")
        return


if __name__ == "__main__":
    run_setup()
