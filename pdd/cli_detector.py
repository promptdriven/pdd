"""CLI detector and bootstrapper for pdd setup.

Detects agentic CLI harnesses (Claude, Codex, Gemini, OpenCode) and walks
the user through installation and API key configuration.
"""

from __future__ import annotations

import os
import re
import shutil
import subprocess
from dataclasses import dataclass
from pathlib import Path
from typing import List, Optional, Tuple

from rich.console import Console

from pdd.setup_tool import _print_step_banner


console = Console()


# ---------------------------------------------------------------------------
# Module-level constants
# ---------------------------------------------------------------------------

# Mapping from provider -> primary env var name used for that provider.
# OpenCode is multi-provider so it has no single primary key.
PROVIDER_PRIMARY_KEY = {
    "anthropic": "ANTHROPIC_API_KEY",
    "google": "GEMINI_API_KEY",
    "openai": "OPENAI_API_KEY",
    "opencode": None,
}

# Mapping from provider -> human-friendly display name.
PROVIDER_DISPLAY = {
    "anthropic": "Claude CLI",
    "google": "Gemini CLI",
    "openai": "Codex CLI",
    "opencode": "OpenCode CLI",
}

# Preferred CLI ordering (best-first) when auto-selecting.
CLI_PREFERENCE = ["claude", "codex", "gemini", "opencode"]

# Shell -> RC file mapping.
SHELL_RC_MAP = {
    "bash": "~/.bashrc",
    "zsh": "~/.zshrc",
    "fish": "~/.config/fish/config.fish",
}

# Provider -> CLI binary name.
_PROVIDER_TO_CLI = {
    "anthropic": "claude",
    "google": "gemini",
    "openai": "codex",
    "opencode": "opencode",
}

# CLI -> npm install command.
_CLI_NPM_PACKAGE = {
    "claude": "@anthropic-ai/claude-code",
    "gemini": "@google/gemini-cli",
    "codex": "@openai/codex",
    "opencode": "opencode-ai",
}

# Table display order: (provider, cli_name)
_TABLE_ORDER = [
    ("anthropic", "claude"),
    ("openai", "codex"),
    ("google", "gemini"),
    ("opencode", "opencode"),
]

# OpenCode provider keys — any of these makes OpenCode "configured".
_OPENCODE_PROVIDER_KEYS = [
    "OPENAI_API_KEY",
    "ANTHROPIC_API_KEY",
    "GEMINI_API_KEY",
    "GOOGLE_API_KEY",
    "OPENROUTER_API_KEY",
    "GITHUB_TOKEN",
    "GROQ_API_KEY",
]

_OPENCODE_AUTH_FILE = Path("~/.local/share/opencode/auth.json")


# ---------------------------------------------------------------------------
# Dataclass
# ---------------------------------------------------------------------------

@dataclass
class CliBootstrapResult:
    """Result of bootstrapping a single CLI."""

    cli_name: str = ""
    provider: str = ""
    cli_path: str = ""
    api_key_configured: bool = False
    skipped: bool = False


# ---------------------------------------------------------------------------
# Shell helpers
# ---------------------------------------------------------------------------

def _detect_shell() -> str:
    """Detect the user's shell from the SHELL env var."""
    shell_path = os.environ.get("SHELL", "")
    if not shell_path:
        return "bash"
    name = os.path.basename(shell_path).lower()
    if "zsh" in name:
        return "zsh"
    if "fish" in name:
        return "fish"
    return "bash"


def _rc_file_for_shell(shell: str) -> Path:
    """Return the RC file path for the given shell."""
    rc = SHELL_RC_MAP.get(shell, SHELL_RC_MAP["bash"])
    return Path(os.path.expanduser(rc))


def _api_env_file_for_shell(shell: str) -> Path:
    """Return the path to the pdd-managed api-env file."""
    pdd_dir = Path.home() / ".pdd"
    pdd_dir.mkdir(parents=True, exist_ok=True)
    return pdd_dir / f"api-env.{shell}"


def _export_line(shell: str, key: str, value: str) -> str:
    """Return a shell-specific export line for the given key/value."""
    if shell == "fish":
        return f"set -gx {key} {value}\n"
    return f"export {key}={value}\n"


def _source_line(shell: str, path: Path) -> str:
    """Return a shell-specific source line for the given path."""
    p = str(path)
    if shell == "fish":
        return f"test -f {p} ; and source {p}\n"
    return f"source {p}\n"


def _save_api_key(provider: str, key_name: str, key_value: str) -> bool:
    """Persist an API key to the pdd-managed env file and ensure RC sources it."""
    shell = _detect_shell()
    env_file = _api_env_file_for_shell(shell)
    rc_file = _rc_file_for_shell(shell)

    # Read existing contents and dedupe lines that set this key.
    existing = ""
    if env_file.exists():
        try:
            existing = env_file.read_text()
        except OSError:
            existing = ""

    if shell == "fish":
        pattern = re.compile(rf"^\s*set\s+-gx\s+{re.escape(key_name)}\s+.*$\n?", re.MULTILINE)
    else:
        pattern = re.compile(rf"^\s*export\s+{re.escape(key_name)}=.*$\n?", re.MULTILINE)
    cleaned = pattern.sub("", existing)
    if cleaned and not cleaned.endswith("\n"):
        cleaned += "\n"
    cleaned += _export_line(shell, key_name, key_value)

    try:
        env_file.write_text(cleaned)
        try:
            os.chmod(env_file, 0o600)
        except OSError:
            pass
    except OSError as e:
        console.print(f"[red]Failed to write {env_file}: {e}[/red]")
        return False

    # Ensure RC file sources our env file.
    src_line = _source_line(shell, env_file)
    try:
        rc_file.parent.mkdir(parents=True, exist_ok=True)
        rc_contents = rc_file.read_text() if rc_file.exists() else ""
        if str(env_file) not in rc_contents:
            with rc_file.open("a") as f:
                if rc_contents and not rc_contents.endswith("\n"):
                    f.write("\n")
                f.write(f"# Added by pdd setup\n{src_line}")
    except OSError as e:
        console.print(f"[yellow]Could not update {rc_file}: {e}[/yellow]")

    # Also set in current process so subsequent steps see the key.
    os.environ[key_name] = key_value
    return True


# ---------------------------------------------------------------------------
# CLI detection
# ---------------------------------------------------------------------------

def _candidate_paths_for(cli_name: str) -> List[Path]:
    """Return common paths where a CLI binary might live."""
    home = Path.home()
    candidates: List[Path] = [
        home / ".local" / "bin" / cli_name,
        Path("/usr/local/bin") / cli_name,
        Path("/opt/homebrew/bin") / cli_name,
    ]
    # nvm node version dirs
    nvm_versions = home / ".nvm" / "versions" / "node"
    if nvm_versions.is_dir():
        try:
            for ver in nvm_versions.iterdir():
                candidates.append(ver / "bin" / cli_name)
        except OSError:
            pass
    return candidates


def _find_cli(cli_name: str) -> Optional[str]:
    """Find a CLI binary using shutil.which() with fallback paths."""
    found = shutil.which(cli_name)
    if found:
        return found
    for p in _candidate_paths_for(cli_name):
        if p.is_file() and os.access(p, os.X_OK):
            return str(p)
    return None


def _opencode_auth_file() -> Path:
    """Return the OpenCode auth file path under the current home directory."""
    path = _OPENCODE_AUTH_FILE
    if path.is_absolute():
        return path
    return Path(os.path.expanduser(str(path)))


# ---------------------------------------------------------------------------
# API key checks
# ---------------------------------------------------------------------------

def _get_active_key(provider: str) -> Tuple[Optional[str], Optional[str]]:
    """Return (key_name, key_value) for a provider or (None, None) if absent.

    For OpenCode this returns the first matching provider key found.
    """
    if provider == "opencode":
        for k in _OPENCODE_PROVIDER_KEYS:
            v = os.environ.get(k)
            if v:
                return k, v
        return None, None

    if provider == "google":
        for k in ("GEMINI_API_KEY", "GOOGLE_API_KEY"):
            v = os.environ.get(k)
            if v:
                return k, v
        return None, None

    primary = PROVIDER_PRIMARY_KEY.get(provider)
    if primary:
        v = os.environ.get(primary)
        if v:
            return primary, v
    return None, None


def _is_key_configured(provider: str) -> bool:
    """Determine whether the API key (or auth) for a provider is configured."""
    if provider == "opencode":
        for k in _OPENCODE_PROVIDER_KEYS:
            if os.environ.get(k):
                return True
        if _opencode_auth_file().exists():
            return True
        return False
    name, _ = _get_active_key(provider)
    return name is not None


# ---------------------------------------------------------------------------
# Subprocess helpers
# ---------------------------------------------------------------------------

def _npm_available() -> bool:
    return shutil.which("npm") is not None


def _run_npm_install(package: str) -> bool:
    """Run `npm install -g <package>` and return success status."""
    if not _npm_available():
        console.print("[red]npm is not installed or not on PATH.[/red]")
        console.print("Please install Node.js (which includes npm) and try again.")
        return False
    cmd = ["npm", "install", "-g", package]
    console.print(f"[cyan]Running:[/cyan] {' '.join(cmd)}")
    try:
        result = subprocess.run(cmd, check=False)
        if result.returncode == 0:
            console.print("[green]Installation succeeded.[/green]")
            return True
        console.print(f"[red]npm install exited with code {result.returncode}.[/red]")
        return False
    except (OSError, subprocess.SubprocessError) as e:
        console.print(f"[red]Failed to run npm: {e}[/red]")
        return False


def _test_cli(cli_path: str) -> bool:
    """Run cli --version (or --help) to verify it works."""
    for arg in ("--version", "--help"):
        try:
            result = subprocess.run(
                [cli_path, arg],
                capture_output=True,
                text=True,
                timeout=15,
                check=False,
            )
            if result.returncode == 0:
                first_line = (result.stdout or result.stderr or "").strip().splitlines()
                snippet = first_line[0] if first_line else ""
                console.print(f"[green]✓[/green] {cli_path} {arg} → {snippet}")
                return True
        except (OSError, subprocess.SubprocessError, subprocess.TimeoutExpired):
            continue
    console.print(f"[red]✗[/red] {cli_path} did not respond to --version or --help")
    return False


# ---------------------------------------------------------------------------
# Input helpers
# ---------------------------------------------------------------------------

def _safe_input(prompt: str, default: str = "") -> Optional[str]:
    """Wrap input() to handle KeyboardInterrupt/EOF; return None on abort."""
    try:
        val = input(prompt)
    except (KeyboardInterrupt, EOFError):
        console.print("\n[yellow]Aborted by user.[/yellow]")
        return None
    if not val.strip():
        return default
    return val.strip()


def _prompt_yes_no(prompt: str, default_yes: bool = True) -> Optional[bool]:
    """Prompt for yes/no. Returns True/False or None on abort."""
    suffix = " [Y/n]: " if default_yes else " [y/N]: "
    val = _safe_input(prompt + suffix, default="y" if default_yes else "n")
    if val is None:
        return None
    v = val.strip().lower()
    if v in ("y", "yes"):
        return True
    if v in ("n", "no"):
        return False
    return default_yes


# ---------------------------------------------------------------------------
# Selection table
# ---------------------------------------------------------------------------

def _gather_status() -> List[dict]:
    """Build status dict per CLI in display order."""
    rows = []
    for provider, cli in _TABLE_ORDER:
        path = _find_cli(cli)
        installed = path is not None
        key_configured = _is_key_configured(provider)
        key_name, _ = _get_active_key(provider)
        rows.append({
            "provider": provider,
            "cli": cli,
            "display": PROVIDER_DISPLAY[provider],
            "installed": installed,
            "path": path or "",
            "key_configured": key_configured,
            "key_name": key_name or ("auth file" if provider == "opencode" and key_configured else ""),
        })
    return rows


def _pick_default_index(rows: List[dict]) -> int:
    """Pick a sensible default index (1-based) based on CLI_PREFERENCE."""
    # Prefer installed + key
    for pref in CLI_PREFERENCE:
        for i, row in enumerate(rows, 1):
            if row["cli"] == pref and row["installed"] and row["key_configured"]:
                return i
    # Then installed
    for pref in CLI_PREFERENCE:
        for i, row in enumerate(rows, 1):
            if row["cli"] == pref and row["installed"]:
                return i
    # Fallback: Claude (first row that matches)
    for i, row in enumerate(rows, 1):
        if row["cli"] == "claude":
            return i
    return 1


def _print_selection_table(rows: List[dict], default_idx: int) -> None:
    """Print a numbered, aligned selection table."""
    name_w = max(len(r["display"]) for r in rows)
    key_w = max(len("API Key"), *(len("yes (" + r["key_name"] + ")") if r["key_name"] else 3 for r in rows))
    console.print()
    header = f"  {'#':<3} {'CLI':<{name_w}}  {'Installed':<10}  {'API Key':<{key_w}}"
    console.print(f"[bold]{header}[/bold]")
    console.print("  " + "-" * (len(header) - 2))
    for i, r in enumerate(rows, 1):
        marker = "*" if i == default_idx else " "
        inst_display = "yes" if r["installed"] else "no"
        if r["key_configured"] and r["key_name"]:
            key_display = f"yes ({r['key_name']})"
        else:
            key_display = "yes" if r["key_configured"] else "no"
        console.print(
            f" {marker}{i:<3} {r['display']:<{name_w}}  {inst_display:<10}  {key_display:<{key_w}}"
        )
    console.print()
    console.print(f"  [dim]* = default (press Enter to accept)[/dim]")


def _prompt_selection(rows: List[dict], default_idx: int) -> Optional[List[int]]:
    """Prompt user for a comma-separated selection. Return list of 0-based indices,
    None on abort, or [] for skip."""
    val = _safe_input(
        f"Select CLI(s) to bootstrap [comma-separated, default={default_idx}, q to skip]: ",
        default=str(default_idx),
    )
    if val is None:
        return None
    v = val.strip().lower()
    if v in ("q", "n", "no", "skip"):
        return []
    indices: List[int] = []
    for piece in v.split(","):
        piece = piece.strip()
        if not piece:
            continue
        try:
            n = int(piece)
        except ValueError:
            console.print(f"[red]Invalid selection: {piece!r}[/red]")
            console.print(f"[yellow]Defaulting to {default_idx}.[/yellow]")
            return [default_idx - 1]
        if not 1 <= n <= len(rows):
            console.print(f"[red]Out of range: {n}[/red]")
            console.print(f"[yellow]Defaulting to {default_idx}.[/yellow]")
            return [default_idx - 1]
        indices.append(n - 1)
    if not indices:
        return [default_idx - 1]
    # Dedupe, preserve order
    seen = set()
    deduped = []
    for i in indices:
        if i not in seen:
            seen.add(i)
            deduped.append(i)
    return deduped


def _run_cli_test_for_result(result: CliBootstrapResult, cli: str, display: str) -> None:
    """Run the mandatory CLI verification step when possible."""
    cli_path = result.cli_path or _find_cli(cli)
    if cli_path:
        result.cli_path = cli_path
        console.print(f"[cyan]Testing {display}...[/cyan]")
        _test_cli(cli_path)
    else:
        console.print(f"[red]Cannot test {display}: binary not found.[/red]")


# ---------------------------------------------------------------------------
# Per-CLI bootstrap workflow
# ---------------------------------------------------------------------------

def _bootstrap_one(row: dict) -> CliBootstrapResult:
    """Walk a single CLI through install, key, and test steps."""
    provider = row["provider"]
    cli = row["cli"]
    display = row["display"]

    console.print()
    console.print(f"[bold cyan]── {display} ──[/bold cyan]")

    result = CliBootstrapResult(
        cli_name=cli,
        provider=provider,
        cli_path=row["path"],
        api_key_configured=row["key_configured"],
        skipped=False,
    )

    # ---- Install step ----
    if not row["installed"]:
        console.print(f"[yellow]{display} is not installed.[/yellow]")
        pkg = _CLI_NPM_PACKAGE.get(cli)
        ans = _prompt_yes_no(f"Install {display} via `npm install -g {pkg}`?", default_yes=True)
        if ans is None:
            result.skipped = True
            _run_cli_test_for_result(result, cli, display)
            return result
        if ans:
            ok = _run_npm_install(pkg)
            if ok:
                # Re-detect path
                new_path = _find_cli(cli)
                if new_path:
                    result.cli_path = new_path
                else:
                    console.print(
                        f"[yellow]Installed but {cli} not found on PATH yet - "
                        "you may need to restart your shell.[/yellow]"
                    )
                    result.skipped = True
                    _run_cli_test_for_result(result, cli, display)
                    return result
            else:
                console.print(f"[yellow]Skipping further steps for {display}.[/yellow]")
                result.skipped = True
                _run_cli_test_for_result(result, cli, display)
                return result
        else:
            console.print(f"[yellow]Skipping {display}.[/yellow]")
            result.skipped = True
            _run_cli_test_for_result(result, cli, display)
            return result
    else:
        console.print(f"[green]✓ {display} already installed at {row['path']}[/green]")

    # ---- API key step ----
    if provider == "opencode":
        # Special case: OpenCode is multi-provider.
        if _is_key_configured("opencode"):
            name, _ = _get_active_key("opencode")
            if name:
                console.print(f"[green]✓ OpenCode auth detected via {name}[/green]")
            elif _opencode_auth_file().exists():
                console.print(f"[green]✓ OpenCode auth file present at {_opencode_auth_file()}[/green]")
            result.api_key_configured = True
        else:
            console.print(
                "[yellow]OpenCode has no provider key configured.[/yellow]\n"
                "OpenCode supports several providers. You can either:\n"
                f"  • Set one of: {', '.join(_OPENCODE_PROVIDER_KEYS)}\n"
                "  • Or run `opencode auth login` after setup completes."
            )
            ans = _prompt_yes_no(
                "Configure an OpenCode provider key now?", default_yes=False
            )
            if ans:
                console.print("Which provider key would you like to set?")
                for i, k in enumerate(_OPENCODE_PROVIDER_KEYS, 1):
                    console.print(f"  {i}. {k}")
                pick = _safe_input("Choose number [default=1]: ", default="1")
                if pick is None:
                    result.api_key_configured = False
                else:
                    try:
                        n = int(pick)
                        if 1 <= n <= len(_OPENCODE_PROVIDER_KEYS):
                            key_name = _OPENCODE_PROVIDER_KEYS[n - 1]
                            key_val = _safe_input(f"Enter value for {key_name}: ")
                            if key_val and _save_api_key("opencode", key_name, key_val):
                                result.api_key_configured = True
                                console.print(f"[green]✓ Saved {key_name}[/green]")
                    except ValueError:
                        console.print("[red]Invalid selection.[/red]")
            else:
                console.print(
                    "[dim]You can run `opencode auth login` later to authenticate.[/dim]"
                )
    else:
        if _is_key_configured(provider):
            name, _ = _get_active_key(provider)
            console.print(f"[green]✓ {name} is set[/green]")
            result.api_key_configured = True
        else:
            primary = PROVIDER_PRIMARY_KEY.get(provider)
            console.print(f"[yellow]No API key found for {display} ({primary}).[/yellow]")
            ans = _prompt_yes_no(f"Configure {primary} now?", default_yes=True)
            if ans is None:
                pass
            elif ans:
                key_val = _safe_input(f"Enter value for {primary}: ")
                if key_val and _save_api_key(provider, primary, key_val):
                    result.api_key_configured = True
                    console.print(f"[green]✓ Saved {primary}[/green]")
                else:
                    console.print("[yellow]No key entered; skipping.[/yellow]")
            else:
                console.print(f"[yellow]Skipping API key configuration for {display}.[/yellow]")

    # ---- CLI test step (always runs) ----
    _run_cli_test_for_result(result, cli, display)

    return result


# ---------------------------------------------------------------------------
# Public entry points
# ---------------------------------------------------------------------------

def detect_and_bootstrap_cli() -> List[CliBootstrapResult]:
    """Detect agentic CLIs and bootstrap one or more selected by the user."""
    _print_step_banner("Step: Detect & bootstrap agentic CLI")

    rows = _gather_status()
    default_idx = _pick_default_index(rows)
    _print_selection_table(rows, default_idx)

    selection = _prompt_selection(rows, default_idx)
    if selection is None:
        # Aborted entirely
        return [CliBootstrapResult(skipped=True)]
    if not selection:
        console.print("[yellow]No CLI selected — skipping bootstrap.[/yellow]")
        return [CliBootstrapResult(skipped=True)]

    results: List[CliBootstrapResult] = []
    for idx in selection:
        try:
            res = _bootstrap_one(rows[idx])
        except (KeyboardInterrupt, EOFError):
            console.print("\n[yellow]Skipping current CLI.[/yellow]")
            res = CliBootstrapResult(
                cli_name=rows[idx]["cli"],
                provider=rows[idx]["provider"],
                cli_path=rows[idx]["path"],
                api_key_configured=rows[idx]["key_configured"],
                skipped=True,
            )
        results.append(res)

    if not results:
        return [CliBootstrapResult(skipped=True)]
    return results


def detect_cli_tools() -> None:
    """Legacy detection: report CLI presence and offer install for missing CLIs
    that have a matching API key already configured."""
    console.print()
    console.print("[bold cyan]Detecting agentic CLI tools...[/bold cyan]")

    for provider, cli in _TABLE_ORDER:
        display = PROVIDER_DISPLAY[provider]
        path = _find_cli(cli)
        key_configured = _is_key_configured(provider)

        if path:
            console.print(f"  [green]✓[/green] {display} found at {path}")
        else:
            console.print(f"  [red]✗[/red] {display} not found")

        if provider == "opencode":
            if key_configured:
                name, _ = _get_active_key("opencode")
                if name:
                    console.print(f"      [green]✓[/green] OpenCode auth via {name}")
                elif _opencode_auth_file().exists():
                    console.print(f"      [green]✓[/green] OpenCode auth file present")
            else:
                console.print("      [yellow]No OpenCode provider key/auth found[/yellow]")
        else:
            primary = PROVIDER_PRIMARY_KEY.get(provider)
            if key_configured:
                name, _ = _get_active_key(provider)
                console.print(f"      [green]✓[/green] {name} is set")
            else:
                console.print(f"      [yellow]{primary} not set[/yellow]")

        # Offer install if not present but key is configured
        if not path and key_configured:
            ans = _prompt_yes_no(
                f"  Install {display} via npm now?", default_yes=True
            )
            if ans:
                pkg = _CLI_NPM_PACKAGE.get(cli)
                _run_npm_install(pkg)
