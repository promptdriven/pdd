"""CLI detector and bootstrapper for pdd setup.

Detects and bootstraps agentic CLI harnesses (Claude CLI, Codex CLI,
Gemini CLI, OpenCode CLI) required for `pdd fix`, `pdd change`, `pdd bug`,
and `pdd setup`.
"""

from __future__ import annotations

import os
import re
import shutil
import subprocess
from dataclasses import dataclass
from pathlib import Path
from typing import Dict, List, Optional, Tuple

try:
    from rich.console import Console
    console = Console()
    _HAS_RICH = True
except Exception:  # pragma: no cover
    console = None
    _HAS_RICH = False

try:
    from pdd.setup_tool import _print_step_banner
except Exception:  # pragma: no cover - setup_tool is expected in normal pdd usage
    def _print_step_banner(text: str) -> None:
        _print()
        _print(f"=== {text} ===")
        _print()


# ---------------------------------------------------------------------------
# Module-level constants
# ---------------------------------------------------------------------------

PROVIDER_PRIMARY_KEY: Dict[str, Optional[str]] = {
    "anthropic": "ANTHROPIC_API_KEY",
    "google": "GEMINI_API_KEY",
    "openai": "OPENAI_API_KEY",
    "opencode": None,  # OpenCode is multi-provider; no single primary key.
}

PROVIDER_DISPLAY: Dict[str, str] = {
    "anthropic": "Claude CLI",
    "google": "Gemini CLI",
    "openai": "Codex CLI",
    "opencode": "OpenCode CLI",
}

# Display order in selection table and preferred-default order.
CLI_PREFERENCE: List[str] = ["claude", "codex", "gemini", "opencode"]

SHELL_RC_MAP: Dict[str, str] = {
    "bash": "~/.bashrc",
    "zsh": "~/.zshrc",
    "fish": "~/.config/fish/config.fish",
}

# Provider -> CLI name.
_PROVIDER_CLI: Dict[str, str] = {
    "anthropic": "claude",
    "google": "gemini",
    "openai": "codex",
    "opencode": "opencode",
}

# CLI name -> provider.
_CLI_PROVIDER: Dict[str, str] = {
    "claude": "anthropic",
    "gemini": "google",
    "codex": "openai",
    "opencode": "opencode",
}

_CLI_NPM_PACKAGE: Dict[str, str] = {
    "claude": "@anthropic-ai/claude-code",
    "gemini": "@google/gemini-cli",
    "codex": "@openai/codex",
    "opencode": "opencode-ai",
}

# Accepted provider env keys for OpenCode (any one => configured).
_OPENCODE_ACCEPTED_KEYS: List[str] = [
    "OPENAI_API_KEY",
    "ANTHROPIC_API_KEY",
    "GEMINI_API_KEY",
    "GOOGLE_API_KEY",
    "OPENROUTER_API_KEY",
    "GITHUB_TOKEN",
    "GROQ_API_KEY",
]

_OPENCODE_AUTH_RELATIVE_PATH = Path(".local") / "share" / "opencode" / "auth.json"


# ---------------------------------------------------------------------------
# Dataclass
# ---------------------------------------------------------------------------

@dataclass
class CliBootstrapResult:
    cli_name: str = ""
    provider: str = ""
    cli_path: str = ""
    api_key_configured: bool = False
    skipped: bool = False


# ---------------------------------------------------------------------------
# Output helpers
# ---------------------------------------------------------------------------

def _print(msg: str = "") -> None:
    if _HAS_RICH and console is not None:
        console.print(msg)
    else:
        # Strip very basic rich tags for plain output.
        text = re.sub(r"\[/?[a-zA-Z0-9_# ]+\]", "", msg)
        print(text)


def _input(prompt: str) -> Optional[str]:
    try:
        return input(prompt)
    except (KeyboardInterrupt, EOFError):
        _print("\n[yellow]Input cancelled.[/yellow]")
        return None


# ---------------------------------------------------------------------------
# Shell helpers
# ---------------------------------------------------------------------------

def _detect_shell() -> str:
    shell_env = os.environ.get("SHELL", "")
    base = os.path.basename(shell_env).lower()
    if base in ("zsh", "bash", "fish"):
        return base
    return "bash"


def _rc_path(shell: str) -> Path:
    rc = SHELL_RC_MAP.get(shell, SHELL_RC_MAP["bash"])
    return Path(os.path.expanduser(rc))


def _api_env_file(shell: str) -> Path:
    pdd_dir = Path.home() / ".pdd"
    pdd_dir.mkdir(parents=True, exist_ok=True)
    return pdd_dir / f"api-env.{shell}"


def _format_export(shell: str, key: str, value: str) -> str:
    if shell == "fish":
        return f"set -gx {key} {value}\n"
    return f"export {key}={value}\n"


def _format_source(shell: str, path: Path) -> str:
    p = str(path)
    if shell == "fish":
        return f"test -f {p} ; and source {p}\n"
    return f"source {p}\n"


def _write_api_key(shell: str, key_name: str, key_value: str) -> Path:
    """Write/update API key in ~/.pdd/api-env.{shell} and source from RC."""
    env_file = _api_env_file(shell)
    existing = ""
    if env_file.exists():
        existing = env_file.read_text(encoding="utf-8")

    # Dedup existing export lines for this key, including older quoted output.
    pattern = re.compile(
        rf"^(export\s+{re.escape(key_name)}=.*|set\s+-gx\s+{re.escape(key_name)}\s+.*)$\n?",
        re.MULTILINE,
    )
    cleaned = pattern.sub("", existing)
    if cleaned and not cleaned.endswith("\n"):
        cleaned += "\n"
    cleaned += _format_export(shell, key_name, key_value)
    env_file.write_text(cleaned, encoding="utf-8")

    # Ensure the RC sources our env file.
    rc = _rc_path(shell)
    try:
        rc.parent.mkdir(parents=True, exist_ok=True)
        rc_content = rc.read_text(encoding="utf-8") if rc.exists() else ""
        source_line = _format_source(shell, env_file).rstrip("\n")
        if source_line not in rc_content:
            with rc.open("a", encoding="utf-8") as fh:
                if rc_content and not rc_content.endswith("\n"):
                    fh.write("\n")
                fh.write("# Added by pdd setup\n")
                fh.write(source_line + "\n")
    except OSError as exc:
        _print(f"[yellow]Warning:[/yellow] could not update {rc}: {exc}")

    return env_file


# ---------------------------------------------------------------------------
# CLI discovery
# ---------------------------------------------------------------------------

def _fallback_dirs() -> List[Path]:
    return [
        Path.home() / ".local" / "bin",
        Path("/usr/local/bin"),
        Path("/opt/homebrew/bin"),
    ]


def _nvm_bin_dirs() -> List[Path]:
    nvm_dir = Path(os.environ.get("NVM_DIR", str(Path.home() / ".nvm")))
    versions = nvm_dir / "versions" / "node"
    if not versions.is_dir():
        return []
    bins: List[Path] = []
    try:
        for entry in versions.iterdir():
            b = entry / "bin"
            if b.is_dir():
                bins.append(b)
    except OSError:
        return []
    return bins


def _which(cli_name: str) -> Optional[str]:
    found = shutil.which(cli_name)
    if found:
        return found
    candidates: List[Path] = _fallback_dirs() + _nvm_bin_dirs()
    for d in candidates:
        candidate = d / cli_name
        if candidate.is_file() and os.access(candidate, os.X_OK):
            return str(candidate)
    return None


def _find_cli(cli_name: str) -> Optional[str]:
    """Find a CLI binary on PATH or in common npm/node install locations."""
    return _which(cli_name)


# ---------------------------------------------------------------------------
# API key state helpers
# ---------------------------------------------------------------------------

def _get_provider_key_state(provider: str) -> Tuple[bool, Optional[str], Optional[str]]:
    """Return (configured, key_name_in_use, key_value)."""
    if provider == "google":
        for k in ("GEMINI_API_KEY", "GOOGLE_API_KEY"):
            v = os.environ.get(k)
            if v:
                return True, k, v
        return False, None, None
    if provider == "opencode":
        for k in _OPENCODE_ACCEPTED_KEYS:
            v = os.environ.get(k)
            if v:
                return True, k, v
        auth_path = Path.home() / _OPENCODE_AUTH_RELATIVE_PATH
        if auth_path.exists():
            return True, "auth file", None
        return False, None, None

    primary = PROVIDER_PRIMARY_KEY.get(provider)
    if primary:
        v = os.environ.get(primary)
        if v:
            return True, primary, v
    return False, None, None


# ---------------------------------------------------------------------------
# npm / install helpers
# ---------------------------------------------------------------------------

def _npm_available() -> bool:
    return shutil.which("npm") is not None


def _install_via_npm(package: str) -> bool:
    if not _npm_available():
        _print("[red]npm is not installed.[/red] Please install Node.js / npm first: https://nodejs.org/")
        return False
    _print(f"[cyan]Running:[/cyan] npm install -g {package}")
    try:
        result = subprocess.run(
            ["npm", "install", "-g", package],
            check=False,
        )
        if result.returncode == 0:
            _print(f"[green]Installed {package}[/green]")
            return True
        _print(f"[red]npm install failed (exit {result.returncode}).[/red]")
        return False
    except (OSError, subprocess.SubprocessError) as exc:
        _print(f"[red]npm install error:[/red] {exc}")
        return False


def _test_cli(cli_path: Optional[str], display: str) -> bool:
    if not cli_path:
        _print(f"[yellow]Cannot test {display}: CLI binary is not available.[/yellow]")
        return False
    for args in (["--version"], ["--help"]):
        try:
            result = subprocess.run(
                [cli_path, *args],
                capture_output=True,
                text=True,
                timeout=15,
            )
            if result.returncode == 0:
                first_line = (result.stdout or result.stderr or "").strip().splitlines()
                hint = first_line[0] if first_line else ""
                _print(f"[green]OK[/green] {cli_path} {' '.join(args)} -> {hint[:80]}")
                return True
        except (OSError, subprocess.SubprocessError, subprocess.TimeoutExpired) as exc:
            _print(f"[yellow]Test {' '.join(args)} failed:[/yellow] {exc}")
    _print(f"[red]CLI test failed for {cli_path}[/red]")
    return False


# ---------------------------------------------------------------------------
# Selection table
# ---------------------------------------------------------------------------

def _gather_cli_state() -> List[Dict]:
    """Return list of dicts describing each CLI's current state, in CLI_PREFERENCE order."""
    rows = []
    for cli_name in CLI_PREFERENCE:
        provider = _CLI_PROVIDER[cli_name]
        npm_pkg = _CLI_NPM_PACKAGE[cli_name]
        cli_path = _find_cli(cli_name)
        configured, key_name, _ = _get_provider_key_state(provider)
        rows.append({
            "provider": provider,
            "display": PROVIDER_DISPLAY[provider],
            "cli_name": cli_name,
            "npm_package": npm_pkg,
            "cli_path": cli_path,
            "installed": cli_path is not None,
            "key_configured": configured,
            "key_name": key_name,
        })
    return rows


def _print_selection_table(rows: List[Dict]) -> None:
    widths = (3, 16, 10, 9, 60)
    header = (
        f"{'#':>{widths[0]}}  {'CLI':<{widths[1]}}  "
        f"{'Installed':<{widths[2]}}  {'API Key':<{widths[3]}}  "
        f"{'Path / Key':<{widths[4]}}"
    )
    _print(header)
    _print("-" * len(header))
    for idx, r in enumerate(rows, start=1):
        installed = "yes" if r["installed"] else "no"
        key = "yes" if r["key_configured"] else "no"
        detail = r["cli_path"] or "-"
        if r["key_configured"] and r["key_name"]:
            detail = f"{detail}  ({r['key_name']})"
        _print(
            f"{idx:>{widths[0]}}  {r['display']:<{widths[1]}}  "
            f"{installed:<{widths[2]}}  {key:<{widths[3]}}  {detail:<{widths[4]}}"
        )


def _default_choice(rows: List[Dict]) -> int:
    # Prefer installed+key, then installed, then anthropic (Claude).
    for i, r in enumerate(rows):
        if r["installed"] and r["key_configured"]:
            return i
    for i, r in enumerate(rows):
        if r["installed"]:
            return i
    for i, r in enumerate(rows):
        if r["provider"] == "anthropic":
            return i
    return 0


def _parse_selection(raw: Optional[str], rows: List[Dict], default_idx: int) -> Optional[List[int]]:
    """Parse comma-separated selection; return None if user wants to skip."""
    if raw is None:
        return None
    s = raw.strip().lower()
    if s in ("q", "n", "quit", "skip"):
        return None
    if not s:
        return [default_idx]
    out: List[int] = []
    for part in s.split(","):
        part = part.strip()
        if not part:
            continue
        try:
            i = int(part) - 1
        except ValueError:
            _print(f"[yellow]Ignoring invalid entry:[/yellow] {part}")
            continue
        if 0 <= i < len(rows):
            if i not in out:
                out.append(i)
        else:
            _print(f"[yellow]Out of range:[/yellow] {part}")
    if out:
        return out
    _print(f"[yellow]Defaulting to {default_idx + 1}.[/yellow]")
    return [default_idx]


# ---------------------------------------------------------------------------
# Per-CLI bootstrap steps
# ---------------------------------------------------------------------------

def _bootstrap_install(row: Dict) -> Optional[str]:
    """Ensure CLI is installed; return path or None on failure/skip."""
    if row["installed"]:
        _print(f"[green]{row['display']} already installed at[/green] {row['cli_path']}")
        return row["cli_path"]
    _print(f"\n[bold]{row['display']} not found.[/bold]")
    ans_raw = _input(f"Install via npm ({row['npm_package']})? [Y/n]: ")
    if ans_raw is None:
        _print(f"[yellow]Skipping {row['display']}.[/yellow]")
        return None
    ans = ans_raw.strip().lower()
    if ans in ("n", "no"):
        _print(f"[yellow]Skipping {row['display']}.[/yellow]")
        return None
    if not _install_via_npm(row["npm_package"]):
        return None
    new_path = _find_cli(row["cli_name"])
    if not new_path:
        _print(f"[red]Installed but {row['cli_name']} was not found on PATH.[/red] "
               "You may need to restart your shell.")
        return None
    return new_path


def _bootstrap_api_key(row: Dict) -> bool:
    """Ensure an API key is configured. Returns True if configured, False otherwise."""
    provider = row["provider"]
    configured, key_name, _ = _get_provider_key_state(provider)
    if configured:
        if provider == "opencode" and key_name == "auth file":
            auth_path = Path.home() / _OPENCODE_AUTH_RELATIVE_PATH
            _print(f"[green]OpenCode auth file detected at[/green] {auth_path}")
        elif provider == "opencode":
            _print(f"[green]OpenCode auth via {key_name} is set.[/green]")
        else:
            _print(f"[green]{key_name} is set for {row['display']}.[/green]")
        return True

    shell = _detect_shell()

    if provider == "opencode":
        _print("\n[bold]OpenCode credentials[/bold]")
        _print("OpenCode is provider-agnostic. Configure any one of the following keys:")
        for index, candidate in enumerate(_OPENCODE_ACCEPTED_KEYS, start=1):
            _print(f"  {index}. {candidate}")
        _print("Or run [cyan]opencode auth login[/cyan] after setup completes.")
        configure_raw = _input("Configure a provider key for OpenCode now? [y/N]: ")
        if configure_raw is None:
            _print("[yellow]Skipping OpenCode key configuration.[/yellow] "
                   "Run `opencode auth login` later if needed.")
            return False
        configure = configure_raw.strip().lower()
        if configure not in ("y", "yes"):
            _print("[yellow]Skipping OpenCode key configuration.[/yellow] "
                   "Run `opencode auth login` later if needed.")
            return False

        selection_raw = _input("Select key number or enter key name: ")
        if selection_raw is None:
            _print("[yellow]No key selected; skipping.[/yellow]")
            return False
        selection = selection_raw.strip()
        if not selection:
            _print("[yellow]No key selected; skipping.[/yellow]")
            return False
        if selection.isdigit():
            selected_index = int(selection) - 1
            if 0 <= selected_index < len(_OPENCODE_ACCEPTED_KEYS):
                key_name = _OPENCODE_ACCEPTED_KEYS[selected_index]
            else:
                _print(f"[yellow]Out of range:[/yellow] {selection}")
                return False
        else:
            key_name = selection.upper()
        if key_name not in _OPENCODE_ACCEPTED_KEYS:
            _print(f"[yellow]Warning:[/yellow] {key_name} is not a recognized OpenCode "
                   "provider key, continuing anyway.")
        value_raw = _input(f"Enter value for {key_name}: ")
        if value_raw is None:
            _print("[yellow]No value provided; skipping.[/yellow]")
            return False
        value = value_raw.strip()
        if not value:
            _print("[yellow]No value provided; skipping.[/yellow]")
            return False
        _write_api_key(shell, key_name, value)
        os.environ[key_name] = value
        _print(f"[green]Saved {key_name} to ~/.pdd/api-env.{shell}[/green]")
        return True

    primary = PROVIDER_PRIMARY_KEY.get(provider)
    if not primary:
        _print(f"[yellow]No primary key defined for provider {provider}; skipping.[/yellow]")
        return False
    _print(f"\n[bold]{row['display']} requires {primary}.[/bold]")
    configure_raw = _input(f"{primary} is not set. Add it now? [Y/n]: ")
    if configure_raw is None:
        _print(f"[yellow]Skipping API key configuration for {row['display']}.[/yellow]")
        return False
    if configure_raw.strip().lower() in ("n", "no"):
        _print(f"[yellow]Skipping API key configuration for {row['display']}.[/yellow]")
        return False
    value_raw = _input(f"Enter {primary}: ")
    if value_raw is None:
        _print(f"[yellow]Skipping API key configuration for {row['display']}.[/yellow]")
        return False
    value = value_raw.strip()
    if not value:
        _print(f"[yellow]Skipping API key configuration for {row['display']}.[/yellow]")
        return False
    _write_api_key(shell, primary, value)
    os.environ[primary] = value
    _print(f"[green]Saved {primary} to ~/.pdd/api-env.{shell}[/green]")
    return True


# ---------------------------------------------------------------------------
# Public: detect_and_bootstrap_cli
# ---------------------------------------------------------------------------

def detect_and_bootstrap_cli() -> List[CliBootstrapResult]:
    """Phase 1 entry point for `pdd setup`.\n\n    Detects available agentic CLIs, presents a numbered table, and walks the\n    user through install / API-key / test for each selected CLI.\n    """
    _print_step_banner("Step: Detect & bootstrap agentic CLI")

    rows = _gather_cli_state()
    _print_selection_table(rows)

    default_idx = _default_choice(rows)
    default_label = rows[default_idx]["display"]
    raw = _input(
        f"\nSelect CLI(s) to set up (comma-separated numbers), "
        f"[Enter] for default [{default_idx + 1}: {default_label}], "
        f"or 'q' to skip: "
    )

    selection = _parse_selection(raw, rows, default_idx)
    if selection is None:
        _print("[yellow]Skipping CLI bootstrap.[/yellow]")
        return [CliBootstrapResult(skipped=True)]

    results: List[CliBootstrapResult] = []
    for idx in selection:
        row = rows[idx]
        _print(f"\n[bold cyan]-- {row['display']} --[/bold cyan]")
        try:
            cli_path = _bootstrap_install(row)
            if not cli_path:
                _test_cli(None, row["display"])
                results.append(CliBootstrapResult(
                    cli_name=row["cli_name"],
                    provider=row["provider"],
                    cli_path="",
                    api_key_configured=row["key_configured"],
                    skipped=True,
                ))
                continue

            key_ok = _bootstrap_api_key(row)
            # Always run the test step.
            _test_cli(cli_path, row["display"])

            results.append(CliBootstrapResult(
                cli_name=row["cli_name"],
                provider=row["provider"],
                cli_path=cli_path,
                api_key_configured=key_ok,
                skipped=False,
            ))
        except KeyboardInterrupt:
            _print(f"\n[yellow]Interrupted while configuring {row['display']}.[/yellow]")
            results.append(CliBootstrapResult(
                cli_name=row["cli_name"],
                provider=row["provider"],
                cli_path=row["cli_path"] or "",
                api_key_configured=row["key_configured"],
                skipped=True,
            ))
            continue
        except Exception as exc:  # pragma: no cover - defensive
            _print(f"[red]Error configuring {row['display']}:[/red] {exc}")
            results.append(CliBootstrapResult(
                cli_name=row["cli_name"],
                provider=row["provider"],
                cli_path=row["cli_path"] or "",
                api_key_configured=row["key_configured"],
                skipped=True,
            ))
            continue

    if not results:
        return [CliBootstrapResult(skipped=True)]
    return results


# ---------------------------------------------------------------------------
# Public: detect_cli_tools (legacy)
# ---------------------------------------------------------------------------

def detect_cli_tools() -> None:
    """Legacy detection: report status of each CLI and offer install if a\n    matching API key is already present.\n    """
    _print("\n[bold]Detecting agentic CLI tools...[/bold]")
    for cli_name in CLI_PREFERENCE:
        provider = _CLI_PROVIDER[cli_name]
        npm_pkg = _CLI_NPM_PACKAGE[cli_name]
        display = PROVIDER_DISPLAY[provider]
        path = _find_cli(cli_name)
        configured, key_name, _ = _get_provider_key_state(provider)
        if path:
            _print(f"{display} found at {path}")
        else:
            _print(f"{display} not found")
        if configured:
            if provider == "opencode" and key_name == "auth file":
                _print("OpenCode auth file is present")
            elif provider == "opencode":
                _print(f"OpenCode auth via {key_name} is set")
            else:
                _print(f"{key_name} is set")
        else:
            primary = PROVIDER_PRIMARY_KEY.get(provider)
            if primary:
                _print(f"{primary} not set")
            else:
                _print("OpenCode auth not configured")

        if not path and configured:
            ans_raw = _input(f"Install {display} via npm ({npm_pkg})? [y/N]: ")
            ans = "" if ans_raw is None else ans_raw.strip().lower()
            if ans in ("y", "yes"):
                _install_via_npm(npm_pkg)


__all__ = [
    "CliBootstrapResult",
    "detect_and_bootstrap_cli",
    "detect_cli_tools",
    "PROVIDER_PRIMARY_KEY",
    "PROVIDER_DISPLAY",
    "CLI_PREFERENCE",
    "SHELL_RC_MAP",
]
