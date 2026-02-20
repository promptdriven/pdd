from __future__ import annotations

import os
import shutil
import subprocess
import sys
from dataclasses import dataclass
from pathlib import Path
from typing import Dict, List, Optional, Tuple

from rich.console import Console

# Maps provider name -> CLI command name
_CLI_COMMANDS: dict[str, str] = {
    "anthropic": "claude",
    "google": "gemini",
    "openai": "codex",
}

# Maps provider name -> environment variable for API key
_API_KEY_ENV_VARS: dict[str, str] = {
    "anthropic": "ANTHROPIC_API_KEY",
    "google": "GEMINI_API_KEY",
    "openai": "OPENAI_API_KEY",
}

# Maps provider name -> npm install command for the CLI
_INSTALL_COMMANDS: dict[str, str] = {
    "anthropic": "npm install -g @anthropic-ai/claude-code",
    "google": "npm install -g @google/gemini-cli",
    "openai": "npm install -g @openai/codex",
}

# Maps provider name -> human-readable CLI name
_CLI_DISPLAY_NAMES: dict[str, str] = {
    "anthropic": "Claude CLI",
    "google": "Gemini CLI",
    "openai": "Codex CLI",
}

# Provider -> primary key env var name (used when saving)
PROVIDER_PRIMARY_KEY: Dict[str, str] = {
    "anthropic": "ANTHROPIC_API_KEY",
    "google": "GEMINI_API_KEY",
    "openai": "OPENAI_API_KEY",
}

# Provider -> display name
PROVIDER_DISPLAY: Dict[str, str] = {
    "anthropic": "Anthropic",
    "google": "Google (Gemini)",
    "openai": "OpenAI",
}

# CLI preference order (claude first because it supports subscription auth)
CLI_PREFERENCE: List[str] = ["gemini", "claude", "codex"]

# Ordered list for the numbered selection table: (provider, cli_name, display_name)
_TABLE_ORDER: List[Tuple[str, str, str]] = [
    ("anthropic", "claude", "Claude CLI"),
    ("openai", "codex", "Codex CLI"),
    ("google", "gemini", "Gemini CLI"),
]

# Shell -> RC file path (relative to home)
SHELL_RC_MAP: Dict[str, str] = {
    "bash": ".bashrc",
    "zsh": ".zshrc",
    "fish": os.path.join(".config", "fish", "config.fish"),
}

# Common installation paths for CLI tools (fallback)
_COMMON_CLI_PATHS: Dict[str, List[Path]] = {
    "claude": [
        Path.home() / ".local" / "bin" / "claude",
        Path("/usr/local/bin/claude"),
        Path("/opt/homebrew/bin/claude"),
    ],
    "codex": [
        Path.home() / ".local" / "bin" / "codex",
        Path("/usr/local/bin/codex"),
        Path("/opt/homebrew/bin/codex"),
    ],
    "gemini": [
        Path.home() / ".local" / "bin" / "gemini",
        Path("/usr/local/bin/gemini"),
        Path("/opt/homebrew/bin/gemini"),
    ],
}

console = Console(highlight=False)

@dataclass
class CliBootstrapResult:
    """Result of CLI detection and bootstrapping."""
    cli_name: str = ""
    provider: str = ""
    cli_path: str = ""
    api_key_configured: bool = False
    skipped: bool = False  # True when user explicitly skipped CLI setup

# ---------------------------------------------------------------------------
# Helpers
# ---------------------------------------------------------------------------

def _which(cmd: str) -> str | None:
    """Return the full path to a command if found on PATH, else None."""
    if not cmd:
        return None
    return shutil.which(cmd)

def _has_api_key(provider: str) -> bool:
    """Check whether the API key environment variable is set for a provider."""
    env_var = _API_KEY_ENV_VARS.get(provider, "")
    if not env_var:
        # Also check fallback keys
        if provider == "google":
            val = os.environ.get("GEMINI_API_KEY") or os.environ.get("GOOGLE_API_KEY")
            return bool(val and val.strip())
        return False
    val = os.environ.get(env_var)
    if val and val.strip():
        return True
    # Fallback for google: also check GOOGLE_API_KEY (Vertex AI convention)
    if provider == "google":
        val = os.environ.get("GOOGLE_API_KEY")
        return bool(val and val.strip())
    return False

def _get_display_key_name(provider: str) -> str:
    """Return the key name to display for a provider, checking which is actually set."""
    if provider == "google":
        # Prefer GEMINI_API_KEY for display if set, else GOOGLE_API_KEY if set, else GEMINI_API_KEY
        if os.environ.get("GEMINI_API_KEY", "").strip():
            return "GEMINI_API_KEY"
        if os.environ.get("GOOGLE_API_KEY", "").strip():
            return "GOOGLE_API_KEY"
        return "GEMINI_API_KEY"
    return _API_KEY_ENV_VARS.get(provider, "")

def _npm_available() -> bool:
    """Check whether npm is available on PATH."""
    return _which("npm") is not None

def _prompt_input(prompt_text: str) -> str:
    """Wrapper around input() for testability."""
    return input(prompt_text)

def _prompt_yes_no(prompt: str) -> bool:
    """Prompt the user with a yes/no question. Default is No."""
    try:
        answer = _prompt_input(prompt).strip().lower()
    except (EOFError, KeyboardInterrupt):
        return False
    return answer in ("y", "yes")

def _run_install(install_cmd: str) -> bool:
    """Run an installation command via subprocess. Returns True on success."""
    try:
        result = subprocess.run(
            install_cmd,
            shell=True,
            capture_output=True,
            text=True,
            timeout=120
        )
        return result.returncode == 0
    except Exception:
        return False

def _detect_shell() -> str:
    """Detect the user's shell from the SHELL environment variable."""
    shell_path = os.environ.get("SHELL", "/bin/bash")
    return os.path.basename(shell_path)

def _get_rc_file_path(shell: str) -> Path:
    """Return the absolute path to the shell's RC file."""
    rc_relative = SHELL_RC_MAP.get(shell, SHELL_RC_MAP["bash"])
    if shell == "fish":
        return Path.home() / ".config" / "fish" / "config.fish"
    return Path.home() / rc_relative

def _get_api_env_file_path(shell: str) -> Path:
    """Return the path to ~/.pdd/api-env.{shell}."""
    return Path.home() / ".pdd" / f"api-env.{shell}"

def _find_cli_binary(cli_name: str) -> Optional[str]:
    """Find a CLI binary by name, including fallbacks."""
    # Use shutil.which first
    result = shutil.which(cli_name)
    if result:
        return result
    
    # Try common paths
    paths = _COMMON_CLI_PATHS.get(cli_name, [])
    for path in paths:
        if path.exists() and os.access(path, os.X_OK):
            return str(path)
            
    # Try nvm fallback for node-based CLIs
    nvm_node = Path.home() / ".nvm" / "versions" / "node"
    if nvm_node.exists():
        try:
            for version_dir in sorted(nvm_node.iterdir(), reverse=True):
                bin_candidate = version_dir / "bin" / cli_name
                if bin_candidate.is_file() and os.access(bin_candidate, os.X_OK):
                    return str(bin_candidate)
        except OSError:
            pass
                
    return None

def _format_export_line(key_name: str, key_value: str, shell: str) -> str:
    """Return the shell-appropriate export line."""
    if shell == "fish":
        return f"set -gx {key_name} {key_value}"
    return f"export {key_name}={key_value}"

def _format_source_line(api_env_path: Path, shell: str) -> str:
    """Return the shell-appropriate source line."""
    path_str = str(api_env_path)
    if shell == "fish":
        return f"test -f {path_str} ; and source {path_str}"
    return f"source {path_str}"

def _save_api_key(key_name: str, key_value: str, shell: str) -> bool:
    """Save API key and update shell RC."""
    pdd_dir = Path.home() / ".pdd"
    api_env_path = _get_api_env_file_path(shell)
    rc_path = _get_rc_file_path(shell)

    try:
        pdd_dir.mkdir(parents=True, exist_ok=True)
        
        # Append or create api-env file
        existing_content = ""
        if api_env_path.exists():
            existing_content = api_env_path.read_text(encoding="utf-8")
        
        export_line = _format_export_line(key_name, key_value, shell)
        lines = existing_content.splitlines()
        # Filter out existing entries for this key
        filtered = [ln for ln in lines if key_name not in ln]
        filtered.append(export_line)
        
        api_env_path.write_text("\n".join(filtered) + "\n", encoding="utf-8")
        
        # Update RC file
        source_line = _format_source_line(api_env_path, shell)
        rc_content = ""
        if rc_path.exists():
            rc_content = rc_path.read_text(encoding="utf-8")
            
        if source_line not in rc_content:
            with open(rc_path, "a", encoding="utf-8") as f:
                f.write(f"\n# pdd CLI API keys\n{source_line}\n")
        
        os.environ[key_name] = key_value
        return True
    except Exception as e:
        console.print(f"[red]Error saving API key: {e}[/red]")
        return False

def _prompt_api_key(provider: str, shell: str) -> bool:
    """Prompt user for API key and save it. Prints save location on success."""
    key_name = PROVIDER_PRIMARY_KEY.get(provider, "")
    if not key_name:
        return False

    display = PROVIDER_DISPLAY.get(provider, provider)
    try:
        key_value = _prompt_input(f"  Enter your {display} API key (or press Enter to skip): ").strip()
    except (EOFError, KeyboardInterrupt):
        return False

    if not key_value:
        if provider == "anthropic":
            console.print("  [dim]Note: Claude CLI may still work with subscription auth.[/dim]")
        return False

    api_env_path = _get_api_env_file_path(shell)
    if _save_api_key(key_name, key_value, shell):
        console.print(f"  [green]\u2713[/green] {key_name} saved to {api_env_path}")
        #console.print(f"  [green]\u2713[/green] {key_name} loaded into current session")
        return True
    return False


def _test_cli(cli_name: str, cli_path: str) -> bool:
    """Run a quick sanity-check invocation of the CLI. Returns True on success."""
    console.print(f"\n  Testing {cli_name}...")
    try:
        result = subprocess.run(
            [cli_path, "--version"],
            capture_output=True,
            text=True,
            timeout=15,
        )
        if result.returncode == 0:
            version_line = (result.stdout or result.stderr or "").strip().splitlines()[0] if (result.stdout or result.stderr) else ""
            console.print(f"  [green]\u2713[/green] {cli_name} version {version_line or 'OK'}")
            return True
        else:
            # Some CLIs exit non-zero for --version but still work; try --help
            result2 = subprocess.run(
                [cli_path, "--help"],
                capture_output=True,
                text=True,
                timeout=15,
            )
            if result2.returncode == 0:
                console.print(f"  [green]\u2713[/green] {cli_name} is responsive")
                return True
            console.print(f"  [red]\u2717[/red] {cli_name} test failed (exit {result.returncode})")
            return False
    except FileNotFoundError:
        console.print(f"  [red]\u2717[/red] {cli_name} binary not found at {cli_path}")
        return False
    except subprocess.TimeoutExpired:
        console.print(f"  [red]\u2717[/red] {cli_name} test timed out")
        return False
    except Exception as exc:
        console.print(f"  [red]\u2717[/red] {cli_name} test error: {exc}")
        return False

# ---------------------------------------------------------------------------
# Public API
# ---------------------------------------------------------------------------

def _bootstrap_single_cli(
    cli_entry: Dict[str, object],
    shell: str,
) -> CliBootstrapResult:
    """Process install/key/test for a single CLI selection.

    Returns a populated CliBootstrapResult (skipped=True on failure).
    """
    display_name = str(cli_entry["display_name"])
    sel_provider: str = str(cli_entry["provider"])
    sel_cli_name: str = str(cli_entry["cli_name"])
    sel_path: Optional[str] = str(cli_entry["path"]) if cli_entry["path"] else None
    sel_has_key: bool = bool(cli_entry["has_key"])

    console.print(f"\n  [bold]Setting up {display_name}...[/bold]")

    def _cli_skip(reason: str = "") -> CliBootstrapResult:
        if reason:
            console.print(f"  [red]\u2717 {reason}[/red]")
        console.print(f"  [red]\u2717 {display_name} not configured.[/red]")
        return CliBootstrapResult(skipped=True)

    # Install step (if not installed)
    if not sel_path:
        install_cmd = _INSTALL_COMMANDS[sel_provider]
        console.print(f"  Install command: [bold]{install_cmd}[/bold]")
        try:
            install_answer = _prompt_input("  Install now? [y/N]: ").strip().lower()
        except (EOFError, KeyboardInterrupt):
            console.print()
            return _cli_skip()

        if install_answer in ("y", "yes"):
            if not _npm_available():
                console.print("  [red]\u2717[/red] npm is not installed. Please install Node.js/npm first.")
                console.print(f"  Then run: {install_cmd}")
                return _cli_skip("npm not available — cannot install CLI")

            console.print(f"  Installing {display_name}...")
            if _run_install(install_cmd):
                sel_path = _find_cli_binary(sel_cli_name)
                if sel_path:
                    console.print(f"  [green]\u2713[/green] Installed {sel_cli_name} at {sel_path}")
                else:
                    console.print("  [yellow]Installation completed but CLI not found on PATH.[/yellow]")
                    return _cli_skip("CLI installed but not found on PATH")
            else:
                console.print("  [red]Installation failed. Try installing manually.[/red]")
                return _cli_skip("installation failed")
        else:
            return _cli_skip()

    # API key step (if not set)
    if not sel_has_key:
        sel_has_key = _prompt_api_key(sel_provider, shell)
        if not sel_has_key and sel_provider != "anthropic":
            console.print(f"  [dim]No API key set. {display_name} may have limited functionality.[/dim]")

    # Force CLI test (no option to skip)
    _test_cli(sel_cli_name, sel_path or sel_cli_name)

    return CliBootstrapResult(
        cli_name=sel_cli_name,
        provider=sel_provider,
        cli_path=sel_path or "",
        api_key_configured=sel_has_key,
    )


def detect_and_bootstrap_cli() -> List[CliBootstrapResult]:
    """Phase 1 entry point for pdd setup.

    Shows a numbered selection table of all three CLI options with their
    install and API-key status, lets the user choose one or more via
    comma-separated input, and walks through installation and key
    configuration for each.

    Returns a list of CliBootstrapResult objects (one per selected CLI).
    On full skip: returns [CliBootstrapResult(skipped=True)].
    """
    # Import banner helper from setup_tool
    from pdd.setup_tool import _print_step_banner
    _print_step_banner("Checking CLI tools...")
    shell = _detect_shell()

    def _skip_all(reason: str = "") -> List[CliBootstrapResult]:
        """Print red CLI-not-configured warning and return a skipped result."""
        if reason:
            console.print(f"  [red]\u2717 {reason}[/red]")
        console.print("  [red]\u2717 CLI not configured. Run `pdd setup` again to configure it.[/red]")
        return [CliBootstrapResult(skipped=True)]

    # ------------------------------------------------------------------
    # 1. Gather status for each CLI in table order
    # ------------------------------------------------------------------
    cli_info: List[Dict[str, object]] = []
    for provider, cli_name, display_name in _TABLE_ORDER:
        path = _find_cli_binary(cli_name)
        has_key = _has_api_key(provider)
        key_display = _get_display_key_name(provider)
        cli_info.append({
            "provider": provider,
            "cli_name": cli_name,
            "display_name": display_name,
            "path": path,
            "has_key": has_key,
            "key_display": key_display,
        })

    # ------------------------------------------------------------------
    # 2. Print numbered selection table with aligned columns
    # ------------------------------------------------------------------
    from rich.markup import escape as _escape

    # Compute column widths using plain strings (no markup) for measurement
    max_name_len = max(len(str(c["display_name"])) for c in cli_info)
    max_install_len = 0
    install_strs_plain: List[str] = []
    install_strs_display: List[str] = []
    for c in cli_info:
        if c["path"]:
            plain = f"\u2713 Found at {c['path']}"
            display = f"[green]\u2713[/green] Found at {_escape(str(c['path']))}"
        else:
            plain = "\u2717 Not found"
            display = "[red]\u2717[/red] Not found"
        install_strs_plain.append(plain)
        install_strs_display.append(display)
        max_install_len = max(max_install_len, len(plain))

    for idx, c in enumerate(cli_info):
        num = idx + 1
        name_padded = str(c["display_name"]).ljust(max_name_len)
        install_display = install_strs_display[idx]
        install_padding = " " * (max_install_len - len(install_strs_plain[idx]))
        if c["has_key"]:
            key_str = f"[green]\u2713[/green] {c['key_display']} is set"
        else:
            key_str = f"[red]\u2717[/red] {c['key_display']} not set"
        console.print(f"  [blue]{num}[/blue]. {name_padded}   {install_display}{install_padding}   {key_str}")

    console.print()

    # ------------------------------------------------------------------
    # 3. Determine smart default
    # ------------------------------------------------------------------
    default_idx = 0  # fallback: Claude (index 0 -> selection "1")
    # Prefer installed + key
    for i, c in enumerate(cli_info):
        if c["path"] and c["has_key"]:
            default_idx = i
            break
    else:
        # Prefer installed only
        for i, c in enumerate(cli_info):
            if c["path"]:
                default_idx = i
                break

    # ------------------------------------------------------------------
    # 4. Prompt for selection (comma-separated)
    # ------------------------------------------------------------------
    try:
        console.print(r"  Select CLIs to use for pdd agentic tools (enter numbers separated by commas, e.g., [blue]1[/blue],[blue]3[/blue]): ", end="")
        raw = _prompt_input("").strip()
    except (EOFError, KeyboardInterrupt):
        console.print()
        return _skip_all()

    if raw.lower() in ("q", "n"):
        return _skip_all()

    # Parse comma-separated selections, deduplicate while preserving order
    selected_indices: List[int] = []
    if raw == "":
        selected_indices = [default_idx]
        console.print(f"  [dim]Defaulting to {cli_info[default_idx]['display_name']}[/dim]")
    else:
        seen: set[int] = set()
        parts = [p.strip() for p in raw.split(",")]
        for part in parts:
            if part in ("1", "2", "3"):
                idx = int(part) - 1
                if idx not in seen:
                    seen.add(idx)
                    selected_indices.append(idx)
        if not selected_indices:
            # No valid numbers found — treat as default
            selected_indices = [default_idx]
            console.print(f"  [dim]Invalid input. Defaulting to {cli_info[default_idx]['display_name']}[/dim]")

    # ------------------------------------------------------------------
    # 5. Process each selected CLI
    # ------------------------------------------------------------------
    results: List[CliBootstrapResult] = []
    for sel_idx in selected_indices:
        try:
            result = _bootstrap_single_cli(cli_info[sel_idx], shell)
            results.append(result)
        except KeyboardInterrupt:
            console.print()
            console.print(f"  [red]\u2717 {cli_info[sel_idx]['display_name']} not configured.[/red]")
            results.append(CliBootstrapResult(skipped=True))
            break  # Stop processing remaining CLIs

    if not results:
        return _skip_all()

    return results


def detect_cli_tools() -> None:
    """Legacy detection function."""
    console.print("Agentic CLI Tool Detection")
    console.print("(Required for: pdd fix, pdd change, pdd bug)")
    console.print()

    found_any = False
    all_with_keys_installed = True
    
    # Use ordered providers
    for provider in ["anthropic", "google", "openai"]:
        cli_cmd = _CLI_COMMANDS[provider]
        display_name = _CLI_DISPLAY_NAMES[provider]
        path = _which(cli_cmd)
        has_key = _has_api_key(provider)
        key_env = _API_KEY_ENV_VARS[provider]

        if path:
            found_any = True
            console.print(f"  [green]\u2713[/green] {display_name} — Found at {path}")
            if has_key:
                console.print(f"    [green]\u2713[/green] {key_env} is set")
            else:
                console.print(f"    [yellow]\u2717[/yellow] {key_env} not set — CLI won't be usable for API calls")
        else:
            console.print(f"  [red]\u2717[/red] {display_name} — Not found")
            if has_key:
                all_with_keys_installed = False
                console.print(f"    [yellow]You have {key_env} set but {display_name} is not installed.[/yellow]")
                console.print(f"    Install: {_INSTALL_COMMANDS[provider]} (install the CLI to use it)")
                if _npm_available():
                    if _prompt_yes_no(f"    Install now? [y/N] "):
                        if _run_install(_INSTALL_COMMANDS[provider]):
                            new_path = _which(cli_cmd)
                            if new_path:
                                console.print(f"    {display_name} installed successfully.")
                            else:
                                console.print("    completed but not found on PATH")
                        else:
                            console.print("    failed (try installing manually)")
                    else:
                        console.print("    Skipped (you can install later).")
                else:
                    console.print("    npm is not installed.")
            else:
                console.print(f"    API key ({key_env}): not set")
        console.print()

    if all_with_keys_installed and found_any:
        console.print("All CLI tools with matching API keys are installed")
    elif not found_any:
        console.print("Quick start: No CLI tools found. Install one of the supported CLIs and set its API key.")

if __name__ == "__main__":
    detect_cli_tools()
