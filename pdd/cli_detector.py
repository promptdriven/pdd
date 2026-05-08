from __future__ import annotations

import json
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
    "opencode": "opencode",
}

# Maps provider name -> environment variable for API key.
# OpenCode is intentionally absent: it is a multi-provider router with no
# canonical API-key env var of its own. It consumes whichever backend
# provider key (ANTHROPIC_API_KEY, OPENAI_API_KEY, OPENROUTER_API_KEY,
# GITHUB_TOKEN, ...) corresponds to the resolved OPENCODE_MODEL — there is
# no single key to prompt for or save. Setup discovers credentials for
# OpenCode via `_has_opencode_oauth_or_config` (auth.json + opencode.json
# + provider env vars) and instructs the user to run `opencode auth login`
# rather than collecting a key into a file under the wrong name.
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
    "opencode": "npm install -g opencode-ai",
}

# Maps provider name -> human-readable CLI name
_CLI_DISPLAY_NAMES: dict[str, str] = {
    "anthropic": "Claude CLI",
    "google": "Gemini CLI",
    "openai": "Codex CLI",
    "opencode": "OpenCode CLI",
}

# Provider -> primary key env var name (used when saving).
# OpenCode is intentionally absent for the same reason as `_API_KEY_ENV_VARS`:
# there is no single "OpenCode API key" to save. `_prompt_api_key` short-
# circuits when the entry is missing so users are not prompted for, and a
# non-OpenCode key is not silently saved under an unrelated name.
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
    "opencode": "OpenCode",
}

# CLI preference order (claude first because it supports subscription auth)
CLI_PREFERENCE: List[str] = ["gemini", "claude", "codex", "opencode"]

# Ordered list for the numbered selection table: (provider, cli_name, display_name)
_TABLE_ORDER: List[Tuple[str, str, str]] = [
    ("anthropic", "claude", "Claude CLI"),
    ("openai", "codex", "Codex CLI"),
    ("google", "gemini", "Gemini CLI"),
    ("opencode", "opencode", "OpenCode CLI"),
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
    "opencode": [
        Path.home() / ".local" / "bin" / "opencode",
        Path.home() / ".npm-global" / "bin" / "opencode",
        Path("/usr/local/bin/opencode"),
        Path("/opt/homebrew/bin/opencode"),
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


def _claude_credentials_file_has_oauth(path: Path) -> bool:
    """True iff ``path`` is a Claude credentials file with a usable OAuth token.

    The Claude Code CLI persists Max/Pro OAuth as
    ``{"claudeAiOauth": {"accessToken": ..., "refreshToken": ..., ...}}``.
    A logged-out or partially-rotated state can leave the file present and
    non-empty but missing those token fields; treating bytes-on-disk as proof
    of OAuth would false-positive on those, then `pdd setup` skips the API-key
    prompt and the user runs into "no credentials" at first call. A few
    non-canonical writers leave the token at the top level, so accept that
    fallback shape too — both google and openai branches do the same.
    """
    try:
        if not path.exists() or path.stat().st_size == 0:
            return False
        data = json.loads(path.read_text(encoding="utf-8"))
    except (OSError, json.JSONDecodeError):
        return False
    if not isinstance(data, dict):
        return False
    oauth = data.get("claudeAiOauth")
    if isinstance(oauth, dict) and (oauth.get("accessToken") or oauth.get("refreshToken")):
        return True
    if data.get("accessToken") or data.get("refreshToken"):
        return True
    return False


def _has_provider_oauth(provider: str) -> bool:
    """Check whether the provider's CLI has a stored OAuth/subscription credential.

    Each agentic CLI maintains its own credential store separate from API-key
    env vars. Setup must treat "OAuth configured" as a fully valid auth path —
    otherwise it tells Max/Pro users they're "missing an API key" and pushes
    them into setting ``ANTHROPIC_API_KEY``, the exact stale-key workflow that
    Issue #813 fixes.

    - **Anthropic**: Claude Code stores Max/Pro OAuth in the macOS keychain
      (``security find-generic-password -s 'Claude Code-credentials'``) or in
      ``~/.claude/.credentials.json`` on Linux. The authoritative runtime check
      is ``claude auth status`` with a ``--json`` fallback (used by
      ``agentic_common`` before launching the subprocess), but setup keeps this
      lightweight to avoid spawning a subprocess and parses the credentials
      file's JSON shape instead — a non-empty file alone is not enough, since a
      stale, corrupt, or logged-out file can still have bytes but no usable
      OAuth token, which would false-positive and skip the API-key prompt the
      user actually needs. The env-supplied ``CLAUDE_CODE_OAUTH_TOKEN`` (used
      by the cloud waterfall) is also accepted.
    - **Google**: Gemini CLI stores OAuth at ``~/.gemini/oauth_creds.json``
      (matches ``_has_gemini_oauth_credentials`` in agentic_common).
    - **OpenAI/Codex**: codex CLI stores ChatGPT login at ``~/.codex/auth.json``.
    """
    if provider == "anthropic":
        if os.environ.get("CLAUDE_CODE_OAUTH_TOKEN", "").strip():
            return True
        # Parse the credentials file's JSON shape (cross-platform). A bare
        # size check would treat a stale/corrupt/logged-out file as OAuth
        # configured, then `pdd setup` skips the API-key prompt and the user
        # is left with no working credential.
        for path in (
            Path.home() / ".claude" / ".credentials.json",
            Path.home() / "Library" / "Application Support" / "Claude" / "credentials.json",
        ):
            if _claude_credentials_file_has_oauth(path):
                return True
        # macOS keychain check is more reliable than file presence; gate on
        # platform to avoid spurious dependencies on Linux/Windows.
        if sys.platform == "darwin":
            try:
                result = subprocess.run(
                    ["security", "find-generic-password", "-s", "Claude Code-credentials"],
                    capture_output=True, text=True, timeout=5, check=False,
                )
                if result.returncode == 0:
                    return True
            except (OSError, subprocess.TimeoutExpired):
                pass
        return False

    if provider == "google":
        creds = Path.home() / ".gemini" / "oauth_creds.json"
        try:
            if creds.exists():
                data = json.loads(creds.read_text(encoding="utf-8"))
                if isinstance(data, dict) and (data.get("refresh_token") or data.get("access_token")):
                    return True
        except (OSError, json.JSONDecodeError):
            pass
        return False

    if provider == "openai":
        auth = Path.home() / ".codex" / "auth.json"
        try:
            if auth.exists():
                data = json.loads(auth.read_text(encoding="utf-8"))
                if isinstance(data, dict) and (data.get("token") or data.get("tokens") or data.get("OPENAI_API_KEY")):
                    return True
        except (OSError, json.JSONDecodeError):
            pass
        return False

    if provider == "opencode":
        return _has_opencode_oauth_or_config()

    return False


def _has_opencode_oauth_or_config() -> bool:
    """Return True when OpenCode has any usable credential / configuration source.

    OpenCode is a multi-provider router with no single canonical API-key env
    var, so setup must look beyond ``~/.local/share/opencode/auth.json`` to
    avoid pushing users into the wrong API-key prompt. Sources (any one
    qualifies):

      * ``~/.local/share/opencode/auth.json`` with non-empty provider data
      * ``~/.config/opencode/opencode.json`` declaring a provider/model
      * Project ``opencode.json`` (walked up from cwd) declaring a provider/model
      * ``OPENCODE_CONFIG`` pointing to a file declaring a provider/model
      * Any backend-provider env var the OpenCode router can route to
        (ANTHROPIC_API_KEY, OPENAI_API_KEY, GEMINI_API_KEY/GOOGLE_API_KEY,
        OPENROUTER_API_KEY, GITHUB_TOKEN, XAI_API_KEY, DEEPSEEK_API_KEY, ...)
    """
    # 1. auth.json with provider data.
    auth = Path.home() / ".local" / "share" / "opencode" / "auth.json"
    try:
        if auth.exists() and auth.stat().st_size > 0:
            data = json.loads(auth.read_text(encoding="utf-8"))
            if isinstance(data, dict) and data:
                for value in data.values():
                    if isinstance(value, dict) and value:
                        return True
                    if isinstance(value, str) and value.strip():
                        return True
    except (OSError, json.JSONDecodeError):
        pass

    # 2. OpenCode config files (global, project, OPENCODE_CONFIG).
    try:
        from pdd.agentic_common import (
            _opencode_config_paths,
            _opencode_config_declares_provider,
        )
    except ImportError:
        _opencode_config_paths = None  # type: ignore[assignment]
        _opencode_config_declares_provider = None  # type: ignore[assignment]
    if _opencode_config_paths is not None and _opencode_config_declares_provider is not None:
        try:
            for cfg in _opencode_config_paths(None):
                if _opencode_config_declares_provider(cfg):
                    return True
        except Exception:
            pass

    # 3. Backend provider env vars the OpenCode router can route to.
    backend_env_keys = (
        "ANTHROPIC_API_KEY", "OPENAI_API_KEY", "GEMINI_API_KEY", "GOOGLE_API_KEY",
        "OPENROUTER_API_KEY", "GITHUB_TOKEN", "XAI_API_KEY", "DEEPSEEK_API_KEY",
        "MISTRAL_API_KEY", "COHERE_API_KEY", "MOONSHOT_API_KEY", "AZURE_API_KEY",
        "AZURE_AI_API_KEY", "AWS_ACCESS_KEY_ID", "GROQ_API_KEY",
        "TOGETHERAI_API_KEY", "FIREWORKS_AI_API_KEY", "FIREWORKS_API_KEY",
        "PERPLEXITYAI_API_KEY", "REPLICATE_API_KEY", "DEEPINFRA_API_KEY",
        "ZAI_API_KEY", "DASHSCOPE_API_KEY", "MINIMAX_API_KEY", "OLLAMA_HOST",
        "LMSTUDIO_HOST",
    )
    for key in backend_env_keys:
        v = os.environ.get(key)
        if v and v.strip():
            return True
    return False


def _has_credential(provider: str) -> bool:
    """True if the provider has *any* working credential (API key OR OAuth).

    Used by setup_tool to decide whether to warn "no API key configured" — a
    stored OAuth login (Claude Max, Gemini OAuth, Codex ChatGPT) is a fully
    valid alternative and should not trigger that warning.
    """
    return _has_api_key(provider) or _has_provider_oauth(provider)

def _get_display_key_name(provider: str) -> str:
    """Return the key name to display for a provider, checking which is actually set."""
    if provider == "google":
        # Prefer GEMINI_API_KEY for display if set, else GOOGLE_API_KEY if set, else GEMINI_API_KEY
        if os.environ.get("GEMINI_API_KEY", "").strip():
            return "GEMINI_API_KEY"
        if os.environ.get("GOOGLE_API_KEY", "").strip():
            return "GOOGLE_API_KEY"
        return "GEMINI_API_KEY"
    if provider == "opencode":
        # OpenCode has no single API-key env var to display — surface the
        # CLI-level auth flow instead so users with `opencode auth login`
        # configured see a meaningful label.
        return "opencode auth login"
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
        if provider == "opencode":
            # OpenCode has no single API key — issuing the generic prompt would
            # silently save user input under the wrong env var (e.g. as
            # ANTHROPIC_API_KEY) and confuse later runs. Guide the user to the
            # supported configuration paths instead.
            console.print(
                "  [yellow]OpenCode has no dedicated API key.[/yellow] Configure it via "
                "[bold]opencode auth login[/bold], an [bold]opencode.json[/bold] config "
                "file (project, ~/.config/opencode/opencode.json, or OPENCODE_CONFIG), "
                "or by setting a backend provider env var (ANTHROPIC_API_KEY, "
                "OPENAI_API_KEY, GEMINI_API_KEY, OPENROUTER_API_KEY, GITHUB_TOKEN, "
                "...). Then set OPENCODE_MODEL=provider/model to pick a route."
            )
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
    sel_has_oauth: bool = bool(cli_entry.get("has_oauth", False))

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

    # Credential step (if no API key AND no OAuth login).
    # Issue #813: Skip the API-key prompt when the CLI already has a stored
    # OAuth/subscription credential (Claude Max keychain, ~/.gemini OAuth,
    # ~/.codex/auth.json) — pushing those users into setting an API key is
    # the exact stale-key workflow this PR exists to make safe.
    if not sel_has_key and not sel_has_oauth:
        sel_has_key = _prompt_api_key(sel_provider, shell)
        if not sel_has_key and sel_provider != "anthropic":
            console.print(f"  [dim]No API key or OAuth login configured. {display_name} may have limited functionality.[/dim]")
    elif sel_has_oauth and not sel_has_key:
        if sel_provider == "anthropic":
            console.print(
                f"  [green]✓[/green] Using stored OAuth/subscription credential for {display_name}; "
                "no API key needed. (Set ANTHROPIC_API_KEY + PDD_KEEP_ANTHROPIC_API_KEY=1 to "
                "force API-key billing instead.)"
            )
        else:
            console.print(
                f"  [green]✓[/green] Using stored OAuth credential for {display_name}; "
                "no API key needed."
            )

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
        # Issue #813: detect OAuth/subscription credentials too — Claude Max,
        # Gemini OAuth, Codex ChatGPT login are valid auth paths that the
        # original API-key-only check missed, leading to UX that pushed
        # OAuth users into the stale-API-key workflow.
        has_oauth = _has_provider_oauth(provider)
        key_display = _get_display_key_name(provider)
        cli_info.append({
            "provider": provider,
            "cli_name": cli_name,
            "display_name": display_name,
            "path": path,
            "has_key": has_key,
            "has_oauth": has_oauth,
            "has_credential": has_key or has_oauth,
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
        # Issue #813: prefer reporting OAuth as credential source when present
        # (more honest than "API key not set" for a Claude Max user).
        if c["has_key"]:
            key_str = f"[green]\u2713[/green] {c['key_display']} is set"
        elif c["has_oauth"]:
            key_str = f"[green]\u2713[/green] OAuth/subscription login configured"
        else:
            key_str = f"[red]\u2717[/red] no credentials ({c['key_display']} or OAuth login)"
        console.print(f"  [blue]{num}[/blue]. {name_padded}   {install_display}{install_padding}   {key_str}")

    console.print()

    # ------------------------------------------------------------------
    # 3. Determine smart default
    # ------------------------------------------------------------------
    default_idx = 0  # fallback: Claude (index 0 -> selection "1")
    # Prefer installed + has any credential (API key OR OAuth login).
    for i, c in enumerate(cli_info):
        if c["path"] and c["has_credential"]:
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
            try:
                num = int(part)
            except ValueError:
                continue
            if 1 <= num <= len(cli_info):
                idx = num - 1
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
