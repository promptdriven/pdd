"""Detect and bootstrap agentic CLI harnesses for `pdd setup`.

Supports Claude, Codex, Antigravity (`agy`), Gemini, and OpenCode CLIs.

Public entry points:
    - ``detect_and_bootstrap_cli()`` — Phase 1 of ``pdd setup``: prints a
      numbered selection table, lets the user choose one or more CLIs, and
      walks each through install/credential/test.
    - ``detect_cli_tools()`` — legacy detection (status only).
    - ``CliBootstrapResult`` — dataclass describing the outcome for each CLI.

Module-level constants ``PROVIDER_PRIMARY_KEY``, ``PROVIDER_DISPLAY``,
``CLI_PREFERENCE``, and ``SHELL_RC_MAP`` are exposed for other modules.
"""
from __future__ import annotations

import json
import os
import re
import shutil
import subprocess
import sys
from dataclasses import dataclass
from pathlib import Path
from typing import Dict, List, Optional

from rich.console import Console

from pdd.setup_tool import _print_step_banner

# Module-level console used for all user-facing output. Tests patch this
# attribute to capture printed lines.
console = Console(highlight=False)


# ---------------------------------------------------------------------------
# Public dataclass
# ---------------------------------------------------------------------------


@dataclass
class CliBootstrapResult:
    """Outcome of bootstrapping a single CLI.

    Attributes:
        cli_name: The CLI binary name (e.g. ``"claude"``, ``"agy"``).
        provider: The model provider key (``anthropic``/``openai``/``google``/``opencode``).
        cli_path: Absolute path of the resolved binary, or ``""`` if unresolved.
        api_key_configured: ``True`` if a primary API key was set or saved.
        skipped: ``True`` if the user opted out for this CLI.
    """

    cli_name: str = ""
    provider: str = ""
    cli_path: str = ""
    api_key_configured: bool = False
    skipped: bool = False


# ---------------------------------------------------------------------------
# Module-level constants
# ---------------------------------------------------------------------------


PROVIDER_PRIMARY_KEY: Dict[str, Optional[str]] = {
    "anthropic": "ANTHROPIC_API_KEY",
    "openai": "OPENAI_API_KEY",
    "google": "GEMINI_API_KEY",
    "opencode": None,
}

PROVIDER_DISPLAY: Dict[str, str] = {
    "anthropic": "Claude CLI",
    "openai": "Codex CLI",
    "google": "Google (Gemini family)",
    "opencode": "OpenCode CLI",
}

# Table order: Claude, Codex, Antigravity, Gemini, OpenCode. Antigravity sits
# immediately above the legacy Gemini CLI per the migration plan.
CLI_PREFERENCE: List[str] = ["claude", "codex", "agy", "gemini", "opencode"]

CLI_LABEL: Dict[str, str] = {
    "claude": "Claude CLI",
    "codex": "Codex CLI",
    "agy": "Antigravity CLI (agy)",
    "gemini": "Gemini CLI",
    "opencode": "OpenCode CLI",
}

CLI_PROVIDER: Dict[str, str] = {
    "claude": "anthropic",
    "codex": "openai",
    "agy": "google",
    "gemini": "google",
    "opencode": "opencode",
}

# npm install command per CLI. ``agy`` is None because Antigravity is not
# distributed via npm — detection MUST NOT shell out to its installer URL.
CLI_INSTALL_HINT: Dict[str, Optional[str]] = {
    "claude": "npm install -g @anthropic-ai/claude-code",
    "codex": "npm install -g @openai/codex",
    "agy": None,
    "gemini": "npm install -g @google/gemini-cli",
    "opencode": "npm install -g opencode-ai",
}

AGY_MANUAL_INSTALL_HINT = "curl -fsSL https://antigravity.google/cli/install.sh | bash"

SHELL_RC_MAP: Dict[str, str] = {
    "bash": ".bashrc",
    "zsh": ".zshrc",
    "fish": ".config/fish/config.fish",
}


# ---------------------------------------------------------------------------
# Low-level helpers (kept patchable for tests)
# ---------------------------------------------------------------------------


def _prompt_input(prompt: str = "") -> str:
    """Wrapper around ``input()`` to provide a single patch-point for tests."""
    return input(prompt)


def _which(cmd: str) -> Optional[str]:
    """Wrapper around ``shutil.which`` (single patch-point for tests)."""
    return shutil.which(cmd)


def _npm_available() -> bool:
    """Return True if ``npm`` is on PATH."""
    return _which("npm") is not None


def _find_cli_binary(name: str) -> Optional[str]:
    """Resolve a CLI binary, falling back to common install dirs + nvm.

    Search order:
        1. ``shutil.which(name)``
        2. ``~/.local/bin``, ``/usr/local/bin``, ``/opt/homebrew/bin``,
           ``~/.antigravity/bin``
        3. Every ``~/.nvm/versions/node/*/bin`` directory.
    """
    path = _which(name)
    if path:
        return path
    home = Path.home()
    dirs: List[Path] = [
        home / ".local" / "bin",
        Path("/usr/local/bin"),
        Path("/opt/homebrew/bin"),
        home / ".antigravity" / "bin",
    ]
    nvm_root = home / ".nvm" / "versions" / "node"
    if nvm_root.is_dir():
        try:
            for ver in nvm_root.iterdir():
                dirs.append(ver / "bin")
        except OSError:
            pass
    for d in dirs:
        candidate = d / name
        try:
            if candidate.exists() and os.access(str(candidate), os.X_OK):
                return str(candidate)
        except OSError:
            continue
    return None


def _get_shell_info() -> "tuple[str, Path]":
    """Detect the user's shell and return ``(shell_name, rc_file_path)``."""
    shell_env = os.environ.get("SHELL") or "/bin/bash"
    shell_name = os.path.basename(shell_env)
    if shell_name not in SHELL_RC_MAP:
        shell_name = "bash"
    rc_file = Path.home() / SHELL_RC_MAP[shell_name]
    return shell_name, rc_file


# ---------------------------------------------------------------------------
# Credential detection
# ---------------------------------------------------------------------------


def _claude_credentials_file_has_oauth(path: Path) -> bool:
    """Return True only when the on-disk file declares a usable OAuth token.

    Required by Issue #813: a stale/corrupt/logged-out credentials file can
    still have bytes but no usable token. We must shape-parse for
    ``claudeAiOauth.accessToken`` or ``claudeAiOauth.refreshToken`` (or a
    top-level fallback) and swallow IO/JSON errors quietly.
    """
    try:
        with open(path, "r", encoding="utf-8") as f:
            data = json.load(f)
    except (OSError, json.JSONDecodeError):
        return False
    if not isinstance(data, dict):
        return False
    oauth = data.get("claudeAiOauth")
    if isinstance(oauth, dict):
        if oauth.get("accessToken") or oauth.get("refreshToken"):
            return True
    if data.get("accessToken") or data.get("refreshToken"):
        return True
    return False


def _macos_claude_keychain_has_credential() -> bool:
    """Return True if macOS keychain holds a ``Claude Code-credentials`` entry."""
    if sys.platform != "darwin":
        return False
    try:
        result = subprocess.run(
            ["security", "find-generic-password", "-s", "Claude Code-credentials"],
            capture_output=True,
            text=True,
            timeout=5,
        )
        return result.returncode == 0
    except (OSError, subprocess.SubprocessError):
        return False


def _strip_jsonc_comments(text: str) -> str:
    """Crudely strip ``//`` and ``/* */`` comments from JSONC text."""
    text = re.sub(r"/\*.*?\*/", "", text, flags=re.DOTALL)
    text = re.sub(r"(^|[^:])//.*", lambda m: m.group(1), text)
    return text


def _opencode_config_has_usable_credential() -> bool:
    """Inspect OpenCode JSON/JSONC config sources for a usable provider/model.

    Returns True only when the parsed config declares a selected
    ``model``/``provider`` pairing backed by a resolvable credential
    (``options.apiKey``, ``{env:...}`` with a set env var, ``{file:...}`` with
    a readable non-empty file), or by an explicit local/no-key provider.
    """
    candidates: List[Path] = []
    cfg_env = os.environ.get("OPENCODE_CONFIG")
    if cfg_env:
        candidates.append(Path(cfg_env))
    home_cfg = Path.home() / ".config" / "opencode" / "opencode.json"
    if home_cfg.exists():
        candidates.append(home_cfg)
    try:
        cwd = Path.cwd()
    except OSError:
        cwd = None
    if cwd is not None:
        for parent in [cwd, *cwd.parents]:
            proj = parent / "opencode.json"
            if proj.exists():
                candidates.append(proj)
                break

    contents: List[str] = []
    for c in candidates:
        try:
            contents.append(c.read_text(encoding="utf-8"))
        except OSError:
            continue
    content_env = os.environ.get("OPENCODE_CONFIG_CONTENT")
    if content_env:
        contents.append(content_env)

    local_providers = {"local", "ollama", "lmstudio"}

    for raw in contents:
        try:
            data = json.loads(_strip_jsonc_comments(raw))
        except json.JSONDecodeError:
            continue
        if not isinstance(data, dict):
            continue
        model = data.get("model")
        provider = data.get("provider")
        if not (model and provider):
            continue
        if isinstance(provider, str) and provider.lower() in local_providers:
            return True
        opts = data.get("options")
        if not isinstance(opts, dict):
            continue
        if opts.get("apiKey"):
            return True
        for v in opts.values():
            if not isinstance(v, str):
                continue
            m = re.match(r"^\{env:([A-Za-z_][A-Za-z0-9_]*)\}$", v)
            if m and os.environ.get(m.group(1)):
                return True
            m = re.match(r"^\{file:(.+)\}$", v)
            if m:
                try:
                    if Path(m.group(1)).read_text(encoding="utf-8").strip():
                        return True
                except OSError:
                    pass
    return False


def _has_provider_oauth(provider: str) -> bool:
    """Return True if a stored OAuth/subscription credential exists."""
    home = Path.home()
    if provider == "anthropic":
        if os.environ.get("CLAUDE_CODE_OAUTH_TOKEN"):
            return True
        for p in (
            home / ".claude" / ".credentials.json",
            home / "Library" / "Application Support" / "Claude" / "credentials.json",
        ):
            try:
                if p.exists() and _claude_credentials_file_has_oauth(p):
                    return True
            except OSError:
                continue
        if _macos_claude_keychain_has_credential():
            return True
        return False
    if provider == "google":
        try:
            return (
                (home / ".gemini" / "oauth_creds.json").exists()
                or (home / ".gemini" / "antigravity-cli" / "oauth_creds.json").exists()
            )
        except OSError:
            return False
    if provider == "openai":
        p = home / ".codex" / "auth.json"
        if p.exists():
            try:
                with open(p, "r", encoding="utf-8") as f:
                    data = json.load(f)
                if isinstance(data, dict):
                    return bool(data)
                if isinstance(data, list):
                    return len(data) > 0
                return bool(data)
            except (OSError, json.JSONDecodeError):
                return False
        return False
    if provider == "opencode":
        auth = home / ".local" / "share" / "opencode" / "auth.json"
        if auth.exists():
            try:
                with open(auth, "r", encoding="utf-8") as f:
                    data = json.load(f)
                if isinstance(data, dict) and any(
                    bool(v) for v in data.values()
                ):
                    return True
            except (OSError, json.JSONDecodeError):
                pass
        if _opencode_config_has_usable_credential():
            return True
        return False
    return False


# ---------------------------------------------------------------------------
# API key detection
# ---------------------------------------------------------------------------


def _load_opencode_provider_keys() -> set:
    """Build the set of env vars that satisfy OpenCode's credential check.

    Drawn from non-empty ``api_key`` fields in ``pdd/data/llm_model.csv``
    (pipe-delimited), augmented with OpenCode-compatible extras like
    ``GITHUB_TOKEN``.
    """
    keys: set = {"GITHUB_TOKEN"}
    csv_path = Path(__file__).parent / "data" / "llm_model.csv"
    if not csv_path.exists():
        # Fallback: most common provider keys, so behavior is sensible if the
        # catalog is missing for any reason.
        keys.update(
            {
                "ANTHROPIC_API_KEY",
                "OPENAI_API_KEY",
                "GEMINI_API_KEY",
                "GOOGLE_API_KEY",
                "OPENROUTER_API_KEY",
            }
        )
        return keys
    try:
        with open(csv_path, "r", encoding="utf-8") as f:
            header = f.readline().strip().split(",")
            if "api_key" not in header:
                return keys
            api_idx = header.index("api_key")
            for line in f:
                parts = line.rstrip("\n").split(",")
                if len(parts) > api_idx:
                    raw = parts[api_idx].strip()
                    if not raw:
                        continue
                    for k in raw.split("|"):
                        k = k.strip()
                        if k:
                            keys.add(k)
    except OSError:
        pass
    return keys


_OPENCODE_PROVIDER_KEYS: set = _load_opencode_provider_keys()


def _has_api_key(provider: str) -> bool:
    """Return True if at least one primary API-key env var is set."""
    if provider == "opencode":
        return any(os.environ.get(k) for k in _OPENCODE_PROVIDER_KEYS)
    if provider == "google":
        return bool(
            os.environ.get("GEMINI_API_KEY")
            or os.environ.get("GOOGLE_API_KEY")
            or os.environ.get("ANTIGRAVITY_API_KEY")
        )
    key = PROVIDER_PRIMARY_KEY.get(provider)
    return bool(key and os.environ.get(key))


def _displayed_google_key() -> str:
    for k in ("GEMINI_API_KEY", "GOOGLE_API_KEY", "ANTIGRAVITY_API_KEY"):
        if os.environ.get(k):
            return k
    return "GEMINI_API_KEY"


def _credential_status_label(provider: str) -> str:
    if provider == "anthropic":
        return "ANTHROPIC_API_KEY"
    if provider == "openai":
        return "OPENAI_API_KEY"
    if provider == "google":
        return _displayed_google_key()
    if provider == "opencode":
        return "OpenCode provider credential"
    return provider


# ---------------------------------------------------------------------------
# API-key file management
# ---------------------------------------------------------------------------


def _save_api_key(key: str, value: str) -> None:
    """Persist an API key to ``~/.pdd/api-env.<shell>`` and source it in RC."""
    shell_name, rc_file = _get_shell_info()
    pdd_dir = Path.home() / ".pdd"
    pdd_dir.mkdir(parents=True, exist_ok=True)
    env_file = pdd_dir / f"api-env.{shell_name}"

    os.environ[key] = value

    existing_lines: List[str] = []
    if env_file.exists():
        existing_lines = env_file.read_text(encoding="utf-8").splitlines(keepends=True)

    # Deduplicate by key name. Matches "export K=" and "set -gx K ...".
    dedup_re = re.compile(
        r"^\s*(?:export\s+" + re.escape(key) + r"\s*=|set\s+-gx\s+" + re.escape(key) + r"\b)"
    )
    existing_lines = [l for l in existing_lines if not dedup_re.match(l)]

    if shell_name == "fish":
        existing_lines.append(f"set -gx {key} {value}\n")
    else:
        existing_lines.append(f"export {key}={value}\n")

    env_file.write_text("".join(existing_lines), encoding="utf-8")

    if rc_file.exists():
        rc_content = rc_file.read_text(encoding="utf-8")
    else:
        rc_content = ""
    if shell_name == "fish":
        source_line = f"test -f {env_file} ; and source {env_file}"
    else:
        source_line = f"source {env_file}"
    if source_line not in rc_content:
        rc_file.parent.mkdir(parents=True, exist_ok=True)
        if rc_content and not rc_content.endswith("\n"):
            rc_content += "\n"
        rc_content += source_line + "\n"
        rc_file.write_text(rc_content, encoding="utf-8")


# ---------------------------------------------------------------------------
# Main entry point
# ---------------------------------------------------------------------------


def _default_index(rows: List[dict]) -> int:
    """Pick the default selection: installed+cred > installed > first row."""
    for i, r in enumerate(rows):
        if r["path"] and (r["has_key"] or r["has_oauth"]):
            return i
    for i, r in enumerate(rows):
        if r["path"]:
            return i
    return 0


def _build_rows() -> List[dict]:
    """Detect each CLI and return a list of row dicts."""
    rows: List[dict] = []
    for cli in CLI_PREFERENCE:
        provider = CLI_PROVIDER[cli]
        rows.append(
            {
                "cli": cli,
                "provider": provider,
                "path": _find_cli_binary(cli),
                "has_key": _has_api_key(provider),
                "has_oauth": _has_provider_oauth(provider),
            }
        )
    return rows


def _print_selection_table(rows: List[dict]) -> None:
    """Print the numbered selection table."""
    console.print("Available agentic CLI harnesses:")
    for idx, row in enumerate(rows, start=1):
        cli = row["cli"]
        provider = row["provider"]
        label = CLI_LABEL[cli]
        prov_disp = PROVIDER_DISPLAY[provider]
        if cli == "agy":
            prov_disp += " — Antigravity (preferred)"
        elif cli == "gemini":
            prov_disp += " — Gemini (legacy rollback)"
        if row["path"]:
            install_str = f"Found at {row['path']}"
        else:
            install_str = "Not found"
        if row["has_key"]:
            cred_str = f"[green]\u2713[/green] {_credential_status_label(provider)} set"
        elif row["has_oauth"]:
            cred_str = "[green]\u2713[/green] OAuth/subscription login configured"
        else:
            cred_str = f"[red]\u2717[/red] {_credential_status_label(provider)} not set"
        console.print(
            f"{idx}. {label} ({prov_disp}) — {install_str}; {cred_str}"
        )


def _parse_selection(raw: str, n_rows: int) -> List[int]:
    """Parse a comma-separated numeric selection. Returns deduplicated indices."""
    out: List[int] = []
    for part in raw.split(","):
        part = part.strip()
        if not part:
            continue
        if not part.isdigit():
            return []
        i = int(part) - 1
        if 0 <= i < n_rows:
            if i not in out:
                out.append(i)
        else:
            return []
    return out


def _install_cli(cli: str) -> "tuple[bool, Optional[str]]":
    """Attempt to install a CLI. Returns (success, message_or_none)."""
    if cli == "agy":
        # Antigravity is installed manually — never shell out to the URL.
        console.print(
            "Antigravity CLI (`agy`) is not distributed via npm. Install hint:"
        )
        console.print(f"    {AGY_MANUAL_INSTALL_HINT}")
        try:
            ans = _prompt_input(
                "Press Enter after running the installer (or 'n' to skip): "
            ).strip().lower()
        except (KeyboardInterrupt, EOFError):
            return False, "User interrupted Antigravity install."
        if ans in ("n", "no", "q", "skip"):
            return False, "User declined Antigravity install."
        return True, None

    if not _npm_available():
        return False, "npm is not available on PATH. Install Node.js/npm first."
    cmd = CLI_INSTALL_HINT[cli]
    if not cmd:
        return False, f"No install command registered for {cli}."
    try:
        proc = subprocess.run(cmd, shell=True)
    except (OSError, subprocess.SubprocessError) as exc:
        return False, f"Install command raised: {exc}"
    if proc.returncode != 0:
        return False, f"Install failed (exit {proc.returncode}). Try manually: {cmd}"
    return True, None


def detect_and_bootstrap_cli() -> List[CliBootstrapResult]:
    """Phase 1 of ``pdd setup``.

    Detects agentic CLIs, presents a selection table, and for each chosen
    CLI walks through install / credential / test in sequence.
    """
    _print_step_banner("Detecting Agentic CLI Harnesses")

    rows = _build_rows()
    _print_selection_table(rows)
    console.print(
        "Enter comma-separated numbers (e.g. 1,3), press Enter for the default, "
        "or 'q'/'n' to skip."
    )

    try:
        raw = _prompt_input("Selection: ").strip()
    except (KeyboardInterrupt, EOFError):
        return [CliBootstrapResult(skipped=True)]

    if raw.lower() in ("q", "n", "quit", "skip"):
        return [CliBootstrapResult(skipped=True)]

    if not raw:
        default_i = _default_index(rows)
        console.print(
            f"Defaulting to {CLI_LABEL[rows[default_i]['cli']]}."
        )
        selected = [default_i]
    else:
        selected = _parse_selection(raw, len(rows))
        if not selected:
            default_i = _default_index(rows)
            console.print(
                f"Invalid input. Defaulting to {CLI_LABEL[rows[default_i]['cli']]}."
            )
            selected = [default_i]

    results: List[CliBootstrapResult] = []
    for i in selected:
        row = rows[i]
        cli = row["cli"]
        provider = row["provider"]
        path = row["path"]
        has_oauth = row["has_oauth"]
        had_key = row["has_key"]
        api_key_configured = had_key

        # --- Install step -------------------------------------------------
        if not path:
            console.print(f"{CLI_LABEL[cli]} is not installed.")
            try:
                ans = _prompt_input(
                    f"Install now? [Y/n]: "
                ).strip().lower()
            except (KeyboardInterrupt, EOFError):
                results.append(
                    CliBootstrapResult(
                        cli_name=cli, provider=provider, skipped=True
                    )
                )
                continue
            if ans in ("n", "no"):
                console.print(f"{cli} not configured — skipping.")
                results.append(
                    CliBootstrapResult(
                        cli_name=cli, provider=provider, skipped=True
                    )
                )
                continue
            ok, err = _install_cli(cli)
            if not ok:
                if err:
                    console.print(err)
                console.print(f"{cli} not configured.")
                results.append(
                    CliBootstrapResult(
                        cli_name=cli, provider=provider, skipped=True
                    )
                )
                continue
            path = _find_cli_binary(cli)
            if not path:
                console.print(
                    f"{cli} not found on PATH after install — not configured."
                )
                results.append(
                    CliBootstrapResult(
                        cli_name=cli, provider=provider, skipped=True
                    )
                )
                continue

        # --- Credential step ---------------------------------------------
        if has_oauth and not had_key:
            console.print(
                f"[green]\u2713[/green] OAuth/subscription login configured for "
                f"{CLI_LABEL[cli]} — using the stored credential."
            )
            if provider == "anthropic":
                console.print(
                    "(Set PDD_KEEP_ANTHROPIC_API_KEY=1 to force API-key billing.)"
                )
        elif had_key:
            # Key already present — no prompt needed.
            pass
        else:
            if provider == "opencode":
                console.print(
                    "[dim]OpenCode has no dedicated API key. Run "
                    "`opencode auth login`, configure "
                    "`~/.config/opencode/opencode.json` (or a project "
                    "`opencode.json`), or export an underlying provider env "
                    "var plus `OPENCODE_MODEL=provider/model`.[/dim]"
                )
                console.print(
                    "[dim]Docs: https://opencode.ai/docs/providers[/dim]"
                )
            else:
                key_name = PROVIDER_PRIMARY_KEY[provider]
                try:
                    val = _prompt_input(
                        f"Enter your {key_name} (press Enter to skip): "
                    ).strip()
                except (KeyboardInterrupt, EOFError):
                    val = ""
                if val:
                    _save_api_key(key_name, val)
                    api_key_configured = True
                else:
                    if provider == "anthropic":
                        console.print(
                            f"{key_name} not configured. Claude CLI can still "
                            "work via subscription auth (run `claude login`)."
                        )
                    else:
                        console.print(
                            f"{key_name} not configured — limited functionality."
                        )

        # --- Test step (always) ------------------------------------------
        console.print(f"Testing {CLI_LABEL[cli]} ({path})...")
        try:
            r = subprocess.run(
                [path, "--version"], capture_output=True, text=True
            )
            if r.returncode != 0:
                r = subprocess.run(
                    [path, "--help"], capture_output=True, text=True
                )
            combined = (r.stdout or "") + (r.stderr or "")
            console.print(combined.strip() or f"{cli} responded.")
        except (OSError, subprocess.SubprocessError) as exc:
            console.print(f"Error invoking {cli}: {exc}")

        results.append(
            CliBootstrapResult(
                cli_name=cli,
                provider=provider,
                cli_path=path or "",
                api_key_configured=api_key_configured,
                skipped=False,
            )
        )

    if not results:
        return [CliBootstrapResult(skipped=True)]
    return results


# ---------------------------------------------------------------------------
# Legacy detection
# ---------------------------------------------------------------------------


def detect_cli_tools() -> None:
    """Legacy detection: show install status and any matching API keys."""
    console.print("Agentic CLI Tool Detection")
    console.print(
        "These CLIs power `pdd fix`, `pdd change`, and `pdd bug`."
    )

    found: List[str] = []
    missing: List[tuple] = []
    for cli in CLI_PREFERENCE:
        path = _which(cli)
        provider = CLI_PROVIDER[cli]
        has_key = _has_api_key(provider)
        if path:
            console.print(
                f"[green]\u2713[/green] {CLI_LABEL[cli]} — Found at {path}"
            )
            found.append(cli)
        else:
            console.print(f"[red]\u2717[/red] {CLI_LABEL[cli]} — Not found")
            missing.append((cli, provider, has_key))

    for cli, provider, has_key in missing:
        if has_key:
            key_name = PROVIDER_PRIMARY_KEY.get(provider) or _credential_status_label(
                provider
            )
            install_hint = CLI_INSTALL_HINT.get(cli) or AGY_MANUAL_INSTALL_HINT
            console.print(
                f"{key_name} is set but {CLI_LABEL[cli]} is not installed. "
                f"Suggested install: {install_hint}"
            )

    if found and all(_has_api_key(CLI_PROVIDER[c]) for c in found):
        console.print(
            "All CLI tools you have installed are configured with credentials."
        )
    if not found:
        console.print(
            "No CLI tools found. Quick start: install Claude CLI via "
            "`npm install -g @anthropic-ai/claude-code`."
        )


__all__ = [
    "CliBootstrapResult",
    "detect_and_bootstrap_cli",
    "detect_cli_tools",
    "PROVIDER_PRIMARY_KEY",
    "PROVIDER_DISPLAY",
    "CLI_PREFERENCE",
    "SHELL_RC_MAP",
]
