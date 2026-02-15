from __future__ import annotations

import os
import shutil
import subprocess
import sys
from pathlib import Path


# Maps provider name -> CLI command name
_CLI_COMMANDS: dict[str, str] = {
    "anthropic": "claude",
    "google": "gemini",
    "openai": "codex",
}

# Maps provider name -> environment variable for API key
_API_KEY_ENV_VARS: dict[str, str] = {
    "anthropic": "ANTHROPIC_API_KEY",
    "google": "GOOGLE_API_KEY",
    "openai": "OPENAI_API_KEY",
}

# Maps provider name -> npm install command for the CLI
_INSTALL_COMMANDS: dict[str, str] = {
    "anthropic": "npm install -g @anthropic-ai/claude-code",
    "google": "npm install -g @anthropic-ai/gemini-cli",
    "openai": "npm install -g @openai/codex",
}

# Maps provider name -> human-readable CLI name
_CLI_DISPLAY_NAMES: dict[str, str] = {
    "anthropic": "Claude CLI",
    "google": "Gemini CLI",
    "openai": "Codex CLI",
}


def _which(cmd: str) -> str | None:
    """Return the full path to a command if found on PATH, else None."""
    return shutil.which(cmd)


def _has_api_key(provider: str) -> bool:
    """Check whether the API key environment variable is set for a provider."""
    env_var = _API_KEY_ENV_VARS.get(provider, "")
    return bool(os.environ.get(env_var, "").strip())


def _npm_available() -> bool:
    """Check whether npm is available on PATH."""
    return _which("npm") is not None


def _prompt_yes_no(prompt: str) -> bool:
    """Prompt the user with a yes/no question. Default is No."""
    try:
        answer = input(prompt).strip().lower()
    except (EOFError, KeyboardInterrupt):
        print()
        return False
    return answer in ("y", "yes")


def _run_install(install_cmd: str) -> bool:
    """Run an installation command via subprocess. Returns True on success."""
    print(f"  Running: {install_cmd}")
    try:
        result = subprocess.run(
            install_cmd,
            shell=True,
            check=False,
            capture_output=False,
        )
        return result.returncode == 0
    except Exception as exc:
        print(f"  Installation failed: {exc}")
        return False


def detect_cli_tools() -> None:
    """
    Detect installed agentic CLI harnesses (Claude CLI, Codex CLI, Gemini CLI)
    required for ``pdd fix``, ``pdd change``, and ``pdd bug``.

    For each CLI tool:
    - Shows ✓ Found at /path or ✗ Not found
    - Cross-references with API keys to highlight actionable installations
    - Offers interactive installation for missing CLIs that have a matching API key

    Handles the case where npm is not installed by suggesting manual installation.
    """
    # Try to import get_available_agents for cross-reference, but don't fail if
    # the import is unavailable (we can still do basic detection).
    available_agents: list[str] = []
    try:
        from pdd.agentic_common import get_available_agents as _get_available_agents
        available_agents = list(_get_available_agents())
    except Exception:
        pass

    print()
    print("Agentic CLI Tool Detection")
    print("=" * 50)
    print("(Required for: pdd fix, pdd change, pdd bug)")
    print()

    missing_with_key: list[str] = []
    found_any = False

    for provider, cli_cmd in _CLI_COMMANDS.items():
        display_name = _CLI_DISPLAY_NAMES[provider]
        path = _which(cli_cmd)
        has_key = _has_api_key(provider)
        key_env = _API_KEY_ENV_VARS[provider]

        if path:
            print(f"  ✓ {display_name} ({cli_cmd}): Found at {path}")
            found_any = True
            if has_key:
                print(f"    API key ({key_env}): set")
            else:
                print(f"    API key ({key_env}): not set — CLI found but won't be usable without it")
        else:
            print(f"  ✗ {display_name} ({cli_cmd}): Not found")
            if has_key:
                print(f"    API key ({key_env}): set — install the CLI to use this provider")
                missing_with_key.append(provider)
            else:
                print(f"    API key ({key_env}): not set")

    print()

    if not missing_with_key:
        if found_any:
            print("All CLI tools with matching API keys are installed.")
        else:
            print("No CLI tools found. Install at least one CLI and set its API key")
            print("to use agentic features (pdd fix, pdd change, pdd bug).")
            print()
            print("Quick start:")
            for provider, install_cmd in _INSTALL_COMMANDS.items():
                display_name = _CLI_DISPLAY_NAMES[provider]
                key_env = _API_KEY_ENV_VARS[provider]
                print(f"  {display_name}: {install_cmd}")
                print(f"    Then set: export {key_env}=<your-key>")
        print()
        return

    # Offer installation for missing CLIs that have a matching API key
    print("The following CLI tools are missing but have API keys configured:")
    print()

    npm_available = _npm_available()

    for provider in missing_with_key:
        display_name = _CLI_DISPLAY_NAMES[provider]
        install_cmd = _INSTALL_COMMANDS[provider]

        print(f"  {display_name}:")
        print(f"    Install command: {install_cmd}")

        if not npm_available:
            print("    ☀  npm is not installed. Please install Node.js/npm first:")
            print("       macOS:  brew install node")
            print("       Ubuntu: sudo apt-get update && sudo apt-get install -y nodejs npm")
            print("       Then run the install command above manually.")
            print()
            continue

        if _prompt_yes_no(f"    Install now? [y/N] "):
            success = _run_install(install_cmd)
            if success:
                new_path = _which(_CLI_COMMANDS[provider])
                if new_path:
                    print(f"    ✓ {display_name} installed successfully at {new_path}")
                else:
                    print(f"    ✓ Installation command completed. You may need to restart your shell.")
            else:
                print(f"    ✗ Installation failed. Try running manually:")
                print(f"       {install_cmd}")
        else:
            print("    Skipped. To install later, run:")
            print(f"       {install_cmd}")

        print()

    print()

if __name__ == "__main__":
    detect_cli_tools()