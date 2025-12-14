"""
Core dump generation and replay logic.
"""
import os
import sys
import json
import platform
import datetime
import shlex
import subprocess
from pathlib import Path
from typing import Any, Dict, List, Optional, Tuple
import click
import requests

from .. import __version__
from .errors import console, get_core_dump_errors

def _write_core_dump(
    ctx: click.Context,
    normalized_results: List[Any],
    invoked_subcommands: List[str],
    total_cost: float,
    terminal_output: Optional[str] = None,
) -> None:
    """Write a JSON core dump for this run if --core-dump is enabled."""
    if not ctx.obj.get("core_dump"):
        return

    try:
        core_dump_dir = Path.cwd() / ".pdd" / "core_dumps"
        core_dump_dir.mkdir(parents=True, exist_ok=True)

        timestamp = datetime.datetime.now(datetime.UTC).strftime("%Y%m%dT%H%M%SZ")
        dump_path = core_dump_dir / f"pdd-core-{timestamp}.json"

        steps: List[Dict[str, Any]] = []
        for i, result_tuple in enumerate(normalized_results):
            command_name = (
                invoked_subcommands[i] if i < len(invoked_subcommands) else f"Unknown Command {i+1}"
            )

            cost = None
            model_name = None
            if isinstance(result_tuple, tuple) and len(result_tuple) == 3:
                _result_data, cost, model_name = result_tuple

            steps.append(
                {
                    "step": i + 1,
                    "command": command_name,
                    "cost": cost,
                    "model": model_name,
                }
            )

        # Only capture a limited subset of env vars to avoid leaking API keys
        sensitive_markers = ("KEY", "TOKEN", "SECRET", "PASSWORD")

        interesting_env = {}
        for k, v in os.environ.items():
            if k.startswith("PDD_") or k in ("VIRTUAL_ENV", "PYTHONPATH", "PATH"):
                # Redact obviously sensitive vars
                if any(m in k.upper() for m in sensitive_markers):
                    interesting_env[k] = "<redacted>"
                else:
                    interesting_env[k] = v

        # Collect file contents from tracked files
        file_contents = {}
        core_dump_files = ctx.obj.get("core_dump_files", set())

        if not ctx.obj.get("quiet"):
            console.print(f"[info]Core dump: Found {len(core_dump_files)} tracked files[/info]")

        # Auto-include relevant meta files for the invoked commands
        meta_dir = Path.cwd() / ".pdd" / "meta"
        if meta_dir.exists():
            for cmd in invoked_subcommands:
                # Look for meta files related to this command
                for meta_file in meta_dir.glob(f"*_{cmd}.json"):
                    core_dump_files.add(str(meta_file.resolve()))
                # Also include general meta files (without command suffix)
                for meta_file in meta_dir.glob("*.json"):
                    if meta_file.stem.endswith(f"_{cmd}") or not any(
                        meta_file.stem.endswith(f"_{c}") for c in ["generate", "test", "run", "fix", "update"]
                    ):
                        core_dump_files.add(str(meta_file.resolve()))

        # Auto-include PDD config files if they exist
        config_files = [
            Path.cwd() / ".pdd" / "config.json",
            Path.cwd() / ".pddconfig",
            Path.cwd() / "pdd.json",
        ]
        for config_file in config_files:
            if config_file.exists() and config_file.is_file():
                core_dump_files.add(str(config_file.resolve()))

        for file_path in core_dump_files:
            try:
                path = Path(file_path)
                if not ctx.obj.get("quiet"):
                    console.print(f"[info]Core dump: Checking file {file_path}[/info]")

                if path.exists() and path.is_file():
                    if path.stat().st_size < 50000:  # 50KB limit
                        try:
                            # Use relative path if possible for cleaner keys
                            try:
                                key = str(path.relative_to(Path.cwd()))
                            except ValueError:
                                key = str(path)

                            file_contents[key] = path.read_text(encoding='utf-8')
                            if not ctx.obj.get("quiet"):
                                console.print(f"[info]Core dump: Added content for {key}[/info]")
                        except UnicodeDecodeError:
                            file_contents[str(path)] = "<binary>"
                            if not ctx.obj.get("quiet"):
                                console.print(f"[warning]Core dump: Binary file {path}[/warning]")
                    else:
                        file_contents[str(path)] = "<too large>"
                        if not ctx.obj.get("quiet"):
                            console.print(f"[warning]Core dump: File too large {path}[/warning]")
                else:
                    if not ctx.obj.get("quiet"):
                        console.print(f"[warning]Core dump: File not found or not a file: {file_path}[/warning]")
            except Exception as e:
                file_contents[str(file_path)] = f"<error reading file: {e}>"
                if not ctx.obj.get("quiet"):
                    console.print(f"[warning]Core dump: Error reading {file_path}: {e}[/warning]")

        payload: Dict[str, Any] = {
            "schema_version": 1,
            "pdd_version": __version__,
            "timestamp_utc": timestamp,
            "argv": sys.argv[1:],  # without the 'pdd' binary name
            "cwd": str(Path.cwd()),
            "platform": {
                "system": platform.system(),
                "release": platform.release(),
                "version": platform.version(),
                "python": sys.version,
            },
            "global_options": {
                "force": ctx.obj.get("force"),
                "strength": ctx.obj.get("strength"),
                "temperature": ctx.obj.get("temperature"),
                "time": ctx.obj.get("time"),
                "verbose": ctx.obj.get("verbose"),
                "quiet": ctx.obj.get("quiet"),
                "local": ctx.obj.get("local"),
                "context": ctx.obj.get("context"),
                "output_cost": ctx.obj.get("output_cost"),
                "review_examples": ctx.obj.get("review_examples"),
            },
            "invoked_subcommands": invoked_subcommands,
            "total_cost": total_cost,
            "steps": steps,
            "errors": get_core_dump_errors(),
            "environment": interesting_env,
            "file_contents": file_contents,
            "terminal_output": terminal_output,
        }

        dump_path.write_text(json.dumps(payload, indent=2), encoding="utf-8")

        if not ctx.obj.get("quiet"):
            console.print(
                f"[info]Core dump written to [path]{dump_path}[/path]. "
                "You can attach this file when reporting a bug.[/info]"
            )
    except Exception as exc:
        # Never let core dumping itself crash the CLI
        if not ctx.obj.get("quiet"):
            console.print(f"[warning]Failed to write core dump: {exc}[/warning]", style="warning")


def _get_github_token() -> Optional[str]:
    """
    Get GitHub token using standard authentication methods.

    Tries in order:
    1. GitHub CLI (gh) if available
    2. GITHUB_TOKEN environment variable (standard in GitHub Actions)
    3. GH_TOKEN environment variable (alternative standard)
    4. PDD_GITHUB_TOKEN (backwards compatibility)

    Returns None if no token found.
    """
    # Try GitHub CLI first
    try:
        result = subprocess.run(
            ["gh", "auth", "token"],
            capture_output=True,
            text=True,
            timeout=5,
            check=False
        )
        if result.returncode == 0 and result.stdout.strip():
            token = result.stdout.strip()
            if token:
                return token
    except (subprocess.TimeoutExpired, FileNotFoundError):
        pass

    # Try standard environment variables
    token = os.getenv("GITHUB_TOKEN") or os.getenv("GH_TOKEN") or os.getenv("PDD_GITHUB_TOKEN")
    if token:
        return token

    return None


def _github_config(repo: Optional[str] = None) -> Optional[Tuple[str, str]]:
    """
    Return (token, repo) if GitHub issue posting is configured, otherwise None.

    Args:
        repo: Optional repository in format "owner/repo". If not provided,
              will try PDD_GITHUB_REPO env var or default to "promptdriven/pdd"
    """
    token = _get_github_token()
    if not token:
        return None

    if not repo:
        repo = os.getenv("PDD_GITHUB_REPO", "promptdriven/pdd")

    return token, repo


def _create_gist_with_files(token: str, payload: Dict[str, Any], core_path: Path) -> Optional[str]:
    """
    Create a GitHub Gist with core dump and all tracked files.

    Returns the Gist URL on success, None on failure.
    """
    try:
        # Prepare files for gist
        gist_files = {}

        # Add the core dump JSON
        gist_files["core-dump.json"] = {
            "content": json.dumps(payload, indent=2)
        }

        # Add all tracked files
        file_contents = payload.get("file_contents", {})
        for filename, content in file_contents.items():
            # GitHub gist filenames can't have slashes, replace with underscores
            safe_filename = filename.replace("/", "_").replace("\\", "_")
            gist_files[safe_filename] = {
                "content": content if not content.startswith("<") else f"# {content}"
            }

        # Add terminal output as a separate file if available
        terminal_output = payload.get("terminal_output")
        if terminal_output:
            gist_files["terminal_output.txt"] = {
                "content": terminal_output
            }

        # Create the gist
        url = "https://api.github.com/gists"
        headers = {
            "Authorization": f"Bearer {token}",
            "Accept": "application/vnd.github+json",
        }

        gist_data = {
            "description": f"PDD Core Dump - {core_path.name}",
            "public": False,  # Private gist
            "files": gist_files
        }

        resp = requests.post(url, headers=headers, json=gist_data, timeout=30)
        if 200 <= resp.status_code < 300:
            data = resp.json()
            return data.get("html_url")
    except Exception as e:
        console.print(f"[warning]Failed to create gist: {e}[/warning]", style="warning")
        return None
    return None


def _post_issue_to_github(token: str, repo: str, title: str, body: str) -> Optional[str]:
    """Post an issue to GitHub, returning the issue URL on success, otherwise None."""
    try:
        url = f"https://api.github.com/repos/{repo}/issues"
        headers = {
            "Authorization": f"Bearer {token}",
            "Accept": "application/vnd.github+json",
        }
        resp = requests.post(url, headers=headers, json={"title": title, "body": body}, timeout=10)
        if 200 <= resp.status_code < 300:
            data = resp.json()
            return data.get("html_url")
    except Exception:
        return None
    return None


def _write_replay_script(core_path: Path, payload: Dict[str, Any]) -> Optional[Path]:
    """Create a small shell script to replay the original core-dumped command."""
    cwd = payload.get("cwd")
    argv = payload.get("argv", [])
    env = payload.get("environment", {})

    if not cwd or not argv:
        return None

    script_path = core_path.with_suffix(".replay.sh")

    lines: List[str] = []
    lines.append("#!/usr/bin/env bash")
    lines.append("set -euo pipefail")
    lines.append("")
    lines.append(f"cd {shlex.quote(str(cwd))}")
    lines.append("")

    for key, value in env.items():
        lines.append(f"export {key}={shlex.quote(str(value))}")

    lines.append("")
    arg_str = " ".join(shlex.quote(str(a)) for a in argv)
    lines.append(f"pdd {arg_str}")
    lines.append("")

    script_path.write_text("\n".join(lines), encoding="utf-8")
    try:
        mode = script_path.stat().st_mode
        script_path.chmod(mode | 0o111)
    except OSError:
        pass

    return script_path

def _build_issue_markdown(
    payload: Dict[str, Any],
    description: str,
    core_path: Path,
    replay_path: Optional[Path],
    attachments: List[str],
    truncate_files: bool = False,
    gist_url: Optional[str] = None,
) -> Tuple[str, str]:
    """
    Build a GitHub issue title and markdown body from a core dump payload.

    Args:
        truncate_files: If True, truncate file contents aggressively for URL length limits.
                       Use True for browser-based submission, False for API submission.
        gist_url: If provided, link to a GitHub Gist containing all files instead of
                 including them in the body.
    """
    platform_info = payload.get("platform", {})
    system = platform_info.get("system", "unknown")
    release = platform_info.get("release", "")
    invoked = payload.get("invoked_subcommands") or []
    cmd_summary = " ".join(invoked) if invoked else "command"

    title = f"[core-dump] {cmd_summary} failed on {system}"

    argv = payload.get("argv", [])
    argv_str = " ".join(str(a) for a in argv)
    cwd = payload.get("cwd", "")
    total_cost = payload.get("total_cost", None)
    errors = payload.get("errors") or []
    pyver = platform_info.get("python")
    pdd_ver = payload.get("pdd_version")

    lines: List[str] = []

    lines.append(f"Core dump file: `{core_path}`")
    lines.append("")
    lines.append("## What happened")
    lines.append("")
    desc = (description or "").strip()
    if desc:
        lines.append(desc)
    else:
        lines.append("_(no additional description provided by user)_")
    lines.append("")
    lines.append("## Environment")
    lines.append("")
    if cwd:
        lines.append(f"- Working directory: `{cwd}`")
    if argv_str:
        lines.append(f"- CLI arguments: `{argv_str}`")
    if system or release:
        lines.append(f"- Platform: `{system} {release}`".strip())
    if pyver:
        lines.append(f"- Python: `{pyver}`")
    if pdd_ver:
        lines.append(f"- PDD version: `{pdd_ver}`")
    if total_cost is not None:
        try:
            lines.append(f"- Total estimated cost: `${float(total_cost):.6f}`")
        except (TypeError, ValueError):
            lines.append(f"- Total estimated cost: `{total_cost}`")
    lines.append("")
    lines.append("## Reproduction")
    lines.append("")

    # No more replay script mention – just show how to rerun the original command
    if cwd or argv:
        lines.append("To reproduce this issue in a similar environment, run:")
        lines.append("")
        lines.append("```bash")
        if cwd:
            lines.append(f"cd {shlex.quote(str(cwd))}")
        if argv:
            cmd_line = "pdd " + " ".join(shlex.quote(str(a)) for a in argv)
            lines.append(cmd_line)
        lines.append("```")
    else:
        lines.append(
            "Re-run the original PDD command in the same repository with `--core-dump` enabled."
        )
    lines.append("")

    if errors:
        lines.append("## Errors")
        lines.append("")
        for err in errors:
            cmd = err.get("command", "unknown")
            etype = err.get("type", "Error")
            lines.append(f"### {cmd} ({etype})")
            lines.append("")
            tb = err.get("traceback") or err.get("message") or ""
            lines.append("```text")
            lines.append(tb)
            lines.append("```")
            lines.append("")

    # Add terminal output section if available
    terminal_output = payload.get("terminal_output")
    if terminal_output:
        lines.append("## Terminal Output")
        lines.append("")
        if gist_url:
            # Link to gist for full output
            lines.append(f"**Full terminal output is available in the Gist:** [{gist_url}]({gist_url})")
            lines.append("")
            lines.append("(See `terminal_output.txt` in the gist)")
            lines.append("")
        elif truncate_files:
            # Truncate for browser mode
            MAX_OUTPUT_CHARS = 500
            lines.append("```text")
            if len(terminal_output) > MAX_OUTPUT_CHARS:
                lines.append(terminal_output[:MAX_OUTPUT_CHARS])
                lines.append(f"\n... (truncated, {len(terminal_output)} total chars)")
            else:
                lines.append(terminal_output)
            lines.append("```")
            lines.append("")
        else:
            # Include full output for API mode
            lines.append("```text")
            lines.append(terminal_output)
            lines.append("```")
            lines.append("")

    if attachments:
        lines.append("## Attachments (local paths)")
        lines.append("")
        for p in attachments:
            lines.append(f"- `{p}`")
        lines.append("")

    file_contents = payload.get("file_contents", {})
    if file_contents:
        lines.append("## File Contents")
        lines.append("")

        if gist_url:
            # Link to gist instead of embedding files
            lines.append(f"**All files are attached in this Gist:** [{gist_url}]({gist_url})")
            lines.append("")
            lines.append("Files included:")
            for filename in file_contents.keys():
                lines.append(f"- `{filename}`")
            lines.append("")
        elif truncate_files:
            # For browser-based submission, truncate to avoid URL length limits
            MAX_FILE_CHARS = 300  # Limit per file
            for filename, content in file_contents.items():
                lines.append(f"### {filename}")
                lines.append("```")
                if len(content) > MAX_FILE_CHARS:
                    lines.append(content[:MAX_FILE_CHARS])
                    lines.append(f"\n... (truncated, {len(content)} total chars)")
                else:
                    lines.append(content)
                lines.append("```")
                lines.append("")
        else:
            # For API-based submission without gist, include full contents
            for filename, content in file_contents.items():
                lines.append(f"### {filename}")
                lines.append("```")
                lines.append(content)
                lines.append("```")
                lines.append("")

    # --- Raw core dump JSON at the bottom ---
    if gist_url:
        # If we have a gist, no need for raw JSON (it's in the gist)
        pass
    elif truncate_files:
        # For browser-based submission, skip or heavily truncate raw JSON to save URL space
        lines.append("## Raw core dump (JSON)")
        lines.append("")
        lines.append("_Core dump JSON omitted to reduce URL length. Full dump available in the attached core file._")
        lines.append("")
    else:
        # For API-based submission, include more of the JSON
        try:
            raw_json = json.dumps(payload, indent=2, sort_keys=True)
        except TypeError:
            # Fallback: make values JSON-safe by stringifying non-serializable objects
            def _safe(obj: Any) -> Any:
                try:
                    json.dumps(obj)
                    return obj
                except TypeError:
                    return str(obj)

            safe_payload = {k: _safe(v) for k, v in payload.items()}
            raw_json = json.dumps(safe_payload, indent=2, sort_keys=True)

        MAX_JSON_CHARS = 8000  # guard so huge dumps don't blow up the issue body
        if len(raw_json) > MAX_JSON_CHARS:
            raw_display = raw_json[:MAX_JSON_CHARS] + (
                "\n... (truncated; see core file on disk for full dump)\n"
            )
        else:
            raw_display = raw_json

        lines.append("## Raw core dump (JSON)")
        lines.append("")
        lines.append("```json")
        lines.append(raw_display)
        lines.append("```")
        lines.append("")
    # ----------------------------------------

    lines.append("<!-- Generated by `pdd report-core` -->")

    body = "\n".join(lines)
    return title, body
