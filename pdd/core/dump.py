"""
Core dump generation and replay logic.
"""
import os
import sys
import json
import platform
import datetime
import shlex
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
) -> None:
    """Write a JSON core dump for this run if --core-dump is enabled."""
    if not ctx.obj.get("core_dump"):
        return

    try:
        core_dump_dir = Path.cwd() / ".pdd" / "core_dumps"
        core_dump_dir.mkdir(parents=True, exist_ok=True)

        timestamp = datetime.datetime.utcnow().strftime("%Y%m%dT%H%M%SZ")
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


def _github_config() -> Optional[Tuple[str, str]]:
    """Return (token, repo) if GitHub issue posting is configured, otherwise None."""
    token = os.getenv("PDD_GITHUB_TOKEN")
    repo = os.getenv("PDD_GITHUB_REPO")
    if not token or not repo:
        return None
    return token, repo


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
) -> Tuple[str, str]:
    """Build a GitHub issue title and markdown body from a core dump payload."""
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
    if attachments:
        lines.append("## Attachments (local paths)")
        lines.append("")
        for p in attachments:
            lines.append(f"- `{p}`")
        lines.append("")

    # --- Raw core dump JSON at the bottom ---
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
