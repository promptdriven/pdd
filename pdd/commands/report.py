"""
Report commands (report-core).
"""
import os
import click
import json
import webbrowser
import urllib.parse
from pathlib import Path
from typing import Optional

from ..core.errors import handle_error, console
from ..core.dump import _build_issue_markdown, _github_config, _post_issue_to_github, _create_gist_with_files

@click.command("report-core")
@click.argument("core_file", type=click.Path(exists=True, dir_okay=False), required=False)
@click.option(
    "--api",
    is_flag=True,
    default=False,
    help="Create issue directly via GitHub API instead of opening browser. Requires authentication."
)
@click.option(
    "--repo",
    default=None,
    help="GitHub repository in format 'owner/repo'. Defaults to 'promptdriven/pdd' or PDD_GITHUB_REPO env var."
)
@click.option(
    "--description",
    "-d",
    default="",
    help="Optional description of what happened to include in the issue."
)
@click.pass_context
def report_core(ctx: click.Context, core_file: Optional[str], api: bool, repo: Optional[str], description: str):
    """Report a bug by creating a GitHub issue with the core dump file.

    If CORE_FILE is not provided, the most recent core dump in .pdd/core_dumps is used.

    By default, opens a browser with a pre-filled issue template. Use --api to create
    the issue directly via GitHub API (requires authentication via gh CLI or GITHUB_TOKEN).
    """
    try:
        if not core_file:
            # Find latest core dump
            core_dump_dir = Path.cwd() / ".pdd" / "core_dumps"
            if not core_dump_dir.exists():
                raise click.UsageError("No core dumps found in .pdd/core_dumps.")

            dumps = sorted(core_dump_dir.glob("pdd-core-*.json"), key=lambda p: p.stat().st_mtime, reverse=True)
            if not dumps:
                raise click.UsageError("No core dumps found in .pdd/core_dumps.")
            core_file = str(dumps[0])
            console.print(f"[info]Using most recent core dump: {core_file}[/info]")

        core_path = Path(core_file)
        try:
            payload = json.loads(core_path.read_text(encoding="utf-8"))
        except Exception as e:
            raise click.UsageError(f"Failed to parse core dump: {e}")

        # Determine repository
        target_repo = repo or os.getenv("PDD_GITHUB_REPO", "promptdriven/pdd")

        # For API submission, create a gist with all files
        gist_url = None
        if api:
            console.print("[info]Attempting to create issue via GitHub API...[/info]")

            github_config = _github_config(target_repo)
            if not github_config:
                console.print(
                    "[error]No GitHub authentication found. Please either:[/error]\n"
                    "  1. Install and authenticate with GitHub CLI: gh auth login\n"
                    "  2. Set GITHUB_TOKEN or GH_TOKEN environment variable\n"
                    "  3. Set PDD_GITHUB_TOKEN environment variable\n"
                    "\n"
                    "[info]Falling back to browser-based submission...[/info]"
                )
                api = False
            else:
                token, resolved_repo = github_config

                # Create gist with all files
                console.print(f"[info]Creating Gist with all files...[/info]")
                gist_url = _create_gist_with_files(token, payload, core_path)

                if gist_url:
                    console.print(f"[success]Gist created: {gist_url}[/success]")
                else:
                    console.print("[warning]Failed to create Gist, including files in issue body...[/warning]")

                # Build issue with gist link
                title, body = _build_issue_markdown(
                    payload=payload,
                    description=description,
                    core_path=core_path,
                    replay_path=None,
                    attachments=[],
                    truncate_files=False,
                    gist_url=gist_url
                )

                console.print(f"[info]Creating issue in {resolved_repo}...[/info]")
                issue_url = _post_issue_to_github(token, resolved_repo, title, body)
                if issue_url:
                    console.print(f"[success]Issue created successfully: {issue_url}[/success]")
                    return
                else:
                    console.print(
                        "[warning]Failed to create issue via API. Falling back to browser...[/warning]"
                    )
                    api = False

        # Build issue content for browser mode (if not already built for API)
        if not api:
            # For browser-based submission, we'll truncate files to avoid URL length limits
            title, body = _build_issue_markdown(
                payload=payload,
                description=description,
                core_path=core_path,
                replay_path=None,
                attachments=[],
                truncate_files=True  # Truncate for browser
            )

        # Browser-based submission (default or fallback)
        if not api:
            # URL encode
            encoded_title = urllib.parse.quote(title)
            encoded_body = urllib.parse.quote(body)

            url = f"https://github.com/{target_repo}/issues/new?title={encoded_title}&body={encoded_body}"

            console.print(f"[info]Opening GitHub issue creation page for {target_repo}...[/info]")
            console.print("[info]Note: File contents are truncated for browser submission. Use --api for full contents.[/info]")

            if len(url) > 8000:
                console.print("[warning]The issue body is large. Browser might truncate it.[/warning]")

            webbrowser.open(url)

    except Exception as e:
        handle_error(e, "report-core", ctx.obj.get("quiet", False))
