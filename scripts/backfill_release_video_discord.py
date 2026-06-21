#!/usr/bin/env python3
"""Backfill a Discord follow-up for a recovered PDD release video."""

from __future__ import annotations

import argparse
import hashlib
import json
import os
import re
import subprocess
import sys
import urllib.error
import urllib.request
from collections.abc import Callable
from typing import Any


SEMVER_TAG_RE = re.compile(r"^v\d+\.\d+\.\d+$")
YOUTUBE_URL_RE = re.compile(r"^https?://(?:www\.)?(?:youtube\.com|youtu\.be)/[^\s\"'<>]+$")
GITHUB_REPO_RE = re.compile(r"^[A-Za-z0-9_.-]+/[A-Za-z0-9_.-]+$")
MARKER_NAME = "pdd-release-video-discord-backfill"


class BackfillError(RuntimeError):
    """Raised for actionable release-video Discord backfill failures."""


class BackfillResult:
    def __init__(
        self,
        *,
        posted: bool,
        release_body_updated: bool,
        marker_added: bool,
        skipped_reason: str | None = None,
    ) -> None:
        self.posted = posted
        self.release_body_updated = release_body_updated
        self.marker_added = marker_added
        self.skipped_reason = skipped_reason


class GitHubReleaseClient:
    """Tiny wrapper around gh release commands for testable release-note edits."""

    def __init__(
        self,
        *,
        gh_cli: str = "gh",
        repo: str,
        run: Callable[..., subprocess.CompletedProcess[str]] = subprocess.run,
    ) -> None:
        self.gh_cli = gh_cli
        self.repo = repo
        self.run = run

    def get_release_body(self, tag: str) -> str:
        completed = self._run(
            [
                self.gh_cli,
                "release",
                "view",
                tag,
                "--repo",
                self.repo,
                "--json",
                "body",
                "--jq",
                ".body",
            ]
        )
        return completed.stdout

    def edit_release_body(self, tag: str, body: str) -> None:
        self._run(
            [
                self.gh_cli,
                "release",
                "edit",
                tag,
                "--repo",
                self.repo,
                "--notes-file",
                "-",
            ],
            input=body,
        )

    def _run(
        self,
        command: list[str],
        *,
        input: str | None = None,
    ) -> subprocess.CompletedProcess[str]:
        try:
            completed = self.run(
                command,
                input=input,
                text=True,
                capture_output=True,
                check=False,
            )
        except FileNotFoundError as exc:
            raise BackfillError(f"Could not run {self.gh_cli!r}: {exc}") from exc
        if completed.returncode != 0:
            detail = (completed.stderr or completed.stdout or "").strip()
            if detail:
                raise BackfillError(f"gh command failed: {' '.join(command)}\n{detail}")
            raise BackfillError(f"gh command failed: {' '.join(command)}")
        return completed


def discord_backfill_marker(tag: str, youtube_url: str) -> str:
    digest = hashlib.sha256(f"{tag}\n{youtube_url}".encode("utf8")).hexdigest()
    return f"<!-- {MARKER_NAME}: tag={tag} url_sha256={digest} -->"


def ensure_release_body_has_video_link(body: str, youtube_url: str) -> tuple[str, bool]:
    if youtube_url in body:
        return body, False
    prefix = f"Release video: {youtube_url}"
    if body.strip():
        return f"{prefix}\n\n{body}", True
    return f"{prefix}\n", True


def ensure_release_body_has_marker(body: str, tag: str, youtube_url: str) -> tuple[str, bool]:
    marker = discord_backfill_marker(tag, youtube_url)
    if marker in body:
        return body, False
    if body.strip():
        return f"{body.rstrip()}\n\n{marker}\n", True
    return f"{marker}\n", True


def build_discord_payload(tag: str, youtube_url: str, repo: str) -> dict[str, str]:
    release_url = f"https://github.com/{repo}/releases/tag/{tag}"
    return {
        "content": f"Release video recovered for {tag}: {youtube_url}\nRelease: {release_url}"
    }


def send_discord_webhook(
    webhook_url: str,
    payload: dict[str, Any],
    *,
    timeout: float = 20,
) -> None:
    data = json.dumps(payload).encode("utf8")
    request = urllib.request.Request(
        webhook_url,
        data=data,
        headers={"Content-Type": "application/json"},
        method="POST",
    )
    try:
        with urllib.request.urlopen(request, timeout=timeout) as response:
            status = getattr(response, "status", response.getcode())
            if status >= 400:
                raise BackfillError(f"Discord webhook returned HTTP {status}")
    except urllib.error.HTTPError as exc:
        raise BackfillError(f"Discord webhook returned HTTP {exc.code}: {exc.reason}") from exc
    except urllib.error.URLError as exc:
        raise BackfillError(f"Discord webhook request failed: {exc.reason}") from exc


def validate_inputs(tag: str, youtube_url: str, repo: str) -> None:
    if not SEMVER_TAG_RE.fullmatch(tag):
        raise BackfillError(f"Release tag must look like vX.Y.Z, got {tag!r}.")
    if not YOUTUBE_URL_RE.fullmatch(youtube_url):
        raise BackfillError(f"YouTube URL does not look valid: {youtube_url!r}.")
    if not GITHUB_REPO_RE.fullmatch(repo):
        raise BackfillError(f"GitHub repo must look like owner/name, got {repo!r}.")


def backfill_release_video_discord(
    *,
    tag: str,
    youtube_url: str,
    repo: str,
    webhook_url: str | None,
    github: GitHubReleaseClient,
    post_discord: Callable[[str, dict[str, Any]], None] = send_discord_webhook,
) -> BackfillResult:
    validate_inputs(tag, youtube_url, repo)

    body = github.get_release_body(tag)
    marker = discord_backfill_marker(tag, youtube_url)
    body_with_link, link_added = ensure_release_body_has_video_link(body, youtube_url)

    if marker in body:
        if link_added:
            github.edit_release_body(tag, body_with_link)
        return BackfillResult(
            posted=False,
            release_body_updated=link_added,
            marker_added=False,
            skipped_reason="discord-followup-already-marked",
        )

    if not webhook_url:
        raise BackfillError("DISCORD_WEBHOOK_URL is required when a follow-up has not been marked.")

    if link_added:
        github.edit_release_body(tag, body_with_link)

    post_discord(webhook_url, build_discord_payload(tag, youtube_url, repo))

    marked_body, marker_added = ensure_release_body_has_marker(body_with_link, tag, youtube_url)
    if marker_added:
        github.edit_release_body(tag, marked_body)

    return BackfillResult(
        posted=True,
        release_body_updated=link_added or marker_added,
        marker_added=marker_added,
    )


def parse_args(argv: list[str] | None = None) -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        description=(
            "Post an idempotent Discord follow-up after a release video is "
            "recovered outside the normal release workflow."
        )
    )
    parser.add_argument("--tag", required=True, help="Release tag, for example v0.0.283.")
    parser.add_argument("--youtube-url", required=True, help="Recovered YouTube release-video URL.")
    parser.add_argument(
        "--repo",
        default=os.environ.get("GITHUB_REPOSITORY", "promptdriven/pdd"),
        help="GitHub repository in owner/name form. Defaults to GITHUB_REPOSITORY.",
    )
    parser.add_argument(
        "--webhook-url",
        default=os.environ.get("DISCORD_WEBHOOK_URL", ""),
        help="Discord webhook URL. Defaults to DISCORD_WEBHOOK_URL.",
    )
    parser.add_argument(
        "--gh-cli",
        default=os.environ.get("GH_CLI", "gh"),
        help="gh executable path. Defaults to gh.",
    )
    return parser.parse_args(argv)


def main(argv: list[str] | None = None) -> int:
    args = parse_args(argv)
    github = GitHubReleaseClient(gh_cli=args.gh_cli, repo=args.repo)
    try:
        result = backfill_release_video_discord(
            tag=args.tag,
            youtube_url=args.youtube_url,
            repo=args.repo,
            webhook_url=args.webhook_url,
            github=github,
        )
    except BackfillError as exc:
        print(f"release-video-discord-backfill: {exc}", file=sys.stderr)
        return 1

    if result.posted:
        print(f"Posted Discord release-video follow-up for {args.tag}.")
    elif result.skipped_reason == "discord-followup-already-marked":
        print(f"Skipped Discord follow-up for {args.tag}; matching marker already exists.")
    if result.release_body_updated:
        print(f"Updated GitHub release body for {args.tag}.")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
