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
import time
import urllib.error
import urllib.parse
import urllib.request
from collections.abc import Callable
from typing import Any


SEMVER_TAG_RE = re.compile(r"^v\d+\.\d+\.\d+$")
YOUTUBE_URL_RE = re.compile(r"^https?://(?:www\.)?(?:youtube\.com|youtu\.be)/[^\s\"'<>]+$")
YOUTUBE_URL_IN_TEXT_RE = re.compile(r"https?://(?:www\.)?(?:youtube\.com|youtu\.be)/[^\s\"'<>]+")
YOUTUBE_VIDEO_ID_RE = re.compile(r"^[A-Za-z0-9_-]{6,}$")
GITHUB_REPO_RE = re.compile(r"^[A-Za-z0-9_.-]+/[A-Za-z0-9_.-]+$")
DISCORD_HTTP_ERROR_RE = re.compile(r"^Discord webhook returned HTTP (\d{3})")
DISCORD_WEBHOOK_URL_RE = re.compile(
    r"https://(?:canary\.|ptb\.)?discord(?:app)?\.com/api/webhooks/[^\s\"'<>]+"
)
DISCORD_EMBED_COLOR = 3447003
DISCORD_USER_AGENT = "curl/8.5.0"
DISCORD_ERROR_BODY_MAX_BYTES = 4096
DISCORD_ERROR_BODY_MAX_CHARS = 500
MARKER_NAME = "pdd-release-video-discord-backfill"
PENDING_MARKER_NAME = "pdd-release-video-discord-backfill-pending"
SKIP_MARKER_NAME = "pdd-release-video-skipped"
POST_MARKER_MAX_ATTEMPTS = 3
POST_MARKER_RETRY_DELAY_SECONDS = 1.0


class BackfillError(RuntimeError):
    """Raised for actionable release-video Discord backfill failures."""


class DiscordWebhookError(BackfillError):
    """Raised when Discord webhook delivery fails."""

    def __init__(self, message: str, *, post_definitely_failed: bool) -> None:
        super().__init__(message)
        self.post_definitely_failed = post_definitely_failed


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


def youtube_video_id(youtube_url: str) -> str:
    parsed = urllib.parse.urlparse(youtube_url)
    if parsed.scheme not in {"http", "https"}:
        raise BackfillError(f"YouTube URL must use http or https: {youtube_url!r}.")

    host = parsed.netloc.lower()
    if host.startswith("www."):
        host = host[4:]

    video_id = ""
    if host == "youtu.be":
        video_id = parsed.path.strip("/").split("/", 1)[0]
    elif host == "youtube.com":
        if parsed.path == "/watch":
            video_id = urllib.parse.parse_qs(parsed.query).get("v", [""])[0]
        elif parsed.path.startswith("/embed/") or parsed.path.startswith("/shorts/"):
            parts = parsed.path.strip("/").split("/")
            if len(parts) >= 2:
                video_id = parts[1]

    if not YOUTUBE_VIDEO_ID_RE.fullmatch(video_id):
        raise BackfillError(f"YouTube URL does not include a valid video id: {youtube_url!r}.")
    return video_id


def discord_backfill_marker(tag: str, youtube_url: str) -> str:
    video_id = youtube_video_id(youtube_url)
    digest = hashlib.sha256(f"{tag}\n{video_id}".encode("utf8")).hexdigest()
    return f"<!-- {MARKER_NAME}: tag={tag} video_sha256={digest} -->"


def discord_backfill_pending_marker(tag: str, youtube_url: str) -> str:
    video_id = youtube_video_id(youtube_url)
    digest = hashlib.sha256(f"{tag}\n{video_id}".encode("utf8")).hexdigest()
    return f"<!-- {PENDING_MARKER_NAME}: tag={tag} video_sha256={digest} -->"


def release_video_skip_marker(tag: str, reason: str) -> str:
    digest = hashlib.sha256(f"{tag}\n{reason.strip()}".encode("utf8")).hexdigest()
    return f"<!-- {SKIP_MARKER_NAME}: tag={tag} reason_sha256={digest} -->"


def release_body_has_youtube_video(body: str, video_id: str) -> bool:
    for match in YOUTUBE_URL_IN_TEXT_RE.finditer(body):
        try:
            if youtube_video_id(match.group(0)) == video_id:
                return True
        except BackfillError:
            continue
    return False


def ensure_release_body_has_video_link(body: str, youtube_url: str) -> tuple[str, bool]:
    video_id = youtube_video_id(youtube_url)
    if release_body_has_youtube_video(body, video_id):
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


def ensure_release_body_has_pending_marker(
    body: str, tag: str, youtube_url: str
) -> tuple[str, bool]:
    pending_marker = discord_backfill_pending_marker(tag, youtube_url)
    if pending_marker in body:
        return body, False
    if body.strip():
        return f"{body.rstrip()}\n\n{pending_marker}\n", True
    return f"{pending_marker}\n", True


def ensure_release_body_has_skip_record(
    body: str, tag: str, reason: str
) -> tuple[str, bool, bool]:
    marker = release_video_skip_marker(tag, reason)
    if marker in body:
        return body, False, False

    skip_text = f"Release video: skipped for {tag}.\nReason: {reason.strip()}"
    body_without_old_skip = remove_release_video_skip_records(body, tag).strip()
    if body_without_old_skip:
        return f"{skip_text}\n\n{body_without_old_skip}\n\n{marker}\n", True, True
    return f"{skip_text}\n\n{marker}\n", True, True


def remove_release_video_skip_records(body: str, tag: str) -> str:
    body = re.sub(
        rf"(?m)^<!-- {re.escape(SKIP_MARKER_NAME)}: tag={re.escape(tag)} "
        r"reason_sha256=[0-9a-f]{64} -->\n?",
        "",
        body,
    )
    return re.sub(
        rf"(?m)^Release video: skipped for {re.escape(tag)}\.\n"
        r"Reason: [^\n]*(?:\n\n|\n?\Z)",
        "",
        body,
    )


def remove_release_body_pending_marker(body: str, tag: str, youtube_url: str) -> tuple[str, bool]:
    pending_marker = discord_backfill_pending_marker(tag, youtube_url)
    if pending_marker not in body:
        return body, False
    lines = body.splitlines()
    kept_lines = [line for line in lines if line.strip() != pending_marker]
    if len(kept_lines) == len(lines):
        return body, False
    while kept_lines and not kept_lines[0]:
        kept_lines.pop(0)
    while kept_lines and not kept_lines[-1]:
        kept_lines.pop()
    cleaned_body = "\n".join(kept_lines)
    if cleaned_body and body.endswith(("\n", "\r")):
        cleaned_body += "\n"
    return cleaned_body, True


def ensure_no_uncertain_pending_marker(body: str, tag: str, youtube_url: str) -> None:
    pending_marker = discord_backfill_pending_marker(tag, youtube_url)
    if pending_marker in body:
        raise BackfillError(
            "Release has a pending Discord backfill marker for this video. "
            "Inspect Discord before rerunning, then remove the pending marker "
            "or replace it with the completed backfill marker."
        )


def mark_release_body_pending(
    github: GitHubReleaseClient,
    tag: str,
    youtube_url: str,
    body: str,
) -> bool:
    body_with_link, link_added = ensure_release_body_has_video_link(body, youtube_url)
    pending_body, pending_added = ensure_release_body_has_pending_marker(
        body_with_link,
        tag,
        youtube_url,
    )
    if link_added or pending_added:
        github.edit_release_body(tag, pending_body)
    return link_added or pending_added


def cleanup_pending_marker_after_failed_post(
    github: GitHubReleaseClient,
    tag: str,
    youtube_url: str,
    post_error: BackfillError,
) -> None:
    try:
        latest_body = github.get_release_body(tag)
        cleanup_body, removed = remove_release_body_pending_marker(latest_body, tag, youtube_url)
        if removed:
            github.edit_release_body(tag, cleanup_body)
    except BackfillError as cleanup_error:
        raise BackfillError(
            f"{post_error} Pending-marker cleanup also failed: {cleanup_error}"
        ) from post_error
    raise post_error


def webhook_post_definitely_failed(error: BackfillError) -> bool:
    if isinstance(error, DiscordWebhookError):
        return error.post_definitely_failed
    match = DISCORD_HTTP_ERROR_RE.match(str(error))
    if not match:
        return False
    return discord_http_status_definitely_failed(int(match.group(1)))


def discord_http_status_definitely_failed(status: int) -> bool:
    return 400 <= status < 500


def mark_release_body_posted(
    github: GitHubReleaseClient,
    tag: str,
    youtube_url: str,
    *,
    attempts: int = POST_MARKER_MAX_ATTEMPTS,
    sleep: Callable[[float], None] = time.sleep,
) -> tuple[bool, bool]:
    last_error: BackfillError | None = None
    for attempt in range(attempts):
        try:
            body = github.get_release_body(tag)
            body_with_link, link_added = ensure_release_body_has_video_link(body, youtube_url)
            body_without_pending, pending_removed = remove_release_body_pending_marker(
                body_with_link,
                tag,
                youtube_url,
            )
            marked_body, marker_added = ensure_release_body_has_marker(
                body_without_pending,
                tag,
                youtube_url,
            )
            if link_added or pending_removed or marker_added:
                github.edit_release_body(tag, marked_body)
            return link_added or pending_removed or marker_added, marker_added
        except BackfillError as exc:
            last_error = exc
            if attempt + 1 < attempts:
                sleep(POST_MARKER_RETRY_DELAY_SECONDS)
    raise BackfillError(
        "Posted Discord release-video follow-up, but could not persist the "
        "completed backfill marker. Do not rerun until Discord has been "
        f"inspected; the release should still contain a pending marker. {last_error}"
    )


def build_discord_payload(tag: str, youtube_url: str, repo: str) -> dict[str, Any]:
    release_url = f"https://github.com/{repo}/releases/tag/{tag}"
    return {
        "embeds": [
            {
                "title": f"Release {tag}",
                "url": release_url,
                "description": (
                    f"\U0001f3a5 **Release video:** {youtube_url}\n\n"
                    f"Recovered release video for {tag}.\n"
                    f"Release: {release_url}"
                ),
                "color": DISCORD_EMBED_COLOR,
            }
        ]
    }


def redact_discord_webhook_references(body: str, webhook_url: str | None) -> str:
    """Redact Discord webhook URLs, including common encoded forms."""
    variants: set[str] = set()
    if webhook_url:
        quoted = urllib.parse.quote(webhook_url, safe="")
        quoted_plus = urllib.parse.quote_plus(webhook_url, safe="")
        variants.update(
            {
                webhook_url,
                webhook_url.replace("/", "\\/"),
                quoted,
                quoted_plus,
                lower_percent_escapes(quoted),
                lower_percent_escapes(quoted_plus),
            }
        )
    for variant in sorted(variants, key=len, reverse=True):
        if variant:
            body = body.replace(variant, "[redacted-discord-webhook]")
    return DISCORD_WEBHOOK_URL_RE.sub("[redacted-discord-webhook]", body)


def lower_percent_escapes(value: str) -> str:
    """Normalize percent escape hex digits to lowercase without changing token text."""
    return re.sub(r"%[0-9A-Fa-f]{2}", lambda match: match.group(0).lower(), value)


def sanitized_response_body_excerpt(response: Any, webhook_url: str | None = None) -> str:
    try:
        raw_body = response.read(DISCORD_ERROR_BODY_MAX_BYTES + 1)
    except (AttributeError, OSError, ValueError):
        return ""

    if not raw_body:
        return ""
    if isinstance(raw_body, str):
        body = raw_body
    else:
        body = raw_body.decode("utf8", errors="replace")

    body = redact_discord_webhook_references(body, webhook_url)
    body = (
        body.replace("\\r", " ")
        .replace("\\n", " ")
        .replace("\\t", " ")
        .replace("\r", " ")
        .replace("\n", " ")
        .replace("\t", " ")
    )
    body = " ".join(body.split())
    if len(body) > DISCORD_ERROR_BODY_MAX_CHARS:
        return f"{body[:DISCORD_ERROR_BODY_MAX_CHARS]}..."
    return body


def discord_http_error_message(
    status: int,
    reason: str,
    response: Any,
    webhook_url: str | None = None,
) -> str:
    message = f"Discord webhook returned HTTP {status}: {reason}"
    body_excerpt = sanitized_response_body_excerpt(response, webhook_url)
    if body_excerpt:
        message = f"{message} Response body excerpt: {body_excerpt}"
    return message


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
        headers={
            "Accept": "*/*",
            "Content-Type": "application/json",
            "User-Agent": DISCORD_USER_AGENT,
        },
        method="POST",
    )
    try:
        with urllib.request.urlopen(request, timeout=timeout) as response:
            status = getattr(response, "status", response.getcode())
            if status >= 400:
                raise DiscordWebhookError(
                    f"Discord webhook returned HTTP {status}",
                    post_definitely_failed=discord_http_status_definitely_failed(status),
                )
    except urllib.error.HTTPError as exc:
        raise DiscordWebhookError(
            discord_http_error_message(exc.code, str(exc.reason), exc, webhook_url),
            post_definitely_failed=discord_http_status_definitely_failed(exc.code),
        ) from exc
    except urllib.error.URLError as exc:
        raise DiscordWebhookError(
            f"Discord webhook request failed: {exc.reason}",
            post_definitely_failed=False,
        ) from exc


def validate_inputs(tag: str, youtube_url: str, repo: str) -> None:
    if not SEMVER_TAG_RE.fullmatch(tag):
        raise BackfillError(f"Release tag must look like vX.Y.Z, got {tag!r}.")
    if not YOUTUBE_URL_RE.fullmatch(youtube_url):
        raise BackfillError(f"YouTube URL does not look valid: {youtube_url!r}.")
    youtube_video_id(youtube_url)
    if not GITHUB_REPO_RE.fullmatch(repo):
        raise BackfillError(f"GitHub repo must look like owner/name, got {repo!r}.")


def validate_skip_inputs(tag: str, reason: str, repo: str) -> None:
    if not SEMVER_TAG_RE.fullmatch(tag):
        raise BackfillError(f"Release tag must look like vX.Y.Z, got {tag!r}.")
    if not GITHUB_REPO_RE.fullmatch(repo):
        raise BackfillError(f"GitHub repo must look like owner/name, got {repo!r}.")
    if not reason.strip():
        raise BackfillError("Skip reason is required when recording a release-video skip.")


def record_release_video_skip(
    *,
    tag: str,
    repo: str,
    reason: str,
    github: GitHubReleaseClient,
    post_discord: Callable[[str, dict[str, Any]], None] | None = None,
) -> BackfillResult:
    """Record that a historical release video was intentionally skipped."""
    del post_discord
    normalized_reason = " ".join(reason.split())
    validate_skip_inputs(tag, normalized_reason, repo)

    body = github.get_release_body(tag)
    marked_body, updated, marker_added = ensure_release_body_has_skip_record(
        body,
        tag,
        normalized_reason,
    )
    if updated:
        github.edit_release_body(tag, marked_body)
        return BackfillResult(
            posted=False,
            release_body_updated=True,
            marker_added=marker_added,
            skipped_reason="release-video-skipped",
        )
    return BackfillResult(
        posted=False,
        release_body_updated=False,
        marker_added=False,
        skipped_reason="release-video-skip-already-marked",
    )


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

    if marker in body:
        body_with_link, link_added = ensure_release_body_has_video_link(body, youtube_url)
        clean_body, pending_removed = remove_release_body_pending_marker(
            body_with_link,
            tag,
            youtube_url,
        )
        if link_added or pending_removed:
            github.edit_release_body(tag, clean_body)
        return BackfillResult(
            posted=False,
            release_body_updated=link_added or pending_removed,
            marker_added=False,
            skipped_reason="discord-followup-already-marked",
        )
    ensure_no_uncertain_pending_marker(body, tag, youtube_url)

    if not webhook_url:
        raise BackfillError("DISCORD_WEBHOOK_URL is required when a follow-up has not been marked.")

    latest_body = github.get_release_body(tag)
    if marker in latest_body:
        latest_body_with_link, link_added = ensure_release_body_has_video_link(
            latest_body,
            youtube_url,
        )
        clean_body, pending_removed = remove_release_body_pending_marker(
            latest_body_with_link,
            tag,
            youtube_url,
        )
        if link_added or pending_removed:
            github.edit_release_body(tag, clean_body)
        return BackfillResult(
            posted=False,
            release_body_updated=link_added or pending_removed,
            marker_added=False,
            skipped_reason="discord-followup-already-marked",
        )
    ensure_no_uncertain_pending_marker(latest_body, tag, youtube_url)

    release_body_updated = mark_release_body_pending(github, tag, youtube_url, latest_body)

    try:
        post_discord(webhook_url, build_discord_payload(tag, youtube_url, repo))
    except BackfillError as exc:
        if webhook_post_definitely_failed(exc):
            cleanup_pending_marker_after_failed_post(github, tag, youtube_url, exc)
        raise BackfillError(
            "Discord webhook delivery failed after writing a pending marker. "
            "Inspect Discord before rerunning; if no post was sent, remove the "
            f"pending marker from the release body. {exc}"
        ) from exc

    post_release_body_updated, marker_added = mark_release_body_posted(
        github,
        tag,
        youtube_url,
    )

    return BackfillResult(
        posted=True,
        release_body_updated=release_body_updated or post_release_body_updated,
        marker_added=marker_added,
    )


def parse_args(argv: list[str] | None = None) -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        description=(
            "Post an idempotent Discord follow-up after a release video is "
            "recovered outside the normal release workflow, or record an "
            "explicit historical skip decision."
        )
    )
    parser.add_argument("--tag", required=True, help="Release tag, for example v0.0.283.")
    mode = parser.add_mutually_exclusive_group(required=True)
    mode.add_argument("--youtube-url", help="Recovered YouTube release-video URL.")
    mode.add_argument(
        "--skip-reason",
        help="Record that no release video will be backfilled for this release.",
    )
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
        if args.skip_reason is not None:
            result = record_release_video_skip(
                tag=args.tag,
                repo=args.repo,
                reason=args.skip_reason,
                github=github,
            )
        else:
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
    elif result.skipped_reason == "release-video-skipped":
        print(f"Recorded release-video skip decision for {args.tag}.")
    elif result.skipped_reason == "release-video-skip-already-marked":
        print(f"Skipped release-video skip update for {args.tag}; matching marker already exists.")
    if result.release_body_updated:
        print(f"Updated GitHub release body for {args.tag}.")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
