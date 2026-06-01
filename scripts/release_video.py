#!/usr/bin/env python3
"""Create and publish a PDD release video through the PDS CLI."""

from __future__ import annotations

import argparse
import json
import os
import re
import shlex
import shutil
import subprocess
import sys
from pathlib import Path
from typing import Any


SEMVER_TAG_RE = re.compile(r"^v\d+\.\d+\.\d+$")
YOUTUBE_URL_RE = re.compile(r"https?://(?:www\.)?(?:youtube\.com|youtu\.be)/[^\s\"'<>]+")


class ReleaseVideoError(RuntimeError):
    """Raised for actionable release-video failures."""


def main(argv: list[str] | None = None) -> int:
    args = parse_args(argv)
    repo = Path(args.repo).resolve()

    try:
        tag = resolve_release_tag(repo, args.tag or os.environ.get("RELEASE_TAG"))
        git_sha = args.git_sha or os.environ.get("RELEASE_GIT_SHA") or git(
            repo,
            "rev-list",
            "-n",
            "1",
            tag,
        )
        previous_tag = previous_release_tag(repo, tag)
        repo_url = args.repo_url or remote_url(repo)
        repo_name = args.repo_name or infer_repo_name(repo_url)

        output_dir = Path(args.output_dir) / safe_path_part(tag)
        output_dir.mkdir(parents=True, exist_ok=True)

        context = build_release_context(
            repo=repo,
            tag=tag,
            previous_tag=previous_tag,
            git_sha=git_sha,
            repo_url=repo_url,
            repo_name=repo_name,
            changelog_path=Path(args.changelog),
        )
        context_path = output_dir / "release_context.md"
        release_notes_path = output_dir / "release_notes.md"
        script_path = output_dir / "release_video_script.md"
        response_path = output_dir / "pds_response.json"

        context_path.write_text(context, encoding="utf8")
        release_notes_path.write_text(release_notes_from_context(context), encoding="utf8")
        script_text = generate_script_with_claude(
            context=context,
            claude_cli=args.claude_cli,
            claude_model=args.claude_model,
            timeout=args.claude_timeout,
            cwd=repo,
        )
        script_path.write_text(script_text, encoding="utf8")

        response = create_release_video(
            args=args,
            repo=repo,
            tag=tag,
            git_sha=git_sha,
            repo_url=repo_url,
            repo_name=repo_name,
            script_path=script_path,
            release_notes_path=release_notes_path,
            changelog_path=Path(args.changelog),
        )
        response_path.write_text(json.dumps(response, indent=2, sort_keys=True) + "\n", encoding="utf8")

        youtube_url = find_youtube_url(response)
        if args.target == "publish" and not args.dry_run and not youtube_url:
            raise ReleaseVideoError(
                "PDS release-video publish completed but did not return a YouTube URL."
            )

        print(f"Release video artifacts: {output_dir}")
        if youtube_url:
            print(f"YouTube video: {youtube_url}")
        return 0
    except ReleaseVideoError as exc:
        print(f"release-video: {exc}", file=sys.stderr)
        return 1


def parse_args(argv: list[str] | None) -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        description="Generate a Claude-authored PDD release video script and publish it through pds.",
    )
    parser.add_argument("--repo", default=".", help="Git repository root. Defaults to cwd.")
    parser.add_argument("--tag", help="Release tag. Defaults to the semver tag at HEAD.")
    parser.add_argument("--git-sha", help="Release commit SHA. Defaults to the tagged commit.")
    parser.add_argument("--repo-url", help="Repository URL passed to PDS.")
    parser.add_argument("--repo-name", help="Repository name passed to PDS, for example promptdriven/pdd.")
    parser.add_argument("--changelog", default="CHANGELOG.md", help="Changelog file to attach.")
    parser.add_argument(
        "--output-dir",
        default=".pdd/release-videos",
        help="Directory for generated release-video artifacts.",
    )
    parser.add_argument("--claude-cli", default=os.environ.get("CLAUDE_CLI", "claude"))
    parser.add_argument("--claude-model", default=os.environ.get("CLAUDE_MODEL", "sonnet"))
    parser.add_argument("--claude-timeout", type=float, default=300.0)
    parser.add_argument("--pds-cli", default=os.environ.get("PDS_CLI", "pds"))
    parser.add_argument(
        "--project-id",
        default=os.environ.get("RELEASE_VIDEO_PROJECT_ID", ""),
        help="Existing PDS project id to use instead of creating a release project.",
    )
    parser.add_argument("--project-name", help="PDS project name. Defaults to 'PDD <tag> release'.")
    parser.add_argument("--preset", default=os.environ.get("RELEASE_VIDEO_PRESET", "release-notes"))
    parser.add_argument("--target", default=os.environ.get("RELEASE_VIDEO_TARGET", "publish"))
    parser.add_argument("--platform", default=os.environ.get("RELEASE_VIDEO_PLATFORM", "youtube"))
    parser.add_argument("--privacy", default=os.environ.get("RELEASE_VIDEO_PRIVACY", "unlisted"))
    parser.add_argument("--idempotency-key", help="PDS idempotency key.")
    parser.add_argument("--dry-run", action="store_true", help="Plan without creating video or uploading.")
    return parser.parse_args(argv)


def run(
    command: list[str],
    *,
    cwd: Path,
    input_text: str | None = None,
    timeout: float | None = None,
    check: bool = True,
) -> subprocess.CompletedProcess[str]:
    try:
        completed = subprocess.run(
            command,
            cwd=str(cwd),
            input=input_text,
            text=True,
            capture_output=True,
            timeout=timeout,
            check=False,
        )
    except subprocess.TimeoutExpired as exc:
        raise ReleaseVideoError(
            f"{shlex.join(command)} timed out after {timeout:g} seconds"
        ) from exc
    except FileNotFoundError as exc:
        raise ReleaseVideoError(f"Executable not found: {command[0]}") from exc
    if check and completed.returncode != 0:
        stderr = completed.stderr.strip()
        stdout = completed.stdout.strip()
        details = stderr or stdout or f"exit code {completed.returncode}"
        raise ReleaseVideoError(f"{shlex.join(command)} failed: {details[:2000]}")
    return completed


def git(repo: Path, *args: str, check: bool = True) -> str:
    return run(["git", *args], cwd=repo, check=check).stdout.strip()


def resolve_release_tag(repo: Path, explicit_tag: str | None) -> str:
    if explicit_tag:
        verify_tag(repo, explicit_tag)
        return explicit_tag

    tags = git(repo, "tag", "--points-at", "HEAD", "--list", "v*").splitlines()
    semver_tags = [tag for tag in tags if SEMVER_TAG_RE.match(tag)]
    if not semver_tags:
        raise ReleaseVideoError("No vN.N.N release tag found at HEAD; pass --tag explicitly.")
    tag = sorted(semver_tags, key=semver_sort_key, reverse=True)[0]
    verify_tag(repo, tag)
    return tag


def verify_tag(repo: Path, tag: str) -> None:
    if not SEMVER_TAG_RE.match(tag):
        raise ReleaseVideoError(f"Release tag must look like vN.N.N, got {tag!r}.")
    completed = run(
        ["git", "rev-parse", "--verify", "--quiet", f"refs/tags/{tag}"],
        cwd=repo,
        check=False,
    )
    if completed.returncode != 0:
        raise ReleaseVideoError(f"Release tag {tag} does not exist locally.")


def semver_sort_key(tag: str) -> tuple[int, int, int]:
    return tuple(int(part) for part in tag.removeprefix("v").split("."))  # type: ignore[return-value]


def previous_release_tag(repo: Path, tag: str) -> str | None:
    completed = run(
        ["git", "describe", "--tags", "--abbrev=0", f"{tag}^"],
        cwd=repo,
        check=False,
    )
    previous = completed.stdout.strip()
    return previous if completed.returncode == 0 and previous else None


def remote_url(repo: Path) -> str:
    completed = run(["git", "remote", "get-url", "origin"], cwd=repo, check=False)
    return completed.stdout.strip() if completed.returncode == 0 else ""


def infer_repo_name(repo_url: str) -> str:
    if not repo_url:
        return "promptdriven/pdd"
    cleaned = repo_url.removesuffix(".git")
    match = re.search(r"github\.com[:/](?P<name>[^/]+/[^/]+)$", cleaned)
    if match:
        return match.group("name")
    return cleaned.rsplit("/", 2)[-2] + "/" + cleaned.rsplit("/", 1)[-1] if "/" in cleaned else cleaned


def build_release_context(
    *,
    repo: Path,
    tag: str,
    previous_tag: str | None,
    git_sha: str,
    repo_url: str,
    repo_name: str,
    changelog_path: Path,
) -> str:
    revision_range = f"{previous_tag}..{tag}" if previous_tag else tag
    commits = git(repo, "log", revision_range, "--pretty=format:- %s (%h)", check=False)
    diff_stat = git(repo, "diff", "--stat", revision_range, check=False) if previous_tag else ""
    changed_files = git(repo, "diff", "--name-status", revision_range, check=False) if previous_tag else ""
    diff = (
        git(
            repo,
            "diff",
            revision_range,
            "--",
            ":(exclude)*.lock",
            ":(exclude)package-lock.json",
            ":(exclude)*test-durations.json",
            ":(exclude)dist/*",
            ":(exclude)*.min.js",
            ":(exclude)*.snap",
            check=False,
        )
        if previous_tag
        else ""
    )
    changelog_excerpt = changelog_context(repo / changelog_path, tag)
    github_notes = github_release_notes(repo, tag)

    return "\n".join(
        [
            f"# PDD release context for {tag}",
            "",
            f"- Repository: {repo_name}",
            f"- Repository URL: {repo_url or 'unknown'}",
            f"- Release tag: {tag}",
            f"- Previous tag: {previous_tag or 'none found'}",
            f"- Git SHA: {git_sha}",
            "",
            "## GitHub release notes",
            github_notes or "_No GitHub release notes found yet._",
            "",
            "## Changelog excerpt",
            changelog_excerpt or "_No changelog excerpt found._",
            "",
            "## Commits",
            commits or "_No commit log found._",
            "",
            "## Diff stat",
            diff_stat or "_No diff stat available._",
            "",
            "## Changed files",
            changed_files or "_No changed-file list available._",
            "",
            "## Diff excerpt",
            truncate(diff, 90_000) or "_No diff excerpt available._",
            "",
        ]
    )


def changelog_context(path: Path, tag: str) -> str:
    if not path.exists():
        return ""
    text = path.read_text(encoding="utf8", errors="replace")
    escaped_tag = re.escape(tag)
    tag_without_v = re.escape(tag.removeprefix("v"))
    match = re.search(
        rf"^##\s+(?:\[)?(?:{escaped_tag}|{tag_without_v})(?:\])?.*?(?=^##\s+|\Z)",
        text,
        flags=re.MULTILINE | re.DOTALL,
    )
    if match:
        return truncate(match.group(0).strip(), 60_000)
    unreleased = re.search(
        r"^##\s+Unreleased\b.*?(?=^##\s+|\Z)",
        text,
        flags=re.MULTILINE | re.DOTALL | re.IGNORECASE,
    )
    if unreleased:
        return truncate(unreleased.group(0).strip(), 60_000)
    return truncate(text, 60_000)


def github_release_notes(repo: Path, tag: str) -> str:
    if not shutil.which("gh"):
        return ""
    completed = run(
        ["gh", "release", "view", tag, "--json", "body", "--jq", ".body"],
        cwd=repo,
        timeout=30,
        check=False,
    )
    if completed.returncode != 0:
        return ""
    return completed.stdout.strip()


def release_notes_from_context(context: str) -> str:
    sections: list[str] = []
    for heading in ("GitHub release notes", "Changelog excerpt", "Commits"):
        match = re.search(
            rf"^## {re.escape(heading)}\n(?P<body>.*?)(?=^## |\Z)",
            context,
            flags=re.MULTILINE | re.DOTALL,
        )
        if match:
            body = match.group("body").strip()
            if body and not body.startswith("_No "):
                sections.append(f"## {heading}\n\n{body}")
    return "\n\n".join(sections).strip() + "\n"


def generate_script_with_claude(
    *,
    context: str,
    claude_cli: str,
    claude_model: str,
    timeout: float,
    cwd: Path,
) -> str:
    command = split_command(claude_cli)
    ensure_command_exists(command[0], "Claude Code")
    command.extend(
        [
            "-p",
            "--model",
            claude_model,
            "--tools",
            "",
            "--no-session-persistence",
            "--output-format",
            "text",
        ]
    )
    prompt = build_claude_prompt(context)
    completed = run(command, cwd=cwd, input_text=prompt, timeout=timeout)
    script = strip_markdown_fence(completed.stdout.strip())
    if len(script) < 200:
        raise ReleaseVideoError("Claude Code produced an unexpectedly short release video script.")
    return script.rstrip() + "\n"


def build_claude_prompt(context: str) -> str:
    return f"""Write the narration script for a short YouTube release video about this PDD CLI release.

Audience: developers who use or may adopt Prompt-Driven Development.
Length: 60-90 seconds.
Style: concise, concrete, technical, and demo-friendly.

Requirements:
- Base every claim on the release context below; do not invent features.
- Lead with the most user-visible change.
- Mention the release tag.
- Use plain Markdown.
- Include a title, a short hook, narration beats, and visual direction cues.
- Keep it suitable for an automated video pipeline: no tables, no footnotes, no citations, no code fences.
- Output only the script.

RELEASE CONTEXT:

{context}
"""


def create_release_video(
    *,
    args: argparse.Namespace,
    repo: Path,
    tag: str,
    git_sha: str,
    repo_url: str,
    repo_name: str,
    script_path: Path,
    release_notes_path: Path,
    changelog_path: Path,
) -> dict[str, Any]:
    command = split_command(args.pds_cli)
    ensure_command_exists(command[0], "PDS CLI")
    project_id = str(args.project_id or "").strip()
    if project_id:
        command.extend(["--project", project_id])
    project_name = args.project_name or ("" if project_id else f"PDD {tag} release")
    idempotency_key = args.idempotency_key or f"pdd-release-video:{tag}:{git_sha}"
    pds_args = [
        "release-video",
        "create",
        "--script",
        str(script_path),
        "--release-notes",
        str(release_notes_path),
        "--repo-url",
        repo_url,
        "--repo-name",
        repo_name,
        "--git-sha",
        git_sha,
        "--release-tag",
        tag,
        "--preset",
        args.preset,
        "--target",
        args.target,
        "--platform",
        args.platform,
        "--privacy",
        args.privacy,
        "--idempotency-key",
        idempotency_key,
        "--wait",
        "--json",
    ]
    if project_name:
        pds_args[2:2] = ["--project-name", project_name]
    changelog_full_path = repo / changelog_path
    if changelog_full_path.exists():
        pds_args.extend(["--changelog", str(changelog_full_path)])
    if args.dry_run:
        pds_args.append("--dry-run")

    completed = run(command + pds_args, cwd=repo, timeout=None)
    try:
        parsed = json.loads(completed.stdout)
    except json.JSONDecodeError as exc:
        raise ReleaseVideoError(
            f"PDS CLI did not return JSON: {exc}. Output: {completed.stdout[:2000]}"
        ) from exc
    if not isinstance(parsed, dict):
        raise ReleaseVideoError("PDS CLI returned JSON that was not an object.")
    return parsed


def find_youtube_url(value: Any) -> str | None:
    if isinstance(value, str):
        match = YOUTUBE_URL_RE.search(value)
        return match.group(0) if match else None
    if isinstance(value, dict):
        preferred_keys = ("youtubeUrl", "videoUrl", "url")
        for key in preferred_keys:
            if key in value:
                found = find_youtube_url(value[key])
                if found:
                    return found
        for item in value.values():
            found = find_youtube_url(item)
            if found:
                return found
    if isinstance(value, list):
        for item in value:
            found = find_youtube_url(item)
            if found:
                return found
    return None


def split_command(command: str) -> list[str]:
    parts = shlex.split(command)
    if not parts:
        raise ReleaseVideoError("Command cannot be empty.")
    return parts


def ensure_command_exists(executable: str, label: str) -> None:
    if "/" in executable:
        if Path(executable).exists():
            return
    elif shutil.which(executable):
        return
    raise ReleaseVideoError(f"{label} executable not found: {executable}")


def strip_markdown_fence(text: str) -> str:
    match = re.fullmatch(r"```(?:markdown|md)?\s*(.*?)\s*```", text, flags=re.DOTALL)
    return match.group(1).strip() if match else text


def truncate(text: str, max_chars: int) -> str:
    if len(text) <= max_chars:
        return text
    return text[:max_chars] + "\n\n[truncated]\n"


def safe_path_part(value: str) -> str:
    return re.sub(r"[^A-Za-z0-9._-]+", "-", value).strip("-") or "release"


if __name__ == "__main__":
    raise SystemExit(main())
