#!/usr/bin/env python3
"""Create and publish a PDD release video through the PDS CLI."""

from __future__ import annotations

import argparse
from datetime import datetime, timezone
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
IDEMPOTENCY_PROVENANCE_RE = re.compile(r"[^a-z0-9._-]+")
PDS_RUN_HANDLE_LINE_RE = re.compile(
    r"^\[pds\]\s+release-video run handle:\s+(?P<fields>.+)$",
    flags=re.IGNORECASE | re.MULTILINE,
)
PDS_RUN_HANDLE_FIELD_RE = re.compile(
    r"\b(?P<key>runId|projectId|status|attemptId)=(?P<value>[^\s]+)"
)
METADATA_CONFLICT_MODES = {"replace", "use-existing"}
RUNNING_PDS_STATUSES = {
    "queued",
    "pending",
    "running",
    "in_progress",
    "in-progress",
}
TERMINAL_PDS_STATUSES = {
    "canceled",
    "cancelled",
    "complete",
    "completed",
    "done",
    "error",
    "errored",
    "failed",
    "failure",
    "succeeded",
    "success",
    "timed_out",
    "timeout",
}
FAILED_PDS_STATUSES = {
    "canceled",
    "cancelled",
    "error",
    "errored",
    "failed",
    "failure",
    "timed_out",
    "timeout",
}
PDS_PROVIDER_QUOTA_CODES = {
    "provider_quota",
    "spec_generation_provider_quota",
    "component_generation_provider_quota",
}
PDS_AUDIT_GATE_CODES = {"audit_failed"}
PDS_REQUEST_HASH_CODES = {"request_hash_mismatch"}
SENSITIVE_COMMAND_OPTIONS = {
    "--access-token",
    "--api-key",
    "--auth-token",
    "--authorization",
    "--password",
    "--secret",
    "--token",
}
SENSITIVE_FIELD_NAMES = {
    "accesstoken",
    "apikey",
    "authorization",
    "clientsecret",
    "credential",
    "password",
    "refreshtoken",
    "secret",
    "signature",
    "signedurl",
    "sig",
    "token",
}
REPO_ROOT = Path(__file__).resolve().parents[1]
DEFAULT_RELEASE_VIDEO_PROMPT = REPO_ROOT / "pdd" / "prompts" / "release_video_script_LLM.prompt"
DEFAULT_CLAUDE_MODEL = "claude-opus-4-8"
DEFAULT_PDS_CLAUDE_MODEL = "glm-5.2"
DEFAULT_RELEASE_VIDEO_OUTPUT_DIR = ".pdd/release-videos"
MIN_PDS_CLI_VERSION = (0, 1, 11)
MIN_PDS_CLI_VERSION_TEXT = ".".join(str(part) for part in MIN_PDS_CLI_VERSION)
PDS_VERSION_RE = re.compile(r"(?<!\d)(?P<version>\d+\.\d+\.\d+)(?!\d)")
PDS_VERSION_PROBE_TIMEOUT_SECONDS = 10.0
DEFAULT_PDS_CREATE_TIMEOUT_SECONDS = 1800.0
VISUAL_SAFETY_CHECKS = {
    "risky_readable_surface": "hasNoReadableSurfaceVisuals",
    "brittle_exact_geometry": "hasNoExactGeometryVisuals",
    "brittle_mandatory_motion": "hasNoMandatoryMotionVisuals",
}
READABLE_VISUAL_RE = re.compile(
    r"\b(?:workstation|laptops?|phones?|monitors?|screens?|terminal|console|shell|"
    r"source\s+code|code(?:\s+snippet)?|commands?|makefile|browsers?|web\s+pages?|"
    r"user\s+interface|ui|dashboard|documents?|docs?|changelog|release\s+notes?|"
    r"github(?:\s+page)?|pull\s+requests?|issues?|json|ya?ml|configuration|config|"
    r"readable|text|words?|labels?|logos?|ides?|editors?|spreadsheets?|charts?|"
    r"graphs?|captions?|subtitles?|menus?|toolbars?|web\s+apps?|"
    r"(?:application|app|browser|editor)\s+windows?|data\s+tables?|"
    r"(?:data|comparison|status)\s+tables?|table\s+(?:of|with)\s+"
    r"(?:data|rows?|columns?|cells?|values?|text)|column\s+headers?|"
    r"ui\s+controls?|(?:input|web|application)\s+forms?|"
    r"(?:graphical|software|application|app)\s+(?:user\s+)?interfaces?)\b",
    flags=re.IGNORECASE,
)
EXACT_GEOMETRY_VISUAL_RE = re.compile(
    r"\b(?:exact(?:ly)?|precise(?:ly)?|perfect(?:ly)?|parallel|"
    r"align(?:ed|ment|s|ing)?|symmetr(?:y|ic|ical|ically)|split[- ]screen|"
    r"side[- ]by[- ]side|grid|x[- ]shap(?:e|ed)|cross(?:es|ed|ing)?|"
    r"non[- ]crossing|(?:left|right|top|bottom)\s+(?:side|panel|orb|strand))\b",
    flags=re.IGNORECASE,
)
CAMERA_MOTION_VISUAL_RE = re.compile(
    r"\b(?:push(?:es|ed|ing)?[- ]in|zoom(?!ed[- ]out)(?:s|ing|ed(?:[- ]in)?)?|"
    r"pan(?:s|ned|ning)?|orbit(?:s|ed|ing)?|track(?:s|ed|ing)?|"
    r"doll(?:y|ies|ied|ying)|tilt(?:s|ed|ing)?|crane(?:s|d|ing)?|"
    r"roll(?:s|ed|ing)?|rack[- ]focus(?:es|ed|ing)?|drift(?:s|ed|ing)?|"
    r"transition(?:s|ed|ing)?|moves?)\b",
    flags=re.IGNORECASE,
)
IMPLICIT_CAMERA_ACTION_RE = re.compile(
    r"\b(?:push(?:es|ed|ing)?[- ]in|zoom(?!ed[- ]out)|pan|orbit|track|doll|"
    r"tilt|crane|rack[- ]focus)",
    flags=re.IGNORECASE,
)
SEMANTIC_MOTION_VISUAL_RE = re.compile(
    r"\b(?:cross(?:es|ed|ing)?|align(?:s|ed|ing)?|merge(?:s|d|ing)?|"
    r"morph(?:s|ed|ing)?|transform(?:s|ed|ing)?|"
    r"mov(?:e|es|ed|ing)\s+into|rotat(?:e|es|ed|ing)|spin(?:s|ning)?)\b",
    flags=re.IGNORECASE,
)
FRAME_EXACT_MOTION_RE = re.compile(
    r"(?:\b(?:at|after|by|on)\s+(?:the\s+)?(?:exactly\s+)?"
    r"(?:(?:\d+(?:\.\d+)?|one|two|three|four|five|six|seven|eight|nine|ten)"
    r"[- ]?(?:seconds?|secs?|s)(?:\s+mark)?|(?:frame|second)\s+"
    r"(?:\d+|one|two|three|four|five|six|seven|eight|nine|ten))\b|"
    r"\b(?:frame|second)\s+(?:\d+|one|two|three|four|five|six|seven|eight|"
    r"nine|ten)\b|\b\d+(?:st|nd|rd|th)\s+(?:frame|second)\b|"
    r"\b(?:at|after|by)\s+\d{1,2}:\d{2}\b|\bframe[- ]by[- ]frame\b)",
    flags=re.IGNORECASE,
)
VISUAL_CLAUSE_SPLIT_RE = re.compile(
    r"[;,.!?]+|\b(?:while|whereas|but|and\s+then|then)\b|"
    r"\b(?:as|with)(?=\s+(?:the\s+)?camera\b)|"
    r"\band(?=\s+(?:the\s+)?camera\b)",
    flags=re.IGNORECASE,
)
MOTION_OPTIONAL_PREFIX_RE = re.compile(
    r"\boptional(?:ly)?(?:\s+(?:gentle|slow|subtle|soft|smooth|slight|"
    r"transform[- ]safe|camera)){0,5}\s*$",
    flags=re.IGNORECASE,
)
CAMERA_MODAL_PREFIX_RE = re.compile(
    r"\bcamera\s+(?:may|can|could)(?:\s+\w+){0,3}\s*$",
    flags=re.IGNORECASE,
)
IMPLICIT_CAMERA_MODAL_PREFIX_RE = re.compile(
    r"^(?:the\s+)?(?:view\s+)?(?:may|can|could)(?:\s+\w+){0,3}\s*$",
    flags=re.IGNORECASE,
)
MOTION_OPTIONAL_SUFFIX_RE = re.compile(
    r"^(?:\s+\w+){0,4}\s+(?:(?:may|can|could)\s+be\s+used|"
    r"if\s+(?:available|supported|desired))\b",
    flags=re.IGNORECASE,
)
MOTION_REQUIRED_PREFIX_RE = re.compile(
    r"\b(?:must|required\s+to|has\s+to|needs\s+to|should|will)"
    r"(?:\s+\w+){0,3}\s*$",
    flags=re.IGNORECASE,
)
SAFE_TEXT_QUALIFIER_RE = re.compile(
    r"\b(?:text[- ]free|non[- ]textual|unlabeled|without\s+(?:readable\s+)?"
    r"(?:text|words?|labels?|logos?)|no\s+(?:readable\s+)?(?:text|words?|labels?|logos?))\b",
    flags=re.IGNORECASE,
)
RELEASE_VIDEO_AUDIT_FIX_POLICY_ARGS = (
    "--audit-fix-max-passes",
    "2",
    "--audit-fix-max-annotations-per-pass",
    "3",
    "--audit-fix-max-spend-pddc",
    "24",
    "--audit-fix-source-approval",
    "not-required",
)
CLAUDE_OAUTH_TOKEN_ENV_VARS = (
    "CLAUDE_CODE_OAUTH_TOKEN_1",
    "CLAUDE_CODE_OAUTH_TOKEN_2",
    "CLAUDE_CODE_OAUTH_TOKEN_3",
    "CLAUDE_CODE_OAUTH_TOKEN",
)
CLAUDE_FAILURE_CLASSES: tuple[tuple[str, tuple[str, ...]], ...] = (
    (
        "credential-limit",
        (
            r"hit\s+your\s+(?:session\s+|usage\s+|weekly\s+|monthly\s+)?limit"
            r"[^\n]{0,80}?\bresets?\b",
            r"weekly\s+(?:usage\s+)?limit",
            r"usage\s+limit",
            r"session\s+limit",
        ),
    ),
    (
        "quota",
        (
            r"quota\s+(?:exhausted|exceeded|reached)",
            r"daily\s+quota",
            r"terminal\s*quota\s*error",
        ),
    ),
    (
        "billing/credit-exhaustion",
        (
            r"credit\s+balance\s+is\s+too\s+low",
            r"insufficient\s+(?:credit|balance|funds)",
        ),
    ),
    (
        "oauth/login",
        (
            r"not\s+logged\s+in",
            r"please\s+run\s+/login",
            r"claude\s+auth\s+login",
        ),
    ),
    (
        "auth",
        (
            r"(?m)^[ \t]*(?:error:[ \t]*)?your\s+organization\s+has\s+disabled\s+"
            r"claude\s+subscription\s+access\s+for\s+claude\s+code(?:[.!]?[ \t]*|"
            r"[.!]?[ \t]+·[ \t]+use\s+an\s+anthropic\s+api\s+key\s+instead,\s+or\s+ask\s+"
            r"your\s+admin\s+to\s+enable\s+access[.!]?[ \t]*)$",
            r"authentication[_\s]error",
            r"authentication\s+failed",
            r"failed\s+to\s+authenticate",
            r"invalid\s+(?:bearer|api\s+key|key)",
            r"\b401\b",
            r"unauthorized",
            r"access\s+denied",
            r"permission\s+denied",
        ),
    ),
)


class ReleaseVideoError(RuntimeError):
    """Raised for actionable release-video failures."""


class ReleaseVideoProcessTimeout(ReleaseVideoError):
    """Raised when a release-video subprocess times out with captured output."""

    def __init__(
        self,
        message: str,
        *,
        completed: subprocess.CompletedProcess[str],
        timeout: float | None,
    ) -> None:
        super().__init__(message)
        self.completed = completed
        self.timeout = timeout


def main(argv: list[str] | None = None) -> int:
    args = parse_args(argv)
    try:
        repo = Path(args.repo).resolve()
        if args.status:
            return print_release_video_status(args, repo)
        validate_release_video_create_options(args)
        if args.preflight:
            return preflight_release_video(args)

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
        raw_script_path = output_dir / "release_video_script.raw.md"
        script_validation_path = output_dir / "release_video_script_validation.json"
        response_path = output_dir / "pds_response.json"
        run_metadata_path = output_dir / "pds_run.json"

        context_path.write_text(context, encoding="utf8")
        if args.release_notes_path:
            release_notes, source_release_notes_path = load_release_video_release_notes(
                Path(args.release_notes_path),
                repo,
            )
            print(
                "release-video: using prewritten release notes from "
                f"{source_release_notes_path}"
            )
        else:
            release_notes = release_notes_from_context(context)
        release_notes_path.write_text(release_notes, encoding="utf8")
        if args.script_path:
            raw_script, source_script_path = load_release_video_script_raw(
                Path(args.script_path),
                repo,
            )
            print(f"release-video: using prewritten script from {source_script_path}")
            script_source = str(source_script_path)
        else:
            raw_script = generate_raw_script_with_claude(
                context=context,
                claude_cli=args.claude_cli,
                claude_model=args.claude_model,
                claude_tools=args.claude_tools,
                prompt_template=Path(args.prompt_template),
                timeout=args.claude_timeout,
                cwd=repo,
            )
            script_source = "claude"
        script_artifacts = prepare_release_video_script(raw_script, source=script_source)
        write_release_video_script_artifacts(
            script_artifacts=script_artifacts,
            script_path=script_path,
            raw_script_path=raw_script_path,
            validation_path=script_validation_path,
        )
        if script_artifacts["validation"]["errors"]:
            errors = ", ".join(script_artifacts["validation"]["errors"])
            raise ReleaseVideoError(
                "release-video script validation failed before PDS publish; "
                f"PDS was not invoked. Failing checks: {errors}. "
                f"Validation saved to {script_validation_path}."
            )

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
            run_metadata_path=run_metadata_path,
        )
        response_path.write_text(json.dumps(response, indent=2, sort_keys=True) + "\n", encoding="utf8")

        youtube_url = find_youtube_url(response)
        if release_video_response_is_pending(response):
            print(f"Release video artifacts: {output_dir}")
            print_pending_release_video_response(response)
            return 0
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
        default=DEFAULT_RELEASE_VIDEO_OUTPUT_DIR,
        help="Directory for generated release-video artifacts.",
    )
    parser.add_argument("--claude-cli", default=env_default("CLAUDE_CLI", "claude"))
    parser.add_argument("--claude-model", default=release_video_claude_model_default())
    parser.add_argument(
        "--pds-claude-model",
        default=os.environ.get(
            "RELEASE_VIDEO_PDS_CLAUDE_MODEL",
            DEFAULT_PDS_CLAUDE_MODEL,
        ),
        help=(
            "Claude Code model passed to PDS for non-vision release-video "
            "pipeline stages. Set RELEASE_VIDEO_PDS_CLAUDE_MODEL='' to use "
            "the server default."
        ),
    )
    parser.add_argument(
        "--claude-tools",
        default=os.environ.get("RELEASE_VIDEO_CLAUDE_TOOLS", ""),
        help=(
            "Optional Claude Code tool allowlist for locked-down environments. "
            "Defaults to Claude Code's normal tool permissions."
        ),
    )
    parser.add_argument("--claude-timeout", type=float, default=float(os.environ.get("CLAUDE_TIMEOUT", "900")))
    parser.add_argument(
        "--prompt-template",
        default=os.environ.get("RELEASE_VIDEO_PROMPT_TEMPLATE", str(DEFAULT_RELEASE_VIDEO_PROMPT)),
        help="Prompt template used to generate the release-video script.",
    )
    parser.add_argument(
        "--script-path",
        default=os.environ.get("RELEASE_VIDEO_SCRIPT_PATH", ""),
        help=(
            "Use an existing release-video script instead of invoking Claude Code. "
            "Useful when reusing a generated artifact after Claude Code quota/auth failure."
        ),
    )
    parser.add_argument(
        "--release-notes-path",
        default=os.environ.get("RELEASE_VIDEO_RELEASE_NOTES_PATH", ""),
        help=(
            "Use an existing release-notes artifact instead of regenerating "
            "release notes from the current release context. Useful for exact "
            "PDS selected-project recovery."
        ),
    )
    parser.add_argument("--pds-cli", default=env_default("PDS_CLI", "pds"))
    parser.add_argument(
        "--pds-create-timeout",
        type=float,
        default=float(
            os.environ.get(
                "RELEASE_VIDEO_PDS_CREATE_TIMEOUT",
                DEFAULT_PDS_CREATE_TIMEOUT_SECONDS,
            )
        ),
        help=(
            "Maximum seconds to allow the PDS release-video create process. "
            "Set to 0 to rely only on the PDS CLI timeout/recovery behavior."
        ),
    )
    parser.add_argument(
        "--project-id",
        default=os.environ.get("RELEASE_VIDEO_PROJECT_ID", ""),
        help="Existing PDS project id to use instead of creating a release project.",
    )
    parser.add_argument(
        "--bootstrap-selected-project",
        action="store_true",
        default=env_flag("RELEASE_VIDEO_BOOTSTRAP_SELECTED_PROJECT"),
        help="Pass --bootstrap-selected-project to PDS for selected-project recovery.",
    )
    parser.add_argument(
        "--force-regenerate",
        action="store_true",
        default=env_flag("RELEASE_VIDEO_FORCE_REGENERATE"),
        help="Pass --force-regenerate to PDS for release-video recovery.",
    )
    parser.add_argument(
        "--metadata-conflict",
        default=os.environ.get("RELEASE_VIDEO_METADATA_CONFLICT", ""),
        help=(
            "Pass --metadata-conflict use-existing|replace to PDS for "
            "release-video project metadata recovery."
        ),
    )
    parser.add_argument("--project-name", help="PDS project name. Defaults to 'PDD <tag> release'.")
    parser.add_argument("--preset", default=os.environ.get("RELEASE_VIDEO_PRESET", "release-notes"))
    parser.add_argument("--target", default=os.environ.get("RELEASE_VIDEO_TARGET", "publish"))
    parser.add_argument("--platform", default=os.environ.get("RELEASE_VIDEO_PLATFORM", "youtube"))
    parser.add_argument("--privacy", default=os.environ.get("RELEASE_VIDEO_PRIVACY", "unlisted"))
    parser.add_argument(
        "--idempotency-key",
        default=os.environ.get("RELEASE_VIDEO_IDEMPOTENCY_KEY", ""),
        help="Full PDS idempotency key. Defaults to RELEASE_VIDEO_IDEMPOTENCY_KEY.",
    )
    parser.add_argument(
        "--idempotency-provenance",
        default=os.environ.get("RELEASE_VIDEO_IDEMPOTENCY_PROVENANCE", ""),
        help=(
            "Execution provenance namespace for default PDS idempotency keys. "
            "Defaults to github-actions on GitHub Actions, ci on generic CI, "
            "and local otherwise."
        ),
    )
    parser.add_argument(
        "--idempotency-attempt-id",
        default=os.environ.get("RELEASE_VIDEO_ATTEMPT_ID", ""),
        help=(
            "Retry attempt label appended to the default release-video idempotency key. "
            "Defaults to RELEASE_VIDEO_ATTEMPT_ID."
        ),
    )
    parser.add_argument("--dry-run", action="store_true", help="Plan without creating video or uploading.")
    parser.add_argument(
        "--preflight",
        action="store_true",
        help="Check local release-video configuration without creating artifacts.",
    )
    parser.add_argument(
        "--status",
        action="store_true",
        help="Print persisted PDS release-video run metadata for the release tag.",
    )
    parser.add_argument(
        "--status-query",
        action="store_true",
        help="With --status, query PDS status using the persisted run id.",
    )
    return parser.parse_args(argv)


def env_flag(name: str) -> bool:
    return os.environ.get(name, "").strip().lower() in {"1", "true", "yes", "on"}


def env_default(name: str, default: str) -> str:
    value = os.environ.get(name)
    if value is None or not value.strip():
        return default
    return value.strip()


def release_video_claude_model_default() -> str:
    return env_default(
        "RELEASE_VIDEO_CLAUDE_MODEL",
        env_default("CLAUDE_MODEL", DEFAULT_CLAUDE_MODEL),
    )


def validate_release_video_create_options(args: argparse.Namespace) -> None:
    """Validate options that only apply to PDS release-video creation."""
    validate_claude_script_model(args)
    validate_release_video_idempotency_options(args)
    validate_release_video_metadata_conflict_options(args)


def validate_claude_script_model(args: argparse.Namespace) -> None:
    model = str(getattr(args, "claude_model", "") or "").strip()
    if not model:
        raise ReleaseVideoError(
            "Claude Code script-generation model must not be empty. "
            "Set RELEASE_VIDEO_CLAUDE_MODEL, CLAUDE_MODEL, or --claude-model "
            "to a non-empty value."
        )
    args.claude_model = model


def validate_release_video_idempotency_options(args: argparse.Namespace) -> None:
    full_key = str(args.idempotency_key or "").strip()
    attempt_id = str(args.idempotency_attempt_id or "").strip()
    if full_key and attempt_id:
        raise ReleaseVideoError(
            "Use either a full release-video idempotency key or an attempt id, not both."
        )


def validate_release_video_metadata_conflict_options(args: argparse.Namespace) -> None:
    """Validate PDS project metadata conflict recovery options."""
    mode = release_video_metadata_conflict(args)
    if not mode:
        return
    if mode not in METADATA_CONFLICT_MODES:
        allowed = ", ".join(sorted(METADATA_CONFLICT_MODES))
        raise ReleaseVideoError(
            f"Release-video metadata conflict must be one of: {allowed}."
        )
    if mode == "replace" and not args.force_regenerate:
        raise ReleaseVideoError(
            "--metadata-conflict replace requires --force-regenerate "
            "or RELEASE_VIDEO_FORCE_REGENERATE=1."
        )


def release_video_metadata_conflict(args: argparse.Namespace) -> str:
    """Return the normalized PDS metadata-conflict recovery mode."""
    return str(args.metadata_conflict or "").strip()


def print_release_video_status(args: argparse.Namespace, repo: Path) -> int:
    """Print the locally persisted PDS run handle for a release tag."""
    tag = resolve_status_release_tag(repo, args.tag or os.environ.get("RELEASE_TAG"))
    run_metadata_path = Path(args.output_dir) / safe_path_part(tag) / "pds_run.json"
    try:
        raw = run_metadata_path.read_text(encoding="utf8")
    except OSError as exc:
        raise ReleaseVideoError(
            f"No persisted PDS run metadata found for {tag}: {run_metadata_path}"
        ) from exc
    if not raw.strip():
        raise ReleaseVideoError(
            f"Persisted PDS run metadata is empty for {tag}: {run_metadata_path}"
        )
    try:
        metadata = json.loads(raw)
    except json.JSONDecodeError as exc:
        raise ReleaseVideoError(
            f"Persisted PDS run metadata is not valid JSON: {run_metadata_path}: {exc}"
        ) from exc
    if not isinstance(metadata, dict):
        raise ReleaseVideoError(
            f"Persisted PDS run metadata is not a JSON object: {run_metadata_path}"
        )

    if args.status_query:
        metadata = query_pds_release_video_status(args, repo, metadata, run_metadata_path)

    display_metadata = release_video_status_display_metadata(metadata, args.pds_cli)
    print(json.dumps(display_metadata, indent=2, sort_keys=True))
    recover_command = str(display_metadata.get("recoverCommand") or "").strip()
    watch_command = str(display_metadata.get("watchCommand") or "").strip()
    if recover_command:
        print(f"recover: {recover_command}")
    if watch_command:
        print(f"watch: {watch_command}")
    status_note = release_video_status_note(metadata)
    if status_note:
        print(f"status-note: {status_note}")
    terminal_failure_hint = pds_terminal_failure_hint_from_status(metadata)
    if terminal_failure_hint:
        print(f"status-note: {terminal_failure_hint}")
    return 0


def release_video_status_display_metadata(
    metadata: dict[str, Any],
    pds_cli: str,
) -> dict[str, Any]:
    """Return persisted run metadata safe to print as status output."""
    display_source = dict(metadata)
    refresh_pds_recovery_commands(display_source, pds_cli)
    display_metadata = redact_status_artifact_value(display_source)
    return display_metadata if isinstance(display_metadata, dict) else {}


def resolve_status_release_tag(repo: Path, explicit_tag: str | None) -> str:
    if explicit_tag:
        if not SEMVER_TAG_RE.match(explicit_tag):
            raise ReleaseVideoError(
                f"Release tag must look like vN.N.N, got {explicit_tag!r}."
            )
        return explicit_tag
    return resolve_release_tag(repo, None)


def query_pds_release_video_status(
    args: argparse.Namespace,
    repo: Path,
    metadata: dict[str, Any],
    run_metadata_path: Path,
) -> dict[str, Any]:
    run_id = str(metadata.get("runId") or "").strip()
    if not run_id:
        raise ReleaseVideoError("Persisted PDS run metadata does not include runId.")
    command = split_command(args.pds_cli)
    ensure_command_exists(command[0], "PDS CLI")
    project_id = str(metadata.get("projectId") or "").strip()
    if project_id:
        command.extend(["--project", project_id])
    completed = run(
        [*command, "release-video", "status", "--run-id", run_id, "--json"],
        cwd=repo,
        timeout=None,
        check=False,
    )
    if completed.stdout.strip():
        print(redact_status_output_text(completed.stdout.rstrip()))
    if completed.stderr.strip():
        print(redact_status_output_text(completed.stderr.rstrip()), file=sys.stderr)
    if completed.returncode != 0:
        status_metadata = extract_pds_run_metadata(
            completed.stdout,
            completed.stderr,
            preferred_run_id=run_id,
        ) or {}
        if status_metadata_has_refresh_data(status_metadata, run_id):
            persist_status_query_success(
                metadata=metadata,
                path=run_metadata_path,
                completed=completed,
                pds_cli=args.pds_cli,
            )
        else:
            persist_status_query_failure(
                metadata=metadata,
                path=run_metadata_path,
                completed=completed,
                pds_cli=args.pds_cli,
            )
        message = (
            f"PDS release-video status failed: {redacted_process_details(completed)}"
        )
        hint = pds_failure_hint(
            completed,
            expected_run_id=run_id,
            allow_unscoped=False,
        )
        if hint:
            message += f" {hint}"
        raise ReleaseVideoError(message)
    return persist_status_query_success(
        metadata=metadata,
        path=run_metadata_path,
        completed=completed,
        pds_cli=args.pds_cli,
    )


def redact_status_output_text(text: str) -> str:
    """Redact PDS status output before it is shown in logs."""
    stripped = str(text or "").rstrip()
    if not stripped:
        return ""
    try:
        parsed = json.loads(stripped)
    except json.JSONDecodeError:
        return redact_secret_text(stripped)
    return json.dumps(redact_status_artifact_value(parsed), sort_keys=True)


def redacted_process_details(completed: subprocess.CompletedProcess[str]) -> str:
    return redact_secret_text(process_details(completed))


def persist_status_query_success(
    *,
    metadata: dict[str, Any],
    path: Path,
    completed: subprocess.CompletedProcess[str],
    pds_cli: str,
) -> dict[str, Any]:
    persisted_run_id = str(metadata.get("runId") or "").strip()
    persisted_project_id = str(metadata.get("projectId") or "").strip()
    response = extract_status_response(
        completed.stdout,
        completed.stderr,
        preferred_run_id=persisted_run_id or None,
    )
    refreshed = dict(metadata)
    status_metadata = extract_pds_run_metadata(
        completed.stdout,
        completed.stderr,
        preferred_run_id=persisted_run_id or None,
    ) or {}
    metadata_refreshed_status = status_metadata_has_refresh_data(
        status_metadata,
        persisted_run_id,
    )
    for key in ("runId", "projectId", "status", "attemptId"):
        value = status_metadata.get(key)
        if key == "runId" and persisted_run_id and value != persisted_run_id:
            continue
        if (
            key == "projectId"
            and persisted_project_id
            and value
            and value != persisted_project_id
        ):
            continue
        if value:
            refreshed[key] = value
    refreshed["statusStale"] = (
        False
        if metadata_refreshed_status
        else release_video_status_is_running(refreshed.get("status"))
    )
    refreshed["pdsContext"] = pds_context(pds_cli)
    refresh_pds_recovery_commands(refreshed, pds_cli)
    refreshed["lastStatusQuery"] = {
        "ok": True,
        "queriedAt": utc_now_iso(),
        "runId": refreshed.get("runId", ""),
        "runStatus": refreshed.get("status", ""),
        "pdsContext": refreshed["pdsContext"],
        "response": redact_status_artifact_value(
            response if response is not None else completed.stdout.strip()
        ),
    }
    refreshed = persistable_status_metadata(refreshed, pds_cli)
    write_json_file(path, refreshed)
    return refreshed


def persist_status_query_failure(
    *,
    metadata: dict[str, Any],
    path: Path,
    completed: subprocess.CompletedProcess[str],
    pds_cli: str,
) -> dict[str, Any]:
    response = extract_status_response(completed.stdout, completed.stderr)
    error = response.get("error") if isinstance(response, dict) else {}
    error = error if isinstance(error, dict) else {}
    pds_ctx = pds_context(pds_cli)
    refreshed = dict(metadata)
    refreshed["statusStale"] = release_video_status_is_running(refreshed.get("status"))
    refreshed["pdsContext"] = pds_ctx
    refresh_pds_recovery_commands(refreshed, pds_cli)
    refreshed["lastStatusQuery"] = {
        "ok": False,
        "queriedAt": utc_now_iso(),
        "exitCode": completed.returncode,
        "errorCode": first_nonempty_string(
            error.get("code"),
            response.get("code") if isinstance(response, dict) else None,
        ),
        "errorMessage": redact_secret_text(
            first_nonempty_string(
                error.get("message"),
                response.get("message") if isinstance(response, dict) else None,
            )
        ),
        "pdsContext": pds_ctx,
        "response": redact_status_artifact_value(
            response if response is not None else completed.stdout.strip()
        ),
        "details": redacted_process_details(completed),
    }
    refreshed = persistable_status_metadata(refreshed, pds_cli)
    write_json_file(path, refreshed)
    return refreshed


def persistable_status_metadata(
    metadata: dict[str, Any],
    pds_cli: str,
) -> dict[str, Any]:
    """Return a redacted sidecar with locally generated recovery commands."""
    refreshed = dict(metadata)
    refresh_pds_recovery_commands(refreshed, pds_cli)
    redacted = redact_status_artifact_value(refreshed)
    return redacted if isinstance(redacted, dict) else {}


def release_video_status_note(metadata: dict[str, Any]) -> str:
    if not release_video_status_is_running(metadata.get("status")):
        return ""
    if metadata.get("statusStale") is True:
        return (
            "create-time run metadata may be stale; refresh with "
            "make release-video-status RELEASE_TAG=<tag> RELEASE_VIDEO_STATUS_QUERY=1."
        )
    last_query = metadata.get("lastStatusQuery")
    if isinstance(last_query, dict) and last_query.get("ok") is True:
        return ""
    return (
        "create-time run metadata may be stale; refresh with "
        "make release-video-status RELEASE_TAG=<tag> RELEASE_VIDEO_STATUS_QUERY=1."
    )


def release_video_status_is_running(status: Any) -> bool:
    value = str(status or "").strip().lower()
    return value in RUNNING_PDS_STATUSES or (
        bool(value) and value not in TERMINAL_PDS_STATUSES
    )


def release_video_response_is_pending(response: dict[str, Any]) -> bool:
    """Return True when PDS create is still active and must be recovered later."""
    return response.get("pending") is True


def print_pending_release_video_response(response: dict[str, Any]) -> None:
    """Print operator recovery commands for a pending release video."""
    pds_run_value = response.get("pdsRun")
    pds_run = pds_run_value if isinstance(pds_run_value, dict) else {}
    project_id = first_nonempty_string(response.get("projectId"), pds_run.get("projectId"))
    run_id = first_nonempty_string(response.get("runId"), pds_run.get("runId"))
    status = first_nonempty_string(response.get("status"), pds_run.get("status")) or "unknown"

    print("release-video: PDS release-video create is still running; release video is pending.")
    identity_parts = []
    if project_id:
        identity_parts.append(f"projectId={project_id}")
    if run_id:
        identity_parts.append(f"runId={run_id}")
    identity_parts.append(f"status={status}")
    print(f"release-video: {' '.join(identity_parts)}")

    for label, key in (
        ("status", "statusCommand"),
        ("recover", "recoverCommand"),
        ("watch", "watchCommand"),
        ("backfill", "backfillCommand"),
    ):
        command = str(response.get(key) or "").strip()
        if command:
            print(f"{label}: {command}")


def pending_release_video_make_prefix(output_dir: Any) -> str:
    """Return a Make invocation prefix that preserves custom artifact roots."""
    output_dir_text = str(output_dir or "").strip()
    if not output_dir_text or output_dir_text == DEFAULT_RELEASE_VIDEO_OUTPUT_DIR:
        return "make"
    return f"make RELEASE_VIDEO_OUTPUT_DIR={shlex.quote(output_dir_text)}"


def pending_release_video_status_command(tag: str, output_dir: Any) -> str:
    """Return the Make target that refreshes persisted PDS run status."""
    return (
        f"{pending_release_video_make_prefix(output_dir)} "
        f"release-video-status RELEASE_TAG={shlex.quote(tag)} "
        "RELEASE_VIDEO_STATUS_QUERY=1"
    )


def pending_release_video_backfill_command(tag: str, output_dir: Any) -> str:
    """Return the Make target used after the pending run publishes to YouTube."""
    return (
        f"{pending_release_video_make_prefix(output_dir)} "
        "release-video-discord-backfill "
        f"RELEASE_TAG={shlex.quote(tag)} RELEASE_VIDEO_YOUTUBE_URL=<youtube-url>"
    )


def load_persisted_pds_run_metadata(path: Path | None) -> dict[str, Any]:
    """Load a persisted PDS run sidecar, returning an empty dict on failure."""
    if path is None:
        return {}
    try:
        raw = path.read_text(encoding="utf8")
    except OSError:
        return {}
    try:
        parsed = json.loads(raw)
    except json.JSONDecodeError:
        return {}
    return parsed if isinstance(parsed, dict) else {}


def pending_pds_create_response_from_sidecar(
    *,
    path: Path | None,
    tag: str,
    reason: str,
    message: str,
    output_dir: Any,
) -> dict[str, Any] | None:
    """Build a nonfatal pending response when sidecar status is still active."""
    metadata = load_persisted_pds_run_metadata(path)
    if not metadata or not release_video_status_is_running(metadata.get("status")):
        return None

    run_id = str(metadata.get("runId") or "").strip()
    project_id = str(metadata.get("projectId") or "").strip()
    status = str(metadata.get("status") or "").strip()
    response: dict[str, Any] = {
        "ok": False,
        "pending": True,
        "reason": reason,
        "message": redact_secret_text(message),
        "tag": tag,
        "status": status,
        "pdsRun": metadata,
        "statusCommand": pending_release_video_status_command(tag, output_dir),
        "backfillCommand": pending_release_video_backfill_command(tag, output_dir),
    }
    if run_id:
        response["runId"] = run_id
    if project_id:
        response["projectId"] = project_id
    for key in ("recoverCommand", "watchCommand"):
        command = str(metadata.get(key) or "").strip()
        if command:
            response[key] = command
    return response


def pds_create_has_project_exists_conflict(completed: subprocess.CompletedProcess[str]) -> bool:
    """Return True when PDS create failed because the release project exists."""
    combined = f"{completed.stderr}\n{completed.stdout}".lower()
    return (
        "release_video_existing_project_metadata_mismatch" in combined
        or "project-exists" in combined
        or "project exists" in combined
        or ("project" in combined and "already exists" in combined)
        or ("metadata" in combined and "conflict" in combined)
    )


def pds_create_has_timeout_failure(completed: subprocess.CompletedProcess[str]) -> bool:
    """Return True when PDS create failed through a timeout-shaped exit."""
    combined = f"{completed.stderr}\n{completed.stdout}".lower()
    return (
        completed.returncode == 124
        or "timed out" in combined
        or "timeout" in combined
        or "deadline exceeded" in combined
    )


def extract_status_response(
    *texts: str,
    preferred_run_id: str | None = None,
) -> Any:
    candidates: list[Any] = []
    for text in texts:
        candidates.extend(iter_json_values(text))
    if preferred_run_id:
        explicit_matches = [
            value
            for value in candidates
            if isinstance(value, dict)
            and response_pds_run_id(value) == preferred_run_id
        ]
        candidates = explicit_matches or [
            value
            for value in candidates
            if status_response_matches_run_id(value, preferred_run_id)
        ]
    if not candidates:
        return None
    terminal_candidates = [
        value
        for value in candidates
        if isinstance(value, dict)
        and status_value_is_terminal(value.get("status") or value.get("state"))
    ]
    return (terminal_candidates or candidates)[-1]


def status_response_matches_run_id(value: Any, run_id: str) -> bool:
    if not isinstance(value, dict):
        return True
    response_run_id = response_pds_run_id(value)
    return not response_run_id or response_run_id == run_id


def response_pds_run_id(value: dict[str, Any]) -> str:
    metadata = pds_run_metadata_from_mapping(value)
    if not metadata:
        nested = extract_primary_pds_run_metadata_from_json_value(value)
        metadata = select_pds_run_metadata(nested, distinct_run_policy="last")
    return str((metadata or {}).get("runId") or "").strip()


def status_metadata_has_refresh_data(
    metadata: dict[str, str],
    persisted_run_id: str,
) -> bool:
    if not metadata:
        return False
    run_id = str(metadata.get("runId") or "").strip()
    if run_id and persisted_run_id and run_id != persisted_run_id:
        return False
    return bool(str(metadata.get("status") or "").strip())


def status_value_is_terminal(status: Any) -> bool:
    value = str(status or "").strip().lower()
    return value in TERMINAL_PDS_STATUSES


def pds_context(pds_cli: str) -> dict[str, str]:
    context: dict[str, str] = {"pdsCli": redact_command_text(pds_cli)}
    api_url = os.environ.get("PDS_API_URL", "").strip()
    if api_url:
        context["apiUrl"] = redact_secret_text(api_url)
        context["apiUrlSource"] = "PDS_API_URL"
    else:
        context["apiUrlSource"] = "pds-default"

    profile = os.environ.get("PDS_PROFILE", "").strip()
    if profile:
        context["profile"] = profile
        context["profileSource"] = "PDS_PROFILE"
    elif os.environ.get("PDS_TOKEN", "").strip():
        context["profileSource"] = "cleared-or-token-auth"
    else:
        context["profileSource"] = "pds-config"

    if os.environ.get("PDS_TOKEN", "").strip():
        context["tokenSource"] = "PDS_TOKEN"
    elif os.environ.get("PDS_RELEASE_TOKEN", "").strip():
        context["tokenSource"] = "PDS_RELEASE_TOKEN"
    else:
        context["tokenSource"] = "pds-profile"

    if env_flag("GITHUB_ACTIONS"):
        context["executionContext"] = "github-actions"
    elif env_flag("CI"):
        context["executionContext"] = "ci"
    else:
        context["executionContext"] = "local"
    return context


def write_json_file(path: Path, value: Any) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(value, indent=2, sort_keys=True) + "\n", encoding="utf8")


def utc_now_iso() -> str:
    return (
        datetime.now(timezone.utc)
        .replace(microsecond=0)
        .isoformat()
        .replace("+00:00", "Z")
    )


def first_nonempty_string(*values: Any) -> str:
    for value in values:
        if isinstance(value, str) and value.strip():
            return value.strip()
    return ""


def redact_status_artifact_value(value: Any) -> Any:
    """Return a status value safe to persist in durable release artifacts."""
    if isinstance(value, dict):
        redacted: dict[str, Any] = {}
        for key, nested in value.items():
            if is_sensitive_artifact_field(key):
                redacted[key] = "[redacted]"
            else:
                redacted[key] = redact_status_artifact_value(nested)
        return redacted
    if isinstance(value, list):
        return [redact_status_artifact_value(item) for item in value]
    if isinstance(value, str):
        return redact_secret_text(value)
    return value


def is_sensitive_artifact_field(key: Any) -> bool:
    normalized = re.sub(r"[^a-z0-9]+", "", str(key).lower())
    if normalized in {"tokensource", "profilesource", "apiurlsource"}:
        return False
    if normalized in SENSITIVE_FIELD_NAMES:
        return True
    return normalized.endswith(
        (
            "token",
            "secret",
            "credential",
            "signature",
            "accesskey",
            "accesskeyid",
            "apikey",
            "password",
            "signedurl",
            "sig",
        )
    )


def redact_secret_text(text: str) -> str:
    redacted = str(text or "")
    stripped = redacted.strip()
    if stripped.startswith(("{", "[")):
        try:
            parsed = json.loads(stripped)
        except json.JSONDecodeError:
            pass
        else:
            if isinstance(parsed, (dict, list)):
                return json.dumps(redact_status_artifact_value(parsed), sort_keys=True)
    redacted = redact_json_values_in_text(redacted)
    redacted = re.sub(
        r"(?i)\b(https?://)[^/\s:@]+:[^/\s@]+@",
        r"\1[redacted]@",
        redacted,
    )
    redacted = re.sub(
        r"(?im)^([ \t]*authorization\s*:\s*).+$",
        r"\1[redacted]",
        redacted,
    )
    redacted = re.sub(
        r"(?i)([\"']?\bauthorization[\"']?\s*[:=]\s*[\"']?)[^\"'\n;}]+",
        r"\1[redacted]",
        redacted,
    )
    redacted = re.sub(
        r"(?i)(\bbearer\s+)[^\s\"'\\,;]+",
        r"\1[redacted]",
        redacted,
    )
    redacted = re.sub(
        (
            r"(?i)([?&](?:access[_-]?token|token|api[_-]?key|secret|"
            r"signature|sig|x-amz-credential|x-amz-security-token|"
            r"x-amz-signature)=)"
            r"[^&\s\"'<>]+"
        ),
        r"\1[redacted]",
        redacted,
    )
    redacted = redact_sensitive_key_value_text(redacted)
    redacted = redact_sensitive_command_option_text(redacted)
    redacted = re.sub(
        (
            r"(?i)([\"']?(?:access[_-]?token|api[_-]?key|"
            r"auth[_-]?token|client[_-]?secret|"
            r"credential|password|refresh[_-]?token|secret|"
            r"signed[_-]?url|token)[\"']?\s*[:=]\s*[\"']?)[^\"'\s,;}]+"
        ),
        r"\1[redacted]",
        redacted,
    )
    redacted = re.sub(
        r"(?i)(\b(?:authorization|credential)\s+)[^\s\"'\\,;]+",
        r"\1[redacted]",
        redacted,
    )
    return redacted


def redact_sensitive_key_value_text(text: str) -> str:
    """Redact arbitrary diagnostic key=value or key: value secret fields."""

    def replace(match: re.Match[str]) -> str:
        key = match.group("key")
        if is_sensitive_artifact_field(key):
            return f"{match.group('prefix')}[redacted]"
        return match.group(0)

    return re.sub(
        (
            r"(?i)(?P<prefix>(?<![a-z0-9_.-])[\"']?"
            r"(?P<key>[a-z_][a-z0-9_.-]{0,80})[\"']?\s*[:=]\s*[\"']?)"
            r"(?P<value>[^&\"'\s,;}]+)"
        ),
        replace,
        text,
    )


def redact_sensitive_command_option_text(text: str) -> str:
    """Redact command option values from unstructured diagnostic text."""

    def replace(match: re.Match[str]) -> str:
        option = match.group("option")
        if is_sensitive_command_option(option):
            return (
                f"{match.group('prefix')}{option}"
                f"{match.group('separator')}[redacted]"
            )
        return match.group(0)

    redacted = re.sub(
        (
            r"(?i)(?P<prefix>^|\s)(?P<option>--[a-z0-9][a-z0-9-]*)"
            r"(?P<separator>\s+)(?P<value>[^\s\"'\\,;]+)"
        ),
        replace,
        text,
    )
    return re.sub(
        (
            r"(?i)(?P<prefix>^|\s)(?P<option>--[a-z0-9][a-z0-9-]*)"
            r"(?P<separator>=)(?P<value>[^\s\"'\\,;]+)"
        ),
        replace,
        redacted,
    )


def redact_json_values_in_text(text: str) -> str:
    pieces: list[str] = []
    last_index = 0
    for value, start, end in iter_json_value_spans(text):
        pieces.append(text[last_index:start])
        pieces.append(json.dumps(redact_status_artifact_value(value), sort_keys=True))
        last_index = end
    if not pieces:
        return text
    pieces.append(text[last_index:])
    return "".join(pieces)


def is_sensitive_command_option(option: str) -> bool:
    if not option.startswith("-"):
        return False
    normalized = re.sub(r"[^a-z0-9]+", "", option.lstrip("-").lower())
    return (
        normalized in {"authorization", "password"}
        or any(
            marker in normalized
            for marker in (
                "token",
                "secret",
                "credential",
                "signature",
                "apikey",
                "accesskey",
                "password",
                "authorization",
            )
        )
    )


def redact_command_text(command: str) -> str:
    try:
        parts = shlex.split(command)
    except ValueError:
        return redact_secret_text(command)
    if not parts:
        return command
    redacted: list[str] = []
    redact_next = False
    for part in parts:
        option, has_equals, _value = part.partition("=")
        if redact_next:
            redacted.append("[redacted]")
            redact_next = False
            continue
        if (
            option.lower() in SENSITIVE_COMMAND_OPTIONS
            or is_sensitive_command_option(option)
        ) and has_equals:
            redacted.append(f"{option}=[redacted]")
            continue
        redacted.append(part)
        if part.lower() in SENSITIVE_COMMAND_OPTIONS or is_sensitive_command_option(part):
            redact_next = True
    return redact_secret_text(shlex.join(redacted))


def preflight_release_video(args: argparse.Namespace) -> int:
    """Warn about local PDS profile shapes that are likely to fail a release."""
    if os.environ.get("RELEASE_VIDEO", "").strip() == "0":
        print("release-video preflight: skipped because RELEASE_VIDEO=0.")
        return 0

    preflight_pds_cli(args, Path(args.repo).resolve())

    project_id = str(args.project_id or "").strip()
    if project_id:
        print(f"release-video preflight: using explicit PDS project {project_id}.")

    if os.environ.get("PDS_TOKEN", "").strip():
        if project_id:
            print(
                "release-video preflight: PDS_TOKEN is set for explicit PDS "
                f"project {project_id}; local preflight cannot verify token "
                "scopes or access to that fixed project unless the PDS server "
                "preflight is run."
            )
        else:
            print(
                "release-video preflight: PDS_TOKEN is set; local preflight "
                "cannot verify token scopes or project access unless the PDS "
                "server preflight is run. Normal create-mode creates a new "
                "per-release project, so the token must create that project "
                "and continue accessing it afterward (or use a backend "
                "fix/wildcard token)."
            )
        return 0

    if project_id:
        return 0

    config_path = pds_config_path()
    config = read_pds_config(config_path)
    if not config:
        print(
            "release-video preflight: no local PDS profile found; set PDS_TOKEN "
            "for CI-like release credentials."
        )
        return 0

    profile_name = str(
        os.environ.get("PDS_PROFILE", "").strip()
        or config.get("currentProfile", "")
        or "default"
    )
    profiles = config.get("profiles")
    profile = profiles.get(profile_name, {}) if isinstance(profiles, dict) else {}
    if not isinstance(profile, dict):
        profile = {}
    profile_project_id = str(profile.get("projectId") or "").strip()

    if profile_project_id:
        print(
            "release-video preflight warning: active local PDS profile "
            f"{profile_name!r} is pinned to project {profile_project_id!r}. "
            "Normal create-mode releases create a new per-release project and "
            "require credentials that can create that project and continue "
            "accessing it afterward. The profile token may fail with "
            "\"PDS agent token is not allowed for this project\". Local "
            "preflight cannot verify server-side scopes unless the PDS server "
            "preflight is run. Use a release-scoped PDS_TOKEN/PDS_PROFILE, a "
            "backend fix/wildcard token, RELEASE_VIDEO_PROJECT_ID for an "
            "authorized fixed project, or RELEASE_VIDEO=0 for recovery.",
            file=sys.stderr,
        )
        return 0

    print(
        f"release-video preflight: active local PDS profile {profile_name!r} "
        "has no fixed project id. Local preflight still cannot prove the "
        "token can create and continue accessing a release project; run the "
        "PDS server preflight for authoritative validation."
    )
    return 0


def pds_config_path() -> Path:
    config_home = os.environ.get("XDG_CONFIG_HOME", "").strip()
    if config_home:
        return Path(config_home) / "pds" / "config.json"
    return Path.home() / ".config" / "pds" / "config.json"


def read_pds_config(path: Path) -> dict[str, Any]:
    try:
        parsed = json.loads(path.read_text(encoding="utf8"))
    except (OSError, json.JSONDecodeError):
        return {}
    return parsed if isinstance(parsed, dict) else {}


def preflight_pds_cli(args: argparse.Namespace, repo: Path) -> None:
    """Print and validate the PDS CLI command used by release-video."""
    redacted_command = redact_command_text(str(args.pds_cli or ""))
    print(f"release-video preflight: PDS CLI command: {redacted_command}")

    version, diagnostic = probe_pds_cli_version(str(args.pds_cli or ""), repo)
    if diagnostic:
        raise ReleaseVideoError(
            "release-video preflight: could not determine PDS CLI version: "
            f"{diagnostic}. Use @promptdriven/pds@{MIN_PDS_CLI_VERSION_TEXT} "
            f"or newer. Command: {redacted_command}"
        )
    if version is None:
        raise ReleaseVideoError(
            "release-video preflight: could not determine PDS CLI version.",
        )

    print(f"release-video preflight: PDS CLI version: {version}")
    if pds_cli_version_tuple(version) < MIN_PDS_CLI_VERSION:
        raise ReleaseVideoError(
            f"PDS CLI {version} is older than required "
            f"{MIN_PDS_CLI_VERSION_TEXT}. Use @promptdriven/pds@"
            f"{MIN_PDS_CLI_VERSION_TEXT} or newer. Command: {redacted_command}"
        )


def probe_pds_cli_version(
    pds_cli: str,
    repo: Path,
) -> tuple[str | None, str | None]:
    """Return the PDS CLI semantic version, or a redacted diagnostic."""
    command = split_command(pds_cli)
    if not command:
        return None, "PDS_CLI is empty"
    try:
        ensure_command_exists(command[0], "PDS CLI")
        completed = run(
            [*command, "--version"],
            cwd=repo,
            timeout=PDS_VERSION_PROBE_TIMEOUT_SECONDS,
            check=False,
        )
    except ReleaseVideoError as exc:
        return None, redact_secret_text(str(exc))

    combined = "\n".join(
        part.strip()
        for part in (completed.stdout, completed.stderr)
        if part and part.strip()
    )
    if completed.returncode != 0:
        return None, redacted_process_details(completed)
    version = extract_pds_cli_version(combined)
    if not version:
        diagnostic = truncate(redact_secret_text(combined), 300) or "empty output"
        return None, f"could not parse --version output: {diagnostic}"
    return version, None


def extract_pds_cli_version(text: str) -> str | None:
    """Extract the first semantic version from PDS CLI version output."""
    match = PDS_VERSION_RE.search(text)
    if not match:
        return None
    return match.group("version")


def pds_cli_version_tuple(version: str) -> tuple[int, int, int]:
    """Return a comparable major/minor/patch tuple for a PDS CLI version."""
    match = PDS_VERSION_RE.search(version)
    if not match:
        return (0, 0, 0)
    major, minor, patch = match.group("version").split(".")
    return (int(major), int(minor), int(patch))


def run(
    command: list[str],
    *,
    cwd: Path,
    input_text: str | None = None,
    timeout: float | None = None,
    env: dict[str, str] | None = None,
    check: bool = True,
) -> subprocess.CompletedProcess[str]:
    rendered_command = redact_command_text(shlex.join(command))
    try:
        completed = subprocess.run(
            command,
            cwd=str(cwd),
            env=env,
            input=input_text,
            text=True,
            capture_output=True,
            timeout=timeout,
            check=False,
        )
    except subprocess.TimeoutExpired as exc:
        timeout_text = f"{timeout:g}" if timeout is not None else "unknown"
        completed = subprocess.CompletedProcess(
            command,
            124,
            stdout=timeout_output_text(getattr(exc, "stdout", None)),
            stderr=timeout_output_text(getattr(exc, "stderr", None)),
        )
        raise ReleaseVideoProcessTimeout(
            f"{rendered_command} timed out after {timeout_text} seconds",
            completed=completed,
            timeout=timeout,
        ) from exc
    except FileNotFoundError as exc:
        raise ReleaseVideoError(f"Executable not found: {command[0]}") from exc
    if check and completed.returncode != 0:
        stderr = completed.stderr.strip()
        stdout = completed.stdout.strip()
        details = stderr or stdout or f"exit code {completed.returncode}"
        raise ReleaseVideoError(
            f"{rendered_command} failed: {redact_secret_text(details[:2000])}"
        )
    return completed


def timeout_output_text(output: str | bytes | None) -> str:
    """Return captured timeout output as text for metadata extraction."""
    if output is None:
        return ""
    if isinstance(output, bytes):
        return output.decode("utf8", errors="replace")
    return str(output)


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


def generate_raw_script_with_claude(
    *,
    context: str,
    claude_cli: str,
    claude_model: str,
    claude_tools: str,
    prompt_template: Path,
    timeout: float,
    cwd: Path,
) -> str:
    claude_model = str(claude_model or "").strip()
    if not claude_model:
        raise ReleaseVideoError(
            "Claude Code script-generation model must not be empty. "
            "Set RELEASE_VIDEO_CLAUDE_MODEL, CLAUDE_MODEL, or --claude-model "
            "to a non-empty value."
        )
    command = split_command(claude_cli)
    ensure_command_exists(command[0], "Claude Code")
    command.extend(
        [
            "-p",
            "--model",
            claude_model,
            "--no-session-persistence",
            "--output-format",
            "text",
        ]
    )
    if claude_tools.strip():
        command.extend(["--allowedTools", claude_tools.strip()])
    prompt = render_release_video_prompt(context, prompt_template, cwd)
    claude_env = os.environ.copy()
    strip_anthropic_creds_for_claude_subprocess(claude_env)

    token_attempts = claude_oauth_token_attempts(claude_env)
    attempts: list[tuple[str | None, dict[str, str]]] = []
    if token_attempts:
        for token_name, token in token_attempts:
            attempt_env = claude_env.copy()
            attempt_env["CLAUDE_CODE_OAUTH_TOKEN"] = token
            attempts.append((token_name, attempt_env))
    else:
        attempts.append((None, claude_env))

    failed_quota_auth_slots: list[str] = []
    for attempt_label, attempt_env in attempts:
        try:
            completed = run(
                command,
                cwd=cwd,
                input_text=prompt,
                timeout=timeout,
                env=attempt_env,
                check=False,
            )
        except ReleaseVideoError as exc:
            raise ReleaseVideoError(
                "Claude Code script generation failed before PDS publish; "
                f"PDS was not invoked. {exc}"
            ) from exc
        if completed.returncode == 0:
            break

        classification = classify_claude_quota_auth_failure(
            "\n".join(
                text for text in (completed.stderr.strip(), completed.stdout.strip()) if text
            )
        )
        if attempt_label and classification:
            failed_quota_auth_slots.append(f"{attempt_label}:{classification}")
            print(
                "release-video: Claude Code OAuth token slot "
                f"{attempt_label} failed with quota/auth class {classification!r}; "
                "trying next token.",
                file=sys.stderr,
            )
            continue

        raise ReleaseVideoError(
            format_claude_script_generation_failure(command, completed, attempt_label)
        )
    else:
        failed = ", ".join(failed_quota_auth_slots) or "none"
        raise ReleaseVideoError(
            "Claude Code script generation failed before PDS publish; PDS was not invoked. "
            f"All configured Claude Code OAuth token slots failed ({failed}). "
            "Set a fresh CLAUDE_CODE_OAUTH_TOKEN_1/2/3 secret or use "
            "RELEASE_VIDEO_SCRIPT_PATH pointing at a previously generated script."
        )

    return completed.stdout


def generate_script_with_claude(
    *,
    context: str,
    claude_cli: str,
    claude_model: str,
    claude_tools: str,
    prompt_template: Path,
    timeout: float,
    cwd: Path,
) -> str:
    raw_script = generate_raw_script_with_claude(
        context=context,
        claude_cli=claude_cli,
        claude_model=claude_model,
        claude_tools=claude_tools,
        prompt_template=prompt_template,
        timeout=timeout,
        cwd=cwd,
    )
    artifacts = prepare_release_video_script(raw_script, source="claude")
    if artifacts["validation"]["errors"]:
        errors = ", ".join(artifacts["validation"]["errors"])
        raise ReleaseVideoError(
            "release-video script validation failed before PDS publish; "
            f"PDS was not invoked. Failing checks: {errors}."
        )
    return artifacts["script"]


def claude_oauth_token_attempts(env: dict[str, str]) -> list[tuple[str, str]]:
    attempts: list[tuple[str, str]] = []
    seen: set[str] = set()
    for name in CLAUDE_OAUTH_TOKEN_ENV_VARS:
        token = env.get(name, "").strip()
        if not token or token in seen:
            continue
        attempts.append((name, token))
        seen.add(token)
    return attempts


def strip_anthropic_creds_for_claude_subprocess(env: dict[str, str]) -> bool:
    """Keep release-video Claude generation on OAuth when both auth paths exist."""
    if env.get("CLAUDE_CODE_USE_BEDROCK") or env.get("CLAUDE_CODE_USE_VERTEX"):
        return False

    if (env.get("PDD_KEEP_ANTHROPIC_API_KEY") or "").strip().lower() in {
        "1",
        "true",
        "yes",
        "on",
    }:
        return False

    if not (env.get("ANTHROPIC_API_KEY") or env.get("ANTHROPIC_AUTH_TOKEN")):
        return False

    if claude_oauth_token_attempts(env):
        env.pop("ANTHROPIC_API_KEY", None)
        env.pop("ANTHROPIC_AUTH_TOKEN", None)
        return True

    try:
        if str(REPO_ROOT) not in sys.path:
            sys.path.insert(0, str(REPO_ROOT))
        from pdd.agentic_common import _strip_anthropic_creds_for_claude_subprocess
    except ModuleNotFoundError:
        return False

    return _strip_anthropic_creds_for_claude_subprocess(env, quiet=True)


def classify_claude_quota_auth_failure(output: str) -> str | None:
    msg = output.lower()
    for classification, patterns in CLAUDE_FAILURE_CLASSES:
        if any(re.search(pattern, msg) for pattern in patterns):
            return classification
    return None


def format_claude_script_generation_failure(
    command: list[str],
    completed: subprocess.CompletedProcess[str],
    attempt_label: str | None = None,
) -> str:
    combined_output = "\n".join(
        text for text in (completed.stderr.strip(), completed.stdout.strip()) if text
    )
    classification = classify_claude_quota_auth_failure(combined_output)
    message = (
        "Claude Code script generation failed before PDS publish "
        f"(exit {completed.returncode}); PDS was not invoked."
    )
    if classification:
        message += (
            f" Detected Claude Code quota/auth class {classification!r}; "
            "check Claude Code auth/subscription state or retry with "
            "RELEASE_VIDEO_SCRIPT_PATH pointing at a previously generated script."
        )
    else:
        message += " This is a script-generation failure, not a PDS publish failure."
    if attempt_label:
        message += f" OAuth token slot: {attempt_label}."
    return f"{message} Command: {shlex.join(command)}. Details: {process_details(completed)}"


def process_details(completed: subprocess.CompletedProcess[str]) -> str:
    details: list[str] = []
    stderr = completed.stderr.strip()
    stdout = completed.stdout.strip()
    if stderr:
        details.append(f"stderr: {truncate(redact_secret_text(stderr), 1200)}")
    if stdout:
        details.append(f"stdout: {truncate(redact_secret_text(stdout), 1200)}")
    if not details:
        details.append(f"exit code {completed.returncode}")
    return " | ".join(details)


def load_release_video_script(script_path: Path, cwd: Path) -> tuple[str, Path]:
    raw_script, path = load_release_video_script_raw(script_path, cwd)
    artifacts = prepare_release_video_script(raw_script, source=str(path))
    if artifacts["validation"]["errors"]:
        errors = ", ".join(artifacts["validation"]["errors"])
        raise ReleaseVideoError(
            f"Release-video script override {path} failed validation: {errors}."
        )
    return artifacts["script"], path


def load_release_video_script_raw(script_path: Path, cwd: Path) -> tuple[str, Path]:
    path = resolve_release_video_script_path(script_path, cwd)
    try:
        raw_script = path.read_text(encoding="utf8")
    except OSError as exc:
        raise ReleaseVideoError(f"Could not read release-video script {path}: {exc}") from exc
    return raw_script, path


def load_release_video_release_notes(release_notes_path: Path, cwd: Path) -> tuple[str, Path]:
    """Load a prewritten release-notes artifact for selected-project recovery."""
    path = resolve_release_video_release_notes_path(release_notes_path, cwd)
    try:
        release_notes = path.read_text(encoding="utf8")
    except OSError as exc:
        raise ReleaseVideoError(
            f"Could not read release-video release notes {path}: {exc}"
        ) from exc
    return release_notes, path


def resolve_release_video_script_path(script_path: Path, cwd: Path) -> Path:
    if script_path.is_absolute():
        if script_path.exists():
            return script_path
        raise ReleaseVideoError(f"Release-video script override not found: {script_path}")
    candidates = [
        cwd / script_path,
        REPO_ROOT / script_path,
    ]
    for candidate in candidates:
        if candidate.exists():
            return candidate.resolve()
    tried = "\n".join(str(candidate) for candidate in candidates)
    raise ReleaseVideoError(f"Release-video script override not found. Tried:\n{tried}")


def resolve_release_video_release_notes_path(release_notes_path: Path, cwd: Path) -> Path:
    if release_notes_path.is_absolute():
        if release_notes_path.exists():
            return release_notes_path
        raise ReleaseVideoError(
            f"Release-video release notes override not found: {release_notes_path}"
        )
    candidates = [
        cwd / release_notes_path,
        REPO_ROOT / release_notes_path,
    ]
    for candidate in candidates:
        if candidate.exists():
            return candidate.resolve()
    tried = "\n".join(str(candidate) for candidate in candidates)
    raise ReleaseVideoError(
        f"Release-video release notes override not found. Tried:\n{tried}"
    )


def render_release_video_prompt(context: str, prompt_template: Path, cwd: Path) -> str:
    path = resolve_prompt_template_path(prompt_template, cwd)
    try:
        template = path.read_text(encoding="utf8")
    except OSError as exc:
        raise ReleaseVideoError(f"Could not read release-video prompt template {path}: {exc}") from exc
    if "{release_context}" not in template:
        raise ReleaseVideoError(
            f"Release-video prompt template {path} must contain {{release_context}}."
        )
    return template.replace("{release_context}", context)


def resolve_prompt_template_path(prompt_template: Path, cwd: Path) -> Path:
    if prompt_template.is_absolute():
        if prompt_template.exists():
            return prompt_template
        raise ReleaseVideoError(f"Release-video prompt template not found: {prompt_template}")
    candidates = [
        cwd / prompt_template,
        REPO_ROOT / prompt_template,
    ]
    for candidate in candidates:
        if candidate.exists():
            return candidate.resolve()
    tried = "\n".join(str(candidate) for candidate in candidates)
    raise ReleaseVideoError(f"Release-video prompt template not found. Tried:\n{tried}")


def pds_create_process_timeout(args: argparse.Namespace) -> float | None:
    """Return the configured PDS create subprocess timeout."""
    timeout = float(
        getattr(args, "pds_create_timeout", DEFAULT_PDS_CREATE_TIMEOUT_SECONDS)
    )
    return timeout if timeout > 0 else None


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
    run_metadata_path: Path,
) -> dict[str, Any]:
    command = split_command(args.pds_cli)
    ensure_command_exists(command[0], "PDS CLI")
    project_id = str(args.project_id or "").strip()
    if project_id:
        command.extend(["--project", project_id])
    project_name = args.project_name or ("" if project_id else f"PDD {tag} release")
    idempotency_key = release_video_idempotency_key(
        tag=tag,
        git_sha=git_sha,
        full_key=args.idempotency_key,
        attempt_id=args.idempotency_attempt_id,
        provenance=args.idempotency_provenance,
    )
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
    add_optional_pds_create_args(
        pds_args,
        args,
        repo,
        changelog_path,
    )

    try:
        completed = run(
            command + pds_args,
            cwd=repo,
            timeout=pds_create_process_timeout(args),
            check=False,
        )
    except ReleaseVideoProcessTimeout as exc:
        persisted_run_metadata_path = persist_timed_out_pds_run_metadata(
            timeout=exc,
            path=run_metadata_path,
            args=args,
            tag=tag,
            idempotency_key=idempotency_key,
            project_id=project_id,
        )
        message = str(exc)
        if persisted_run_metadata_path:
            print(
                f"release-video: persisted PDS run metadata to {persisted_run_metadata_path}",
                file=sys.stderr,
            )
            message += f" PDS run metadata saved to {persisted_run_metadata_path}."
        pending_response = pending_pds_create_response_from_sidecar(
            path=persisted_run_metadata_path,
            tag=tag,
            reason="pds_create_timeout_active_run",
            message=message,
            output_dir=getattr(args, "output_dir", DEFAULT_RELEASE_VIDEO_OUTPUT_DIR),
        )
        if pending_response:
            return pending_response
        raise ReleaseVideoError(message) from exc
    persisted_run_metadata_path = persist_pds_run_metadata_from_output(
        completed=completed,
        path=run_metadata_path,
        pds_cli=args.pds_cli,
        tag=tag,
        idempotency_key=idempotency_key,
        attempt_id=args.idempotency_attempt_id,
        provenance=release_video_idempotency_provenance(args.idempotency_provenance),
        project_id=project_id,
    )
    if persisted_run_metadata_path:
        print(
            f"release-video: persisted PDS run metadata to {persisted_run_metadata_path}",
            file=sys.stderr,
        )
    if completed.returncode != 0:
        rendered_command = redact_command_text(shlex.join(command + pds_args))
        message = (
            f"{rendered_command} failed: "
            f"{process_details(completed)}"
        )
        persisted_metadata = load_persisted_pds_run_metadata(
            persisted_run_metadata_path
        )
        persisted_run_id = str(persisted_metadata.get("runId") or "").strip()
        hint = pds_failure_hint(
            completed,
            expected_run_id=persisted_run_id or None,
            allow_unscoped=not bool(persisted_run_id),
        )
        if hint:
            message += f" {hint}"
        if persisted_run_metadata_path:
            message += f" PDS run metadata saved to {persisted_run_metadata_path}."
        is_timeout_failure = pds_create_has_timeout_failure(completed)
        is_project_exists_conflict = pds_create_has_project_exists_conflict(completed)
        if is_timeout_failure or is_project_exists_conflict:
            reason = (
                "pds_create_timeout_active_run"
                if is_timeout_failure
                else "pds_create_project_exists_active_run"
            )
            pending_response = pending_pds_create_response_from_sidecar(
                path=persisted_run_metadata_path,
                tag=tag,
                reason=reason,
                message=message,
                output_dir=getattr(args, "output_dir", DEFAULT_RELEASE_VIDEO_OUTPUT_DIR),
            )
            if pending_response:
                return pending_response
        raise ReleaseVideoError(message)
    try:
        parsed = parse_pds_create_response(completed.stdout)
    except ReleaseVideoError as exc:
        message = str(exc)
        if persisted_run_metadata_path:
            message += f" PDS run metadata saved to {persisted_run_metadata_path}."
        raise ReleaseVideoError(message) from exc
    return parsed


def add_optional_pds_create_args(
    pds_args: list[str],
    args: argparse.Namespace,
    repo: Path,
    changelog_path: Path,
) -> None:
    """Append optional PDS release-video create flags in-place."""
    pds_args.extend(RELEASE_VIDEO_AUDIT_FIX_POLICY_ARGS)
    changelog_full_path = repo / changelog_path
    if changelog_full_path.exists():
        pds_args.extend(["--changelog", str(changelog_full_path)])
    if args.bootstrap_selected_project:
        pds_args.append("--bootstrap-selected-project")
    metadata_conflict = release_video_metadata_conflict(args)
    if metadata_conflict:
        pds_args.extend(["--metadata-conflict", metadata_conflict])
    pds_claude_model = str(getattr(args, "pds_claude_model", "") or "").strip()
    if pds_claude_model:
        pds_args.extend(["--claude-model", pds_claude_model])
    if args.force_regenerate:
        pds_args.append("--force-regenerate")
    if args.dry_run:
        pds_args.append("--dry-run")


def persist_timed_out_pds_run_metadata(
    *,
    timeout: ReleaseVideoProcessTimeout,
    path: Path,
    args: argparse.Namespace,
    tag: str,
    idempotency_key: str,
    project_id: str | None,
) -> Path | None:
    """Persist a PDS run sidecar from partial output captured on timeout."""
    return persist_pds_run_metadata_from_output(
        completed=timeout.completed,
        path=path,
        pds_cli=args.pds_cli,
        tag=tag,
        idempotency_key=idempotency_key,
        attempt_id=args.idempotency_attempt_id,
        provenance=release_video_idempotency_provenance(args.idempotency_provenance),
        project_id=project_id,
    )


def parse_pds_create_response(stdout: str) -> dict[str, Any]:
    stripped = str(stdout or "").strip()
    parse_error: json.JSONDecodeError | None = None
    if stripped:
        try:
            parsed = json.loads(stripped)
        except json.JSONDecodeError as exc:
            parse_error = exc
        else:
            if isinstance(parsed, dict):
                return parsed
            raise ReleaseVideoError("PDS CLI returned JSON that was not an object.")

    embedded_objects = [
        value for value in iter_json_values(stripped) if isinstance(value, dict)
    ]
    if embedded_objects:
        for value in reversed(embedded_objects):
            if find_youtube_url(value):
                return value
        return embedded_objects[-1]

    output = truncate(redact_secret_text(stripped), 2000)
    if parse_error:
        raise ReleaseVideoError(
            f"PDS CLI did not return JSON: {parse_error}. Output: {output}"
        ) from parse_error
    raise ReleaseVideoError(f"PDS CLI did not return JSON. Output: {output}")


def release_video_idempotency_key(
    *,
    tag: str,
    git_sha: str,
    full_key: str | None,
    attempt_id: str | None,
    provenance: str | None,
) -> str:
    full_key = str(full_key or "").strip()
    attempt_id = str(attempt_id or "").strip()
    if full_key and attempt_id:
        raise ReleaseVideoError(
            "Use either a full release-video idempotency key or an attempt id, not both."
        )

    if full_key:
        return full_key
    default_key = (
        f"pdd-release-video:{tag}:{git_sha}:"
        f"{release_video_idempotency_provenance(provenance)}"
    )
    if attempt_id:
        return f"{default_key}:retry-{attempt_id}"
    return default_key


def release_video_idempotency_provenance(explicit_provenance: str | None) -> str:
    provenance = str(explicit_provenance or "").strip()
    if not provenance:
        if env_flag("GITHUB_ACTIONS"):
            provenance = "github-actions"
        elif env_flag("CI"):
            provenance = "ci"
        else:
            provenance = "local"
    sanitized = IDEMPOTENCY_PROVENANCE_RE.sub("-", provenance.lower()).strip("-._")
    return sanitized or "local"


def persist_pds_run_metadata_from_output(
    *,
    completed: subprocess.CompletedProcess[str],
    path: Path,
    pds_cli: str,
    tag: str,
    idempotency_key: str,
    attempt_id: str | None,
    provenance: str,
    project_id: str | None,
) -> Path | None:
    metadata = extract_pds_run_metadata(completed.stdout, completed.stderr)
    if not metadata:
        return None
    metadata = enrich_pds_run_metadata(
        metadata,
        pds_cli=pds_cli,
        tag=tag,
        idempotency_key=idempotency_key,
        attempt_id=attempt_id,
        provenance=provenance,
        project_id=project_id,
    )
    write_json_file(path, metadata)
    return path


def extract_pds_run_metadata(
    *texts: str,
    preferred_run_id: str | None = None,
) -> dict[str, str] | None:
    primary_metadata: list[dict[str, str]] = []
    json_metadata: list[dict[str, str]] = []
    compat_metadata: list[dict[str, str]] = []
    for text in texts:
        primary_metadata.extend(extract_primary_pds_run_metadata_from_json_text(text))
        json_metadata.extend(extract_all_pds_run_metadata_from_json_text(text))
        metadata = extract_pds_run_metadata_from_compat_lines(text)
        if metadata:
            compat_metadata.append(metadata)
    if preferred_run_id:
        for candidates in (primary_metadata, json_metadata, compat_metadata):
            preferred = [
                metadata
                for metadata in merge_pds_run_metadata_candidates(candidates)
                if metadata.get("runId") == preferred_run_id
            ]
            if preferred:
                return select_pds_run_metadata(preferred, distinct_run_policy="last")
        if primary_metadata or json_metadata or compat_metadata:
            return None
    if primary_metadata:
        return select_pds_run_metadata(primary_metadata, distinct_run_policy="last")
    if json_metadata:
        return select_pds_run_metadata(json_metadata, distinct_run_policy="first")
    if compat_metadata:
        return select_pds_run_metadata(compat_metadata, distinct_run_policy="last")
    return None


def extract_primary_pds_run_metadata_from_json_text(text: str) -> list[dict[str, str]]:
    values: list[dict[str, str]] = []
    for value in iter_json_values(text):
        values.extend(extract_primary_pds_run_metadata_from_json_value(value))
    return values


def extract_primary_pds_run_metadata_from_json_value(value: Any) -> list[dict[str, str]]:
    if isinstance(value, dict):
        metadata = pds_run_metadata_from_mapping(value)
        if metadata:
            return [metadata]
        values: list[dict[str, str]] = []
        for key in ("result", "current", "currentRun", "latest", "data"):
            nested = value.get(key)
            for nested_metadata in extract_primary_pds_run_metadata_from_json_value(nested):
                values.append(add_parent_pds_context(nested_metadata, value))
        return values
    if isinstance(value, list):
        values: list[dict[str, str]] = []
        for nested in value:
            if isinstance(nested, dict):
                metadata = pds_run_metadata_from_mapping(nested)
                if metadata:
                    values.append(metadata)
        return values
    return []


def add_parent_pds_context(
    metadata: dict[str, str],
    parent: dict[str, Any],
) -> dict[str, str]:
    enriched = dict(metadata)
    project_value = parent.get("project")
    project = project_value if isinstance(project_value, dict) else {}
    project_id = first_string(parent, "projectId", "project_id") or first_string(
        project,
        "projectId",
        "project_id",
        "id",
    )
    nested_run_id = str(enriched.get("runId") or "").strip()
    if project_id and nested_run_id and "projectId" not in enriched:
        enriched["projectId"] = project_id
    return enriched


def select_pds_run_metadata(
    candidates: list[dict[str, str]],
    *,
    distinct_run_policy: str,
) -> dict[str, str] | None:
    merged = merge_pds_run_metadata_candidates(candidates)
    if not merged:
        return None
    run_ids = {metadata.get("runId", "") for metadata in merged if metadata.get("runId")}
    if len(run_ids) <= 1:
        terminal = [
            metadata
            for metadata in merged
            if status_value_is_terminal(metadata.get("status"))
        ]
        return (terminal or merged)[-1]
    if distinct_run_policy == "first":
        return merged[0]
    return merged[-1]


def extract_pds_run_metadata_from_json_text(text: str) -> dict[str, str] | None:
    metadata_values = extract_all_pds_run_metadata_from_json_text(text)
    return metadata_values[0] if metadata_values else None


def extract_all_pds_run_metadata_from_json_text(text: str) -> list[dict[str, str]]:
    values: list[dict[str, str]] = []
    for value in iter_json_values(text):
        values.extend(extract_all_pds_run_metadata_from_json_value(value))
    return values


def extract_all_pds_run_metadata_from_json_value(value: Any) -> list[dict[str, str]]:
    values: list[dict[str, str]] = []
    if isinstance(value, dict):
        metadata = pds_run_metadata_from_mapping(value)
        if metadata:
            values.append(metadata)
        for nested in value.values():
            values.extend(extract_all_pds_run_metadata_from_json_value(nested))
    elif isinstance(value, list):
        for nested in value:
            values.extend(extract_all_pds_run_metadata_from_json_value(nested))
    return values


def merge_pds_run_metadata_candidates(
    candidates: list[dict[str, str]],
) -> list[dict[str, str]]:
    merged: list[dict[str, str]] = []
    run_indexes: dict[str, int] = {}
    for candidate in candidates:
        run_id = candidate.get("runId", "")
        if run_id and run_id in run_indexes:
            existing = merged[run_indexes[run_id]]
            for key, value in candidate.items():
                if not value:
                    continue
                if (
                    key == "status"
                    and existing.get("status")
                    and status_value_is_terminal(existing["status"])
                    and not status_value_is_terminal(value)
                ):
                    continue
                existing[key] = value
            continue
        merged.append(dict(candidate))
        if run_id:
            run_indexes[run_id] = len(merged) - 1
    return merged


def iter_json_values(text: str):
    for value, _, _ in iter_json_value_spans(text):
        yield value


def iter_json_value_spans(text: str):
    decoder = json.JSONDecoder()
    index = 0
    while index < len(text):
        json_starts = (
            text.find("{", index),
            text.find("[", index),
        )
        next_object = min(
            (position for position in json_starts if position >= 0),
            default=-1,
        )
        if next_object < 0:
            return
        try:
            value, end = decoder.raw_decode(text[next_object:])
        except json.JSONDecodeError:
            index = next_object + 1
            continue
        yield value, next_object, next_object + end
        index = next_object + end


def extract_pds_run_metadata_from_json_value(value: Any) -> dict[str, str] | None:
    if isinstance(value, dict):
        metadata = pds_run_metadata_from_mapping(value)
        if metadata:
            return metadata
        for nested in value.values():
            metadata = extract_pds_run_metadata_from_json_value(nested)
            if metadata:
                return metadata
    elif isinstance(value, list):
        for nested in value:
            metadata = extract_pds_run_metadata_from_json_value(nested)
            if metadata:
                return metadata
    return None


def pds_run_metadata_from_mapping(mapping: dict[str, Any]) -> dict[str, str] | None:
    run_value = mapping.get("run")
    project_value = mapping.get("project")
    run = run_value if isinstance(run_value, dict) else {}
    project = project_value if isinstance(project_value, dict) else {}
    mapping_run_id = first_string(mapping, "runId", "run_id")
    nested_run_id = first_string(
        run,
        "runId",
        "run_id",
        "id",
    )
    run_id = mapping_run_id or nested_run_id
    project_id = first_string(
        project,
        "projectId",
        "project_id",
        "id",
    )
    if not project_id and run_id:
        project_id = first_string(mapping, "projectId", "project_id")
    run_status = first_string(run, "status", "state")
    mapping_status = first_string(mapping, "status", "state")
    run_has_identity = bool(first_string(run, "runId", "run_id", "id"))
    metadata = {
        "runId": run_id,
        "projectId": project_id,
        "status": run_status or (None if run_has_identity else mapping_status),
        "attemptId": first_string(mapping, "attemptId", "attempt_id"),
        "recoverCommand": first_string(mapping, "recoverCommand", "recover_command"),
        "watchCommand": first_string(mapping, "watchCommand", "watch_command"),
    }
    if not metadata["runId"]:
        return None
    return {key: value for key, value in metadata.items() if value}


def first_string(mapping: dict[str, Any], *keys: str) -> str | None:
    for key in keys:
        value = mapping.get(key)
        if isinstance(value, str) and value.strip():
            return value.strip()
    return None


def extract_pds_run_metadata_from_compat_lines(text: str) -> dict[str, str] | None:
    match = PDS_RUN_HANDLE_LINE_RE.search(text)
    if not match:
        return None
    metadata = {
        field_match.group("key"): field_match.group("value")
        for field_match in PDS_RUN_HANDLE_FIELD_RE.finditer(match.group("fields"))
    }
    recover_command = extract_pds_command_line(text, "[pds] recover:")
    watch_command = extract_pds_command_line(text, "[pds] watch:")
    if recover_command:
        metadata["recoverCommand"] = recover_command
    if watch_command:
        metadata["watchCommand"] = watch_command
    return metadata if metadata.get("runId") else None


def extract_pds_command_line(text: str, prefix: str) -> str | None:
    for line in text.splitlines():
        if line.startswith(prefix):
            command = line.removeprefix(prefix).strip()
            if command:
                return command
    return None


def enrich_pds_run_metadata(
    metadata: dict[str, str],
    *,
    pds_cli: str,
    tag: str,
    idempotency_key: str,
    attempt_id: str | None,
    provenance: str,
    project_id: str | None,
) -> dict[str, Any]:
    enriched: dict[str, Any] = {
        key: str(value).strip()
        for key, value in metadata.items()
        if str(value).strip()
    }
    run_id = enriched.get("runId", "")
    if str(attempt_id or "").strip() and "attemptId" not in enriched:
        enriched["attemptId"] = str(attempt_id).strip()
    enriched.setdefault("tag", tag)
    enriched.setdefault("idempotencyKey", idempotency_key)
    enriched.setdefault("idempotencyProvenance", provenance)
    if str(project_id or "").strip() and "projectId" not in enriched:
        enriched["projectId"] = str(project_id).strip()
    sanitize_pds_recovery_commands(enriched)
    enriched.setdefault("pdsContext", pds_context(pds_cli))
    if run_id:
        refresh_pds_recovery_commands(enriched, pds_cli)
    return enriched


def sanitize_pds_recovery_commands(metadata: dict[str, Any]) -> None:
    for key in ("recoverCommand", "watchCommand"):
        command = str(metadata.get(key) or "").strip()
        if command:
            metadata[key] = redact_command_text(command)


def refresh_pds_recovery_commands(metadata: dict[str, Any], pds_cli: str) -> None:
    run_id = str(metadata.get("runId") or "").strip()
    if not run_id:
        return
    pds_command = split_command(redact_command_text(pds_cli))
    project_id = str(metadata.get("projectId") or "").strip()
    if project_id:
        pds_command.extend(["--project", project_id])
    pds_base = shlex.join(pds_command)
    recover_command = (
        f"{pds_base} release-video status --run-id {shlex.quote(run_id)} --json"
    )
    watch_command = f"{pds_base} jobs watch --run-id {shlex.quote(run_id)} --jsonl"
    metadata["recoverCommand"] = recover_command
    metadata["watchCommand"] = watch_command


def pds_failure_hint(
    completed: subprocess.CompletedProcess[str],
    *,
    expected_run_id: str | None = None,
    allow_unscoped: bool = True,
) -> str:
    """Return fixed, redacted recovery guidance for a terminal PDS failure."""
    payloads = pds_authoritative_failure_payloads(
        completed.stderr,
        completed.stdout,
        expected_run_id=expected_run_id,
        allow_unscoped=allow_unscoped,
    )
    return pds_terminal_failure_hint(*payloads)


def pds_terminal_failure_hint_from_status(metadata: dict[str, Any]) -> str:
    """Classify a refreshed failed-run sidecar without trusting stale history."""
    status = str(metadata.get("status") or "").strip().lower()
    if status not in FAILED_PDS_STATUSES:
        return ""
    last_query = metadata.get("lastStatusQuery")
    if not isinstance(last_query, dict) or last_query.get("ok") is not True:
        return ""
    run_id = str(metadata.get("runId") or "").strip()
    query_run_id = str(last_query.get("runId") or "").strip()
    if not run_id or query_run_id != run_id:
        return ""
    response = last_query.get("response")
    payloads = pds_authoritative_failure_payloads(
        response,
        expected_run_id=run_id,
        allow_unscoped=False,
    )
    return pds_terminal_failure_hint(*payloads)


def pds_authoritative_failure_payloads(
    *values: Any,
    expected_run_id: str | None,
    allow_unscoped: bool,
) -> list[Any]:
    """Select failure payloads owned by the current command or exact run."""
    payloads: list[Any] = []
    for value in values:
        if isinstance(value, (dict, list)):
            payloads.extend(
                pds_authoritative_json_failure_payloads(
                    value,
                    expected_run_id=expected_run_id,
                    allow_unscoped=allow_unscoped,
                )
            )
            continue
        if not isinstance(value, str):
            continue
        parsed_spans = list(iter_json_value_spans(value))
        for parsed, _, _ in parsed_spans:
            payloads.extend(
                pds_authoritative_json_failure_payloads(
                    parsed,
                    expected_run_id=expected_run_id,
                    allow_unscoped=allow_unscoped,
                )
            )
        plain_text = text_without_json_spans(value, parsed_spans)
        if expected_run_id:
            payloads.extend(
                pds_plain_failure_segments_for_run(plain_text, expected_run_id)
            )
        elif allow_unscoped and not PDS_RUN_HANDLE_LINE_RE.search(plain_text):
            payloads.append(plain_text)
    return payloads


def pds_authoritative_json_failure_payloads(
    value: Any,
    *,
    expected_run_id: str | None,
    allow_unscoped: bool,
) -> list[Any]:
    """Select a history-pruned JSON payload under explicit authority rules."""
    if not isinstance(value, dict):
        return []
    current = pds_current_status_failure_payload(value)
    if not isinstance(current, dict):
        return []
    run_id = response_pds_run_id(current)
    if expected_run_id:
        return [current] if run_id == expected_run_id else []
    if not allow_unscoped:
        return []
    return [current] if not run_id else []


def text_without_json_spans(
    text: str,
    spans: list[tuple[Any, int, int]],
) -> str:
    """Remove parsed JSON while preserving line boundaries for plain parsing."""
    characters = list(text)
    for _, start, end in spans:
        for index in range(start, end):
            if characters[index] != "\n":
                characters[index] = " "
    return "".join(characters)


def pds_plain_failure_segments_for_run(text: str, run_id: str) -> list[str]:
    """Return only diagnostic segments introduced by a matching run handle."""
    matches = list(PDS_RUN_HANDLE_LINE_RE.finditer(text))
    segments: list[str] = []
    for index, match in enumerate(matches):
        fields = {
            field.group("key"): field.group("value")
            for field in PDS_RUN_HANDLE_FIELD_RE.finditer(match.group("fields"))
        }
        if fields.get("runId") != run_id:
            continue
        end = matches[index + 1].start() if index + 1 < len(matches) else len(text)
        segments.append(text[match.start():end])
    return segments


def pds_current_status_failure_payload(value: Any) -> Any:
    """Remove historical run collections before classifying current status."""
    if isinstance(value, list):
        return [pds_current_status_failure_payload(item) for item in value]
    if not isinstance(value, dict):
        return value
    current: dict[str, Any] = {}
    for key, nested in value.items():
        normalized_key = re.sub(r"[^a-z0-9]", "", str(key).lower())
        if normalized_key in {
            "attempts",
            "events",
            "history",
            "previous",
            "previousruns",
            "runs",
        }:
            continue
        current[key] = pds_current_status_failure_payload(nested)
    return current


def pds_terminal_failure_hint(*values: Any) -> str:
    """Classify stable PDS terminal signals and return payload-free guidance."""
    failure_class = classify_pds_terminal_failure(*values)
    if failure_class == "request_hash_mismatch":
        return (
            "PDS reported request_hash_mismatch: the same idempotency key was "
            "reused with a different request body. Retry with a distinct "
            "RELEASE_VIDEO_ATTEMPT_ID, RELEASE_VIDEO_IDEMPOTENCY_PROVENANCE, or "
            "explicit RELEASE_VIDEO_IDEMPOTENCY_KEY."
        )
    if failure_class == "provider_quota":
        return (
            "PDS/GVS provider quota interrupted release-video generation. "
            "No YouTube URL is expected from this run. Do not rerun "
            "package/tag/PyPI release steps. Recover or switch the upstream "
            "provider, then retry release-video with a new attempt id; if the "
            "team intentionally abandons the historical video, use "
            "make release-video-skip with an explicit reason."
        )
    if failure_class == "audit_gate":
        return (
            "The PDS/GVS distribution audit gate blocked safe video publish. "
            "No YouTube URL is expected from this run. Do not rerun "
            "package/tag/PyPI release steps or fabricate a video URL. Repair "
            "the upstream audit failure, then retry release-video with a fresh "
            "RELEASE_VIDEO_ATTEMPT_ID; if the team "
            "intentionally abandons the historical video, use "
            "make release-video-skip with an explicit reason."
        )
    return ""


def classify_pds_terminal_failure(*values: Any) -> str | None:
    """Return a stable terminal class from structured codes or bounded text."""
    for value in values:
        for structured in pds_structured_failure_values(value):
            failure_class = classify_pds_failure_signal(structured, plain=False)
            if failure_class:
                return failure_class

    for value in values:
        if not isinstance(value, str):
            continue
        for line in value.splitlines():
            failure_class = classify_pds_failure_signal(line, plain=True)
            if failure_class:
                return failure_class
    return None


def classify_pds_failure_signal(signal: str, *, plain: bool) -> str | None:
    """Classify one structured value or code-shaped diagnostic line."""
    normalized = signal.strip().lower()
    if not normalized or len(normalized) > 512:
        return None
    if normalized == "distribution audit gate failed" or (
        plain and pds_plain_audit_gate_failure(normalized)
    ):
        return "audit_gate"
    if normalized in PDS_REQUEST_HASH_CODES or (
        plain and pds_plain_failure_code(normalized, PDS_REQUEST_HASH_CODES)
    ):
        return "request_hash_mismatch"
    if normalized in PDS_AUDIT_GATE_CODES or (
        plain and pds_plain_failure_code(normalized, PDS_AUDIT_GATE_CODES)
    ):
        return "audit_gate"
    if normalized in PDS_PROVIDER_QUOTA_CODES or (
        plain and pds_plain_failure_code(normalized, PDS_PROVIDER_QUOTA_CODES)
    ):
        return "provider_quota"
    return "provider_quota" if pds_provider_429_line(normalized) else None


def pds_structured_failure_values(value: Any) -> list[str]:
    """Extract only authoritative failure fields from JSON-like PDS output."""
    if isinstance(value, str):
        parsed_values = list(iter_json_values(value))
        extracted: list[str] = []
        for parsed in parsed_values:
            extracted.extend(pds_structured_failure_values(parsed))
        return extracted
    if isinstance(value, list):
        extracted = []
        for nested in value:
            extracted.extend(pds_structured_failure_values(nested))
        return extracted
    if not isinstance(value, dict):
        return []

    extracted = []
    for key, nested in value.items():
        normalized_key = re.sub(r"[^a-z0-9]", "", str(key).lower())
        if isinstance(nested, str) and normalized_key in {
            "code",
            "error",
            "errorcode",
            "failurecode",
            "reason",
            "type",
            "message",
        }:
            extracted.append(nested)
        if isinstance(nested, (dict, list)):
            extracted.extend(pds_structured_failure_values(nested))
    return extracted


def pds_plain_failure_code(line: str, codes: set[str]) -> bool:
    """Accept a code-shaped diagnostic line, not an arbitrary prose mention."""
    if line in codes:
        return True
    if not any(code in line for code in codes):
        return False
    return bool(
        re.match(r"^(?:\[pds\]\s*)?(?:error|code|reason|failure|failed)\b", line)
        or (line.startswith("{") and line.endswith("}"))
    )


def pds_plain_audit_gate_failure(line: str) -> bool:
    """Recognize the stable audit phrase with a compact diagnostic prefix."""
    return bool(
        re.fullmatch(
            r"(?:\[pds\]\s*)?(?:error|failed|failure|reason):?\s*"
            r"distribution audit gate failed[.!]?",
            line,
        )
    )


def pds_provider_429_line(line: str) -> bool:
    """Recognize only compact provider-request HTTP 429 diagnostics."""
    if len(line) > 240:
        return False
    return bool(
        re.search(
            r"\bprovider(?:\s+request)?\s+(?:failed|error(?:ed)?)\b.{0,32}"
            r"\b(?:http\s*)?429\b",
            line,
        )
        or re.search(
            r"\bprovider\b.{0,16}\b(?:http\s*)?429\b.{0,48}"
            r"\b(?:error|exhausted|failed|limit|quota)\b",
            line,
        )
    )


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


def prepare_release_video_script(raw_script: str, *, source: str) -> dict[str, Any]:
    raw = str(raw_script or "")
    candidate = strip_markdown_fence(raw.strip())
    candidate, wrapper_changed = strip_model_wrapper_text(candidate)
    changes: list[str] = []
    if wrapper_changed:
        changes.append("stripped_model_wrapper_text")
    candidate, fence_changed = strip_outer_markdown_fence_lines(candidate)
    if fence_changed:
        changes.append("stripped_markdown_fence")
    candidate, duplicate_changed = collapse_duplicate_narrator_labels(candidate)
    if duplicate_changed:
        changes.append("collapsed_duplicate_narrator_labels")
    candidate, visual_changed = collapse_label_only_visual_cues(candidate)
    if visual_changed:
        changes.append("collapsed_label_only_visual_cues")
    candidate, wrapped_visual_changed = collapse_wrapped_visual_cues(candidate)
    if wrapped_visual_changed:
        changes.append("collapsed_wrapped_visual_cues")
    normalized = normalize_release_video_script(candidate)
    normalized, duplicate_changed_after = collapse_duplicate_narrator_labels(normalized)
    if duplicate_changed_after and "collapsed_duplicate_narrator_labels" not in changes:
        changes.append("collapsed_duplicate_narrator_labels")
    normalized = normalized.rstrip() + "\n"
    validation = validate_release_video_script(
        script=normalized,
        raw_script=raw,
        source=source,
        changes=changes,
    )
    return {
        "raw": raw,
        "script": normalized,
        "validation": validation,
    }


def write_release_video_script_artifacts(
    *,
    script_artifacts: dict[str, Any],
    script_path: Path,
    raw_script_path: Path,
    validation_path: Path,
) -> None:
    raw_script_path.write_text(str(script_artifacts["raw"]), encoding="utf8")
    script_path.write_text(str(script_artifacts["script"]), encoding="utf8")
    write_json_file(validation_path, script_artifacts["validation"])


def strip_model_wrapper_text(script: str) -> tuple[str, bool]:
    lines = script.splitlines()
    lines, changed = strip_leading_model_wrapper_lines(lines)
    first_script_line = release_video_script_start_index(lines)
    if first_script_line:
        lines = lines[first_script_line:]

    changed = changed or first_script_line > 0
    while lines and not lines[-1].strip():
        lines.pop()
    while (
        lines
        and is_model_wrapper_line(lines[-1])
    ):
        lines.pop()
        changed = True
        while lines and not lines[-1].strip():
            lines.pop()
    return "\n".join(lines).strip(), changed


def strip_leading_model_wrapper_lines(lines: list[str]) -> tuple[list[str], bool]:
    changed = False
    while lines and not lines[0].strip():
        lines.pop(0)
        changed = True
    while lines and is_model_wrapper_line(lines[0]):
        lines.pop(0)
        changed = True
        while lines and not lines[0].strip():
            lines.pop(0)
            changed = True
    return lines, changed


def release_video_script_start_index(lines: list[str]) -> int:
    for index, line in enumerate(lines):
        if not is_release_video_script_line(line):
            continue
        if has_non_wrapper_content_before(lines, index):
            return 0
        if has_markdown_fence_before(lines, index):
            return 0
        return index
    return 0


def has_non_wrapper_content_before(lines: list[str], end_index: int) -> bool:
    return any(
        line.strip() and not is_model_wrapper_line(line) and not is_markdown_fence_line(line)
        for line in lines[:end_index]
    )


def has_markdown_fence_before(lines: list[str], end_index: int) -> bool:
    return any(is_markdown_fence_line(line) for line in lines[:end_index])


def is_markdown_fence_line(line: str) -> bool:
    return bool(re.match(r"^\s*```(?:markdown|md)?\s*$", line, flags=re.IGNORECASE))


def strip_outer_markdown_fence_lines(script: str) -> tuple[str, bool]:
    lines = script.splitlines()
    changed = False
    while lines and not lines[0].strip():
        lines.pop(0)
    if lines and re.match(r"^```(?:markdown|md)?\s*$", lines[0].strip(), flags=re.IGNORECASE):
        lines.pop(0)
        changed = True
    while lines and not lines[-1].strip():
        lines.pop()
    if lines and lines[-1].strip() == "```":
        lines.pop()
        changed = True
    return "\n".join(lines).strip(), changed


def is_model_wrapper_line(line: str) -> bool:
    stripped = line.strip()
    if not stripped:
        return False
    normalized = stripped.replace("\u2019", "'")
    if re.match(
        r"^(?:(?:absolutely|sure|certainly|of course)[,!]?\s+)?"
        r"(?:here(?:'s| is)|below is|the following is|"
        r"below you(?:'ll| will) find)\b",
        normalized,
        flags=re.IGNORECASE,
    ):
        return mentions_release_video_script(normalized)
    if re.match(
        r"^i(?:'ve| have)?\s+"
        r"(?:drafted|prepared|created|written|wrote|generated|put together)\b",
        normalized,
        flags=re.IGNORECASE,
    ):
        return mentions_release_video_script(normalized)
    return bool(
        re.match(
            r"^(?:sure[,!]?|certainly[,!]?|of course[,!]?|"
            r"let me know|i can also|i hope this helps)\b",
            stripped,
            flags=re.IGNORECASE,
        )
    )


def mentions_release_video_script(text: str) -> bool:
    return bool(
        re.search(
            r"\b(?:release[- ]video\s+)?script\b",
            text,
            flags=re.IGNORECASE,
        )
    )


def collapse_duplicate_narrator_labels(script: str) -> tuple[str, bool]:
    lines = script.splitlines()
    normalized: list[str] = []
    changed = False
    pending_label = False
    blank_after_pending_label = False

    for line in lines:
        duplicate_body = duplicate_narrator_label_body(line)
        if duplicate_body is not None:
            if not pending_label:
                append_spaced(normalized, "NARRATOR:")
            if duplicate_body:
                normalized.append(duplicate_body)
                pending_label = False
            else:
                pending_label = True
            blank_after_pending_label = False
            changed = True
            continue

        if is_narrator_label(line):
            if pending_label:
                while normalized and not normalized[-1].strip():
                    normalized.pop()
                changed = True
                continue
            append_spaced(normalized, "NARRATOR:")
            pending_label = True
            blank_after_pending_label = False
            if line.strip() != "NARRATOR:":
                changed = True
            continue

        inline_body = inline_narrator_label_body(line)
        if inline_body is not None:
            if not pending_label:
                append_spaced(normalized, "NARRATOR:")
            normalized.append(inline_body)
            pending_label = False
            blank_after_pending_label = False
            changed = True
            continue

        if not line.strip():
            if pending_label:
                if not blank_after_pending_label:
                    normalized.append("")
                    blank_after_pending_label = True
                else:
                    changed = True
            else:
                normalized.append("")
            continue

        normalized.append(line)
        pending_label = False
        blank_after_pending_label = False

    return trim_repeated_blank_lines(normalized), changed


def collapse_label_only_visual_cues(script: str) -> tuple[str, bool]:
    """Collapse safe label-only visual blocks into same-line VISUAL cues."""
    lines = script.splitlines()
    normalized: list[str] = []
    changed = False
    index = 0

    while index < len(lines):
        line = lines[index]
        if is_visual_label_only(line):
            cue_lines, next_index = collect_visual_cue_paragraph(lines, index + 1)
            if cue_lines:
                cue = " ".join(cue_lines)
                append_spaced(normalized, f"VISUAL: {cue}")
                index = next_index
                changed = True
                continue
        normalized.append(line)
        index += 1

    if not changed:
        return script, False
    return trim_repeated_blank_lines(normalized), True


def collect_visual_cue_paragraph(lines: list[str], start: int) -> tuple[list[str], int]:
    """Collect cue paragraph lines after a label-only visual marker."""
    cue_lines: list[str] = []
    index = start
    while index < len(lines) and not lines[index].strip():
        index += 1
    while index < len(lines):
        line = lines[index]
        if not line.strip():
            break
        if is_collapsible_visual_cue_line(line):
            cue_lines.append(clean_visual_cue(line))
            index += 1
            continue
        visual = visual_cue_text(line)
        if visual and not cue_lines:
            cue_lines.append(visual)
            index += 1
        break
    return cue_lines, index


def collapse_wrapped_visual_cues(script: str) -> tuple[str, bool]:
    """Collapse safe continuation lines into their preceding VISUAL cue."""
    lines = script.splitlines()
    normalized: list[str] = []
    changed = False
    index = 0

    while index < len(lines):
        line = lines[index]
        visual = visual_cue_text(line)
        if visual:
            continuation_lines, next_index = collect_visual_cue_continuation(
                lines,
                index + 1,
            )
            if continuation_lines:
                cue = " ".join([visual, *continuation_lines])
                append_spaced(normalized, f"VISUAL: {cue}")
                index = next_index
                changed = True
                continue
        normalized.append(line)
        index += 1

    if not changed:
        return script, False
    return trim_repeated_blank_lines(normalized), True


def collect_visual_cue_continuation(
    lines: list[str],
    start: int,
) -> tuple[list[str], int]:
    """Collect safe visual cue continuation lines until the next block boundary."""
    cue_lines: list[str] = []
    index = start
    while index < len(lines):
        line = lines[index]
        if not line.strip():
            break
        if not is_collapsible_visual_cue_line(line):
            break
        cue_lines.append(clean_visual_cue(line))
        index += 1
    return cue_lines, index


def is_collapsible_visual_cue_line(line: str) -> bool:
    """Return whether a line can safely become cue text after VISUAL:."""
    stripped = line.strip()
    return bool(
        stripped
        and not re.match(r"^#{1,6}\s+\S", stripped)
        and not is_release_video_script_line(line)
        and not is_model_wrapper_line(line)
        and not is_markdown_fence_line(line)
    )


def visual_safety_findings(script: str) -> list[dict[str, Any]]:
    """Return deterministic safety findings for release-video visual cues."""
    findings: list[dict[str, Any]] = []
    cue_index = 0
    for line_number, line in enumerate(script.splitlines(), start=1):
        cue = visual_cue_text(line)
        if not cue:
            continue
        cue_index += 1
        categories = visual_safety_categories(cue)
        findings.extend(
            {
                "category": category,
                "check": VISUAL_SAFETY_CHECKS[category],
                "cueIndex": cue_index,
                "line": line_number,
            }
            for category in categories
        )
    return findings


def visual_safety_categories(cue: str) -> list[str]:
    """Classify one visual cue using stable, machine-readable categories."""
    categories: list[str] = []
    readable_candidate = SAFE_TEXT_QUALIFIER_RE.sub("", cue)
    if READABLE_VISUAL_RE.search(readable_candidate):
        categories.append("risky_readable_surface")
    if EXACT_GEOMETRY_VISUAL_RE.search(cue):
        categories.append("brittle_exact_geometry")
    if has_unsafe_visual_motion(cue):
        categories.append("brittle_mandatory_motion")
    return categories


def has_unsafe_visual_motion(cue: str) -> bool:
    """Return whether a cue requires timed, semantic, or mandatory motion."""
    if FRAME_EXACT_MOTION_RE.search(cue) or SEMANTIC_MOTION_VISUAL_RE.search(cue):
        return True
    for clause in visual_motion_clauses(cue):
        for match in CAMERA_MOTION_VISUAL_RE.finditer(clause):
            if not camera_motion_is_locally_optional(clause, match):
                return True
    return False


def visual_motion_clauses(cue: str) -> list[str]:
    """Split a cue at boundaries that separate independently required actions."""
    return [part.strip() for part in VISUAL_CLAUSE_SPLIT_RE.split(cue) if part.strip()]


def camera_motion_is_locally_optional(clause: str, match: re.Match[str]) -> bool:
    """Return whether the matched camera action has local optional grammar."""
    before = clause[: match.start()]
    after = clause[match.end() :]
    if MOTION_REQUIRED_PREFIX_RE.search(before):
        return False
    camera_context = bool(re.search(r"\bcamera\b", clause, flags=re.IGNORECASE))
    camera_context = camera_context or bool(IMPLICIT_CAMERA_ACTION_RE.match(match.group(0)))
    if not camera_context:
        return False
    return bool(
        MOTION_OPTIONAL_PREFIX_RE.search(before)
        or CAMERA_MODAL_PREFIX_RE.search(before)
        or IMPLICIT_CAMERA_MODAL_PREFIX_RE.search(before)
        or MOTION_OPTIONAL_SUFFIX_RE.search(after)
    )


def validate_release_video_script(
    *,
    script: str,
    raw_script: str,
    source: str,
    changes: list[str],
) -> dict[str, Any]:
    safety_findings = visual_safety_findings(script)
    safety_categories = {
        str(finding["category"])
        for finding in safety_findings
    }
    checks = {
        "minLength": len(script.strip()) >= 200,
        "hasSection": bool(re.search(r"(?m)^##\s+\S", script)),
        "hasNarrator": any(is_narrator_label(line) for line in script.splitlines()),
        "hasVisual": any(visual_cue_text(line) for line in script.splitlines()),
        "hasNoModelWrapperText": not has_unstripped_model_wrapper_text(script),
        "hasNoDuplicateNarratorLabels": not has_duplicate_narrator_labels(script),
        "hasNoLabelOnlyVisualCues": not has_label_only_visual_cues(script),
        "hasNoMarkdownFences": not has_markdown_fence_line(script),
        **{
            check: category not in safety_categories
            for category, check in VISUAL_SAFETY_CHECKS.items()
        },
    }
    errors = [name for name, passed in checks.items() if not passed]
    return {
        "source": source,
        "checkedAt": utc_now_iso(),
        "normalized": script.strip() != raw_script.strip(),
        "changes": changes,
        "checks": checks,
        "errors": errors,
        "visualSafetyFindings": safety_findings,
    }


def has_duplicate_narrator_labels(script: str) -> bool:
    previous_pending_label = False
    for line in script.splitlines():
        if duplicate_narrator_label_body(line) is not None:
            return True
        if is_narrator_label(line):
            if previous_pending_label:
                return True
            previous_pending_label = True
            continue
        if inline_narrator_label_body(line) is not None:
            return True
        if line.strip():
            previous_pending_label = False
    return False


def has_label_only_visual_cues(script: str) -> bool:
    """Return whether the script still contains empty visual cue labels."""
    return any(is_visual_label_only(line) for line in script.splitlines())


def has_markdown_fence_line(script: str) -> bool:
    return any(re.match(r"^\s*```", line) for line in script.splitlines())


def has_unstripped_model_wrapper_text(script: str) -> bool:
    return any(is_model_wrapper_line(line) for line in script.splitlines())


def duplicate_narrator_label_body(line: str) -> str | None:
    remainder = consume_narrator_label_prefix(line)
    if remainder is None:
        return None
    duplicate_count = 0
    while True:
        next_remainder = consume_narrator_label_prefix(remainder)
        if next_remainder is None:
            break
        duplicate_count += 1
        remainder = next_remainder
    if duplicate_count == 0:
        return None
    return remainder.strip()


def consume_narrator_label_prefix(text: str) -> str | None:
    stripped = text.lstrip()
    upper = stripped.upper()
    index = 0
    has_opening_bold = upper.startswith("**")
    if has_opening_bold:
        index = 2
    if not upper[index:].startswith("NARRATOR:"):
        return None
    index += len("NARRATOR:")
    whitespace_start = index
    while index < len(stripped) and stripped[index].isspace():
        index += 1
    has_spacing_before_close = index > whitespace_start
    if stripped[index : index + 2] == "**" and should_consume_label_close_marker(
        stripped,
        index,
        has_opening_bold=has_opening_bold,
        has_spacing_before_close=has_spacing_before_close,
    ):
        index += 2
    return stripped[index:].lstrip()


def should_consume_label_close_marker(
    text: str,
    marker_index: int,
    *,
    has_opening_bold: bool,
    has_spacing_before_close: bool,
) -> bool:
    after_marker = marker_index + 2
    if has_opening_bold or after_marker >= len(text):
        return True
    if not has_spacing_before_close:
        return True
    return text[after_marker].isspace()


def inline_narrator_label_body(line: str) -> str | None:
    remainder = consume_narrator_label_prefix(line)
    if remainder is None:
        return None
    body = remainder.strip()
    return body or None


def normalize_release_video_script(script: str) -> str:
    script = ensure_release_video_sections(script)
    script = ensure_timestamped_headings(script)
    return ensure_narrator_blocks(script)


def ensure_release_video_sections(script: str) -> str:
    """Ensure PDS can split the script into scene sections."""
    script = script.strip()
    if re.search(r"(?m)^##\s+\S", script):
        return script

    lines = script.splitlines()
    normalized: list[str] = []
    inserted = 0
    used_headings: set[str] = set()
    visual_cue_re = re.compile(
        r"^\s*(?:\*\*)?\[(?:Visual|Scene|Shot|On[- ]screen):\s*(?P<cue>[^\]]+)\](?:\*\*)?\s*$",
        flags=re.IGNORECASE,
    )

    for line in lines:
        match = visual_cue_re.match(line)
        if match:
            heading = unique_heading(heading_from_visual_cue(match.group("cue")), used_headings)
            if normalized and normalized[-1].strip():
                normalized.append("")
            normalized.extend([f"## {heading}", "", line])
            inserted += 1
        else:
            normalized.append(line)

    if inserted:
        return "\n".join(normalized).strip()

    heading = "Release Overview"
    if lines and re.match(r"^#\s+\S", lines[0]):
        return "\n".join([lines[0], "", f"## {heading}", *lines[1:]]).strip()
    return f"## {heading}\n\n{script}"


def ensure_timestamped_headings(script: str) -> str:
    lines = script.splitlines()
    heading_indexes = [
        index for index, line in enumerate(lines) if re.match(r"^##\s+\S", line)
    ]
    if not heading_indexes:
        return script

    section_count = len(heading_indexes)
    total_seconds = max(60, min(90, section_count * 15))
    for section_index, line_index in enumerate(heading_indexes):
        heading_text = lines[line_index].removeprefix("##").strip()
        if has_heading_timestamp(heading_text):
            continue
        start = round(section_index * total_seconds / section_count)
        end = round((section_index + 1) * total_seconds / section_count)
        clean_heading = strip_heading_timestamp(heading_text)
        lines[line_index] = f"## {clean_heading} ({format_timestamp(start)} - {format_timestamp(end)})"
    return "\n".join(lines).strip()


def has_heading_timestamp(heading_text: str) -> bool:
    return bool(re.search(r"\(\d{1,2}:\d{2}\s*-\s*\d{1,2}:\d{2}\)\s*$", heading_text))


def strip_heading_timestamp(heading_text: str) -> str:
    return re.sub(r"\s*\(\d{1,2}:\d{2}\s*-\s*\d{1,2}:\d{2}\)\s*$", "", heading_text).strip()


def format_timestamp(total_seconds: int) -> str:
    minutes, seconds = divmod(max(0, total_seconds), 60)
    return f"{minutes}:{seconds:02d}"


def ensure_narrator_blocks(script: str) -> str:
    lines = script.splitlines()
    has_narrator = any(
        is_narrator_label(line) or inline_narrator_label_body(line) is not None
        for line in lines
    )
    normalized: list[str] = []
    in_narrator = False

    for line in lines:
        stripped = line.strip()
        visual = visual_cue_text(line)
        inline_narrator = inline_narrator_label_body(line)
        if is_narrator_label(line):
            append_spaced(normalized, "NARRATOR:")
            in_narrator = True
        elif inline_narrator:
            append_spaced(normalized, "NARRATOR:")
            normalized.append(inline_narrator)
            in_narrator = True
        elif visual:
            append_spaced(normalized, f"VISUAL: {visual}")
            in_narrator = False
        elif not stripped:
            normalized.append("")
        elif re.match(r"^#{1,2}\s+\S", stripped):
            normalized.append(stripped)
            in_narrator = False
        elif has_narrator:
            normalized.append(line)
        else:
            if not in_narrator:
                append_spaced(normalized, "NARRATOR:")
                in_narrator = True
            normalized.append(line)

    return trim_repeated_blank_lines(normalized)


def is_narrator_label(line: str) -> bool:
    remainder = consume_narrator_label_prefix(line)
    return remainder is not None and not remainder.strip()


def is_release_video_script_line(line: str) -> bool:
    stripped = line.strip()
    return bool(
        re.match(r"^#{1,2}\s+\S", stripped)
        or is_narrator_label(line)
        or inline_narrator_label_body(line) is not None
        or is_visual_label_only(line)
        or visual_cue_text(line)
    )


def is_visual_label_only(line: str) -> bool:
    """Return whether a line is only a visual label with no cue text."""
    stripped = line.strip()
    return bool(
        re.match(
            r"^(?:\*\*)?"
            r"(?:VISUAL|Visual direction|Scene|Shot|On[- ]screen):"
            r"\s*(?:\*\*)?$",
            stripped,
            flags=re.IGNORECASE,
        )
    )


def visual_cue_text(line: str) -> str | None:
    stripped = line.strip()
    label_match = re.match(
        r"^(?:\*\*)?(?:VISUAL|Visual direction|Scene|Shot|On[- ]screen):\s*(?P<cue>.+?)(?:\*\*)?$",
        stripped,
        flags=re.IGNORECASE,
    )
    if label_match:
        return clean_visual_cue(label_match.group("cue"))

    bracket_match = re.match(
        r"^(?:\*\*)?\[(?:(?:VISUAL|Scene|Shot|On[- ]screen):\s*)?(?P<cue>[^\]]+)\](?:\*\*)?$",
        stripped,
        flags=re.IGNORECASE,
    )
    if bracket_match:
        cue = clean_visual_cue(bracket_match.group("cue"))
        if re.match(r"^(show|cut to|display|zoom|pan|overlay|terminal|github|makefile)\b", cue, flags=re.IGNORECASE):
            return cue
    return None


def clean_visual_cue(cue: str) -> str:
    return cue.strip().strip("*").strip()


def append_spaced(lines: list[str], value: str) -> None:
    while lines and not lines[-1].strip():
        lines.pop()
    if lines and lines[-1].strip():
        lines.append("")
    lines.append(value)


def trim_repeated_blank_lines(lines: list[str]) -> str:
    normalized: list[str] = []
    previous_blank = False
    for line in lines:
        blank = not line.strip()
        if blank and previous_blank:
            continue
        normalized.append(line.rstrip())
        previous_blank = blank
    return "\n".join(normalized).strip()


def heading_from_visual_cue(cue: str) -> str:
    cleaned = re.sub(r"`([^`]+)`", r"\1", cue)
    words = re.findall(r"[A-Za-z0-9]+", cleaned)
    heading = " ".join(words[:8]).title()
    return heading or "Release Highlight"


def unique_heading(heading: str, used_headings: set[str]) -> str:
    candidate = heading
    suffix = 2
    while candidate.lower() in used_headings:
        candidate = f"{heading} {suffix}"
        suffix += 1
    used_headings.add(candidate.lower())
    return candidate


def truncate(text: str, max_chars: int) -> str:
    if len(text) <= max_chars:
        return text
    return text[:max_chars] + "\n\n[truncated]\n"


def safe_path_part(value: str) -> str:
    return re.sub(r"[^A-Za-z0-9._-]+", "-", value).strip("-") or "release"


if __name__ == "__main__":
    raise SystemExit(main())
