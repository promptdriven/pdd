import importlib.util
from pathlib import Path

import pytest


ROOT = Path(__file__).resolve().parents[1]
SCRIPT = ROOT / "scripts" / "backfill_release_video_discord.py"


class FakeGitHubReleaseClient:
    def __init__(self, body: str):
        self.body = body
        self.edits: list[tuple[str, str]] = []
        self.viewed_tags: list[str] = []

    def get_release_body(self, tag: str) -> str:
        self.viewed_tags.append(tag)
        return self.body

    def edit_release_body(self, tag: str, body: str) -> None:
        self.edits.append((tag, body))
        self.body = body


class SequencedGitHubReleaseClient(FakeGitHubReleaseClient):
    def __init__(self, bodies: list[str]):
        super().__init__(bodies[-1])
        self.bodies = bodies

    def get_release_body(self, tag: str) -> str:
        self.viewed_tags.append(tag)
        if self.bodies:
            self.body = self.bodies.pop(0)
        return self.body


def load_backfill_module():
    spec = importlib.util.spec_from_file_location("backfill_release_video_discord", SCRIPT)
    assert spec is not None
    module = importlib.util.module_from_spec(spec)
    assert spec.loader is not None
    spec.loader.exec_module(module)
    return module


def test_backfill_posts_discord_followup_and_marks_release_body():
    module = load_backfill_module()
    youtube_url = "https://www.youtube.com/watch?v=RIkxCaylRAQ"
    github = FakeGitHubReleaseClient("PDD v0.0.283 fixes release video recovery.\n")
    posts: list[tuple[str, dict]] = []

    result = module.backfill_release_video_discord(
        tag="v0.0.283",
        youtube_url=youtube_url,
        repo="promptdriven/pdd",
        webhook_url="https://discord.example/webhook",
        github=github,
        post_discord=lambda webhook_url, payload: posts.append((webhook_url, payload)),
    )

    assert result.posted is True
    assert posts == [
        (
            "https://discord.example/webhook",
            {
                "content": (
                    "Release video recovered for v0.0.283: "
                    "https://www.youtube.com/watch?v=RIkxCaylRAQ\n"
                    "Release: https://github.com/promptdriven/pdd/releases/tag/v0.0.283"
                )
            },
        )
    ]
    assert github.body.startswith(f"Release video: {youtube_url}\n\n")
    assert module.discord_backfill_marker("v0.0.283", youtube_url) in github.body


def test_backfill_persists_marker_before_posting_discord():
    module = load_backfill_module()
    github = FakeGitHubReleaseClient("Existing notes.\n")
    posts: list[tuple[str, dict]] = []

    def fail_edit(tag: str, body: str) -> None:
        raise module.BackfillError("release edit failed")

    github.edit_release_body = fail_edit

    with pytest.raises(module.BackfillError, match="release edit failed"):
        module.backfill_release_video_discord(
            tag="v0.0.283",
            youtube_url="https://youtu.be/RIkxCaylRAQ",
            repo="promptdriven/pdd",
            webhook_url="https://discord.example/webhook",
            github=github,
            post_discord=lambda webhook_url, payload: posts.append((webhook_url, payload)),
        )

    assert posts == []


def test_backfill_merges_marker_into_latest_release_body_before_posting():
    module = load_backfill_module()
    youtube_url = "https://youtu.be/RIkxCaylRAQ"
    github = SequencedGitHubReleaseClient(
        [
            "Initial notes.\n",
            "Concurrent maintainer edit.\n",
        ]
    )
    posts: list[tuple[str, dict]] = []

    result = module.backfill_release_video_discord(
        tag="v0.0.283",
        youtube_url=youtube_url,
        repo="promptdriven/pdd",
        webhook_url="https://discord.example/webhook",
        github=github,
        post_discord=lambda webhook_url, payload: posts.append((webhook_url, payload)),
    )

    assert result.posted is True
    assert len(posts) == 1
    assert "Concurrent maintainer edit." in github.body
    assert "Initial notes." not in github.body
    assert module.discord_backfill_marker("v0.0.283", youtube_url) in github.body


def test_backfill_is_idempotent_when_same_video_marker_exists():
    module = load_backfill_module()
    youtube_url = "https://youtu.be/RIkxCaylRAQ"
    marker = module.discord_backfill_marker("v0.0.283", youtube_url)
    github = FakeGitHubReleaseClient(f"Release video: {youtube_url}\n\nNotes.\n\n{marker}\n")
    posts: list[tuple[str, dict]] = []

    result = module.backfill_release_video_discord(
        tag="v0.0.283",
        youtube_url=youtube_url,
        repo="promptdriven/pdd",
        webhook_url="https://discord.example/webhook",
        github=github,
        post_discord=lambda webhook_url, payload: posts.append((webhook_url, payload)),
    )

    assert result.posted is False
    assert result.skipped_reason == "discord-followup-already-marked"
    assert posts == []
    assert github.edits == []


def test_backfill_adds_missing_link_without_reposting_when_marker_exists():
    module = load_backfill_module()
    youtube_url = "https://youtu.be/RIkxCaylRAQ"
    marker = module.discord_backfill_marker("v0.0.283", youtube_url)
    github = FakeGitHubReleaseClient(f"Notes.\n\n{marker}\n")
    posts: list[tuple[str, dict]] = []

    result = module.backfill_release_video_discord(
        tag="v0.0.283",
        youtube_url=youtube_url,
        repo="promptdriven/pdd",
        webhook_url="",
        github=github,
        post_discord=lambda webhook_url, payload: posts.append((webhook_url, payload)),
    )

    assert result.posted is False
    assert result.release_body_updated is True
    assert result.skipped_reason == "discord-followup-already-marked"
    assert posts == []
    assert github.body.startswith(f"Release video: {youtube_url}\n\n")


def test_backfill_uses_canonical_youtube_id_for_markers_and_existing_links():
    module = load_backfill_module()
    watch_url = "https://www.youtube.com/watch?v=RIkxCaylRAQ&utm_source=discord"
    short_url = "https://youtu.be/RIkxCaylRAQ"
    marker = module.discord_backfill_marker("v0.0.283", watch_url)
    github = FakeGitHubReleaseClient(f"Release video: {watch_url}\n\nNotes.\n\n{marker}\n")
    posts: list[tuple[str, dict]] = []

    result = module.backfill_release_video_discord(
        tag="v0.0.283",
        youtube_url=short_url,
        repo="promptdriven/pdd",
        webhook_url="",
        github=github,
        post_discord=lambda webhook_url, payload: posts.append((webhook_url, payload)),
    )

    assert marker == module.discord_backfill_marker("v0.0.283", short_url)
    assert result.posted is False
    assert posts == []
    assert github.edits == []


def test_backfill_does_not_skip_for_a_different_video_url():
    module = load_backfill_module()
    first_url = "https://youtu.be/oldvideo"
    second_url = "https://youtu.be/newvideo"
    old_marker = module.discord_backfill_marker("v0.0.283", first_url)
    github = FakeGitHubReleaseClient(f"Release video: {first_url}\n\nNotes.\n\n{old_marker}\n")
    posts: list[tuple[str, dict]] = []

    result = module.backfill_release_video_discord(
        tag="v0.0.283",
        youtube_url=second_url,
        repo="promptdriven/pdd",
        webhook_url="https://discord.example/webhook",
        github=github,
        post_discord=lambda webhook_url, payload: posts.append((webhook_url, payload)),
    )

    assert result.posted is True
    assert len(posts) == 1
    assert f"Release video recovered for v0.0.283: {second_url}" in posts[0][1]["content"]
    assert module.discord_backfill_marker("v0.0.283", second_url) in github.body


def test_backfill_requires_webhook_before_mutating_unmarked_release_body():
    module = load_backfill_module()
    github = FakeGitHubReleaseClient("Existing notes.\n")

    with pytest.raises(module.BackfillError, match="DISCORD_WEBHOOK_URL is required"):
        module.backfill_release_video_discord(
            tag="v0.0.283",
            youtube_url="https://youtu.be/recoveredvideo",
            repo="promptdriven/pdd",
            webhook_url="",
            github=github,
            post_discord=lambda webhook_url, payload: None,
        )

    assert github.edits == []


def test_github_client_uses_gh_release_view_and_edit_without_network():
    module = load_backfill_module()
    calls: list[tuple[list[str], str | None]] = []

    def fake_run(command, **kwargs):
        calls.append((command, kwargs.get("input")))
        if command[:3] == ["gh", "release", "view"]:
            return type("Completed", (), {"returncode": 0, "stdout": "Existing notes\n", "stderr": ""})()
        return type("Completed", (), {"returncode": 0, "stdout": "", "stderr": ""})()

    client = module.GitHubReleaseClient(
        gh_cli="gh",
        repo="promptdriven/pdd",
        run=fake_run,
    )

    assert client.get_release_body("v0.0.283") == "Existing notes\n"
    client.edit_release_body("v0.0.283", "Updated notes\n")

    assert calls == [
        (
            [
                "gh",
                "release",
                "view",
                "v0.0.283",
                "--repo",
                "promptdriven/pdd",
                "--json",
                "body",
                "--jq",
                ".body",
            ],
            None,
        ),
        (
            [
                "gh",
                "release",
                "edit",
                "v0.0.283",
                "--repo",
                "promptdriven/pdd",
                "--notes-file",
                "-",
            ],
            "Updated notes\n",
        ),
    ]
