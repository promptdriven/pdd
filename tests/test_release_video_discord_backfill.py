import importlib.util
import io
from pathlib import Path
import urllib.error

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


def expected_discord_embed_payload(tag: str, youtube_url: str, repo: str) -> dict:
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
                "color": 3447003,
            }
        ]
    }


def test_build_discord_payload_uses_release_workflow_embed_style():
    module = load_backfill_module()
    youtube_url = "https://www.youtube.com/watch?v=RIkxCaylRAQ"

    payload = module.build_discord_payload("v0.0.283", youtube_url, "promptdriven/pdd")

    assert "content" not in payload
    assert payload == expected_discord_embed_payload(
        "v0.0.283",
        youtube_url,
        "promptdriven/pdd",
    )


def test_send_discord_webhook_posts_json_with_user_agent(monkeypatch):
    module = load_backfill_module()
    payload = expected_discord_embed_payload(
        "v0.0.283",
        "https://youtu.be/RIkxCaylRAQ",
        "promptdriven/pdd",
    )
    captured: dict[str, object] = {}

    class FakeResponse:
        status = 204

        def getcode(self) -> int:
            return self.status

        def __enter__(self):
            return self

        def __exit__(self, exc_type, exc, traceback) -> bool:
            return False

    def fake_urlopen(request, *, timeout):
        captured["request"] = request
        captured["timeout"] = timeout
        return FakeResponse()

    monkeypatch.setattr(module.urllib.request, "urlopen", fake_urlopen)

    module.send_discord_webhook("https://discord.example/webhook", payload, timeout=7)

    request = captured["request"]
    assert request.get_method() == "POST"
    assert request.get_header("Content-type") == "application/json"
    assert request.get_header("User-agent").startswith("curl/")
    assert request.get_header("Accept") == "*/*"
    assert module.json.loads(request.data.decode("utf8")) == payload
    assert captured["timeout"] == 7


def test_send_discord_webhook_includes_sanitized_http_error_response_body(monkeypatch):
    module = load_backfill_module()
    payload = expected_discord_embed_payload(
        "v0.0.283",
        "https://youtu.be/RIkxCaylRAQ",
        "promptdriven/pdd",
    )
    response_body = (
        b'{"message":"blocked webhook\\ntry again",'
        b'"webhook":"https://discord.com/api/webhooks/123456789/secret-token"}'
    )

    def fake_urlopen(request, *, timeout):
        raise urllib.error.HTTPError(
            request.full_url,
            403,
            "Forbidden",
            hdrs={},
            fp=io.BytesIO(response_body),
        )

    monkeypatch.setattr(module.urllib.request, "urlopen", fake_urlopen)

    with pytest.raises(module.DiscordWebhookError) as exc_info:
        module.send_discord_webhook("https://discord.example/webhook", payload)

    message = str(exc_info.value)
    assert "Discord webhook returned HTTP 403: Forbidden" in message
    assert "Response body excerpt:" in message
    assert "blocked webhook try again" in message
    assert "secret-token" not in message
    assert "https://discord.com/api/webhooks/123456789/secret-token" not in message


def test_send_discord_webhook_redacts_encoded_webhook_urls_from_error_body(monkeypatch):
    module = load_backfill_module()
    webhook_url = "https://discord.com/api/webhooks/123456789/Secret-Token"
    payload = expected_discord_embed_payload(
        "v0.0.283",
        "https://youtu.be/RIkxCaylRAQ",
        "promptdriven/pdd",
    )
    response_body = (
        b'{"literal":"https://discord.com/api/webhooks/123456789/Secret-Token",'
        b'"json_escaped":"https:\\/\\/discord.com\\/api\\/webhooks\\/123456789\\/Secret-Token",'
        b'"encoded":"https%3A%2F%2Fdiscord.com%2Fapi%2Fwebhooks%2F123456789%2FSecret-Token",'
        b'"encoded_lower":"https%3a%2f%2fdiscord.com%2fapi%2fwebhooks%2f123456789%2fSecret-Token"}'
    )

    def fake_urlopen(request, *, timeout):
        raise urllib.error.HTTPError(
            request.full_url,
            403,
            "Forbidden",
            hdrs={},
            fp=io.BytesIO(response_body),
        )

    monkeypatch.setattr(module.urllib.request, "urlopen", fake_urlopen)

    with pytest.raises(module.DiscordWebhookError) as exc_info:
        module.send_discord_webhook(webhook_url, payload)

    message = str(exc_info.value)
    assert "Response body excerpt:" in message
    assert "Secret-Token" not in message
    assert "123456789" not in message
    assert "https:\\/\\/discord.com\\/api\\/webhooks" not in message
    assert "https%3A%2F%2Fdiscord.com%2Fapi%2Fwebhooks" not in message
    assert "https%3a%2f%2fdiscord.com%2fapi%2fwebhooks" not in message


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
            expected_discord_embed_payload("v0.0.283", youtube_url, "promptdriven/pdd"),
        )
    ]
    assert github.body.startswith(f"Release video: {youtube_url}\n\n")
    assert module.discord_backfill_marker("v0.0.283", youtube_url) in github.body
    assert module.discord_backfill_pending_marker("v0.0.283", youtube_url) not in github.body


def test_backfill_does_not_post_discord_when_release_link_edit_fails():
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


def test_backfill_does_not_mark_release_when_discord_post_fails():
    module = load_backfill_module()
    youtube_url = "https://youtu.be/RIkxCaylRAQ"
    github = FakeGitHubReleaseClient("Existing notes.\n")

    def fail_post(webhook_url: str, payload: dict) -> None:
        raise module.DiscordWebhookError(
            "Discord webhook returned HTTP 403: Forbidden",
            post_definitely_failed=True,
        )

    with pytest.raises(module.BackfillError, match="Discord webhook returned HTTP 403"):
        module.backfill_release_video_discord(
            tag="v0.0.283",
            youtube_url=youtube_url,
            repo="promptdriven/pdd",
            webhook_url="https://discord.example/webhook",
            github=github,
            post_discord=fail_post,
        )

    assert github.body.startswith(f"Release video: {youtube_url}\n\n")
    assert module.discord_backfill_marker("v0.0.283", youtube_url) not in github.body
    assert module.discord_backfill_pending_marker("v0.0.283", youtube_url) not in github.body


def test_backfill_keeps_pending_marker_when_discord_failure_is_ambiguous():
    module = load_backfill_module()
    youtube_url = "https://youtu.be/RIkxCaylRAQ"
    github = FakeGitHubReleaseClient("Existing notes.\n")
    posts: list[tuple[str, dict]] = []

    def fail_post(webhook_url: str, payload: dict) -> None:
        posts.append((webhook_url, payload))
        raise module.DiscordWebhookError(
            "Discord webhook request failed: timed out",
            post_definitely_failed=False,
        )

    with pytest.raises(module.BackfillError, match="pending marker"):
        module.backfill_release_video_discord(
            tag="v0.0.283",
            youtube_url=youtube_url,
            repo="promptdriven/pdd",
            webhook_url="https://discord.example/webhook",
            github=github,
            post_discord=fail_post,
        )

    assert len(posts) == 1
    assert module.discord_backfill_marker("v0.0.283", youtube_url) not in github.body
    assert module.discord_backfill_pending_marker("v0.0.283", youtube_url) in github.body

    with pytest.raises(module.BackfillError, match="pending Discord backfill marker"):
        module.backfill_release_video_discord(
            tag="v0.0.283",
            youtube_url=youtube_url,
            repo="promptdriven/pdd",
            webhook_url="https://discord.example/webhook",
            github=github,
            post_discord=fail_post,
        )

    assert len(posts) == 1


def test_backfill_keeps_pending_marker_for_discord_5xx_http_error_text():
    module = load_backfill_module()
    youtube_url = "https://youtu.be/RIkxCaylRAQ"
    github = FakeGitHubReleaseClient("Existing notes.\n")

    def fail_post(webhook_url: str, payload: dict) -> None:
        raise module.BackfillError("Discord webhook returned HTTP 502: Bad Gateway")

    with pytest.raises(module.BackfillError, match="pending marker"):
        module.backfill_release_video_discord(
            tag="v0.0.283",
            youtube_url=youtube_url,
            repo="promptdriven/pdd",
            webhook_url="https://discord.example/webhook",
            github=github,
            post_discord=fail_post,
        )

    assert module.discord_backfill_marker("v0.0.283", youtube_url) not in github.body
    assert module.discord_backfill_pending_marker("v0.0.283", youtube_url) in github.body


def test_discord_http_status_classification_keeps_5xx_ambiguous():
    module = load_backfill_module()

    assert module.discord_http_status_definitely_failed(403) is True
    assert module.discord_http_status_definitely_failed(429) is True
    assert module.discord_http_status_definitely_failed(500) is False
    assert module.discord_http_status_definitely_failed(504) is False


def test_remove_pending_marker_handles_marker_without_trailing_newline():
    module = load_backfill_module()
    youtube_url = "https://youtu.be/RIkxCaylRAQ"
    pending_marker = module.discord_backfill_pending_marker("v0.0.283", youtube_url)
    body = f"Release video: {youtube_url}\n\nExisting notes.\n\n{pending_marker}"

    cleaned_body, removed = module.remove_release_body_pending_marker(
        body,
        "v0.0.283",
        youtube_url,
    )

    assert removed is True
    assert pending_marker not in cleaned_body
    assert cleaned_body == f"Release video: {youtube_url}\n\nExisting notes."


def test_backfill_retries_final_marker_edit_after_discord_post():
    module = load_backfill_module()
    module.POST_MARKER_RETRY_DELAY_SECONDS = 0
    youtube_url = "https://youtu.be/RIkxCaylRAQ"
    github = FakeGitHubReleaseClient(f"Release video: {youtube_url}\n\nExisting notes.\n")
    original_edit = github.edit_release_body
    edit_calls = 0
    posts: list[tuple[str, dict]] = []

    def flaky_edit(tag: str, body: str) -> None:
        nonlocal edit_calls
        edit_calls += 1
        if edit_calls == 2:
            raise module.BackfillError("transient gh release edit failure")
        original_edit(tag, body)

    github.edit_release_body = flaky_edit

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
    assert edit_calls == 3
    assert module.discord_backfill_marker("v0.0.283", youtube_url) in github.body
    assert module.discord_backfill_pending_marker("v0.0.283", youtube_url) not in github.body


def test_backfill_blocks_duplicate_post_when_final_marker_edit_keeps_failing():
    module = load_backfill_module()
    module.POST_MARKER_RETRY_DELAY_SECONDS = 0
    youtube_url = "https://youtu.be/RIkxCaylRAQ"
    github = FakeGitHubReleaseClient(f"Release video: {youtube_url}\n\nExisting notes.\n")
    original_edit = github.edit_release_body
    posts: list[tuple[str, dict]] = []

    def fail_after_post(tag: str, body: str) -> None:
        if posts:
            raise module.BackfillError("gh release edit failed after Discord post")
        original_edit(tag, body)

    github.edit_release_body = fail_after_post

    with pytest.raises(module.BackfillError, match="could not persist"):
        module.backfill_release_video_discord(
            tag="v0.0.283",
            youtube_url=youtube_url,
            repo="promptdriven/pdd",
            webhook_url="https://discord.example/webhook",
            github=github,
            post_discord=lambda webhook_url, payload: posts.append((webhook_url, payload)),
        )

    assert len(posts) == 1
    assert module.discord_backfill_marker("v0.0.283", youtube_url) not in github.body
    assert module.discord_backfill_pending_marker("v0.0.283", youtube_url) in github.body

    with pytest.raises(module.BackfillError, match="pending Discord backfill marker"):
        module.backfill_release_video_discord(
            tag="v0.0.283",
            youtube_url=youtube_url,
            repo="promptdriven/pdd",
            webhook_url="https://discord.example/webhook",
            github=github,
            post_discord=lambda webhook_url, payload: posts.append((webhook_url, payload)),
        )

    assert len(posts) == 1


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
    assert posts[0][1] == expected_discord_embed_payload(
        "v0.0.283",
        second_url,
        "promptdriven/pdd",
    )
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


def test_record_skip_marks_release_without_discord_or_youtube_url():
    module = load_backfill_module()
    github = FakeGitHubReleaseClient("Existing notes\n")
    posts = []

    result = module.record_release_video_skip(
        tag="v0.0.297",
        repo="promptdriven/pdd",
        reason="Provider quota and audit gate failures blocked safe publication.",
        github=github,
        post_discord=lambda webhook_url, payload: posts.append((webhook_url, payload)),
    )

    assert result.posted is False
    assert result.release_body_updated is True
    assert result.marker_added is True
    assert result.skipped_reason == "release-video-skipped"
    assert posts == []
    assert "Release video: skipped for v0.0.297." in github.body
    assert "Reason: Provider quota and audit gate failures blocked safe publication." in github.body
    assert module.release_video_skip_marker(
        "v0.0.297",
        "Provider quota and audit gate failures blocked safe publication.",
    ) in github.body


def test_record_skip_is_idempotent_for_same_reason():
    module = load_backfill_module()
    reason = "Provider quota and audit gate failures blocked safe publication."
    marker = module.release_video_skip_marker("v0.0.297", reason)
    github = FakeGitHubReleaseClient(
        "Release video: skipped for v0.0.297.\n"
        f"Reason: {reason}\n\n"
        "Existing notes\n\n"
        f"{marker}\n"
    )

    result = module.record_release_video_skip(
        tag="v0.0.297",
        repo="promptdriven/pdd",
        reason=reason,
        github=github,
    )

    assert result.posted is False
    assert result.release_body_updated is False
    assert result.marker_added is False
    assert result.skipped_reason == "release-video-skip-already-marked"
    assert github.edits == []


def test_github_client_uses_gh_release_view_and_edit_without_network():
    module = load_backfill_module()
    calls: list[tuple[list[str], str | None]] = []

    def fake_run(command, **kwargs):
        calls.append((command, kwargs.get("input")))
        if command[:3] == ["gh", "release", "view"]:
            return type(
                "Completed",
                (),
                {"returncode": 0, "stdout": "Existing notes\n", "stderr": ""},
            )()
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
