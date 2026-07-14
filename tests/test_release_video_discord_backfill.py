import importlib.util
import io
import os
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

    assert not posts


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
    assert not github.edits


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


def test_backfill_rejects_existing_skip_before_release_or_discord_mutation():
    module = load_backfill_module()
    reason = "Provider quota and audit gate failures blocked safe publication."
    marker = module.release_video_skip_marker("v0.0.297", reason)
    original_body = (
        "Release video: skipped for v0.0.297.\n"
        f"Reason: {reason}\n\n"
        "Existing notes\n\n"
        f"{marker}\n"
    )
    github = FakeGitHubReleaseClient(original_body)
    posts = []

    with pytest.raises(module.BackfillError, match="skip record"):
        module.backfill_release_video_discord(
            tag="v0.0.297",
            youtube_url="https://youtu.be/recoveredvideo",
            repo="promptdriven/pdd",
            webhook_url="https://discord.example/webhook",
            github=github,
            post_discord=lambda webhook_url, payload: posts.append(
                (webhook_url, payload)
            ),
        )

    assert posts == []
    assert github.edits == []
    assert github.body == original_body


def test_backfill_rejects_stale_mismatched_skip_marker_before_mutation():
    module = load_backfill_module()
    stale_marker = module.release_video_skip_marker(
        "v0.0.296",
        "An older release was intentionally skipped.",
    )
    original_body = f"Existing notes\n\n{stale_marker}\n"
    github = FakeGitHubReleaseClient(original_body)
    posts = []

    with pytest.raises(module.BackfillError, match="stale or mismatched"):
        module.backfill_release_video_discord(
            tag="v0.0.297",
            youtube_url="https://youtu.be/recoveredvideo",
            repo="promptdriven/pdd",
            webhook_url="https://discord.example/webhook",
            github=github,
            post_discord=lambda webhook_url, payload: posts.append(
                (webhook_url, payload)
            ),
        )

    assert posts == []
    assert github.edits == []
    assert github.body == original_body


def test_reconciled_skip_can_transition_to_one_completed_backfill():
    module = load_backfill_module()
    reason = "Provider quota blocked safe publication."
    skipped_body, _updated, _marker_added = module.ensure_release_body_has_skip_record(
        "Existing notes\n",
        "v0.0.297",
        reason,
    )
    reconciled_body = module.remove_release_video_skip_records(
        skipped_body,
        "v0.0.297",
    )
    github = FakeGitHubReleaseClient(reconciled_body)
    posts = []
    youtube_url = "https://youtu.be/recoveredvideo"

    result = module.backfill_release_video_discord(
        tag="v0.0.297",
        youtube_url=youtube_url,
        repo="promptdriven/pdd",
        webhook_url="https://discord.example/webhook",
        github=github,
        post_discord=lambda webhook_url, payload: posts.append(
            (webhook_url, payload)
        ),
    )

    assert result.posted is True
    assert len(posts) == 1
    assert module.SKIP_MARKER_NAME not in github.body
    assert "Release video: skipped" not in github.body
    assert module.discord_backfill_marker("v0.0.297", youtube_url) in github.body
    assert module.discord_backfill_pending_marker("v0.0.297", youtube_url) not in github.body


def test_reconciled_skip_ambiguous_delivery_stays_pending_not_skipped_or_complete():
    module = load_backfill_module()
    reason = "Provider quota blocked safe publication."
    skipped_body, _updated, _marker_added = module.ensure_release_body_has_skip_record(
        "Existing notes\n",
        "v0.0.297",
        reason,
    )
    reconciled_body = module.remove_release_video_skip_records(
        skipped_body,
        "v0.0.297",
    )
    github = FakeGitHubReleaseClient(reconciled_body)
    youtube_url = "https://youtu.be/recoveredvideo"

    def ambiguous_post(_webhook_url, _payload):
        raise module.DiscordWebhookError(
            "Discord webhook request failed: timed out",
            post_definitely_failed=False,
        )

    with pytest.raises(module.BackfillError, match="Inspect Discord before rerunning"):
        module.backfill_release_video_discord(
            tag="v0.0.297",
            youtube_url=youtube_url,
            repo="promptdriven/pdd",
            webhook_url="https://discord.example/webhook",
            github=github,
            post_discord=ambiguous_post,
        )

    assert module.SKIP_MARKER_NAME not in github.body
    assert "Release video: skipped" not in github.body
    assert module.discord_backfill_pending_marker("v0.0.297", youtube_url) in github.body
    assert module.discord_backfill_marker("v0.0.297", youtube_url) not in github.body


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


def test_record_skip_replaces_prior_skip_reason():
    module = load_backfill_module()
    old_reason = "Provider quota blocked publication."
    new_reason = "Provider quota and audit gate failures blocked safe publication."
    old_marker = module.release_video_skip_marker("v0.0.297", old_reason)
    github = FakeGitHubReleaseClient(
        "Release video: skipped for v0.0.297.\n"
        f"Reason: {old_reason}\n\n"
        "Existing notes\n\n"
        f"{old_marker}\n"
    )

    result = module.record_release_video_skip(
        tag="v0.0.297",
        repo="promptdriven/pdd",
        reason=new_reason,
        github=github,
    )

    assert result.release_body_updated is True
    assert result.marker_added is True
    assert f"Reason: {new_reason}" in github.body
    assert old_reason not in github.body
    assert old_marker not in github.body
    assert module.release_video_skip_marker("v0.0.297", new_reason) in github.body


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


@pytest.mark.parametrize("env_value", [None, "", "   "])
def test_gh_cli_env_defaults_to_gh_when_unset_or_blank(monkeypatch, env_value):
    module = load_backfill_module()
    if env_value is None:
        monkeypatch.delenv("GH_CLI", raising=False)
    else:
        monkeypatch.setenv("GH_CLI", env_value)

    args = module.parse_args(
        ["--tag", "v0.0.297", "--skip-reason", "No safe video was produced."]
    )

    assert args.gh_cli == "gh"


def test_gh_cli_env_preserves_non_empty_executable_path(monkeypatch):
    module = load_backfill_module()
    gh_path = os.fspath(Path("/opt/tools/gh"))
    monkeypatch.setenv("GH_CLI", gh_path)

    args = module.parse_args(
        ["--tag", "v0.0.297", "--skip-reason", "No safe video was produced."]
    )

    assert args.gh_cli == gh_path


@pytest.mark.parametrize(
    "mode_args",
    [
        ["--youtube-url", "https://youtu.be/RIkxCaylRAQ"],
        ["--skip-reason", "No safe video was produced."],
    ],
)
@pytest.mark.parametrize("blank_cli", ["", "   "])
def test_blank_explicit_gh_cli_fails_before_github_mutation(
    monkeypatch,
    capsys,
    mode_args,
    blank_cli,
):
    module = load_backfill_module()
    constructed = []

    def fail_if_constructed(**kwargs):
        constructed.append(kwargs)
        raise AssertionError("GitHub client must not be constructed")

    monkeypatch.setattr(module, "GitHubReleaseClient", fail_if_constructed)

    result = module.main(
        ["--tag", "v0.0.297", *mode_args, "--gh-cli", blank_cli]
    )

    assert result == 1
    assert constructed == []
    assert "--gh-cli must be a non-empty executable path" in capsys.readouterr().err


@pytest.mark.parametrize(
    ("mode_args", "operation_name"),
    [
        (
            ["--youtube-url", "https://youtu.be/RIkxCaylRAQ"],
            "backfill_release_video_discord",
        ),
        (["--skip-reason", "No safe video was produced."], "record_release_video_skip"),
    ],
)
def test_both_modes_use_shared_github_client_with_explicit_override(
    monkeypatch,
    mode_args,
    operation_name,
):
    module = load_backfill_module()
    captured = {}
    fake_github = object()

    def fake_client(**kwargs):
        captured["client_kwargs"] = kwargs
        return fake_github

    def fake_operation(**kwargs):
        captured["operation_kwargs"] = kwargs
        return module.BackfillResult(
            posted=False,
            release_body_updated=False,
            marker_added=False,
            skipped_reason="release-video-skip-already-marked",
        )

    monkeypatch.setattr(module, "GitHubReleaseClient", fake_client)
    monkeypatch.setattr(module, operation_name, fake_operation)

    result = module.main(
        ["--tag", "v0.0.297", *mode_args, "--gh-cli", "/opt/tools/gh"]
    )

    assert result == 0
    assert captured["client_kwargs"] == {
        "gh_cli": "/opt/tools/gh",
        "repo": "promptdriven/pdd",
    }
    assert captured["operation_kwargs"]["github"] is fake_github
