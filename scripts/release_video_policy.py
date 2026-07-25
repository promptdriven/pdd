"""Fail-closed policy for release-video operations."""

from __future__ import annotations


RELEASE_VIDEO_OPT_OUT_TAGS = frozenset({"v0.0.309"})


def release_video_opt_out_reason(tag: str) -> str | None:
    """Return the release-video denial reason for an exact excluded tag."""
    if tag in RELEASE_VIDEO_OPT_OUT_TAGS:
        return (
            f"{tag} is opted out and release video operations must not create, "
            "upload, or distribute a video."
        )
    return None
