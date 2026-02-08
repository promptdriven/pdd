"""Baseline user id parser used for replay-stability experiments."""


def parse_user_id(raw: object) -> str | None:
    """Extract a user id from strings like 'user:abc123'."""
    if not isinstance(raw, str):
        return None

    text = raw.strip()
    if ":" not in text:
        return None

    prefix, user_id = text.split(":", 1)
    if prefix != "user":
        return None

    cleaned = user_id.strip()
    if not cleaned:
        return None

    return cleaned
