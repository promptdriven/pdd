def parse_user_id(raw: object) -> str | None:
    """
    Parses a user ID from a string or dictionary.

    Args:
        raw: Input data, expected to be "user:<id>" or {"user_id": "<id>"}.

    Returns:
        The trimmed user ID string, or None if input is invalid.
    """
    user_id = None

    if isinstance(raw, str) and raw.startswith("user:"):
        user_id = raw[5:]
    elif isinstance(raw, dict):
        user_id = raw.get("user_id")

    if isinstance(user_id, str):
        return user_id.strip()
    
    return None