import re

# Configuration
ID_PATTERN = re.compile(r"^[a-z0-9_-]{3,20}$")
RESERVED_IDS = {"admin", "root", "system"}

def parse_user_id(raw: object) -> str | None:
    """
    Extracts, normalizes, and validates a user ID from various input formats.
    Returns None if the input is invalid or the ID is malformed/reserved.
    """
    extracted_id = None

    # 1. Extract raw ID based on input type
    try:
        if isinstance(raw, str):
            if raw.startswith("user:"):
                extracted_id = raw[5:]
        elif isinstance(raw, dict):
            # Check {"user_id": "<id>"}
            if "user_id" in raw:
                extracted_id = raw["user_id"]
            # Check {"user": {"id": "<id>"}}
            elif "user" in raw and isinstance(raw["user"], dict):
                extracted_id = raw["user"].get("id")
    except (AttributeError, TypeError):
        # Catch unexpected types inside nested structures
        return None

    # 2. Basic type check on extracted value
    if not isinstance(extracted_id, str):
        return None

    # 3. Normalize
    normalized_id = extracted_id.strip().lower()

    # 4. Validate Regex
    if not ID_PATTERN.match(normalized_id):
        return None

    # 5. Check Reserved Words
    if normalized_id in RESERVED_IDS:
        return None

    return normalized_id