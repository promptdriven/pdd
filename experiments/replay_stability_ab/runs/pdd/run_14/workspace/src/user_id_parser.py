'''User ID parser with normalization and validation.'''

import re

_VALID_PATTERN = re.compile(r'^[a-z0-9_-]{3,20}$')
_RESERVED_IDS = frozenset({'admin', 'root', 'system'})


def parse_user_id(raw: object) -> str | None:
    '''Extract, normalize, and validate a user ID from string or dict input.

    Accepted formats:
        - 'user:<id>'
        - {'user_id': '<id>'}
        - {'user': {'id': '<id>'}}

    Returns the normalized (trimmed, lowercased) ID if valid, else None.
    '''
    uid = _extract(raw)
    if uid is None:
        return None
    return _validate(uid)


def _extract(raw: object) -> str | None:
    '''Extract raw ID string from supported input shapes.'''
    if isinstance(raw, str):
        if raw.startswith('user:'):
            return raw[len('user:'):]
        return None

    if isinstance(raw, dict):
        # Form: {'user_id': '<id>'}
        if 'user_id' in raw:
            val = raw['user_id']
            return val if isinstance(val, str) else None

        # Form: {'user': {'id': '<id>'}}
        if 'user' in raw:
            nested = raw['user']
            if isinstance(nested, dict) and 'id' in nested:
                val = nested['id']
                return val if isinstance(val, str) else None

    return None


def _validate(uid: str) -> str | None:
    '''Normalize and validate an extracted ID string.'''
    uid = uid.strip().lower()

    if not _VALID_PATTERN.match(uid):
        return None

    if uid in _RESERVED_IDS:
        return None

    return uid