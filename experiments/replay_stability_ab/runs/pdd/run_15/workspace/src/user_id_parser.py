# src/user_id_parser.py
import collections
import re

ParseResult = collections.namedtuple('ParseResult', ['user_id', 'source'])

_DEFAULT_RESERVED = {'admin', 'root', 'system'}
_VALID_ID_RE = re.compile(r'^[a-z0-9_-]{3,20}$')
_CONSECUTIVE_SPECIALS_RE = re.compile(r'[_-]{2}')


def parse_user_id(raw, reserved_ids=None, strict=False):
    '''Parse a user ID from various input formats, returning ParseResult or None.'''
    try:
        user_id, source = _extract(raw)
    except Exception:
        return None

    if user_id is None:
        return None

    # Normalize
    user_id = user_id.strip().lower()

    # Validate
    if not _VALID_ID_RE.match(user_id):
        return None

    reserved = reserved_ids if reserved_ids is not None else _DEFAULT_RESERVED
    if user_id in reserved:
        return None

    if strict and _CONSECUTIVE_SPECIALS_RE.search(user_id):
        return None

    return ParseResult(user_id=user_id, source=source)


def parse_user_ids(items, reserved_ids=None, strict=False):
    '''Batch-process a list of items through parse_user_id, preserving order.'''
    return [parse_user_id(item, reserved_ids=reserved_ids, strict=strict) for item in items]


def _extract(raw):
    '''Extract (raw_id, source) from the supported input formats.

    Returns (None, None) when the format is unrecognised.
    '''
    if isinstance(raw, dict):
        # dict_flat: {'user_id': '<id>'}
        if 'user_id' in raw:
            val = raw['user_id']
            if not isinstance(val, str):
                return None, None
            return val, 'dict_flat'
        # dict_nested: {'user': {'id': '<id>'}}
        if 'user' in raw and isinstance(raw['user'], dict) and 'id' in raw['user']:
            val = raw['user']['id']
            if not isinstance(val, str):
                return None, None
            return val, 'dict_nested'
        return None, None

    if isinstance(raw, str):
        # 'user:<id>'
        if raw.startswith('user:'):
            return raw[5:], 'string'
        # 'email:user@domain'
        if raw.startswith('email:'):
            email_part = raw[6:]
            if '@' not in email_part:
                return None, None
            username = email_part.split('@', 1)[0]
            return username, 'email'
        return None, None

    return None, None