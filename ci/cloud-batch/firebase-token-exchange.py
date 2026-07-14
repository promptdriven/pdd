#!/usr/bin/env python3
"""Exchange Cloud test credentials without placing them in process arguments."""
# pylint: disable=invalid-name

from __future__ import annotations

import os
import sys
import urllib.error
import urllib.parse
import urllib.request
from collections.abc import Callable


def exchange_token(
    firebase_api_key: str,
    refresh_token: str,
    *,
    opener: Callable[..., object] = urllib.request.urlopen,
) -> bytes:
    """Return the provider response while keeping request values in memory."""
    url = "https://securetoken.googleapis.com/v1/token?" + urllib.parse.urlencode(
        {"key": firebase_api_key}
    )
    body = urllib.parse.urlencode(
        {"grant_type": "refresh_token", "refresh_token": refresh_token}
    ).encode("ascii")
    request = urllib.request.Request(
        url,
        data=body,
        headers={"Content-Type": "application/x-www-form-urlencoded"},
    )
    try:
        with opener(request, timeout=15) as response:
            return response.read()
    except urllib.error.HTTPError as error:
        # Firebase uses structured HTTP-error bodies for quota/auth failures.
        # Return the body for the caller's existing sanitized category parser;
        # never render the exception because its URL contains the API key.
        return error.read()
    except (OSError, urllib.error.URLError) as error:
        raise RuntimeError("token exchange transport failed") from error


def main() -> int:
    """Read credentials from the inherited environment and write only response bytes."""
    firebase_api_key = os.environ.get("FIREBASE_API_KEY", "")
    refresh_token = os.environ.get("PDD_REFRESH_TOKEN", "")
    if not firebase_api_key or not refresh_token:
        return 2
    try:
        response = exchange_token(firebase_api_key, refresh_token)
    except RuntimeError:
        return 3
    if not response or len(response) > 1_000_000:
        return 4
    sys.stdout.buffer.write(response)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
