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


class _NoRedirectHandler(urllib.request.HTTPRedirectHandler):
    """Reject redirects before urllib can forward refresh credentials."""

    # Signature is defined by urllib's redirect-handler protocol.
    # pylint: disable=too-many-arguments,too-many-positional-arguments
    def redirect_request(self, req, fp, code, msg, headers, newurl):
        del req, fp, code, msg, headers, newurl
        raise urllib.error.HTTPError(
            "redirects-disabled", 400, "redirects disabled", {}, None
        )


_NO_REDIRECT_OPENER = urllib.request.build_opener(_NoRedirectHandler()).open


def exchange_token(
    firebase_api_key: str,
    refresh_token: str,
    *,
    opener: Callable[..., object] = _NO_REDIRECT_OPENER,
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
            if (
                getattr(response, "status", None) != 200
                or response.geturl() != url
            ):
                raise RuntimeError("token exchange transport failed")
            return response.read()
    except urllib.error.HTTPError as error:
        # Firebase uses structured HTTP-error bodies for quota/auth failures.
        # Return the body for the caller's existing sanitized category parser;
        # never render the exception because its URL contains the API key.
        if error.code in {301, 302, 303, 307, 308} or error.geturl() != url:
            raise RuntimeError("token exchange transport failed") from error
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
