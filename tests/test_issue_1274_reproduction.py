"""Regression reproduction for issue #1274.

The web auth status path should not report an authenticated session when the
cached Firebase ID token belongs to a different PDD environment. A stale prod
token presented to staging/billing can make the UI look signed in while the
backend treats the user as unknown and sends them through signup.
"""

from __future__ import annotations

import base64
import json
import time
from typing import Any

from pdd import auth_service


def _unsigned_jwt(payload: dict[str, Any]) -> str:
    """Build an unsigned JWT-shaped token for cache/audience tests."""
    header = {"alg": "none", "typ": "JWT"}

    def encode(value: dict[str, Any]) -> str:
        raw = json.dumps(value, separators=(",", ":")).encode("utf-8")
        return base64.urlsafe_b64encode(raw).decode("ascii").rstrip("=")

    return f"{encode(header)}.{encode(payload)}.signature"


def test_issue_1274_reproduction_auth_status_rejects_wrong_environment_cached_jwt(
    monkeypatch,
    tmp_path,
):
    """Auth status must not treat a prod-audience token as signed in on staging.

    The reported billing redirect happens after sign-in. This reproduces the
    local auth-state half of that failure: the frontend/server auth endpoint can
    say "authenticated" from a cached JWT even when that token has the wrong
    Firebase audience for the selected PDD environment.
    """
    monkeypatch.setenv("PDD_ENV", "staging")
    monkeypatch.setenv("STAGING_PROJECT_ID", "prompt-driven-development-stg")
    monkeypatch.setattr(
        auth_service,
        "_get_refresh_token_status",
        lambda: (None, None),
    )

    cache_file = tmp_path / "jwt_cache"
    now = int(time.time())
    cache_file.write_text(
        json.dumps(
            {
                "id_token": _unsigned_jwt(
                    {
                        "aud": "prompt-driven-development",
                        "email": "signed-in@example.com",
                        "exp": now + 3600,
                    }
                ),
                "expires_at": now + 3600,
            }
        ),
        encoding="utf-8",
    )
    monkeypatch.setattr(auth_service, "JWT_CACHE_FILE", cache_file)

    status = auth_service.get_auth_status()

    assert status == {
        "authenticated": False,
        "cached": False,
        "expires_at": None,
    }
    assert auth_service.get_cached_jwt() is None
