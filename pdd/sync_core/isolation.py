"""Shared environment policy for untrusted child processes."""

from __future__ import annotations

import os
from pathlib import Path

SECRET_ENV_MARKERS = (
    "API_KEY",
    "CREDENTIAL",
    "PASSWORD",
    "SECRET",
    "SIGNING_KEY",
    "TOKEN",
)

SAFE_UNTRUSTED_ENV_KEYS = frozenset(
    {
        "CI",
        "HOME",
        "LANG",
        "LC_ALL",
        "PATH",
        "PATHEXT",
        "SSL_CERT_DIR",
        "SSL_CERT_FILE",
        "SYSTEMROOT",
        "TEMP",
        "TMP",
        "TMPDIR",
        "USERPROFILE",
        "WINDIR",
    }
)

BLOCKED_CAPABILITY_TOKENS = (
    "ATTESTATION",
    "CERTIFICATE",
    "SIGNER",
    "RELEASED_CHECKER",
)


def untrusted_child_environment(
    *,
    home: Path | None = None,
    extra: dict[str, str] | None = None,
    drop: set[str] | None = None,
) -> dict[str, str]:
    """Return a small environment for candidate-authored code."""
    environment = {
        key: value
        for key, value in os.environ.items()
        if key.upper() in SAFE_UNTRUSTED_ENV_KEYS
        and not any(marker in key.upper() for marker in SECRET_ENV_MARKERS)
        and not any(token in key.upper() for token in BLOCKED_CAPABILITY_TOKENS)
    }
    if home is not None:
        environment["HOME"] = str(home)
        environment["XDG_CONFIG_HOME"] = str(home / ".config")
        environment["XDG_CACHE_HOME"] = str(home / ".cache")
    for key in drop or set():
        environment.pop(key, None)
    environment.update(extra or {})
    return environment
