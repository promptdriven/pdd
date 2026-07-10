"""Shared credential-removal policy for untrusted child processes."""

SECRET_ENV_MARKERS = (
    "API_KEY",
    "CREDENTIAL",
    "PASSWORD",
    "SECRET",
    "SIGNING_KEY",
    "TOKEN",
)
