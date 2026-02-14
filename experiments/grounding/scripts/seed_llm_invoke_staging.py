#!/usr/bin/env python3
"""Seed the llm_invoke few-shot example into staging via the submitExample endpoint.

The llm_invoke example only exists in prod (submitted via `pdd fix --auto-submit`).
This script reads the raw prompt, canonical code, and test file from the local pdd
repo and POSTs them to staging's submitExample endpoint, which generates the
2048-dim Vertex AI embedding automatically.

Usage:
    cd pdd/experiments/grounding
    infisical run --env=staging -- python3 scripts/seed_llm_invoke_staging.py
"""

from __future__ import annotations

import os
import sys
from pathlib import Path

import requests

# ---------------------------------------------------------------------------
# Paths
# ---------------------------------------------------------------------------

PDD_REPO_ROOT = Path("/Users/gregtanaka/Documents/pdd_cloud/pdd")
PROMPT_FILE = PDD_REPO_ROOT / "prompts" / "llm_invoke_python.prompt"
CODE_FILE = PDD_REPO_ROOT / "pdd" / "llm_invoke.py"
TEST_FILE = PDD_REPO_ROOT / "tests" / "test_llm_invoke.py"

STAGING_BASE_URL = "https://us-central1-prompt-driven-development-stg.cloudfunctions.net"

# ---------------------------------------------------------------------------
# JWT helper (mirrors run_llm_invoke_stability.py)
# ---------------------------------------------------------------------------


def _get_staging_jwt() -> str:
    """Obtain a JWT for staging via Firebase Auth REST API."""
    api_key = os.environ.get("NEXT_PUBLIC_FIREBASE_API_KEY_STAGING")
    email = os.environ.get("STAGING_TEST_EMAIL")
    password = os.environ.get("STAGING_TEST_PASSWORD")

    if api_key and email and password:
        url = f"https://identitytoolkit.googleapis.com/v1/accounts:signInWithPassword?key={api_key}"
        resp = requests.post(url, json={
            "email": email,
            "password": password,
            "returnSecureToken": True,
        }, timeout=30)

        if resp.status_code == 200:
            print("Obtained fresh JWT via Firebase Auth")
            return resp.json()["idToken"]

        print(f"WARNING: Firebase Auth sign-in failed: {resp.status_code} {resp.text}")

    token = os.environ.get("PDD_JWT_TOKEN") or os.environ.get("JWT_TOKEN_STAGING")
    if token:
        print("Using JWT from environment variable (may be stale)")
        return token

    print("ERROR: Missing staging credentials. Set env vars:")
    print("  NEXT_PUBLIC_FIREBASE_API_KEY_STAGING, STAGING_TEST_EMAIL, STAGING_TEST_PASSWORD")
    sys.exit(1)


# ---------------------------------------------------------------------------
# Main
# ---------------------------------------------------------------------------


def main() -> int:
    """Read local files and POST to staging submitExample."""
    # Validate files exist
    for label, path in [("Prompt", PROMPT_FILE), ("Code", CODE_FILE), ("Test", TEST_FILE)]:
        if not path.exists():
            print(f"ERROR: {label} file not found: {path}")
            return 1

    raw_prompt = PROMPT_FILE.read_text(encoding="utf-8")
    canonical_code = CODE_FILE.read_text(encoding="utf-8")
    test_content = TEST_FILE.read_text(encoding="utf-8")

    print(f"Raw prompt:     {len(raw_prompt):,} chars ({PROMPT_FILE.name})")
    print(f"Canonical code: {len(canonical_code):,} chars ({CODE_FILE.name})")
    print(f"Test file:      {len(test_content):,} chars ({TEST_FILE.name})")

    # Get JWT
    jwt = _get_staging_jwt()
    headers = {
        "Authorization": f"Bearer {jwt}",
        "Content-Type": "application/json",
    }

    payload = {
        "command": "fix",
        "input": {
            "prompts": [{"content": raw_prompt, "filename": "llm_invoke_python.prompt"}],
            "code": [],
            "test": [],
        },
        "output": {
            "code": [{"content": canonical_code, "filename": "llm_invoke.py"}],
            "test": [{"content": test_content, "filename": "test_llm_invoke.py"}],
        },
        "metadata": {
            "title": "llm_invoke implementation",
            "description": "LiteLLM-based LLM invocation with model selection, caching, and cloud fallback",
            "language": "Python",
            "tags": ["llm_invoke", "experiment"],
            "isPublic": True,
            "price": 0,
        },
        "searchInput": raw_prompt,
    }

    url = f"{STAGING_BASE_URL}/submitExample"
    print(f"\nPOSTing to {url} ...")

    resp = requests.post(url, headers=headers, json=payload, timeout=120)
    print(f"HTTP {resp.status_code}")

    if resp.status_code == 200:
        data = resp.json()
        print(f"  Success: exampleId={data.get('exampleId')}")
        print(f"  Slug:    {data.get('slug')}")
        print(f"  Message: {data.get('message')}")
        return 0

    print(f"  Error: {resp.text[:500]}")
    return 1


if __name__ == "__main__":
    raise SystemExit(main())
