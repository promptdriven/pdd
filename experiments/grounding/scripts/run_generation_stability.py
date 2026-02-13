#!/usr/bin/env python3
"""Run generation stability experiment: grounding ON vs OFF.

Grounded arm: POST /generateCode (cloud endpoint with few-shot example retrieval).
Ungrounded arm: pdd --local --force --temperature 0.0 generate (local CLI, no grounding).

Both paths call the same code_generator() from pdd/pdd/code_generator.py.
The only meaningful difference is whether a few-shot example is injected.

Usage:
    python3 scripts/run_generation_stability.py --env staging [--runs 3] [--base-url URL]
"""

from __future__ import annotations

import argparse
import csv
import hashlib
import json
import os
import subprocess
import sys
import tempfile
import time
from datetime import datetime, timezone
from pathlib import Path
from typing import Any, Dict, List, Optional

import requests

# ---------------------------------------------------------------------------
# Defaults
# ---------------------------------------------------------------------------

STAGING_BASE_URL = "https://us-central1-prompt-driven-development-stg.cloudfunctions.net"
PROD_BASE_URL = "https://us-central1-prompt-driven-development.cloudfunctions.net"

RESULTS_DIR = Path(__file__).resolve().parent.parent / "results"
CSV_PATH = RESULTS_DIR / "generation_stability.csv"
GENERATIONS_DIR = RESULTS_DIR / "generations"

CSV_FIELDS = [
    "timestamp_utc",
    "env",
    "prompt_id",
    "domain",
    "language",
    "arm",
    "run_number",
    "http_status",
    "generated_code_hash",
    "generated_code_lines",
    "examples_used",
    "total_cost",
    "model_name",
    "response_time_ms",
]


# ---------------------------------------------------------------------------
# JWT helpers (mirrors run_retrieval.py)
# ---------------------------------------------------------------------------

def _get_staging_jwt() -> str:
    """Obtain a JWT for staging via Firebase Auth REST API, falling back to env var."""
    # Prefer generating a fresh token (env-var tokens may be stale)
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
            print("  Obtained fresh JWT via Firebase Auth")
            return resp.json()["idToken"]

        print(f"  WARNING: Firebase Auth sign-in failed: {resp.status_code} {resp.text}")

    # Fall back to pre-set token
    token = os.environ.get("PDD_JWT_TOKEN") or os.environ.get("JWT_TOKEN_STAGING")
    if token:
        print("  Using JWT from environment variable (may be stale)")
        return token

    print("ERROR: Missing staging credentials. Set PDD_JWT_TOKEN or provide")
    print("  NEXT_PUBLIC_FIREBASE_API_KEY_STAGING, STAGING_TEST_EMAIL, STAGING_TEST_PASSWORD")
    sys.exit(1)


def _get_prod_jwt() -> str:
    """Obtain a JWT for prod via env var."""
    token = os.environ.get("PDD_JWT_TOKEN")
    if not token:
        print("ERROR: PDD_JWT_TOKEN is required for prod environment.")
        sys.exit(1)
    return token


# ---------------------------------------------------------------------------
# CSV helpers
# ---------------------------------------------------------------------------

def _init_csv() -> None:
    """Create CSV with headers if it doesn't exist."""
    RESULTS_DIR.mkdir(parents=True, exist_ok=True)
    GENERATIONS_DIR.mkdir(parents=True, exist_ok=True)
    if not CSV_PATH.exists():
        with CSV_PATH.open("w", newline="", encoding="utf-8") as f:
            writer = csv.DictWriter(f, fieldnames=CSV_FIELDS)
            writer.writeheader()


def _append_row(row: Dict[str, Any]) -> None:
    """Append a single row to the CSV."""
    with CSV_PATH.open("a", newline="", encoding="utf-8") as f:
        writer = csv.DictWriter(f, fieldnames=CSV_FIELDS)
        writer.writerow(row)


# ---------------------------------------------------------------------------
# Code hashing
# ---------------------------------------------------------------------------

def _hash_code(code: str) -> str:
    """Return SHA-256 hex digest of normalized code (strip trailing whitespace)."""
    normalized = code.rstrip()
    return hashlib.sha256(normalized.encode("utf-8")).hexdigest()[:16]


# ---------------------------------------------------------------------------
# Generation calls
# ---------------------------------------------------------------------------

def _call_generate_cloud(
    base_url: str,
    headers: Dict[str, str],
    prompt: Dict[str, Any],
    temperature: float,
) -> Dict[str, Any]:
    """Call POST /generateCode (grounded arm) and return parsed result."""
    payload = {
        "promptContent": prompt["promptContent"],
        "language": prompt.get("language", "Python"),
        "temperature": temperature,
    }

    url = f"{base_url}/generateCode"
    start = time.monotonic()
    try:
        resp = requests.post(url, headers=headers, json=payload, timeout=300)
        elapsed_ms = int((time.monotonic() - start) * 1000)
    except Exception as e:
        return {
            "http_status": 0,
            "generated_code": "",
            "examples_used": [],
            "total_cost": 0.0,
            "model_name": "",
            "response_time_ms": 0,
            "error": str(e),
        }

    generated_code = ""
    examples_used: List[Dict[str, Any]] = []
    total_cost = 0.0
    model_name = ""

    if resp.status_code == 200:
        try:
            data = resp.json()
            generated_code = data.get("generatedCode", "")
            examples_used = data.get("examplesUsed", [])
            total_cost = data.get("totalCost", 0.0)
            model_name = data.get("modelName", "")
        except Exception:
            pass
    else:
        print(f"      HTTP {resp.status_code}: {resp.text[:200]}")

    return {
        "http_status": resp.status_code,
        "generated_code": generated_code,
        "examples_used": examples_used,
        "total_cost": total_cost,
        "model_name": model_name,
        "response_time_ms": elapsed_ms,
        "error": None,
    }


def _call_generate_local(
    prompt: Dict[str, Any],
    temperature: float,
) -> Dict[str, Any]:
    """Run pdd --local (ungrounded arm) via subprocess and return parsed result.

    Writes prompt to a temp .md file with frontmatter, invokes pdd CLI,
    reads generated code from output file, then cleans up.
    """
    language = prompt.get("language", "Python")
    prompt_content = prompt["promptContent"]

    # Create temp directory for prompt and output files
    tmp_dir = tempfile.mkdtemp(prefix="gen_stability_")
    prompt_path = os.path.join(tmp_dir, "prompt.md")
    output_path = os.path.join(tmp_dir, "output.py")

    try:
        # Write prompt file with frontmatter
        with open(prompt_path, "w", encoding="utf-8") as f:
            f.write(f"---\nlanguage: {language.lower()}\n---\n{prompt_content}")

        # Run pdd --local
        cmd = [
            "pdd", "--local", "--force",
            "--temperature", str(temperature),
            "generate", prompt_path,
            "--output", output_path,
        ]

        start = time.monotonic()
        try:
            result = subprocess.run(
                cmd,
                capture_output=True,
                text=True,
                timeout=300,
            )
            elapsed_ms = int((time.monotonic() - start) * 1000)
        except subprocess.TimeoutExpired:
            return {
                "http_status": 0,
                "generated_code": "",
                "examples_used": [],
                "total_cost": 0.0,
                "model_name": "local",
                "response_time_ms": int((time.monotonic() - start) * 1000),
                "error": "timeout (300s)",
            }
        except FileNotFoundError:
            return {
                "http_status": 0,
                "generated_code": "",
                "examples_used": [],
                "total_cost": 0.0,
                "model_name": "local",
                "response_time_ms": 0,
                "error": "pdd not found on PATH",
            }

        # Check for errors
        if result.returncode != 0:
            return {
                "http_status": 0,
                "generated_code": "",
                "examples_used": [],
                "total_cost": 0.0,
                "model_name": "local",
                "response_time_ms": elapsed_ms,
                "error": f"pdd exit code {result.returncode}: {result.stderr[:500]}",
            }

        # Read generated code from output file
        generated_code = ""
        if os.path.exists(output_path):
            with open(output_path, "r", encoding="utf-8") as f:
                generated_code = f.read()

        return {
            "http_status": 0,
            "generated_code": generated_code,
            "examples_used": [],
            "total_cost": 0.0,
            "model_name": "local",
            "response_time_ms": elapsed_ms,
            "error": None,
        }

    finally:
        # Clean up temp files
        for p in [prompt_path, output_path]:
            try:
                os.remove(p)
            except OSError:
                pass
        try:
            os.rmdir(tmp_dir)
        except OSError:
            pass


# ---------------------------------------------------------------------------
# Main runner
# ---------------------------------------------------------------------------

def run_experiment(
    env: str,
    runs: int = 3,
    temperature: float = 0.0,
    base_url: Optional[str] = None,
) -> int:
    """Run generation stability experiment. Returns 0 on success."""
    prompts_path = Path(__file__).resolve().parent.parent / "seed_data" / "generation_prompts.json"
    with prompts_path.open("r", encoding="utf-8") as f:
        data = json.load(f)
    prompts = data["prompts"]

    if base_url is None:
        base_url = STAGING_BASE_URL if env == "staging" else PROD_BASE_URL

    # Get JWT (needed for grounded/cloud arm)
    if env == "staging":
        jwt = _get_staging_jwt()
    else:
        jwt = _get_prod_jwt()

    headers = {
        "Authorization": f"Bearer {jwt}",
        "Content-Type": "application/json",
    }

    _init_csv()

    total_calls = len(prompts) * 2 * runs
    completed = 0
    errors = 0

    print(f"\nGeneration Stability Experiment")
    print(f"{'=' * 60}")
    print(f"Environment:  {env}")
    print(f"Grounded:     POST {base_url}/generateCode")
    print(f"Ungrounded:   pdd --local --force --temperature {temperature}")
    print(f"Prompts:      {len(prompts)}")
    print(f"Runs per arm: {runs}")
    print(f"Temperature:  {temperature}")
    print(f"Total calls:  {total_calls}")
    print(f"{'=' * 60}\n")

    for prompt in prompts:
        pid = prompt["id"]
        domain = prompt.get("domain", "unknown")
        language = prompt.get("language", "Python")

        print(f"Prompt: {pid} ({domain}/{language})")
        print(f"  \"{prompt['promptContent'][:60]}...\"")

        for arm in ["grounded", "ungrounded"]:
            print(f"  Arm: {arm}")

            for run_num in range(1, runs + 1):
                if arm == "grounded":
                    result = _call_generate_cloud(
                        base_url, headers, prompt,
                        temperature=temperature,
                    )
                else:
                    result = _call_generate_local(
                        prompt,
                        temperature=temperature,
                    )

                code = result["generated_code"]
                code_hash = _hash_code(code) if code else "EMPTY"
                code_lines = len(code.splitlines()) if code else 0
                examples = result["examples_used"]
                examples_str = ";".join(
                    ex.get("id", ex.get("slug", "?")) for ex in examples
                ) if examples else ""

                # Flag grounded runs with no example
                grounded_flag = ""
                if arm == "grounded" and not examples:
                    grounded_flag = " [NO_EXAMPLE]"

                # Save raw generated code
                if code:
                    gen_file = GENERATIONS_DIR / f"{pid}_{arm}_run{run_num}.py"
                    gen_file.write_text(code, encoding="utf-8")

                row = {
                    "timestamp_utc": datetime.now(timezone.utc).isoformat(),
                    "env": env,
                    "prompt_id": pid,
                    "domain": domain,
                    "language": language,
                    "arm": arm,
                    "run_number": run_num,
                    "http_status": result["http_status"],
                    "generated_code_hash": code_hash,
                    "generated_code_lines": code_lines,
                    "examples_used": examples_str,
                    "total_cost": result["total_cost"],
                    "model_name": result["model_name"],
                    "response_time_ms": result["response_time_ms"],
                }
                _append_row(row)

                # Status display
                if arm == "grounded":
                    status_icon = "OK" if result["http_status"] == 200 else "ERR"
                    is_error = result["http_status"] != 200
                else:
                    status_icon = "OK" if result["error"] is None else "ERR"
                    is_error = result["error"] is not None

                if is_error:
                    errors += 1

                completed += 1
                print(
                    f"    run {run_num}/{runs}: [{status_icon}] "
                    f"hash={code_hash} lines={code_lines} "
                    f"cost=${result['total_cost']:.4f} "
                    f"time={result['response_time_ms']}ms"
                    f"{grounded_flag}"
                )

        print()

    print(f"{'=' * 60}")
    print(f"Completed: {completed}/{total_calls} calls ({errors} errors)")
    print(f"CSV:        {CSV_PATH}")
    print(f"Generations: {GENERATIONS_DIR}/")

    return 0 if errors == 0 else 1


# ---------------------------------------------------------------------------
# CLI
# ---------------------------------------------------------------------------

def main() -> int:
    parser = argparse.ArgumentParser(
        description="Run generation stability experiment (grounding ON vs OFF)"
    )
    parser.add_argument(
        "--env",
        choices=["staging", "prod"],
        required=True,
        help="Target environment",
    )
    parser.add_argument(
        "--runs",
        type=int,
        default=3,
        help="Number of repetitions per arm per prompt (default: 3)",
    )
    parser.add_argument(
        "--temperature",
        type=float,
        default=0.0,
        help="Generation temperature (default: 0.0)",
    )
    parser.add_argument(
        "--base-url",
        default=None,
        help="Override base URL for generateCode endpoint (grounded arm)",
    )
    args = parser.parse_args()

    return run_experiment(
        env=args.env,
        runs=args.runs,
        temperature=args.temperature,
        base_url=args.base_url,
    )


if __name__ == "__main__":
    raise SystemExit(main())
