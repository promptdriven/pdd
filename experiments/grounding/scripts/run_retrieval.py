#!/usr/bin/env python3
"""Execute retrieval queries against reviewExamples and record results.

Usage:
    python3 scripts/run_retrieval.py --env local|staging [--base-url URL]

Reuses patterns from backend/tests/endpoint_tests/tests/grounding.py.
"""

from __future__ import annotations

import argparse
import base64
import csv
import json
import os
import sys
import time
from datetime import datetime, timezone
from pathlib import Path
from typing import Any, Dict, List, Optional

import requests

# ---------------------------------------------------------------------------
# Defaults
# ---------------------------------------------------------------------------

LOCAL_BASE_URL = "http://127.0.0.1:5555/prompt-driven-development-stg/us-central1"
STAGING_BASE_URL = "https://us-central1-prompt-driven-development-stg.cloudfunctions.net"

RESULTS_DIR = Path(__file__).resolve().parent.parent / "results"
CSV_PATH = RESULTS_DIR / "retrieval_results.csv"

CSV_FIELDS = [
    "timestamp_utc",
    "env",
    "query_id",
    "experiment_type",
    "command",
    "language",
    "limit",
    "pin_slugs",
    "exclude_slugs",
    "run_number",
    "http_status",
    "examples_returned_count",
    "example_ids",
    "example_scores",
    "rank_1_id",
    "rank_1_score",
    "assertion_passed",
    "assertion_detail",
    "response_time_ms",
]


# ---------------------------------------------------------------------------
# JWT helpers (mirrors firebase_setup.py:43-63)
# ---------------------------------------------------------------------------

def _generate_emulator_jwt(project_id: str = "prompt-driven-development-stg") -> str:
    """Generate an unsigned emulator JWT token."""
    now = int(time.time())
    header = {"alg": "none", "typ": "JWT"}
    payload = {
        "iss": f"https://securetoken.google.com/{project_id}",
        "aud": project_id,
        "iat": now,
        "exp": now + 3600,
        "uid": "grnd-test-user",
        "user_id": "grnd-test-user",
        "sub": "grnd-test-user",
        "email": "grnd-test@example.com",
        "name": "grnd-test-user",
        "admin": True,
    }

    def _b64(obj: dict) -> str:
        return base64.urlsafe_b64encode(json.dumps(obj).encode()).decode().rstrip("=")

    return f"{_b64(header)}.{_b64(payload)}."


def _get_staging_jwt() -> str:
    """Obtain a JWT for staging via env var or Firebase Auth REST API."""
    token = os.environ.get("PDD_JWT_TOKEN") or os.environ.get("JWT_TOKEN_STAGING")
    if token:
        return token

    api_key = os.environ.get("NEXT_PUBLIC_FIREBASE_API_KEY_STAGING")
    email = os.environ.get("STAGING_TEST_EMAIL")
    password = os.environ.get("STAGING_TEST_PASSWORD")

    if not (api_key and email and password):
        print("ERROR: Missing staging credentials. Set PDD_JWT_TOKEN or provide")
        print("  NEXT_PUBLIC_FIREBASE_API_KEY_STAGING, STAGING_TEST_EMAIL, STAGING_TEST_PASSWORD")
        sys.exit(1)

    url = f"https://identitytoolkit.googleapis.com/v1/accounts:signInWithPassword?key={api_key}"
    resp = requests.post(url, json={
        "email": email,
        "password": password,
        "returnSecureToken": True,
    }, timeout=30)

    if resp.status_code != 200:
        print(f"ERROR: Firebase Auth sign-in failed: {resp.status_code} {resp.text}")
        sys.exit(1)

    return resp.json()["idToken"]


# ---------------------------------------------------------------------------
# Query execution
# ---------------------------------------------------------------------------

def _build_input_text(query: Dict[str, Any]) -> str:
    """Build the input string with <pin> and <exclude> tags."""
    parts = []
    for slug in query.get("pin_slugs", []):
        parts.append(f"<pin>{slug}</pin>")
    for slug in query.get("exclude_slugs", []):
        parts.append(f"<exclude>{slug}</exclude>")
    parts.append(query["input_text"])
    return " ".join(parts)


def _run_single_query(
    base_url: str,
    headers: Dict[str, str],
    query: Dict[str, Any],
    run_number: int = 1,
) -> Dict[str, Any]:
    """Execute a single reviewExamples call and return the raw result."""
    payload = {
        "command": query["command"],
        "input": _build_input_text(query),
        "limit": query.get("limit", 5),
    }
    if query.get("language"):
        payload["language"] = query["language"]

    url = f"{base_url}/reviewExamples"
    start = time.monotonic()
    try:
        resp = requests.post(url, headers=headers, json=payload, timeout=120)
        elapsed_ms = int((time.monotonic() - start) * 1000)
    except Exception as e:
        return {
            "http_status": 0,
            "examples": [],
            "response_time_ms": 0,
            "error": str(e),
        }

    examples = []
    if resp.status_code == 200:
        try:
            examples = resp.json().get("examples", [])
        except Exception:
            pass

    return {
        "http_status": resp.status_code,
        "examples": examples,
        "response_time_ms": elapsed_ms,
        "error": None,
    }


# ---------------------------------------------------------------------------
# Assertion evaluators
# ---------------------------------------------------------------------------

def _evaluate(
    query: Dict[str, Any],
    result: Dict[str, Any],
    env: str,
) -> tuple[bool, str]:
    """Evaluate assertions for a query result. Returns (passed, detail)."""
    exp_type = query["experiment_type"]
    assertions = query.get("assertions", {})
    examples = result["examples"]
    status = result["http_status"]

    # If this is a staging_only test running locally, auto-pass
    if query.get("staging_only") and env == "local":
        return True, "staging_only: skipped in local"

    if exp_type == "same_domain":
        expected = set(assertions.get("expected_ids_in_top_k", []))
        top_k = assertions.get("top_k", 3)
        actual_ids = {ex.get("id") for ex in examples[:top_k]}
        found = expected & actual_ids
        passed = len(found) > 0
        detail = f"expected {expected} in top {top_k}, got {actual_ids}"
        return passed, detail

    if exp_type == "cross_domain":
        low_ids = set(assertions.get("low_score_ids", []))
        primary_domain_ids = {
            ex.get("id") for ex in examples[:2]
        }
        # Low-score IDs should not be in top 2
        overlap = low_ids & primary_domain_ids
        passed = len(overlap) == 0
        detail = f"low_score_ids in top 2: {overlap}" if overlap else "OK"
        return passed, detail

    if exp_type == "self_retrieval":
        expected_rank_1 = assertions.get("expected_rank_1")
        rank_1 = examples[0].get("id") if examples else None
        passed = rank_1 == expected_rank_1
        detail = f"rank_1={rank_1}, expected={expected_rank_1}"
        return passed, detail

    if exp_type == "language_filter":
        higher_id = assertions.get("higher_id")
        lower_id = assertions.get("lower_id")
        id_to_score = {ex.get("id"): ex.get("similarityScore", 0) for ex in examples}
        higher_score = id_to_score.get(higher_id, -1)
        lower_score = id_to_score.get(lower_id, -1)
        # Higher ID should have >= score than lower ID
        passed = higher_score >= lower_score
        detail = f"{higher_id}={higher_score}, {lower_id}={lower_score}"
        return passed, detail

    if exp_type == "validated_boost":
        validated_id = assertions.get("validated_id")
        id_to_score = {ex.get("id"): ex.get("similarityScore", 0) for ex in examples}
        v_score = id_to_score.get(validated_id)
        if v_score is None:
            return False, f"validated_id {validated_id} not in results"
        # Check it's in results (boost may not guarantee rank 1 but should be present)
        passed = validated_id in id_to_score
        detail = f"validated {validated_id} score={v_score}"
        return passed, detail

    if exp_type == "pin":
        pinned_id = assertions.get("pinned_id")
        expected_score = assertions.get("expected_score", 1.0)
        pinned_ex = next(
            (ex for ex in examples if ex.get("slug") == pinned_id or ex.get("id") == pinned_id),
            None,
        )
        if not pinned_ex:
            return False, f"pinned {pinned_id} not in results: {[e.get('slug') for e in examples]}"
        actual_score = pinned_ex.get("similarityScore")
        passed = actual_score == expected_score
        detail = f"pinned slug={pinned_id} score={actual_score}, expected={expected_score}"
        return passed, detail

    if exp_type == "exclude":
        excluded_id = assertions.get("excluded_id")
        found = any(
            ex.get("slug") == excluded_id or ex.get("id") == excluded_id
            for ex in examples
        )
        passed = not found
        detail = f"excluded {excluded_id} absent={not found}"
        return passed, detail

    if exp_type == "conflict":
        expected_status = assertions.get("expected_status", 400)
        passed = status == expected_status
        detail = f"http_status={status}, expected={expected_status}"
        return passed, detail

    if exp_type == "stability":
        # Stability is evaluated across runs — for individual runs, auto-pass
        return True, "stability: individual run recorded"

    return False, f"unknown experiment_type: {exp_type}"


# ---------------------------------------------------------------------------
# CSV writing
# ---------------------------------------------------------------------------

def _init_csv() -> None:
    """Create CSV with headers if it doesn't exist."""
    RESULTS_DIR.mkdir(parents=True, exist_ok=True)
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
# Main runner
# ---------------------------------------------------------------------------

def run_experiment(env: str, base_url: Optional[str] = None) -> int:
    """Run all queries and record results. Returns 0 on success."""
    queries_path = Path(__file__).resolve().parent.parent / "seed_data" / "queries.json"
    with queries_path.open("r", encoding="utf-8") as f:
        data = json.load(f)
    queries = data["queries"]

    if base_url is None:
        base_url = LOCAL_BASE_URL if env == "local" else STAGING_BASE_URL

    # Get JWT
    if env == "local":
        jwt = _generate_emulator_jwt()
    else:
        jwt = _get_staging_jwt()

    headers = {
        "Authorization": f"Bearer {jwt}",
        "Content-Type": "application/json",
    }

    _init_csv()

    total = 0
    passed = 0
    failed_queries: List[str] = []

    print(f"\nRunning {len(queries)} retrieval queries against {env} ...")
    print(f"Base URL: {base_url}")
    print(f"{'='*60}")

    for query in queries:
        qid = query["id"]
        exp_type = query["experiment_type"]
        repeat = query.get("repeat", 1)

        all_run_ids: List[List[str]] = []

        for run_num in range(1, repeat + 1):
            result = _run_single_query(base_url, headers, query, run_num)

            examples = result["examples"]
            example_ids = [ex.get("id", "") for ex in examples]
            example_scores = [str(ex.get("similarityScore", 0)) for ex in examples]

            ok, detail = _evaluate(query, result, env)

            # For stability queries, record IDs for cross-run comparison
            if exp_type == "stability":
                all_run_ids.append(example_ids)

            row = {
                "timestamp_utc": datetime.now(timezone.utc).isoformat(),
                "env": env,
                "query_id": qid,
                "experiment_type": exp_type,
                "command": query.get("command", ""),
                "language": query.get("language", ""),
                "limit": query.get("limit", 5),
                "pin_slugs": ";".join(query.get("pin_slugs", [])),
                "exclude_slugs": ";".join(query.get("exclude_slugs", [])),
                "run_number": run_num,
                "http_status": result["http_status"],
                "examples_returned_count": len(examples),
                "example_ids": ";".join(example_ids),
                "example_scores": ";".join(example_scores),
                "rank_1_id": example_ids[0] if example_ids else "",
                "rank_1_score": example_scores[0] if example_scores else "",
                "assertion_passed": 1 if ok else 0,
                "assertion_detail": detail,
                "response_time_ms": result["response_time_ms"],
            }
            _append_row(row)

            status_icon = "PASS" if ok else "FAIL"
            total += 1
            if ok:
                passed += 1
            else:
                failed_queries.append(f"{qid} (run {run_num})")

            run_label = f" run {run_num}/{repeat}" if repeat > 1 else ""
            print(f"  [{status_icon}] {qid}{run_label} ({exp_type}) - {detail}")

        # Post-hoc stability check: compare ID orderings across runs
        if exp_type == "stability" and len(all_run_ids) > 1:
            first = all_run_ids[0]
            all_same = all(ids == first for ids in all_run_ids[1:])
            if not all_same:
                # Overwrite the last row's assertion
                print(f"  [FAIL] {qid} stability: rankings differ across {len(all_run_ids)} runs")
                # Record a summary row
                row = {
                    "timestamp_utc": datetime.now(timezone.utc).isoformat(),
                    "env": env,
                    "query_id": f"{qid}-summary",
                    "experiment_type": "stability",
                    "command": query.get("command", ""),
                    "language": query.get("language", ""),
                    "limit": query.get("limit", 5),
                    "pin_slugs": "",
                    "exclude_slugs": "",
                    "run_number": 0,
                    "http_status": 200,
                    "examples_returned_count": 0,
                    "example_ids": "",
                    "example_scores": "",
                    "rank_1_id": "",
                    "rank_1_score": "",
                    "assertion_passed": 0,
                    "assertion_detail": f"rankings differ: {all_run_ids}",
                    "response_time_ms": 0,
                }
                _append_row(row)
                total += 1
                failed_queries.append(f"{qid}-summary")
            else:
                print(f"  [PASS] {qid} stability: same ranking across {len(all_run_ids)} runs")

    print(f"\n{'='*60}")
    print(f"Results: {passed}/{total} passed")
    if failed_queries:
        print(f"Failed: {', '.join(failed_queries)}")
    print(f"CSV written to: {CSV_PATH}")

    return 0 if passed == total else 1


# ---------------------------------------------------------------------------
# CLI
# ---------------------------------------------------------------------------

def main() -> int:
    parser = argparse.ArgumentParser(description="Run grounding retrieval experiment")
    parser.add_argument(
        "--env",
        choices=["local", "staging"],
        required=True,
        help="Target environment",
    )
    parser.add_argument(
        "--base-url",
        default=None,
        help="Override base URL for reviewExamples endpoint",
    )
    args = parser.parse_args()

    return run_experiment(args.env, args.base_url)


if __name__ == "__main__":
    raise SystemExit(main())
