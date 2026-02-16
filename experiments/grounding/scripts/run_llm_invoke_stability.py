#!/usr/bin/env python3
"""Run module regeneration stability experiment: grounded vs ungrounded.

Grounded arm: POST /generateCode on prod/staging (vector search finds
few-shot example, injects it as XML, calls code_generator()).
Ungrounded arm: litellm direct call with same model but no few-shot examples.
Ungrounded-pdd arm: `pdd generate --local` (auto-discovers test files, no few-shot).

All arms use vertex_ai/gemini-3-flash-preview at temperature 1.0 by default.

Usage:
    python3 scripts/run_llm_invoke_stability.py --env prod --runs 5 --temperature 1.0
    python3 scripts/run_llm_invoke_stability.py --env prod --runs 5 --module sync_orchestration
    python3 scripts/run_llm_invoke_stability.py --env prod --runs 5 --arms ungrounded-pdd
"""

from __future__ import annotations

import argparse
import ast
import csv
import hashlib
import os
import py_compile
import subprocess
import sys
import tempfile
import time
import uuid
from datetime import datetime, timezone
from pathlib import Path
from typing import Any, Dict, List, Optional

import requests

# ---------------------------------------------------------------------------
# Defaults
# ---------------------------------------------------------------------------

STAGING_BASE_URL = "https://us-central1-prompt-driven-development-stg.cloudfunctions.net"
PROD_BASE_URL = "https://us-central1-prompt-driven-development.cloudfunctions.net"

PDD_REPO_ROOT = Path("/Users/gregtanaka/Documents/pdd_cloud/pdd")

MODULE_NAME = "llm_invoke"
PROMPT_FILE = PDD_REPO_ROOT / "prompts" / f"{MODULE_NAME}_python.prompt"

RESULTS_DIR = Path(__file__).resolve().parent.parent / "results"
CSV_PATH = RESULTS_DIR / f"{MODULE_NAME}_stability.csv"
GENERATIONS_DIR = RESULTS_DIR / f"{MODULE_NAME}_generations"

CSV_FIELDS = [
    "timestamp_utc",
    "env",
    "arm",
    "run_number",
    "http_status",
    "generated_code_hash",
    "generated_code_lines",
    "function_count",
    "class_count",
    "syntax_valid",
    "examples_used",
    "total_cost",
    "model_name",
    "response_time_ms",
]

TIMEOUT_PER_RUN = 3600  # 1 hour — Opus needs more time per call


# ---------------------------------------------------------------------------
# JWT helpers (mirrors run_generation_stability.py)
# ---------------------------------------------------------------------------

def _get_staging_jwt() -> str:
    """Obtain a JWT for staging via Firebase Auth REST API, falling back to env var."""
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

    token = os.environ.get("PDD_JWT_TOKEN") or os.environ.get("JWT_TOKEN_STAGING")
    if token:
        print("  Using JWT from environment variable (may be stale)")
        return token

    print("ERROR: Missing staging credentials. Set PDD_JWT_TOKEN or provide")
    print("  NEXT_PUBLIC_FIREBASE_API_KEY_STAGING, STAGING_TEST_EMAIL, STAGING_TEST_PASSWORD")
    sys.exit(1)


def _get_prod_jwt() -> str:
    """Obtain a JWT for prod via env var or Firebase Admin SDK custom token."""
    token = os.environ.get("PDD_JWT_TOKEN")
    if token:
        return token

    # Fall back to generating a JWT via Firebase Admin SDK custom token
    try:
        result = subprocess.run(
            [
                "node", "-e",
                """
const admin = require('firebase-admin');
async function main() {
  const app = admin.initializeApp({ projectId: 'prompt-driven-development' });
  const customToken = await admin.auth().createCustomToken(
    'QxhdEyciK7ark7LxMdvrm38Ufsn1', { admin: true }
  );
  const apiKey = 'AIzaSyC0w2jwRR82ZFgQs_YXJoEBqnnTH71X6BE';
  const resp = await globalThis.fetch(
    'https://identitytoolkit.googleapis.com/v1/accounts:signInWithCustomToken?key=' + apiKey,
    { method: 'POST', headers: {'Content-Type': 'application/json'},
      body: JSON.stringify({token: customToken, returnSecureToken: true}) }
  );
  const data = await resp.json();
  if (data.idToken) { console.log(data.idToken); } else { process.exit(1); }
  process.exit(0);
}
main().catch(() => process.exit(1));
""",
            ],
            capture_output=True,
            text=True,
            timeout=30,
        )
        if result.returncode == 0 and result.stdout.strip():
            print("  Obtained fresh JWT via Firebase Admin SDK custom token")
            return result.stdout.strip()
    except Exception as e:
        print(f"  WARNING: Firebase Admin SDK token generation failed: {e}")

    print("ERROR: PDD_JWT_TOKEN is required for prod environment.")
    print("  Set PDD_JWT_TOKEN or ensure Firebase CLI is authenticated (firebase login).")
    sys.exit(1)


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
# Code analysis helpers
# ---------------------------------------------------------------------------

def _hash_code(code: str) -> str:
    """Return SHA-256 hex digest of normalized code (strip trailing whitespace)."""
    normalized = code.rstrip()
    return hashlib.sha256(normalized.encode("utf-8")).hexdigest()[:16]


def _check_syntax(code: str) -> bool:
    """Check if code is valid Python syntax using py_compile."""
    with tempfile.NamedTemporaryFile(
        mode="w", suffix=".py", delete=False, encoding="utf-8"
    ) as f:
        f.write(code)
        tmp_path = f.name
    try:
        py_compile.compile(tmp_path, doraise=True)
        return True
    except py_compile.PyCompileError:
        return False
    finally:
        try:
            os.remove(tmp_path)
        except OSError:
            pass


def _count_ast_nodes(code: str) -> Dict[str, int]:
    """Parse code with AST and count functions and classes."""
    try:
        tree = ast.parse(code)
    except SyntaxError:
        return {"function_count": 0, "class_count": 0}

    functions = sum(
        1 for node in ast.walk(tree)
        if isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef))
    )
    classes = sum(
        1 for node in ast.walk(tree) if isinstance(node, ast.ClassDef)
    )
    return {"function_count": functions, "class_count": classes}


# ---------------------------------------------------------------------------
# Prompt resolution
# ---------------------------------------------------------------------------

def _resolve_prompt() -> str:
    """Resolve the module prompt by running preprocess from the pdd repo root.

    Changes CWD to pdd repo root so <include>, <shell>, and <web> tags resolve
    correctly via PathResolver.
    """
    raw = PROMPT_FILE.read_text(encoding="utf-8")
    original_cwd = os.getcwd()
    try:
        os.chdir(PDD_REPO_ROOT)
        from pdd.preprocess import preprocess
        return preprocess(raw, recursive=True, double_curly_brackets=True)
    finally:
        os.chdir(original_cwd)


# ---------------------------------------------------------------------------
# Generation calls
# ---------------------------------------------------------------------------

def _call_generate_cloud(
    base_url: str,
    headers: Dict[str, str],
    resolved_prompt: str,
    temperature: float,
    raw_prompt: Optional[str] = None,
    strength: float = 0.5,
) -> Dict[str, Any]:
    """Call POST /generateCode (grounded arm) and return parsed result."""
    payload = {
        "promptContent": resolved_prompt,
        "language": "Python",
        "temperature": temperature,
        "strength": strength,
    }
    if raw_prompt:
        payload["searchInput"] = raw_prompt

    url = f"{base_url}/generateCode"
    start = time.monotonic()
    try:
        resp = requests.post(url, headers=headers, json=payload, timeout=TIMEOUT_PER_RUN)
        elapsed_ms = int((time.monotonic() - start) * 1000)
    except Exception as e:
        return {
            "http_status": 0,
            "generated_code": "",
            "examples_used": [],
            "total_cost": 0.0,
            "model_name": "",
            "response_time_ms": int((time.monotonic() - start) * 1000),
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
        print(f"      HTTP {resp.status_code}: {resp.text[:300]}")

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
    resolved_prompt: str,
    temperature: float,
    model: str = "vertex_ai/gemini-3-flash-preview",
) -> Dict[str, Any]:
    """Call litellm directly with the resolved prompt (ungrounded arm).

    Uses the same model as the grounded arm but without few-shot example
    injection, giving a fair comparison.
    """
    try:
        import litellm
    except ImportError:
        return {
            "http_status": 0,
            "generated_code": "",
            "examples_used": [],
            "total_cost": 0.0,
            "model_name": model,
            "response_time_ms": 0,
            "error": "litellm not installed",
        }

    start = time.monotonic()
    try:
        # Pass vertex_location for vertex_ai models that need global endpoint
        extra_kwargs = {}
        if model.startswith("vertex_ai/"):
            extra_kwargs["vertex_location"] = "global"
        response = litellm.completion(
            model=model,
            messages=[{"role": "user", "content": resolved_prompt}],
            temperature=temperature,
            timeout=TIMEOUT_PER_RUN,
            **extra_kwargs,
        )
        elapsed_ms = int((time.monotonic() - start) * 1000)

        generated_code = response.choices[0].message.content or ""

        # Strip markdown code fences if present
        if generated_code.startswith("```"):
            lines = generated_code.split("\n")
            # Remove first line (```python or ```)
            lines = lines[1:]
            # Remove last line if it's ```
            if lines and lines[-1].strip() == "```":
                lines = lines[:-1]
            generated_code = "\n".join(lines)

        # Extract cost from response (3-tier fallback, cf. llm_invoke.py)
        total_cost = 0.0
        try:
            cost_val = litellm.completion_cost(completion_response=response)
            total_cost = cost_val if cost_val is not None else 0.0
        except Exception as e1:
            print(f"      Cost attempt 1 failed: {e1}")
            usage = getattr(response, "usage", None)
            if usage:
                in_tok = getattr(usage, "prompt_tokens", 0) or 0
                out_tok = (
                    getattr(usage, "completion_tokens", 0)
                    or getattr(usage, "output_tokens", 0)
                    or 0
                )
                try:
                    cost_val = litellm.completion_cost(
                        model=model,
                        prompt_tokens=in_tok,
                        completion_tokens=out_tok,
                    )
                    total_cost = cost_val if cost_val is not None else 0.0
                except Exception:
                    # Manual: Gemini 3 Flash = $0.50/M input, $3.00/M output
                    total_cost = (in_tok * 0.5 + out_tok * 3.0) / 1_000_000
                    print(
                        f"      Cost fallback: {in_tok} in + {out_tok} out "
                        f"= ${total_cost:.6f}"
                    )

        return {
            "http_status": 0,
            "generated_code": generated_code,
            "examples_used": [],
            "total_cost": total_cost,
            "model_name": model,
            "response_time_ms": elapsed_ms,
            "error": None,
        }

    except Exception as e:
        elapsed_ms = int((time.monotonic() - start) * 1000)
        return {
            "http_status": 0,
            "generated_code": "",
            "examples_used": [],
            "total_cost": 0.0,
            "model_name": model,
            "response_time_ms": elapsed_ms,
            "error": str(e)[:500],
        }


def _call_generate_pdd_local(
    temperature: float,
    strength: float = 0.5,
) -> Dict[str, Any]:
    """Run `pdd generate --local` as a subprocess (ungrounded-pdd arm).

    Uses the same model as the grounded arm but without few-shot example
    injection. Unlike the litellm ungrounded arm, pdd auto-discovers and
    appends test files in <unit_test_content> tags, giving the LLM visibility
    into the test suite.
    """
    import re as _re

    # Create temp prompt file with cache-busting nonce inside PDD_REPO_ROOT
    # so that <include> tags resolve correctly via PathResolver.
    nonce = f"\n# experiment-run-seed: {uuid.uuid4()}\n"
    tmp_prompt = PDD_REPO_ROOT / "prompts" / "_tmp_experiment_python.prompt"
    tmp_output = None

    start = time.monotonic()
    try:
        # Write prompt with nonce
        original_prompt = PROMPT_FILE.read_text(encoding="utf-8")
        tmp_prompt.write_text(original_prompt + nonce, encoding="utf-8")

        # Output file must be named {MODULE_NAME}.py so _find_default_test_files()
        # auto-discovers tests/test_{MODULE_NAME}*.py
        tmp_dir = tempfile.mkdtemp(prefix="pdd_exp_")
        tmp_output = Path(tmp_dir) / f"{MODULE_NAME}.py"

        cmd = [
            sys.executable, "-c", "from pdd.cli import cli; cli()",
            "--local", "--force", "--no-core-dump",
            "--strength", str(strength),
            "--temperature", str(temperature),
            "generate",
            "--output", str(tmp_output),
            str(tmp_prompt),
        ]

        result = subprocess.run(
            cmd,
            capture_output=True,
            text=True,
            timeout=TIMEOUT_PER_RUN,
            cwd=str(PDD_REPO_ROOT),
        )

        elapsed_ms = int((time.monotonic() - start) * 1000)

        if result.returncode != 0:
            error_msg = (result.stderr or result.stdout or "unknown error")[:500]
            return {
                "http_status": 0,
                "generated_code": "",
                "examples_used": [],
                "total_cost": 0.0,
                "model_name": "",
                "response_time_ms": elapsed_ms,
                "error": f"pdd exit code {result.returncode}: {error_msg}",
            }

        # Read generated code
        generated_code = ""
        if tmp_output.exists():
            generated_code = tmp_output.read_text(encoding="utf-8")

        # Parse cost and model from pdd's Command Execution Summary
        # Format: "Step 1 (generate): Cost: $X, Model: Y"
        stdout = result.stdout + "\n" + result.stderr
        total_cost = 0.0
        model_name = ""

        # Parse from "Step 1 (generate): Cost: $X, Model: Y" format
        cost_match = _re.search(
            r"Cost:\s*\$([0-9.]+),\s*Model:\s*(\S+)",
            stdout,
        )
        if cost_match:
            try:
                total_cost = float(cost_match.group(1))
            except ValueError:
                pass
            model_name = cost_match.group(2).strip()

        return {
            "http_status": 0,
            "generated_code": generated_code,
            "examples_used": [],
            "total_cost": total_cost,
            "model_name": model_name,
            "response_time_ms": elapsed_ms,
            "error": None,
        }

    except subprocess.TimeoutExpired:
        elapsed_ms = int((time.monotonic() - start) * 1000)
        return {
            "http_status": 0,
            "generated_code": "",
            "examples_used": [],
            "total_cost": 0.0,
            "model_name": "",
            "response_time_ms": elapsed_ms,
            "error": f"pdd generate timed out after {TIMEOUT_PER_RUN}s",
        }
    except Exception as e:
        elapsed_ms = int((time.monotonic() - start) * 1000)
        return {
            "http_status": 0,
            "generated_code": "",
            "examples_used": [],
            "total_cost": 0.0,
            "model_name": "",
            "response_time_ms": elapsed_ms,
            "error": str(e)[:500],
        }
    finally:
        # Cleanup temp files
        if tmp_prompt.exists():
            try:
                tmp_prompt.unlink()
            except OSError:
                pass
        if tmp_output is not None:
            try:
                import shutil
                shutil.rmtree(tmp_output.parent, ignore_errors=True)
            except OSError:
                pass


# ---------------------------------------------------------------------------
# Main runner
# ---------------------------------------------------------------------------

def run_experiment(
    env: str,
    runs: int = 5,
    temperature: float = 1.0,
    base_url: Optional[str] = None,
    arms: Optional[List[str]] = None,
    model: str = "vertex_ai/gemini-3-flash-preview",
    strength_cloud: float = 0.5,
    strength_local: float = 0.5,
) -> int:
    """Run module regeneration stability experiment. Returns 0 on success."""
    if arms is None:
        arms = ["grounded", "ungrounded", "ungrounded-pdd"]
    if base_url is None:
        base_url = STAGING_BASE_URL if env == "staging" else PROD_BASE_URL

    # Read raw prompt before expansion (concise semantic content for embedding search)
    raw_prompt = PROMPT_FILE.read_text(encoding="utf-8")
    print(f"Raw prompt: {len(raw_prompt):,} chars, {len(raw_prompt.splitlines()):,} lines")

    # Resolve prompt once (used by grounded and ungrounded arms)
    needs_resolved = "grounded" in arms or "ungrounded" in arms
    resolved_prompt = ""
    if needs_resolved:
        print(f"Resolving {MODULE_NAME} prompt (expanding includes)...")
        resolved_prompt = _resolve_prompt()
        print(f"  Resolved prompt: {len(resolved_prompt):,} chars, {len(resolved_prompt.splitlines()):,} lines")

    # Get JWT (only needed for grounded arm)
    headers = {}
    if "grounded" in arms:
        print(f"\nObtaining JWT for {env}...")
        if env == "staging":
            jwt = _get_staging_jwt()
        else:
            jwt = _get_prod_jwt()
        headers = {
            "Authorization": f"Bearer {jwt}",
            "Content-Type": "application/json",
        }

    _init_csv()

    total_calls = len(arms) * runs
    completed = 0
    errors = 0
    grounded_no_example = 0

    arm_descriptions = {
        "grounded": f"POST {base_url}/generateCode (strength={strength_cloud})",
        "ungrounded": f"litellm {model} (no examples)",
        "ungrounded-pdd": f"pdd generate --local (strength={strength_local}, auto-discovers tests, no few-shot)",
    }

    print(f"\n{MODULE_NAME} Regeneration Stability Experiment")
    print(f"{'=' * 70}")
    print(f"Environment:  {env}")
    print(f"Model (ungrounded): {model}")
    print(f"Strength (cloud):   {strength_cloud}")
    print(f"Strength (local):   {strength_local}")
    for arm in arms:
        print(f"  {arm:18s} {arm_descriptions.get(arm, '')}")
    if resolved_prompt:
        print(f"Prompt:       {PROMPT_FILE.name} ({len(resolved_prompt):,} chars resolved)")
    print(f"Runs per arm: {runs}")
    print(f"Temperature:  {temperature}")
    print(f"Arms:         {', '.join(arms)}")
    print(f"Total calls:  {total_calls}")
    print(f"{'=' * 70}\n")

    for arm in arms:
        print(f"Arm: {arm}")

        for run_num in range(1, runs + 1):
            print(f"  Run {run_num}/{runs}...", end="", flush=True)

            if arm == "grounded":
                # Cache-busting nonce
                nonce = f"\n# experiment-run-seed: {uuid.uuid4()}\n"
                run_prompt = resolved_prompt + nonce
                result = _call_generate_cloud(
                    base_url, headers, run_prompt,
                    temperature=temperature,
                    raw_prompt=raw_prompt,
                    strength=strength_cloud,
                )
            elif arm == "ungrounded":
                nonce = f"\n# experiment-run-seed: {uuid.uuid4()}\n"
                run_prompt = resolved_prompt + nonce
                result = _call_generate_local(
                    resolved_prompt=run_prompt,
                    temperature=temperature,
                    model=model,
                )
            elif arm == "ungrounded-pdd":
                result = _call_generate_pdd_local(
                    temperature=temperature,
                    strength=strength_local,
                )
            else:
                print(f" [SKIP] unknown arm: {arm}")
                continue

            code = result["generated_code"]
            code_hash = _hash_code(code) if code else "EMPTY"
            code_lines = len(code.splitlines()) if code else 0
            syntax_valid = _check_syntax(code) if code else False
            ast_counts = _count_ast_nodes(code) if code else {"function_count": 0, "class_count": 0}

            examples = result["examples_used"]
            examples_str = ";".join(
                ex.get("id", ex.get("slug", "?")) for ex in examples
            ) if examples else ""

            # Flag grounded runs with no example (silently became ungrounded)
            grounded_flag = ""
            if arm == "grounded" and not examples:
                grounded_flag = " [NO_EXAMPLE!]"
                grounded_no_example += 1

            # Save generated code
            if code:
                gen_file = GENERATIONS_DIR / f"{MODULE_NAME}_{arm}_run{run_num}.py"
                gen_file.write_text(code, encoding="utf-8")

            row = {
                "timestamp_utc": datetime.now(timezone.utc).isoformat(),
                "env": env,
                "arm": arm,
                "run_number": run_num,
                "http_status": result["http_status"],
                "generated_code_hash": code_hash,
                "generated_code_lines": code_lines,
                "function_count": ast_counts["function_count"],
                "class_count": ast_counts["class_count"],
                "syntax_valid": syntax_valid,
                "examples_used": examples_str,
                "total_cost": result["total_cost"],
                "model_name": result["model_name"],
                "response_time_ms": result["response_time_ms"],
            }
            _append_row(row)

            # Status
            if arm == "grounded":
                is_error = result["http_status"] != 200
                status_icon = "OK" if not is_error else "ERR"
            else:
                is_error = result["error"] is not None
                status_icon = "OK" if not is_error else "ERR"

            if is_error:
                errors += 1
                if result.get("error"):
                    print(f" [{status_icon}] {result['error']}")
                    continue

            completed += 1
            time_s = result["response_time_ms"] / 1000.0
            print(
                f" [{status_icon}] hash={code_hash} lines={code_lines} "
                f"syntax={'OK' if syntax_valid else 'FAIL'} "
                f"funcs={ast_counts['function_count']} classes={ast_counts['class_count']} "
                f"cost=${result['total_cost']:.4f} time={time_s:.1f}s"
                f"{grounded_flag}"
            )

        print()

    print(f"{'=' * 70}")
    print(f"Completed: {completed}/{total_calls} calls ({errors} errors)")
    print(f"CSV:         {CSV_PATH}")
    print(f"Generations: {GENERATIONS_DIR}/")

    if grounded_no_example > 0:
        print(
            f"\nWARNING: {grounded_no_example} grounded run(s) had no example selected. "
            f"These are effectively ungrounded. Check that the {MODULE_NAME} few-shot "
            f"example exists in Firestore and was not rejected by judge."
        )

    return 0 if errors == 0 else 1


# ---------------------------------------------------------------------------
# CLI
# ---------------------------------------------------------------------------

def main() -> int:
    """Parse args and run experiment."""
    parser = argparse.ArgumentParser(
        description="Run module regeneration stability experiment (grounded vs ungrounded)"
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
        default=5,
        help="Number of repetitions per arm (default: 5)",
    )
    parser.add_argument(
        "--temperature",
        type=float,
        default=1.0,
        help="Generation temperature (default: 1.0)",
    )
    parser.add_argument(
        "--base-url",
        default=None,
        help="Override base URL for generateCode endpoint (grounded arm)",
    )
    parser.add_argument(
        "--arms",
        nargs="+",
        default=["grounded", "ungrounded", "ungrounded-pdd"],
        choices=["grounded", "ungrounded", "ungrounded-pdd"],
        help="Which arms to run (default: all three)",
    )
    parser.add_argument(
        "--module",
        default="llm_invoke",
        help="Module name to test (default: llm_invoke)",
    )
    parser.add_argument(
        "--model",
        default="vertex_ai/gemini-3-flash-preview",
        help="Model for ungrounded litellm arm (default: vertex_ai/gemini-3-flash-preview)",
    )
    parser.add_argument(
        "--strength-cloud",
        type=float,
        default=0.5,
        help="Strength for grounded (cloud) arm — maps to model via server llm_model.csv (default: 0.5)",
    )
    parser.add_argument(
        "--strength-local",
        type=float,
        default=0.5,
        help="Strength for ungrounded-pdd (local) arm — maps to model via local llm_model.csv (default: 0.5)",
    )
    parser.add_argument(
        "--suffix",
        default="",
        help="Suffix for output CSV/dir names (e.g. '_pro' → llm_invoke_pro_stability.csv)",
    )
    args = parser.parse_args()

    global MODULE_NAME, PROMPT_FILE, CSV_PATH, GENERATIONS_DIR
    MODULE_NAME = args.module
    PROMPT_FILE = PDD_REPO_ROOT / "prompts" / f"{MODULE_NAME}_python.prompt"
    output_name = args.module + args.suffix
    CSV_PATH = RESULTS_DIR / f"{output_name}_stability.csv"
    GENERATIONS_DIR = RESULTS_DIR / f"{output_name}_generations"

    return run_experiment(
        env=args.env,
        runs=args.runs,
        temperature=args.temperature,
        base_url=args.base_url,
        arms=args.arms,
        model=args.model,
        strength_cloud=args.strength_cloud,
        strength_local=args.strength_local,
    )


if __name__ == "__main__":
    raise SystemExit(main())
