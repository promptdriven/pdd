#!/usr/bin/env python3
"""Local oMLX throughput and coding-regression harness.

Runs the same Qwen3.8 BF16 checkpoint with native MTP disabled/enabled,
benchmarks throughput through the local OpenAI-compatible endpoint, and
scores a deterministic coding sample using macOS Seatbelt and resource limits.

The execution isolation is best effort, not a security boundary against
adversarial generated code. MBPP prompts expose a subset of the tests that are
later scored, so this suite is a regression smoke test rather than a blind
accuracy benchmark. See README.md for the full methodology and limitations.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import os
import random
import re
import resource
import shutil
import statistics
import subprocess
import tempfile
import threading
import time
from pathlib import Path
from typing import Any

import requests


USER_HOME = Path.home()
BASE_URL = os.environ.get("OMLX_BASE_URL", "http://127.0.0.1:8000").rstrip("/")
MODEL_ID = "Qwen3.8-27B-MLX-bf16-mtp"
SETTINGS_PATH = Path(
    os.environ.get("OMLX_SETTINGS_PATH", USER_HOME / ".omlx/settings.json")
)
LOG_PATH = Path(os.environ.get("OMLX_LOG_PATH", USER_HOME / ".omlx/logs/server.log"))
DATA_DIR = Path(
    os.environ.get(
        "OMLX_EVAL_DATA_DIR",
        "/Applications/oMLX.app/Contents/Resources/omlx/eval/data",
    )
)
PYTHON = "/Library/Developer/CommandLineTools/usr/bin/python3"
RESULT_PATH = Path("/private/tmp/omlx_qwen38_bf16_mtp_ab_results.json")
SOURCE_REVISION = os.environ.get(
    "OMLX_SOURCE_REVISION", "fe34c8d6784c6d9b463756dd020492123137b732"
)
OMLX_BIN = os.environ.get("OMLX_BIN") or shutil.which("omlx") or str(
    USER_HOME / ".local/bin/omlx"
)
SAMPLE_SEED = 42
SAMPLE_PER_BENCHMARK = 20
THROUGHPUT_REPEATS = 3
PROMPT_LENGTHS = [1024, 4096, 16384]
GENERATION_LENGTH = 128


def say(message: str) -> None:
    print(f"[{time.strftime('%H:%M:%S')}] {message}", flush=True)


def load_api_key() -> str:
    settings = json.loads(SETTINGS_PATH.read_text())
    key = settings.get("auth", {}).get("api_key") or settings.get("api_key")
    if not key:
        raise RuntimeError("oMLX API key not found")
    return key


def configured_model_dirs() -> list[Path]:
    """Return model roots from settings, followed by the LM Studio default."""
    settings = json.loads(SETTINGS_PATH.read_text())
    model = settings.get("model", {})
    values = model.get("model_dirs") or []
    if isinstance(values, str):
        values = [values]
    if model.get("model_dir"):
        values.append(model["model_dir"])
    values.append(str(USER_HOME / ".lmstudio/models"))
    return list(dict.fromkeys(Path(value).expanduser() for value in values))


def find_model_path(model_id: str, models: list[dict[str, Any]]) -> Path | None:
    """Resolve a discovered model without embedding a workstation username."""
    discovered = next(
        (
            Path(model.get("path") or model["model_path"])
            for model in models
            if model.get("id") == model_id
            and (model.get("path") or model.get("model_path"))
        ),
        None,
    )
    if discovered:
        return discovered
    for root in configured_model_dirs():
        direct = root / model_id
        if direct.is_dir():
            return direct
        matches = list(root.glob(f"*/{model_id}"))
        if matches:
            return matches[0]
    return None


def admin_session(api_key: str) -> requests.Session:
    session = requests.Session()
    response = session.post(
        f"{BASE_URL}/admin/api/login",
        json={"api_key": api_key, "remember": False},
        timeout=15,
    )
    response.raise_for_status()
    return session


def checked(response: requests.Response) -> dict[str, Any]:
    if not response.ok:
        raise RuntimeError(
            f"HTTP {response.status_code} {response.request.method} "
            f"{response.request.url}: {response.text[:1000]}"
        )
    return response.json()


def get_models(session: requests.Session) -> list[dict[str, Any]]:
    return checked(session.get(f"{BASE_URL}/admin/api/models", timeout=60))["models"]


def wait_loaded(
    session: requests.Session, model_id: str, loaded: bool, timeout: float = 600
) -> None:
    deadline = time.monotonic() + timeout
    while time.monotonic() < deadline:
        model = next((m for m in get_models(session) if m.get("id") == model_id), None)
        if model and bool(model.get("loaded")) == loaded and not model.get("is_loading"):
            return
        time.sleep(1)
    raise TimeoutError(f"Timed out waiting for {model_id} loaded={loaded}")


def unload_model(session: requests.Session, model_id: str) -> None:
    model = next((m for m in get_models(session) if m.get("id") == model_id), None)
    if not model or not model.get("loaded"):
        return
    response = session.post(
        f"{BASE_URL}/admin/api/models/{model_id}/unload", timeout=120
    )
    if response.status_code not in (200, 202):
        checked(response)
    wait_loaded(session, model_id, False)


def unload_all(session: requests.Session) -> None:
    for model in get_models(session):
        if model.get("loaded") and not model.get("virtual"):
            say(f"Unloading {model['id']}")
            unload_model(session, model["id"])


def set_arm(session: requests.Session, mtp_enabled: bool) -> None:
    body = {
        "temperature": 0.0,
        "top_p": 1.0,
        "top_k": 0,
        "repetition_penalty": 1.0,
        "force_sampling": False,
        "enable_thinking": False,
        "thinking_budget_enabled": False,
        "turboquant_kv_enabled": False,
        "qwen35_ane_prefill_enabled": False,
        "specprefill_enabled": False,
        "dflash_enabled": False,
        "mtp_enabled": mtp_enabled,
        "vlm_mtp_enabled": False,
        "guided_grammar_enabled": False,
        "trust_remote_code": False,
    }
    checked(
        session.put(
            f"{BASE_URL}/admin/api/models/{MODEL_ID}/settings",
            json=body,
            timeout=60,
        )
    )


def restore_settings(session: requests.Session, settings: dict[str, Any]) -> None:
    """Restore the target's complete pre-benchmark settings snapshot."""
    if not settings:
        set_arm(session, False)
        return
    checked(
        session.put(
            f"{BASE_URL}/admin/api/models/{MODEL_ID}/settings",
            json=settings,
            timeout=60,
        )
    )


def load_target(session: requests.Session) -> float:
    started = time.perf_counter()
    checked(
        session.post(
            f"{BASE_URL}/admin/api/models/{MODEL_ID}/load", timeout=600
        )
    )
    wait_loaded(session, MODEL_ID, True)
    return time.perf_counter() - started


class FootprintSampler:
    def __init__(self, api_key: str) -> None:
        self.api_key = api_key
        self.samples: list[int] = []
        self._stop = threading.Event()
        self._thread: threading.Thread | None = None

    def start(self) -> None:
        self._thread = threading.Thread(target=self._run, daemon=True)
        self._thread.start()

    def _run(self) -> None:
        try:
            session = admin_session(self.api_key)
        except Exception:
            return
        while not self._stop.is_set():
            try:
                response = session.get(
                    f"{BASE_URL}/admin/api/global-settings", timeout=5
                )
                if response.ok:
                    value = int(
                        response.json().get("system", {}).get(
                            "omlx_phys_footprint_bytes", 0
                        )
                    )
                    if value:
                        self.samples.append(value)
            except Exception:
                pass
            self._stop.wait(0.25)
        session.close()

    def stop(self) -> dict[str, Any]:
        self._stop.set()
        if self._thread:
            self._thread.join(timeout=10)
        return {
            "samples": len(self.samples),
            "min_bytes": min(self.samples) if self.samples else None,
            "max_bytes": max(self.samples) if self.samples else None,
            "median_bytes": int(statistics.median(self.samples))
            if self.samples
            else None,
        }


def run_throughput_once(
    session: requests.Session, api_key: str, repeat: int
) -> dict[str, Any]:
    body = {
        "model_id": MODEL_ID,
        "context_profile": "code_python",
        "prompt_lengths": PROMPT_LENGTHS,
        "generation_length": GENERATION_LENGTH,
        "batch_sizes": [],
        "warmup_mode": "quick",
        "force_lm_engine": False,
        "external": {
            "base_url": f"{BASE_URL}/v1",
            "api_key": api_key,
            "model": MODEL_ID,
            "extra_body": {},
        },
    }
    started = checked(
        session.post(f"{BASE_URL}/admin/api/bench/start", json=body, timeout=60)
    )
    bench_id = started["bench_id"]
    say(f"Throughput repeat {repeat}/{THROUGHPUT_REPEATS}: {bench_id}")
    while True:
        try:
            result = checked(
                session.get(
                    f"{BASE_URL}/admin/api/bench/{bench_id}/results", timeout=30
                )
            )
        except (requests.ConnectionError, requests.Timeout) as exc:
            # Metal graph compilation can briefly stall/close an idle admin
            # keep-alive connection. The benchmark itself remains active.
            say(f"  transient admin poll error ({type(exc).__name__}); retrying")
            time.sleep(2)
            continue
        if result["status"] in {"completed", "cancelled", "error"}:
            if result["status"] != "completed":
                raise RuntimeError(f"Throughput benchmark failed: {result}")
            for row in result["results"]:
                say(
                    "  pp{requested_pp}: prompt={processing_tps:.1f} tok/s, "
                    "generation={gen_tps:.1f} tok/s, TTFT={ttft_ms:.1f} ms".format(
                        **row
                    )
                )
            return result
        time.sleep(1)


def load_jsonl(path: Path) -> list[dict[str, Any]]:
    with path.open(encoding="utf-8") as handle:
        return [json.loads(line) for line in handle if line.strip()]


def deterministic_sample(items: list[dict[str, Any]], n: int) -> list[dict[str, Any]]:
    if n >= len(items):
        return items
    return random.Random(SAMPLE_SEED).sample(items, n)


def coding_items() -> list[dict[str, Any]]:
    human = deterministic_sample(load_jsonl(DATA_DIR / "humaneval.jsonl"), SAMPLE_PER_BENCHMARK)
    mbpp_all = [x for x in load_jsonl(DATA_DIR / "mbpp.jsonl") if x.get("test_list")]
    mbpp = deterministic_sample(mbpp_all, SAMPLE_PER_BENCHMARK)
    items: list[dict[str, Any]] = []
    for item in human:
        items.append(
            {
                "suite": "humaneval",
                "id": item["task_id"],
                "prompt": item["prompt"],
                "test": item["test"],
                "entry_point": item["entry_point"],
            }
        )
    for item in mbpp:
        items.append(
            {
                "suite": "mbpp",
                "id": str(item["task_id"]),
                "prompt": item["prompt"],
                "test_list": item["test_list"],
                "test_setup_code": item.get("test_setup_code", ""),
            }
        )
    return items


def format_messages(item: dict[str, Any]) -> list[dict[str, str]]:
    if item["suite"] == "humaneval":
        content = (
            "Complete the following Python function. Provide only the complete "
            "function implementation, no explanations.\n\n" + item["prompt"]
        )
    else:
        test_str = "\n".join(item["test_list"][:3])
        content = (
            "Write a Python function to solve the following problem. Provide only "
            "the complete function implementation, no explanations.\n\n"
            f"Problem: {item['prompt']}\n\nTest cases:\n{test_str}\n\nSolution:"
        )
    return [{"role": "user", "content": content}]


def strip_think_tags(text: str) -> str:
    if "<think>" not in text and "</think>" in text:
        return text.split("</think>", 1)[1].strip()
    return re.sub(r"<think>.*?</think>", "", text, flags=re.DOTALL).strip()


def extract_last_code_block(response: str) -> str:
    response = response.strip()
    blocks = re.findall(r"```python\s*\n(.*?)```", response, re.DOTALL)
    if blocks:
        return blocks[-1].strip()
    blocks = re.findall(r"```\s*\n(.*?)```", response, re.DOTALL)
    if blocks:
        return blocks[-1].strip()
    lines = response.split("\n")
    code_lines: list[str] = []
    in_code = False
    for line in lines:
        if not in_code and line.startswith(
            ("def ", "class ", "import ", "from ", "#")
        ):
            in_code = True
        if in_code:
            code_lines.append(line)
    return "\n".join(code_lines) if code_lines else response


def get_imports(prompt: str) -> str:
    return "\n".join(
        line
        for line in prompt.split("\n")
        if line.strip().startswith(("import ", "from "))
    )


def extract_code(response: str, item: dict[str, Any]) -> str:
    code = extract_last_code_block(strip_think_tags(response))
    if item["suite"] == "mbpp":
        return code
    imports = get_imports(item["prompt"])
    if "def " in code and imports:
        if not any(
            line.strip().startswith(("import ", "from "))
            for line in code.split("\n")
        ):
            return imports + "\n\n" + code
    if "def " not in code:
        return item["prompt"] + code
    return code


def set_limits() -> None:
    limits = [
        (resource.RLIMIT_AS, 256 * 1024 * 1024),
        (resource.RLIMIT_CPU, 20),
        (resource.RLIMIT_FSIZE, 4 * 1024 * 1024),
        (resource.RLIMIT_NOFILE, 64),
        (resource.RLIMIT_NPROC, 32),
    ]
    for limit, value in limits:
        try:
            resource.setrlimit(limit, (value, value))
        except (ValueError, resource.error):
            pass


def sandbox_score(code: str, item: dict[str, Any]) -> tuple[bool, str]:
    temp_dir = Path(tempfile.mkdtemp(prefix="omlx-code-", dir="/private/tmp"))
    try:
        script_path = temp_dir / "candidate.py"
        if item["suite"] == "humaneval":
            script = f"{code}\n\n{item['test']}\n\ncheck({item['entry_point']})\n"
        else:
            script = (
                f"{item.get('test_setup_code', '')}\n{code}\n"
                + "\n".join(item["test_list"])
                + "\n"
            )
        script_path.write_text(script, encoding="utf-8")
        profile = " ".join(
            [
                "(version 1)",
                '(import "system.sb")',
                "(allow process*)",
                "(allow sysctl-read)",
                f'(allow file-read* (subpath "/Library") (subpath "/System") '
                f'(subpath "/usr/lib") (subpath "{temp_dir}"))',
                f'(allow file-map-executable (subpath "/Library") '
                f'(subpath "/System") (subpath "/usr/lib"))',
                "(deny network*)",
                f'(deny file-read* (subpath "{USER_HOME}"))',
                f'(allow file-write* (subpath "{temp_dir}"))',
            ]
        )
        result = subprocess.run(
            [
                "/usr/bin/sandbox-exec",
                "-p",
                profile,
                PYTHON,
                "-I",
                "-S",
                str(script_path),
            ],
            cwd=temp_dir,
            capture_output=True,
            text=True,
            timeout=15,
            preexec_fn=set_limits,
            env={
                "PATH": "/usr/bin:/bin",
                "HOME": str(temp_dir),
                "TMPDIR": str(temp_dir),
                "LANG": "en_US.UTF-8",
            },
        )
        if result.returncode == 0:
            return True, ""
        return False, (result.stderr or result.stdout)[:500]
    except subprocess.TimeoutExpired:
        return False, "Execution timed out"
    except Exception as exc:
        return False, str(exc)[:500]
    finally:
        shutil.rmtree(temp_dir, ignore_errors=True)


def chat_completion(api_key: str, item: dict[str, Any]) -> dict[str, Any]:
    body = {
        "model": MODEL_ID,
        "messages": format_messages(item),
        "temperature": 0.0,
        "top_p": 1.0,
        "max_tokens": 2048,
        "stream": False,
        "chat_template_kwargs": {"enable_thinking": False},
    }
    started = time.perf_counter()
    response = requests.post(
        f"{BASE_URL}/v1/chat/completions",
        headers={"Authorization": f"Bearer {api_key}"},
        json=body,
        timeout=900,
    )
    elapsed = time.perf_counter() - started
    payload = checked(response)
    choice = payload["choices"][0]
    raw = choice["message"].get("content") or ""
    usage = payload.get("usage", {})
    code = extract_code(raw, item)
    passed, error = sandbox_score(code, item)
    return {
        "suite": item["suite"],
        "id": item["id"],
        "passed": passed,
        "error": error,
        "elapsed_seconds": elapsed,
        "prompt_tokens": usage.get("prompt_tokens"),
        "completion_tokens": usage.get("completion_tokens"),
        "finish_reason": choice.get("finish_reason"),
        "raw_response": raw,
        "response_sha256": hashlib.sha256(raw.encode()).hexdigest(),
        "extracted_code_sha256": hashlib.sha256(code.encode()).hexdigest(),
    }


def run_accuracy(api_key: str) -> dict[str, Any]:
    rows: list[dict[str, Any]] = []
    items = coding_items()
    started = time.perf_counter()
    for index, item in enumerate(items, 1):
        row = chat_completion(api_key, item)
        rows.append(row)
        say(
            f"Coding {index:02d}/{len(items)} {row['suite']}:{row['id']} "
            f"{'PASS' if row['passed'] else 'FAIL'} "
            f"({row['completion_tokens']} tokens, {row['elapsed_seconds']:.1f}s)"
        )
    summaries: dict[str, Any] = {}
    for suite in ("humaneval", "mbpp", "all"):
        subset = rows if suite == "all" else [r for r in rows if r["suite"] == suite]
        summaries[suite] = {
            "passed": sum(bool(r["passed"]) for r in subset),
            "total": len(subset),
            "score": sum(bool(r["passed"]) for r in subset) / len(subset),
            "completion_tokens": sum(int(r["completion_tokens"] or 0) for r in subset),
            "elapsed_seconds": sum(float(r["elapsed_seconds"]) for r in subset),
        }
    return {
        "seed": SAMPLE_SEED,
        "sample_per_benchmark": SAMPLE_PER_BENCHMARK,
        "wall_seconds": time.perf_counter() - started,
        "summary": summaries,
        "results": rows,
    }


def log_slice(offset: int) -> list[str]:
    if not LOG_PATH.exists():
        return []
    with LOG_PATH.open("rb") as handle:
        handle.seek(offset)
        data = handle.read().decode("utf-8", errors="replace")
    return [line for line in data.splitlines() if "MTP[" in line]


def run_arm(
    label: str,
    mtp_enabled: bool,
    session: requests.Session,
    api_key: str,
    *,
    throughput_only: bool = False,
) -> dict[str, Any]:
    say(f"=== Starting arm: {label} (mtp_enabled={mtp_enabled}) ===")
    unload_all(session)
    set_arm(session, mtp_enabled)
    log_offset = LOG_PATH.stat().st_size if LOG_PATH.exists() else 0
    load_seconds = load_target(session)
    say(f"Loaded target in {load_seconds:.1f}s")
    sampler = FootprintSampler(api_key)
    sampler.start()
    started = time.perf_counter()
    try:
        throughput = [
            run_throughput_once(session, api_key, repeat)
            for repeat in range(1, THROUGHPUT_REPEATS + 1)
        ]
        accuracy = None if throughput_only else run_accuracy(api_key)
    finally:
        footprint = sampler.stop()
    arm = {
        "label": label,
        "mtp_enabled": mtp_enabled,
        "load_seconds": load_seconds,
        "wall_seconds": time.perf_counter() - started,
        "throughput": throughput,
        "accuracy": accuracy,
        "footprint": footprint,
        "mtp_log_lines": log_slice(log_offset),
    }
    unload_model(session, MODEL_ID)
    say(f"=== Completed arm: {label} ===")
    return arm


def summarize_comparison(arms: list[dict[str, Any]]) -> dict[str, Any]:
    baseline, mtp = arms
    throughput: dict[str, Any] = {}
    for requested_pp in PROMPT_LENGTHS:
        values: dict[str, list[float]] = {}
        for arm in arms:
            values[arm["label"]] = [
                float(row["gen_tps"])
                for run in arm["throughput"]
                for row in run["results"]
                if int(row["requested_pp"]) == requested_pp
            ]
        base_median = statistics.median(values[baseline["label"]])
        mtp_median = statistics.median(values[mtp["label"]])
        throughput[str(requested_pp)] = {
            "baseline_generation_tps": values[baseline["label"]],
            "mtp_generation_tps": values[mtp["label"]],
            "baseline_median": base_median,
            "mtp_median": mtp_median,
            "speedup": mtp_median / base_median,
        }
    base_rows = {
        (r["suite"], r["id"]): r for r in baseline["accuracy"]["results"]
    }
    mtp_rows = {(r["suite"], r["id"]): r for r in mtp["accuracy"]["results"]}
    exact = []
    code_exact = []
    pass_changed = []
    for key, left in base_rows.items():
        right = mtp_rows[key]
        if left["response_sha256"] == right["response_sha256"]:
            exact.append(key)
        if left["extracted_code_sha256"] == right["extracted_code_sha256"]:
            code_exact.append(key)
        if left["passed"] != right["passed"]:
            pass_changed.append(
                {
                    "suite": key[0],
                    "id": key[1],
                    "baseline_passed": left["passed"],
                    "mtp_passed": right["passed"],
                }
            )
    return {
        "throughput": throughput,
        "accuracy": {
            "raw_response_exact_matches": len(exact),
            "extracted_code_exact_matches": len(code_exact),
            "total": len(base_rows),
            "pass_changed": pass_changed,
            "baseline_summary": baseline["accuracy"]["summary"],
            "mtp_summary": mtp["accuracy"]["summary"],
        },
    }


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument(
        "--smoke", action="store_true", help="Run one throughput pass and two tasks"
    )
    parser.add_argument(
        "--single-model",
        help="Benchmark one discovered model with MTP enabled instead of the BF16 A/B",
    )
    parser.add_argument(
        "--result-path",
        type=Path,
        help="Override the JSON output path (required with --single-model)",
    )
    parser.add_argument(
        "--throughput-only",
        action="store_true",
        help="Skip the coding sample (useful for fresh speed brackets)",
    )
    parser.add_argument(
        "--label", default="oq8e_mtp", help="Result arm label in single-model mode"
    )
    args = parser.parse_args()
    global MODEL_ID, RESULT_PATH, SAMPLE_PER_BENCHMARK, THROUGHPUT_REPEATS, PROMPT_LENGTHS
    if args.single_model:
        if not args.result_path:
            parser.error("--result-path is required with --single-model")
        MODEL_ID = args.single_model
        RESULT_PATH = args.result_path
    if args.smoke:
        SAMPLE_PER_BENCHMARK = 1
        THROUGHPUT_REPEATS = 1
        PROMPT_LENGTHS = [1024]

    api_key = load_api_key()
    session = admin_session(api_key)
    models = get_models(session)
    if not any(m.get("id") == MODEL_ID for m in models):
        raise RuntimeError(f"Target model not discovered: {MODEL_ID}")
    originally_loaded = [
        m["id"] for m in models if m.get("loaded") and not m.get("virtual")
    ]
    target_model = next(m for m in models if m.get("id") == MODEL_ID)
    original_target_settings = dict(target_model.get("settings") or {})
    say(f"Originally loaded models: {', '.join(originally_loaded) or '(none)'}")
    document: dict[str, Any] = {
        "metadata": {
            "model_id": MODEL_ID,
            "source_checkpoint_revision": SOURCE_REVISION,
            "omlx_version": subprocess.check_output(
                [OMLX_BIN, "--version"], text=True
            ).strip(),
            "started_at": time.strftime("%Y-%m-%dT%H:%M:%S%z"),
            "prompt_lengths": PROMPT_LENGTHS,
            "generation_length": GENERATION_LENGTH,
            "throughput_repeats": THROUGHPUT_REPEATS,
            "coding_sample_per_suite": SAMPLE_PER_BENCHMARK,
            "sandbox": (
                "best-effort macOS Seatbelt; network/home denied; "
                "15s/256MiB limits; not adversarially secure"
            ),
            "accuracy_limitations": (
                "Regression smoke sample only. MBPP prompts expose up to three "
                "tests that are also scored; generated code can deliberately "
                "circumvent an exit-code-only scorer."
            ),
            "external_upload": False,
            "dataset_sha256": {
                name: hashlib.sha256((DATA_DIR / name).read_bytes()).hexdigest()
                for name in ("humaneval.jsonl", "mbpp.jsonl")
            },
            "sample_task_ids": [
                [item["suite"], item["id"]] for item in coding_items()
            ],
        },
        "arms": [],
    }
    try:
        if args.single_model:
            model_path = find_model_path(MODEL_ID, models)
            if model_path:
                manifest = []
                for path in sorted(model_path.iterdir()):
                    if path.is_file():
                        row = {"name": path.name, "size": path.stat().st_size}
                        if path.suffix in {".json", ".jinja"}:
                            row["sha256"] = hashlib.sha256(path.read_bytes()).hexdigest()
                        manifest.append(row)
                document["metadata"]["artifact_path"] = str(model_path)
                document["metadata"]["artifact_manifest"] = manifest
                config_path = model_path / "config.json"
                if config_path.exists():
                    document["metadata"]["target_config"] = json.loads(
                        config_path.read_text(encoding="utf-8")
                    )
            document["arms"].append(
                run_arm(
                    args.label,
                    True,
                    session,
                    api_key,
                    throughput_only=args.throughput_only,
                )
            )
        else:
            document["arms"].append(
                run_arm("standard_bf16", False, session, api_key)
            )
            RESULT_PATH.write_text(json.dumps(document, indent=2), encoding="utf-8")
            document["arms"].append(run_arm("fcmeyer_mtp", True, session, api_key))
            document["comparison"] = summarize_comparison(document["arms"])
        document["metadata"]["finished_at"] = time.strftime(
            "%Y-%m-%dT%H:%M:%S%z"
        )
        RESULT_PATH.write_text(json.dumps(document, indent=2), encoding="utf-8")
        say(f"Results written to {RESULT_PATH}")
        if "comparison" in document:
            say(json.dumps(document["comparison"], indent=2))
    finally:
        try:
            unload_model(session, MODEL_ID)
            restore_settings(session, original_target_settings)
            for model_id in originally_loaded:
                model = next(
                    (m for m in get_models(session) if m.get("id") == model_id), None
                )
                if model and not model.get("loaded"):
                    say(f"Restoring originally loaded model: {model_id}")
                    checked(
                        session.post(
                            f"{BASE_URL}/admin/api/models/{model_id}/load",
                            timeout=600,
                        )
                    )
            say("Restored target settings and original loaded-model state")
        finally:
            session.close()


if __name__ == "__main__":
    main()
