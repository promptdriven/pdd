#!/usr/bin/env python3
"""Paired Pi versus official DeepSeek Harness benchmark through local oMLX.

This runner intentionally keeps benchmark tasks and hidden graders outside the
agent sandbox.  It materializes one disposable workspace per cell, runs one
stock harness against a loopback-only metering proxy, grades externally, and
records a compact JSON result.  Raw transcripts stay in the local run root.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import os
import re
import shutil
import signal
import subprocess
import sys
import tempfile
import threading
import time
from dataclasses import asdict, dataclass
from http.server import BaseHTTPRequestHandler, ThreadingHTTPServer
from pathlib import Path
from typing import Any

import requests


MODEL_ID = "Qwen3.8-27B-MLX-oQ8e-mtp"
DEFAULT_TASKS = ("make-ci-green", "add-feature", "taskflow", "webcore")
EXPECTED_TASK_HASHES = {
    "make-ci-green": "4a32fed72b90141fe985416c4b7d44d4f7b34c453fde69773e326b3994f9ce21",
    "add-feature": "d38f578795043c0f10f139647374d3d2563fbea21161ae978ce3c3297f9dbfba",
    "taskflow": "6ed568c66534b0f7839438bfd34c0696a2b6f4a07d2f9469c1541c7e0be074bb",
    "webcore": "a5119ebfed497c749d2d0c93ea41b85dc1fbcd35d22fb0377a836ffa411f4dde",
}
DEFAULT_TIMEOUT_SECONDS = 20 * 60
THINKING_LEVEL = "medium"
TOOL_SUBDIRECTORIES = ("pi", "dsh")
BASE_URL = "http://127.0.0.1:8000"
SETTINGS_PATH = Path.home() / ".omlx" / "settings.json"
MODEL_SETTINGS_PATH = Path.home() / ".omlx" / "model_settings.json"
RESULT_SCHEMA_VERSION = 2
DELTA_MARKER = '"type":"message_update"'
DSH_VERSION = "0.1.1-rc.2"
DSH_TAG = "dsh-v0.1.1-rc.2"
DSH_COMMIT = "b150a551b8d465e31e418e1b2eaf5e79bbb7d28e"
PI_VERSION = "0.73.1"
EXPECTED_MODEL_SETTINGS = {
    "max_context_window": 98304,
    "max_tokens": 32768,
    "temperature": 0.6,
    "top_p": 0.95,
    "top_k": 20,
    "repetition_penalty": 1.0,
    "enable_thinking": True,
    "preserve_thinking": None,
    "thinking_budget_enabled": False,
    "turboquant_kv_enabled": False,
    "qwen35_ane_prefill_enabled": False,
    "specprefill_enabled": False,
    "dflash_enabled": False,
    "mtp_enabled": True,
    "mtp_num_draft_tokens": 4,
    "vlm_mtp_enabled": False,
    "guided_grammar_enabled": False,
    "trust_remote_code": False,
}


def sha256_file(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as handle:
        for chunk in iter(lambda: handle.read(1024 * 1024), b""):
            digest.update(chunk)
    return digest.hexdigest()


def sha256_tree(root: Path) -> str:
    digest = hashlib.sha256()
    for path in sorted(item for item in root.rglob("*") if item.is_file()):
        relative = path.relative_to(root).as_posix()
        digest.update(relative.encode())
        digest.update(b"\0")
        digest.update(sha256_file(path).encode())
        digest.update(b"\n")
    return digest.hexdigest()


def load_api_key() -> str:
    payload = json.loads(SETTINGS_PATH.read_text(encoding="utf-8"))
    key = payload.get("auth", {}).get("api_key")
    if not key:
        raise RuntimeError("oMLX API key is not configured")
    return str(key)


def admin_session(api_key: str) -> requests.Session:
    session = requests.Session()
    response = session.post(
        f"{BASE_URL}/admin/api/login",
        json={"api_key": api_key, "remember": False},
        timeout=15,
    )
    response.raise_for_status()
    return session


def get_models(session: requests.Session) -> list[dict[str, Any]]:
    response = session.get(f"{BASE_URL}/admin/api/models", timeout=30)
    response.raise_for_status()
    return list(response.json()["models"])


def wait_omlx_idle(api_key: str, timeout: int = 60) -> None:
    """Require two consecutive idle status samples before crossing a cell boundary."""
    deadline = time.monotonic() + timeout
    idle_samples = 0
    while time.monotonic() < deadline:
        response = requests.get(
            f"{BASE_URL}/api/status",
            headers={"Authorization": f"Bearer {api_key}"},
            timeout=15,
        )
        response.raise_for_status()
        status = response.json()
        if (
            int(status.get("active_requests") or 0) == 0
            and int(status.get("waiting_requests") or 0) == 0
        ):
            idle_samples += 1
            if idle_samples >= 2:
                return
        else:
            idle_samples = 0
        time.sleep(0.5)
    raise TimeoutError("Timed out waiting for oMLX active/waiting requests to drain")


def persisted_model_settings() -> dict[str, Any]:
    """Read the target's persisted settings without changing model state."""
    payload = json.loads(MODEL_SETTINGS_PATH.read_text(encoding="utf-8"))
    models = payload.get("models") or payload
    settings = models.get(MODEL_ID) if isinstance(models, dict) else None
    if not isinstance(settings, dict):
        raise RuntimeError(f"Missing persisted settings for {MODEL_ID}")
    return settings


def verify_runtime(session: requests.Session, api_key: str) -> dict[str, Any]:
    """Fail closed unless the exact preconfigured oMLX runtime is ready."""
    response = requests.get(
        f"{BASE_URL}/api/status",
        headers={"Authorization": f"Bearer {api_key}"},
        timeout=15,
    )
    response.raise_for_status()
    status = response.json()
    if status.get("version") != "0.6.1":
        raise RuntimeError(f"Expected oMLX 0.6.1, got {status.get('version')!r}")
    model = next((item for item in get_models(session) if item.get("id") == MODEL_ID), None)
    if not model or not model.get("loaded") or model.get("is_loading"):
        raise RuntimeError(f"{MODEL_ID} must already be loaded and stable")
    settings = persisted_model_settings()
    mismatches = {
        key: {"expected": expected, "actual": settings.get(key)}
        for key, expected in EXPECTED_MODEL_SETTINGS.items()
        if settings.get(key) != expected
    }
    chat_kwargs = settings.get("chat_template_kwargs") or {}
    if chat_kwargs.get("reasoning_effort") != THINKING_LEVEL:
        mismatches["chat_template_kwargs.reasoning_effort"] = {
            "expected": THINKING_LEVEL,
            "actual": chat_kwargs.get("reasoning_effort"),
        }
    if mismatches:
        raise RuntimeError(f"Persisted model settings mismatch: {mismatches}")
    wait_omlx_idle(api_key)
    return {
        "omlx_version": status["version"],
        "model_loaded": True,
        "model_settings": {
            **EXPECTED_MODEL_SETTINGS,
            "thinking": THINKING_LEVEL,
        },
    }


def get_memory_guard_tier(session: requests.Session) -> str:
    response = session.get(f"{BASE_URL}/admin/api/global-settings", timeout=30)
    response.raise_for_status()
    payload = response.json()
    tier = (payload.get("memory") or {}).get("memory_guard_tier")
    if not isinstance(tier, str):
        raise RuntimeError("oMLX global settings omitted memory_guard_tier")
    return tier


def set_memory_guard_tier(session: requests.Session, tier: str) -> None:
    response = session.post(
        f"{BASE_URL}/admin/api/global-settings",
        json={"memory_guard_tier": tier},
        timeout=30,
    )
    response.raise_for_status()
    actual = get_memory_guard_tier(session)
    if actual != tier:
        raise RuntimeError(f"Memory Guard restoration failed: expected {tier}, got {actual}")


def record_post_run_verification(
    manifest_path: Path, session: requests.Session, api_key: str
) -> None:
    """Record secret-free evidence that benchmark traffic drained and guard restored."""
    if not manifest_path.exists():
        return
    wait_omlx_idle(api_key, timeout=120)
    final_tier = get_memory_guard_tier(session)
    if final_tier != "balanced":
        raise RuntimeError(
            f"Post-run Memory Guard verification failed: expected balanced, got {final_tier}"
        )
    manifest = json.loads(manifest_path.read_text(encoding="utf-8"))
    manifest["post_run_verification"] = {
        "verified_at": time.strftime("%Y-%m-%dT%H:%M:%S%z"),
        "memory_guard_final_tier": final_tier,
        "two_consecutive_idle_samples": True,
        "active_requests": 0,
        "waiting_requests": 0,
    }
    manifest_path.write_text(
        json.dumps(manifest, indent=2, sort_keys=True) + "\n", encoding="utf-8"
    )


def restore_runtime_state(
    manifest_path: Path, session: requests.Session, api_key: str
) -> None:
    """Drain traffic, restore balanced even after a drain failure, and record proof."""
    idle_error: Exception | None = None
    try:
        wait_omlx_idle(api_key, timeout=120)
    except Exception as exc:  # noqa: BLE001
        idle_error = exc
    set_memory_guard_tier(session, "balanced")
    if idle_error is not None:
        raise RuntimeError(
            "Memory Guard restored to balanced, but oMLX did not drain cleanly"
        ) from idle_error
    record_post_run_verification(manifest_path, session, api_key)


@dataclass
class ProxyTotals:
    requests: int = 0
    failures: int = 0
    input_tokens: int = 0
    output_tokens: int = 0
    cache_read_tokens: int = 0
    cache_write_tokens: int = 0
    response_bytes: int = 0
    completed_responses: int = 0
    generation_duration_seconds: float = 0.0
    prompt_eval_duration_seconds: float = 0.0
    time_to_first_token_seconds: float = 0.0


class TrackedThreadingHTTPServer(ThreadingHTTPServer):
    """Handler lifetime is drained explicitly by :class:`MeteringProxy`."""

    daemon_threads = True


class MeteringProxy:
    def __init__(self, upstream: str, api_key: str, log_path: Path):
        self.upstream = upstream.rstrip("/")
        self.api_key = api_key
        self.log_path = log_path
        self.totals = ProxyTotals()
        self._lock = threading.Lock()
        self._server: ThreadingHTTPServer | None = None
        self._thread: threading.Thread | None = None
        self._active_responses: set[requests.Response] = set()
        self._handler_condition = threading.Condition()
        self._active_handlers = 0

    def _handler_started(self) -> None:
        with self._handler_condition:
            self._active_handlers += 1

    def _handler_finished(self) -> None:
        with self._handler_condition:
            self._active_handlers -= 1
            self._handler_condition.notify_all()

    def _register_response(self, response: requests.Response) -> None:
        with self._lock:
            self._active_responses.add(response)

    def _unregister_response(self, response: requests.Response) -> None:
        with self._lock:
            self._active_responses.discard(response)

    def _cancel_active_responses(self) -> None:
        with self._lock:
            responses = tuple(self._active_responses)
        for response in responses:
            response.close()

    def _drain_handlers(self, timeout: float = 30) -> None:
        deadline = time.monotonic() + timeout
        while True:
            self._cancel_active_responses()
            with self._handler_condition:
                if self._active_handlers == 0:
                    return
                remaining = deadline - time.monotonic()
                if remaining <= 0:
                    raise TimeoutError(
                        f"Timed out draining {self._active_handlers} proxy handler(s)"
                    )
                self._handler_condition.wait(timeout=min(0.1, remaining))

    def _append(self, event: dict[str, Any]) -> None:
        with self._lock:
            with self.log_path.open("a", encoding="utf-8") as handle:
                handle.write(json.dumps(event, sort_keys=True) + "\n")

    def _add_usage(self, usage: dict[str, Any] | None) -> None:
        if not isinstance(usage, dict):
            return
        with self._lock:
            self.totals.input_tokens += int(usage.get("prompt_tokens") or 0)
            self.totals.output_tokens += int(usage.get("completion_tokens") or 0)
            details = usage.get("prompt_tokens_details") or {}
            self.totals.cache_read_tokens += int(details.get("cached_tokens") or 0)
            self.totals.cache_write_tokens += int(
                details.get("cache_write_tokens") or 0
            )
            self.totals.completed_responses += 1
            self.totals.generation_duration_seconds += float(
                usage.get("generation_duration") or 0
            )
            self.totals.prompt_eval_duration_seconds += float(
                usage.get("prompt_eval_duration") or 0
            )
            self.totals.time_to_first_token_seconds += float(
                usage.get("time_to_first_token") or 0
            )

    def start(self) -> int:
        owner = self

        class Handler(BaseHTTPRequestHandler):
            protocol_version = "HTTP/1.1"

            def handle(self) -> None:
                owner._handler_started()
                try:
                    super().handle()
                finally:
                    owner._handler_finished()

            def log_message(self, *_args: Any) -> None:
                return

            def do_GET(self) -> None:  # noqa: N802
                self._forward()

            def do_POST(self) -> None:  # noqa: N802
                self._forward()

            def _forward(self) -> None:
                length = int(self.headers.get("Content-Length") or 0)
                body = self.rfile.read(length) if length else b""
                parsed: dict[str, Any] = {}
                if body:
                    try:
                        candidate = json.loads(body)
                        if isinstance(candidate, dict):
                            parsed = candidate
                    except json.JSONDecodeError:
                        pass
                request_id = f"req-{time.time_ns()}-{threading.get_ident()}"
                summary = {
                    "event": "request",
                    "request_id": request_id,
                    "method": self.command,
                    "path": self.path,
                    "model": parsed.get("model"),
                    "messages": len(parsed.get("messages") or []),
                    "tools": len(parsed.get("tools") or []),
                    "stream": bool(parsed.get("stream")),
                    "temperature": parsed.get("temperature"),
                    "top_p": parsed.get("top_p"),
                    "max_tokens": parsed.get("max_tokens")
                    or parsed.get("max_completion_tokens"),
                    "reasoning_effort": parsed.get("reasoning_effort"),
                    "chat_template_kwargs": parsed.get("chat_template_kwargs"),
                    "body_sha256": hashlib.sha256(body).hexdigest(),
                    "started_at": time.time(),
                }
                owner._append(summary)
                headers = {
                    key: value
                    for key, value in self.headers.items()
                    if key.lower()
                    not in {"host", "authorization", "content-length", "connection"}
                }
                headers["Authorization"] = f"Bearer {owner.api_key}"
                upstream_response: requests.Response | None = None
                try:
                    upstream_response = requests.request(
                        self.command,
                        owner.upstream + self.path,
                        headers=headers,
                        data=body or None,
                        stream=True,
                        timeout=(15, 1800),
                    )
                    owner._register_response(upstream_response)
                    self.send_response(upstream_response.status_code)
                    content_type = upstream_response.headers.get(
                        "Content-Type", "application/json"
                    )
                    self.send_header("Content-Type", content_type)
                    self.send_header("Connection", "close")
                    self.end_headers()
                    collected = bytearray()
                    for chunk in upstream_response.iter_content(chunk_size=8192):
                        if not chunk:
                            continue
                        collected.extend(chunk)
                        self.wfile.write(chunk)
                        self.wfile.flush()
                    payload = bytes(collected)
                    usage = extract_usage(payload, content_type)
                    owner._add_usage(usage)
                    with owner._lock:
                        owner.totals.requests += 1
                        owner.totals.response_bytes += len(payload)
                        if upstream_response.status_code >= 400:
                            owner.totals.failures += 1
                    owner._append(
                        {
                            "event": "response",
                            "request_id": request_id,
                            "status": upstream_response.status_code,
                            "bytes": len(payload),
                            "usage": usage,
                            "finished_at": time.time(),
                        }
                    )
                except Exception as exc:  # noqa: BLE001
                    with owner._lock:
                        owner.totals.requests += 1
                        owner.totals.failures += 1
                    owner._append(
                        {
                            "event": "proxy_error",
                            "request_id": request_id,
                            "error": type(exc).__name__,
                            "finished_at": time.time(),
                        }
                    )
                    try:
                        self.send_error(502, "loopback proxy failure")
                    except OSError:
                        pass
                finally:
                    if upstream_response is not None:
                        owner._unregister_response(upstream_response)
                        upstream_response.close()

        self._server = TrackedThreadingHTTPServer(("127.0.0.1", 0), Handler)
        port = int(self._server.server_address[1])
        self._thread = threading.Thread(target=self._server.serve_forever, daemon=True)
        self._thread.start()
        return port

    def stop(self) -> None:
        if self._server is not None:
            self._server.shutdown()
            try:
                self._drain_handlers()
            finally:
                self._server.server_close()
        if self._thread is not None:
            self._thread.join(timeout=5)


def extract_usage(payload: bytes, content_type: str) -> dict[str, Any] | None:
    candidates: list[dict[str, Any]] = []
    text = payload.decode("utf-8", "replace")
    if "text/event-stream" in content_type:
        for line in text.splitlines():
            if not line.startswith("data:"):
                continue
            value = line[5:].strip()
            if value == "[DONE]":
                continue
            try:
                item = json.loads(value)
            except json.JSONDecodeError:
                continue
            if isinstance(item, dict) and isinstance(item.get("usage"), dict):
                candidates.append(item["usage"])
    else:
        try:
            item = json.loads(text)
        except json.JSONDecodeError:
            item = None
        if isinstance(item, dict) and isinstance(item.get("usage"), dict):
            candidates.append(item["usage"])
    return candidates[-1] if candidates else None


def assert_proxy_log_complete(log_path: Path, totals: ProxyTotals) -> None:
    events = [
        json.loads(line) for line in log_path.read_text().splitlines() if line.strip()
    ]
    request_ids = [
        event["request_id"] for event in events if event.get("event") == "request"
    ]
    terminal_ids = [
        event["request_id"]
        for event in events
        if event.get("event") in {"response", "proxy_error"}
    ]
    if len(request_ids) != len(set(request_ids)):
        raise RuntimeError("Proxy log contains duplicate request IDs")
    if len(terminal_ids) != len(set(terminal_ids)):
        raise RuntimeError("Proxy log contains duplicate terminal events")
    if set(request_ids) != set(terminal_ids):
        raise RuntimeError("Proxy log contains unmatched request/terminal events")
    if totals.requests != len(terminal_ids):
        raise RuntimeError(
            f"Proxy totals/log mismatch: totals={totals.requests}, terminals={len(terminal_ids)}"
        )


def assert_proxy_identity(log_path: Path) -> dict[str, Any]:
    """Prove all model traffic used the loopback proxy and exact target model."""
    events = [
        json.loads(line) for line in log_path.read_text().splitlines() if line.strip()
    ]
    requests_by_id = {
        event["request_id"]: event
        for event in events
        if event.get("event") == "request"
    }
    terminals_by_id = {
        event["request_id"]: event
        for event in events
        if event.get("event") in {"response", "proxy_error"}
    }
    completion_requests = [
        event
        for event in requests_by_id.values()
        if event.get("path") == "/v1/chat/completions"
    ]
    if not completion_requests:
        raise RuntimeError("Harness sent no proxied /v1/chat/completions request")
    wrong_models = sorted(
        {event.get("model") for event in completion_requests if event.get("model") != MODEL_ID},
        key=str,
    )
    if wrong_models:
        raise RuntimeError(f"Proxy observed wrong model IDs: {wrong_models}")
    unexpected = [
        {"method": event.get("method"), "path": event.get("path")}
        for event in requests_by_id.values()
        if event.get("method") != "POST"
        or event.get("path") != "/v1/chat/completions"
    ]
    if unexpected:
        raise RuntimeError(f"Proxy observed unexpected endpoint traffic: {unexpected}")
    ordered = sorted(requests_by_id.values(), key=lambda event: event["started_at"])
    prior_finished = 0.0
    for event in ordered:
        if event["started_at"] < prior_finished:
            raise RuntimeError("Proxy observed overlapping oMLX requests within one cell")
        prior_finished = float(terminals_by_id[event["request_id"]]["finished_at"])
    def values(key: str) -> list[Any]:
        serialized = {json.dumps(event.get(key), sort_keys=True) for event in ordered}
        return [json.loads(value) for value in sorted(serialized)]

    return {
        "verified": True,
        "base_url": BASE_URL,
        "path": "/v1/chat/completions",
        "model": MODEL_ID,
        "completion_requests": len(completion_requests),
        "max_tokens": values("max_tokens"),
        "temperature": values("temperature"),
        "top_p": values("top_p"),
        "reasoning_effort": values("reasoning_effort"),
        "chat_template_kwargs": values("chat_template_kwargs"),
        "tool_counts": values("tools"),
        "serial_requests": True,
    }


def write_pi_model_config(config_dir: Path, proxy_port: int) -> None:
    config_dir.mkdir(parents=True, exist_ok=True)
    payload = {
        "providers": {
            "omlx-benchmark": {
                "baseUrl": f"http://127.0.0.1:{proxy_port}/v1",
                "api": "openai-completions",
                "apiKey": "loopback-proxy",
                "compat": {
                    "supportsDeveloperRole": False,
                    "supportsReasoningEffort": False,
                    "supportsUsageInStreaming": True,
                    "maxTokensField": "max_tokens",
                    "thinkingFormat": "qwen-chat-template",
                },
                "models": [
                    {
                        "id": MODEL_ID,
                        "name": "Qwen3.8 27B oQ8e MTP benchmark",
                        "reasoning": True,
                        "thinkingLevelMap": {
                            "off": None,
                            "minimal": None,
                            "low": "low",
                            "medium": THINKING_LEVEL,
                            "high": "high",
                            "xhigh": "xhigh",
                            "max": None,
                        },
                        "input": ["text"],
                        "contextWindow": 98304,
                        "maxTokens": 32768,
                        "cost": {
                            "input": 0,
                            "output": 0,
                            "cacheRead": 0,
                            "cacheWrite": 0,
                        },
                    }
                ],
            }
        }
    }
    (config_dir / "models.json").write_text(
        json.dumps(payload, indent=2) + "\n", encoding="utf-8"
    )


def write_dsh_config(home: Path, proxy_port: int) -> Path:
    """Write a secret-free custom provider and fixed benchmark overlay."""
    home.mkdir(parents=True, exist_ok=True)
    settings = f"""llm-pi-ai:
  providers:
    omlx-benchmark:
      displayName: oMLX benchmark
      apiKeyEnv: OMLX_BENCHMARK_API_KEY
      api: openai-completions
      baseURL: http://127.0.0.1:{proxy_port}/v1
      reasoning: {THINKING_LEVEL}
      retryPolicy:
        mode: normal
        maxRetries: 0
      compat:
        supportsDeveloperRole: false
        supportsReasoningEffort: false
        supportsUsageInStreaming: true
        maxTokensField: max_tokens
        thinkingFormat: qwen-chat-template
      models:
        - id: {MODEL_ID}
          name: Qwen3.8 27B oQ8e MTP benchmark
          contextWindow: 98304
          maxTokens: 32000
          reasoningEfforts:
            medium: medium
"""
    (home / "settings.yaml").write_text(settings, encoding="utf-8")
    patch = home / "benchmark.cordis.patch.yml"
    patch.write_text(
        f"""- id: agent-default-model
  config:
    provider: omlx-benchmark
    model: {MODEL_ID}

# Match Pi's no-context-files/no-skills and the loopback-only capability boundary.
- id: agent-instructions
  disabled: true

- id: tool-skill
  disabled: true

- id: tool-web
  disabled: true

- id: session-title-llm
  disabled: true

# Prevent DSH-native fan-out from creating concurrent oMLX traffic.
- id: tool-subagent
  disabled: true

- id: tool-subagent-fork
  disabled: true

- id: tool-workflow
  disabled: true

- id: tool-ralph
  disabled: true
""",
        encoding="utf-8",
    )
    return patch


def tool_read_roots(tool_root: Path) -> tuple[Path, ...]:
    return tuple((tool_root / name).resolve() for name in TOOL_SUBDIRECTORIES)


def sandbox_profile(
    run_root: Path,
    workspace: Path,
    home: Path,
    tool_root: Path,
    temp_dir: Path,
    port: int,
) -> str:
    def quoted(path: Path) -> str:
        return str(path).replace('"', '\\"')

    read_roots = " ".join(
        f'(subpath "{quoted(path)}")' for path in tool_read_roots(tool_root)
    )
    rules = [
        "(version 1)",
        '(import "system.sb")',
        "(allow process*)",
        "(allow sysctl-read)",
        "(allow file-read-metadata)",
        f"(allow file-read* {read_roots} "
        f'(subpath "{quoted(run_root)}") (subpath "{quoted(temp_dir)}") '
        '(subpath "/opt/homebrew") '
        '(subpath "/usr/local") (subpath "/Library") (subpath "/System") '
        '(subpath "/usr") (subpath "/bin") (subpath "/sbin") (subpath "/etc"))',
        f"(allow file-map-executable {read_roots} "
        '(subpath "/opt/homebrew") (subpath "/usr/local") '
        '(subpath "/Library") (subpath "/System") (subpath "/usr"))',
        "(deny network*)",
        f'(allow network-outbound (remote ip "localhost:{port}"))',
        f'(allow file-write* (subpath "{quoted(workspace)}") '
        f'(subpath "{quoted(home)}") (subpath "{quoted(temp_dir)}"))',
    ]
    return " ".join(rules)


def terminate_group(process: subprocess.Popen[str]) -> None:
    try:
        os.killpg(process.pid, signal.SIGTERM)
        process.wait(timeout=5)
    except (ProcessLookupError, subprocess.TimeoutExpired):
        try:
            os.killpg(process.pid, signal.SIGKILL)
        except ProcessLookupError:
            pass
        process.wait(timeout=5)


def cleanup_marked_processes(markers: tuple[str, ...]) -> list[int]:
    """Terminate only orphan processes carrying a cell's unique path markers."""
    rows = subprocess.run(
        ["ps", "-axo", "pid=,command="],
        capture_output=True,
        text=True,
        check=True,
    ).stdout.splitlines()
    pids = sorted(
        int(row.strip().split(maxsplit=1)[0])
        for row in rows
        if any(marker in row for marker in markers)
    )
    for pid in pids:
        try:
            os.kill(pid, signal.SIGTERM)
        except ProcessLookupError:
            pass
    deadline = time.monotonic() + 5
    remaining = set(pids)
    while remaining and time.monotonic() < deadline:
        for pid in tuple(remaining):
            try:
                os.kill(pid, 0)
            except ProcessLookupError:
                remaining.remove(pid)
        if remaining:
            time.sleep(0.1)
    for pid in remaining:
        try:
            os.kill(pid, signal.SIGKILL)
        except ProcessLookupError:
            pass
    if remaining:
        time.sleep(0.2)
    survivors: list[int] = []
    for pid in remaining:
        try:
            os.kill(pid, 0)
            survivors.append(pid)
        except ProcessLookupError:
            pass
    if survivors:
        raise RuntimeError(f"Cell cleanup could not terminate PIDs: {survivors}")
    return pids


def run_harness(
    harness: str,
    executable: Path,
    tool_root: Path,
    workspace: Path,
    instruction: str,
    run_root: Path,
    proxy_port: int,
    timeout_seconds: int,
) -> dict[str, Any]:
    home = run_root / "home"
    temp_dir = run_root / "tmp"
    home.mkdir(parents=True)
    temp_dir.mkdir(parents=True)
    if harness == "pi":
        config_dir = home / ".pi" / "agent"
        write_pi_model_config(config_dir, proxy_port)
        command = [
            str(executable),
            "--provider",
            "omlx-benchmark",
            "--model",
            MODEL_ID,
            "--thinking",
            THINKING_LEVEL,
            "--mode",
            "json",
            "--print",
            "--no-session",
            "--no-extensions",
            "--no-skills",
            "--no-prompt-templates",
            "--no-context-files",
            instruction,
        ]
    elif harness == "dsh":
        patch_path = write_dsh_config(home, proxy_port)
        command = [
            str(executable),
            "--profile",
            "headless",
            "--patch",
            str(patch_path),
            instruction,
        ]
    else:
        raise ValueError(f"Unknown harness: {harness}")

    environment = {
        "PATH": "/opt/homebrew/bin:/usr/local/bin:/usr/bin:/bin:/usr/sbin:/sbin",
        "HOME": str(home),
        "TMPDIR": str(temp_dir),
        "LANG": "en_US.UTF-8",
        "LC_ALL": "en_US.UTF-8",
        "NO_PROXY": "localhost,127.0.0.1",
        "no_proxy": "localhost,127.0.0.1",
        "PI_CODING_AGENT_DIR": str(home / ".pi" / "agent"),
        "PI_OFFLINE": "1",
        "PI_TELEMETRY": "0",
        "DSH_HOME": str(home),
        "DSH_PERMISSION_MODE": "danger-full-access",
        "DSH_TELEMETRY_DISABLED": "1",
        "DSH_TOOLS_MODE": "native",
        "OMLX_BENCHMARK_API_KEY": "loopback-proxy",
        "PYTHONDONTWRITEBYTECODE": "1",
    }
    profile = sandbox_profile(run_root, workspace, home, tool_root, temp_dir, proxy_port)
    wrapped = ["/usr/bin/sandbox-exec", "-p", profile, *command]
    started = time.monotonic()
    process = subprocess.Popen(
        wrapped,
        cwd=workspace,
        env=environment,
        stdin=subprocess.DEVNULL,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
        text=True,
        start_new_session=True,
    )
    timed_out = False
    try:
        stdout, stderr = process.communicate(timeout=timeout_seconds)
    except subprocess.TimeoutExpired:
        timed_out = True
        terminate_group(process)
        stdout, stderr = process.communicate()
    elapsed = time.monotonic() - started
    filtered_lines = [line for line in stdout.splitlines() if DELTA_MARKER not in line]
    (run_root / "transcript.jsonl").write_text(
        "\n".join(filtered_lines) + "\n", encoding="utf-8"
    )
    (run_root / "stderr.txt").write_text(stderr[-100_000:], encoding="utf-8")
    forced_pids = cleanup_marked_processes((str(home), str(temp_dir)))
    return {
        "returncode": process.returncode,
        "timed_out": timed_out,
        "wall_seconds": elapsed,
        "stdout_bytes": len(stdout.encode()),
        "stderr_bytes": len(stderr.encode()),
        "stderr_tail": stderr[-2000:],
        "forced_residual_pids": forced_pids,
    }


def checker_sandbox_profile(task_dir: Path, workspace: Path, temp_dir: Path) -> str:
    """Constrain trusted pinned checker code and deny inherited network access."""
    def quoted(path: Path) -> str:
        return str(path.resolve()).replace('"', '\\"')

    return " ".join(
        [
            "(version 1)",
            '(import "system.sb")',
            "(allow process*)",
            "(allow sysctl-read)",
            "(allow file-read-metadata)",
            "(deny network*)",
            (
                f'(allow file-read* (subpath "{quoted(task_dir)}") '
                f'(subpath "{quoted(workspace)}") (subpath "{quoted(temp_dir)}") '
                f'(subpath "{quoted(Path(sys.prefix))}") '
                '(subpath "/opt/homebrew") (subpath "/usr/local") '
                '(subpath "/Library") (subpath "/System") (subpath "/usr") '
                '(subpath "/bin") (subpath "/sbin") (subpath "/etc"))'
            ),
            (
                f'(allow file-write* (subpath "{quoted(workspace)}") '
                f'(subpath "{quoted(temp_dir)}"))'
            ),
            (
                f'(allow file-map-executable (subpath "{quoted(Path(sys.prefix))}") '
                '(subpath "/opt/homebrew") (subpath "/usr/local") '
                '(subpath "/Library") (subpath "/System") (subpath "/usr"))'
            ),
        ]
    )


def grade_task(task_dir: Path, workspace: Path) -> dict[str, Any]:
    for cache_dir in workspace.rglob("__pycache__"):
        shutil.rmtree(cache_dir, ignore_errors=True)
    try:
        with tempfile.TemporaryDirectory(prefix="checker-", dir="/private/tmp") as raw:
            temp_dir = Path(raw)
            environment = {
                "PATH": "/opt/homebrew/bin:/usr/local/bin:/usr/bin:/bin:/usr/sbin:/sbin",
                "HOME": str(temp_dir),
                "TMPDIR": str(temp_dir),
                "LANG": "en_US.UTF-8",
                "LC_ALL": "en_US.UTF-8",
                "TASK_DIR": str(task_dir.resolve()),
                "PYTHONDONTWRITEBYTECODE": "1",
            }
            profile = checker_sandbox_profile(task_dir, workspace, temp_dir)
            result = subprocess.run(
                [
                    "/usr/bin/sandbox-exec",
                    "-p",
                    profile,
                    sys.executable,
                    str(task_dir / "checker_data" / "run_score.py"),
                ],
                cwd=workspace,
                env=environment,
                capture_output=True,
                text=True,
                timeout=180,
                check=False,
            )
        output = (result.stdout or "") + (result.stderr or "")
        matches = re.findall(
            r"^SCORE:\s*([0-9]+(?:\.[0-9]+)?)\s*$", output, re.MULTILINE
        )
        score = (
            float(matches[-1]) if matches else (1.0 if result.returncode == 0 else 0.0)
        )
        return {
            "checker_exit": result.returncode,
            "score": score,
            "passed": result.returncode == 0,
            "output": output[-5000:],
        }
    except subprocess.TimeoutExpired as exc:
        return {
            "checker_exit": "timeout",
            "score": 0.0,
            "passed": False,
            "output": ((exc.stdout or "") + (exc.stderr or ""))[-5000:],
        }


def initialize_workspace(task_dir: Path, destination: Path) -> None:
    shutil.copytree(task_dir / "workspace", destination)
    subprocess.run(["git", "init", "-q"], cwd=destination, check=True)
    subprocess.run(
        ["git", "config", "user.email", "benchmark@localhost"],
        cwd=destination,
        check=True,
    )
    subprocess.run(
        ["git", "config", "user.name", "Benchmark"], cwd=destination, check=True
    )
    subprocess.run(["git", "add", "-A"], cwd=destination, check=True)
    subprocess.run(["git", "commit", "-qm", "baseline"], cwd=destination, check=True)


def workspace_changes(workspace: Path) -> dict[str, Any]:
    status = subprocess.run(
        ["git", "status", "--short"],
        cwd=workspace,
        capture_output=True,
        text=True,
        check=True,
    ).stdout
    diff = subprocess.run(
        ["git", "diff", "--binary"], cwd=workspace, capture_output=True, check=True
    ).stdout
    return {
        "status": status.splitlines(),
        "changed_files": len(status.splitlines()),
        "diff_bytes": len(diff),
        "diff_sha256": hashlib.sha256(diff).hexdigest(),
    }


def run_cell(
    *,
    task: str,
    harness: str,
    trial: int,
    tasks_root: Path,
    run_base: Path,
    executable: Path,
    tool_root: Path,
    api_key: str,
    timeout_seconds: int,
    phase: str = "benchmark",
) -> dict[str, Any]:
    task_dir = tasks_root / task
    if not (task_dir / "workspace").is_dir() or not (task_dir / "checker.sh").is_file():
        raise FileNotFoundError(f"Invalid task: {task_dir}")
    run_id = f"{trial:02d}-{task}-{harness}"
    run_root = (run_base / "raw" / run_id).resolve()
    resolved_tasks_root = tasks_root.resolve()
    if (
        run_root == resolved_tasks_root
        or run_root.is_relative_to(resolved_tasks_root)
        or resolved_tasks_root.is_relative_to(run_root)
    ):
        raise RuntimeError(f"Run root overlaps hidden task/checker tree: {run_root}")
    run_root.mkdir(parents=True)
    workspace = run_root / "workspace"
    initialize_workspace(task_dir, workspace)
    instruction = (task_dir / "instruction.md").read_text(encoding="utf-8").strip()
    instruction += (
        "\n\nWork only in the current workspace. Implement the requested coding change, "
        "run the relevant tests, and finish when the implementation is correct."
    )
    proxy = MeteringProxy(BASE_URL, api_key, run_root / "proxy.jsonl")
    wait_omlx_idle(api_key)
    port = proxy.start()
    try:
        harness_result = run_harness(
            harness,
            executable,
            tool_root,
            workspace,
            instruction,
            run_root,
            port,
            timeout_seconds,
        )
    finally:
        proxy.stop()
    wait_omlx_idle(api_key)
    assert_proxy_log_complete(run_root / "proxy.jsonl", proxy.totals)
    proxy_identity = assert_proxy_identity(run_root / "proxy.jsonl")
    grade = grade_task(task_dir, workspace)
    changes = workspace_changes(workspace)
    result = {
        "schema_version": RESULT_SCHEMA_VERSION,
        "run_id": run_id,
        "phase": phase,
        "task": task,
        "task_sha256": sha256_tree(task_dir),
        "harness": harness,
        "trial": trial,
        "model": MODEL_ID,
        "thinking": THINKING_LEVEL,
        "timeout_seconds": timeout_seconds,
        "harness_result": harness_result,
        "proxy_totals": asdict(proxy.totals),
        "proxy_identity": proxy_identity,
        "grade": grade,
        "changes": changes,
        "finished_at": time.strftime("%Y-%m-%dT%H:%M:%S%z"),
    }
    result_path = run_base / "results.jsonl"
    with result_path.open("a", encoding="utf-8") as handle:
        handle.write(json.dumps(result, sort_keys=True) + "\n")
        handle.flush()
        os.fsync(handle.fileno())
    print(
        f"{run_id}: score={grade['score']:.3f} pass={grade['passed']} "
        f"wall={harness_result['wall_seconds']:.1f}s requests={proxy.totals.requests} "
        f"out={proxy.totals.output_tokens}",
        flush=True,
    )
    return result


def validate_tasks(tasks_root: Path, tasks: tuple[str, ...]) -> None:
    for task in tasks:
        task_dir = tasks_root / task
        expected_hash = EXPECTED_TASK_HASHES.get(task)
        if expected_hash is None:
            raise RuntimeError(f"No pinned task hash for requested task: {task}")
        actual_hash = sha256_tree(task_dir)
        if actual_hash != expected_hash:
            raise RuntimeError(
                f"Pinned task hash mismatch for {task}: "
                f"expected {expected_hash}, got {actual_hash}"
            )
        with tempfile.TemporaryDirectory(
            prefix=f"validate-{task}-", dir="/private/tmp"
        ) as temp:
            workspace = Path(temp) / "workspace"
            shutil.copytree(task_dir / "workspace", workspace)
            untouched = grade_task(task_dir, workspace)
            if untouched["passed"]:
                raise RuntimeError(f"Untouched workspace unexpectedly passes: {task}")
            solution = task_dir / "solution"
            if solution.is_dir():
                shutil.copytree(solution, workspace, dirs_exist_ok=True)
                golden = grade_task(task_dir, workspace)
                if not golden["passed"]:
                    raise RuntimeError(
                        f"Golden solution fails: {task}: {golden['output']}"
                    )
        print(f"validated {task}: untouched={untouched['score']:.3f}", flush=True)


def validate_hidden_grader_boundary(
    tasks_root: Path, tasks: tuple[str, ...], tool_root: Path
) -> None:
    tasks_root = tasks_root.resolve()
    read_roots = tool_read_roots(tool_root)
    for read_root in read_roots:
        if not read_root.is_dir():
            raise FileNotFoundError(f"Missing tool read root: {read_root}")
        if (
            tasks_root == read_root
            or tasks_root.is_relative_to(read_root)
            or read_root.is_relative_to(tasks_root)
        ):
            raise RuntimeError(
                f"Task/checker tree overlaps agent-readable tool root: {read_root}"
            )

    with tempfile.TemporaryDirectory(
        prefix="grader-boundary-", dir="/private/tmp"
    ) as raw:
        canary_root = Path(raw)
        workspace = canary_root / "workspace"
        home = canary_root / "home"
        temp_dir = canary_root / "tmp"
        for path in (workspace, home, temp_dir):
            path.mkdir()
        readable_control = workspace / "readable-control.txt"
        readable_control.write_text("sandbox-positive-control\n", encoding="utf-8")
        profile = sandbox_profile(
            canary_root, workspace, home, tool_root, temp_dir, 9
        )
        positive_probe = subprocess.run(
            ["sandbox-exec", "-p", profile, "/bin/cat", str(readable_control)],
            capture_output=True,
            timeout=10,
        )
        if (
            positive_probe.returncode != 0
            or positive_probe.stdout != b"sandbox-positive-control\n"
        ):
            raise RuntimeError("Sandbox positive-control read failed")
        targets: list[Path] = []
        for task in tasks:
            task_dir = tasks_root / task
            targets.append(task_dir / "checker.sh")
            for private_name in ("checker_data", "solution"):
                private_root = task_dir / private_name
                if private_root.is_dir():
                    target = next(
                        (item for item in private_root.rglob("*") if item.is_file()),
                        None,
                    )
                    if target is not None:
                        targets.append(target)
        for target in targets:
            probe = subprocess.run(
                ["sandbox-exec", "-p", profile, "/bin/cat", str(target)],
                capture_output=True,
                timeout=10,
            )
            if probe.returncode == 0:
                raise RuntimeError(
                    f"Hidden grader is readable inside agent sandbox: {target}"
                )
    print(
        f"validated hidden-grader boundary: denied {len(targets)} file probes",
        flush=True,
    )


def validate_root_separation(tasks_root: Path, tool_root: Path, run_base: Path) -> None:
    """Reject overlap among hidden tasks, readable tools, and raw run artifacts."""
    roots = {
        "task/checker tree": tasks_root.resolve(),
        "run root": run_base.resolve(),
        **{
            f"tool root {name}": path
            for name, path in zip(TOOL_SUBDIRECTORIES, tool_read_roots(tool_root))
        },
    }
    items = list(roots.items())
    for index, (left_name, left) in enumerate(items):
        for right_name, right in items[index + 1 :]:
            if left == right or left.is_relative_to(right) or right.is_relative_to(left):
                raise RuntimeError(
                    f"Overlapping benchmark roots: {left_name}={left}, "
                    f"{right_name}={right}"
                )


def build_schedule(tasks: tuple[str, ...], trials: int) -> list[tuple[int, str, str]]:
    schedule: list[tuple[int, str, str]] = []
    for trial in range(1, trials + 1):
        for index, task in enumerate(tasks):
            pi_first = (index + trial) % 2 == 1
            order = ("pi", "dsh") if pi_first else ("dsh", "pi")
            schedule.extend((trial, task, harness) for harness in order)
    return schedule


def dsh_environment(home: Path, temp_dir: Path) -> dict[str, str]:
    return {
        "PATH": "/opt/homebrew/bin:/usr/local/bin:/usr/bin:/bin:/usr/sbin:/sbin",
        "HOME": str(home),
        "TMPDIR": str(temp_dir),
        "LANG": "en_US.UTF-8",
        "LC_ALL": "en_US.UTF-8",
        "NO_PROXY": "localhost,127.0.0.1",
        "no_proxy": "localhost,127.0.0.1",
        "DSH_HOME": str(home),
        "DSH_PERMISSION_MODE": "danger-full-access",
        "DSH_TELEMETRY_DISABLED": "1",
        "DSH_TOOLS_MODE": "native",
        "OMLX_BENCHMARK_API_KEY": "loopback-proxy",
    }


def preflight_dsh_config(executable: Path, tool_root: Path) -> dict[str, Any]:
    """Resolve the official headless profile and benchmark overlay without booting it."""
    with tempfile.TemporaryDirectory(prefix="dsh-config-", dir="/private/tmp") as raw:
        root = Path(raw)
        home = root / "home"
        temp_dir = root / "tmp"
        workspace = root / "workspace"
        for path in (home, temp_dir, workspace):
            path.mkdir()
        patch = write_dsh_config(home, 9)
        profile = sandbox_profile(root, workspace, home, tool_root, temp_dir, 9)
        command = [
            "/usr/bin/sandbox-exec",
            "-p",
            profile,
            str(executable),
            "--profile",
            "headless",
            "--patch",
            str(patch),
            "--dump-config",
        ]
        result = subprocess.run(
            command,
            cwd=workspace,
            env=dsh_environment(home, temp_dir),
            capture_output=True,
            text=True,
            timeout=120,
        )
        if result.returncode != 0:
            raise RuntimeError(f"DSH config preflight failed: {result.stderr[-4000:]}")
        required = (
            "provider: omlx-benchmark",
            f"model: {MODEL_ID}",
            "id: llm-pi-ai",
            "id: tool-web",
            "disabled: true",
        )
        missing = [value for value in required if value not in result.stdout]
        if missing:
            raise RuntimeError(f"DSH composed config omitted required values: {missing}")
        if "loopback-proxy" in result.stdout:
            raise RuntimeError("DSH composed config unexpectedly materialized a credential")
        return {
            "returncode": result.returncode,
            "config_sha256": hashlib.sha256(result.stdout.encode()).hexdigest(),
            "stderr": result.stderr[-1000:],
        }


def version_output(executable: Path) -> str:
    result = subprocess.run(
        [str(executable), "--version"], capture_output=True, text=True, check=True
    )
    return result.stdout.strip()


def assert_smoke_gate(results: dict[str, dict[str, Any]]) -> None:
    if set(results) != {"pi", "dsh"}:
        raise RuntimeError("Matched smoke requires exactly one Pi and one DSH result")
    for harness, row in results.items():
        harness_result = row["harness_result"]
        if harness_result["timed_out"] or harness_result["returncode"] != 0:
            raise RuntimeError(f"{harness} smoke did not finish successfully")
        if row["proxy_totals"]["failures"] or not row["proxy_identity"]["verified"]:
            raise RuntimeError(f"{harness} smoke request telemetry failed")
        if row["grade"]["checker_exit"] == "timeout":
            raise RuntimeError(f"{harness} smoke hidden checker timed out")
    comparable_fields = (
        "max_tokens",
        "temperature",
        "top_p",
        "reasoning_effort",
        "chat_template_kwargs",
    )
    mismatches = {
        field: {
            "pi": results["pi"]["proxy_identity"][field],
            "dsh": results["dsh"]["proxy_identity"][field],
        }
        for field in comparable_fields
        if results["pi"]["proxy_identity"][field]
        != results["dsh"]["proxy_identity"][field]
    }
    if mismatches:
        raise RuntimeError(f"Matched smoke request settings differ: {mismatches}")


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser()
    parser.add_argument("--tasks-root", type=Path, required=True)
    parser.add_argument("--pi", type=Path, required=True)
    parser.add_argument("--dsh", type=Path, required=True)
    parser.add_argument("--tool-root", type=Path, required=True)
    parser.add_argument("--run-base", type=Path, required=True)
    parser.add_argument("--tasks", default=",".join(DEFAULT_TASKS))
    parser.add_argument("--trials", type=int, default=2)
    parser.add_argument("--timeout-seconds", type=int, default=DEFAULT_TIMEOUT_SECONDS)
    parser.add_argument("--smoke-timeout-seconds", type=int, default=10 * 60)
    parser.add_argument("--validate-only", action="store_true")
    return parser.parse_args()


def main() -> None:
    args = parse_args()
    tasks = tuple(item.strip() for item in args.tasks.split(",") if item.strip())
    validate_root_separation(args.tasks_root, args.tool_root, args.run_base)
    validate_hidden_grader_boundary(args.tasks_root, tasks, args.tool_root)
    validate_tasks(args.tasks_root, tasks)
    dsh_preflight = preflight_dsh_config(args.dsh, args.tool_root)
    if args.validate_only:
        return
    args.run_base.mkdir(parents=True, exist_ok=True)
    manifest_path = args.run_base / "manifest.json"
    api_key = load_api_key()
    session = admin_session(api_key)
    try:
        runtime = verify_runtime(session, api_key)
        initial_guard_tier = get_memory_guard_tier(session)
        if initial_guard_tier not in {"balanced", "aggressive"}:
            raise RuntimeError(f"Unexpected Memory Guard tier: {initial_guard_tier}")
        if initial_guard_tier != "aggressive":
            set_memory_guard_tier(session, "aggressive")
        task_hashes = {task: sha256_tree(args.tasks_root / task) for task in tasks}
        pi_version = version_output(args.pi)
        dsh_version = version_output(args.dsh)
        if pi_version != PI_VERSION or dsh_version != DSH_VERSION:
            raise RuntimeError(
                f"Harness version mismatch: pi={pi_version!r}, dsh={dsh_version!r}"
            )
        manifest = {
            "schema_version": RESULT_SCHEMA_VERSION,
            "started_at": time.strftime("%Y-%m-%dT%H:%M:%S%z"),
            "access_date": "2026-08-23",
            "endpoint": f"{BASE_URL}/v1",
            "model": MODEL_ID,
            "runtime": runtime,
            "memory_guard_during_trials": "aggressive",
            "memory_guard_initial_tier": initial_guard_tier,
            "memory_guard_required_final_tier": "balanced",
            "tasks": list(tasks),
            "task_hashes": task_hashes,
            "task_source": {
                "repository": "https://github.com/minghinmatthewlam/openbench",
                "commit": "9e26c96a7df012ca9173e9725211c4cc58e11948",
            },
            "trials": args.trials,
            "timeout_seconds": args.timeout_seconds,
            "smoke_timeout_seconds": args.smoke_timeout_seconds,
            "pi_version": pi_version,
            "dsh": {
                "version": dsh_version,
                "tag": DSH_TAG,
                "commit": DSH_COMMIT,
                "license": "MIT",
            },
            "dsh_config_preflight": dsh_preflight,
            "tool_policy": {
                "pi": (
                    "stock built-ins; extensions, skills, prompt templates, "
                    "context files disabled"
                ),
                "dsh": (
                    "official headless native tools; web, skills, context files, "
                    "model-spawning tools, and model title generation disabled"
                ),
                "dsh_retry_max_retries": 0,
                "outer_sandbox": (
                    "macOS Seatbelt; exact tool roots; workspace/home/temp writes; "
                    "proxy-only network"
                ),
            },
            "operational_notes_not_measurements": [
                (
                    "Qwen3.6-35B-A3B-bf16 unloaded before trials; oMLX logged "
                    "65.39 GB freed."
                ),
                (
                    "First orchestration preflight failed at the hard memory "
                    "watermark before any trial."
                ),
                (
                    "Second orchestration preflight failed the balanced prefill "
                    "guard before any trial."
                ),
                "Global Memory Guard changed from balanced to aggressive for benchmark traffic.",
            ],
        }
        if manifest_path.exists():
            existing = json.loads(manifest_path.read_text(encoding="utf-8"))
            existing_protocol = {
                key: value
                for key, value in existing.items()
                if key
                not in {
                    "started_at",
                    "memory_guard_initial_tier",
                    "post_run_verification",
                }
            }
            current_protocol = {
                key: value
                for key, value in manifest.items()
                if key not in {"started_at", "memory_guard_initial_tier"}
            }
            if existing_protocol != current_protocol:
                raise RuntimeError("Resume protocol does not match the existing manifest")
        else:
            manifest_path.write_text(
                json.dumps(manifest, indent=2, sort_keys=True) + "\n",
                encoding="utf-8",
            )

        smoke_base = args.run_base / "smoke"
        smoke_base.mkdir(parents=True, exist_ok=True)
        smoke_rows: dict[str, dict[str, Any]] = {}
        smoke_results_path = smoke_base / "results.jsonl"
        if smoke_results_path.exists():
            for line in smoke_results_path.read_text(encoding="utf-8").splitlines():
                if line.strip():
                    row = json.loads(line)
                    smoke_rows[row["harness"]] = row
        for harness in ("dsh", "pi"):
            if harness in smoke_rows:
                print(f"smoke {harness}: already complete; skipping", flush=True)
                continue
            executable = args.dsh if harness == "dsh" else args.pi
            smoke_rows[harness] = run_cell(
                task=tasks[0],
                harness=harness,
                trial=1,
                tasks_root=args.tasks_root,
                run_base=smoke_base,
                executable=executable,
                tool_root=args.tool_root,
                api_key=api_key,
                timeout_seconds=args.smoke_timeout_seconds,
                phase="smoke",
            )
        assert_smoke_gate(smoke_rows)

        benchmark_base = args.run_base / "benchmark"
        benchmark_base.mkdir(parents=True, exist_ok=True)
        results_path = benchmark_base / "results.jsonl"
        completed_run_ids: set[str] = set()
        if results_path.exists():
            completed_run_ids = {
                json.loads(line)["run_id"]
                for line in results_path.read_text(encoding="utf-8").splitlines()
                if line.strip()
            }
        for trial, task, harness in build_schedule(tasks, args.trials):
            run_id = f"{trial:02d}-{task}-{harness}"
            if run_id in completed_run_ids:
                print(f"{run_id}: already complete; skipping", flush=True)
                continue
            executable = args.pi if harness == "pi" else args.dsh
            run_cell(
                task=task,
                harness=harness,
                trial=trial,
                tasks_root=args.tasks_root,
                run_base=benchmark_base,
                executable=executable,
                tool_root=args.tool_root,
                api_key=api_key,
                timeout_seconds=args.timeout_seconds,
                phase="benchmark",
            )
    finally:
        restore_runtime_state(manifest_path, session, api_key)


if __name__ == "__main__":
    main()
