#!/usr/bin/env python3
"""Paired Pi versus Prime Agent coding benchmark through local oMLX.

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
DEFAULT_TIMEOUT_SECONDS = 20 * 60
THINKING_LEVEL = "medium"
TOOL_SUBDIRECTORIES = ("pi", "prime", "prime-kernel")
BASE_URL = "http://127.0.0.1:8000"
SETTINGS_PATH = Path.home() / ".omlx" / "settings.json"
RESULT_SCHEMA_VERSION = 1
DELTA_MARKER = '"type":"message_update"'


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


def wait_loaded(session: requests.Session, loaded: bool, timeout: int = 600) -> None:
    deadline = time.monotonic() + timeout
    while time.monotonic() < deadline:
        model = next(
            (item for item in get_models(session) if item.get("id") == MODEL_ID),
            None,
        )
        if (
            model
            and bool(model.get("loaded")) == loaded
            and not model.get("is_loading")
        ):
            return
        time.sleep(1)
    raise TimeoutError(f"Timed out waiting for {MODEL_ID} loaded={loaded}")


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


def configure_model(session: requests.Session) -> dict[str, Any]:
    model = next(item for item in get_models(session) if item.get("id") == MODEL_ID)
    original = dict(model.get("settings") or {})
    benchmark_settings = {
        "max_context_window": 98304,
        "max_tokens": 32768,
        "temperature": 0.6,
        "top_p": 0.95,
        "top_k": 20,
        "repetition_penalty": 1.0,
        "force_sampling": False,
        "chat_template_kwargs": {"reasoning_effort": THINKING_LEVEL},
        "forced_ct_kwargs": [
            "enable_thinking",
            "preserve_thinking",
            "reasoning_effort",
        ],
        "enable_thinking": True,
        "preserve_thinking": True,
        "thinking_budget_enabled": False,
        "turboquant_kv_enabled": False,
        "qwen35_ane_prefill_enabled": False,
        "specprefill_enabled": False,
        "dflash_enabled": False,
        "mtp_enabled": True,
        "mtp_num_draft_tokens": 3,
        "vlm_mtp_enabled": False,
        "guided_grammar_enabled": False,
        "trust_remote_code": False,
    }
    response = session.put(
        f"{BASE_URL}/admin/api/models/{MODEL_ID}/settings",
        json=benchmark_settings,
        timeout=60,
    )
    response.raise_for_status()
    if not model.get("loaded"):
        response = session.post(
            f"{BASE_URL}/admin/api/models/{MODEL_ID}/load", timeout=600
        )
        response.raise_for_status()
        wait_loaded(session, True)
    return original


def restore_model(
    session: requests.Session,
    original: dict[str, Any],
    was_loaded: bool,
    api_key: str,
) -> None:
    response = session.put(
        f"{BASE_URL}/admin/api/models/{MODEL_ID}/settings",
        json=original,
        timeout=60,
    )
    response.raise_for_status()
    if not was_loaded:
        response = requests.post(
            f"{BASE_URL}/v1/models/{MODEL_ID}/unload",
            headers={"Authorization": f"Bearer {api_key}"},
            timeout=120,
        )
        if response.status_code not in (200, 202, 400):
            response.raise_for_status()
        wait_loaded(session, False)


@dataclass
class ProxyTotals:
    requests: int = 0
    failures: int = 0
    input_tokens: int = 0
    output_tokens: int = 0
    cache_read_tokens: int = 0
    cache_write_tokens: int = 0
    response_bytes: int = 0


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


def write_model_config(config_dir: Path, proxy_port: int) -> None:
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


def tool_read_roots(tool_root: Path) -> tuple[Path, ...]:
    return tuple((tool_root / name).resolve() for name in TOOL_SUBDIRECTORIES)


def sandbox_profile(
    run_root: Path,
    workspace: Path,
    home: Path,
    tool_root: Path,
    temp_dir: Path,
    port: int,
    daemon_socket: Path | None = None,
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
    if daemon_socket is not None:
        worker_socket_dir = temp_dir / f"prime-agent-{os.getuid()}"
        rules.append('(allow network-bind (local ip "localhost:*"))')
        rules.append('(allow network-inbound (local ip "localhost:*"))')
        rules.append('(allow network-outbound (local ip "localhost:*"))')
        rules.append(
            f"(allow network-bind (local unix-socket "
            f'(literal "{quoted(daemon_socket)}")))'
        )
        rules.append(
            f"(allow network-outbound (remote unix-socket "
            f'(literal "{quoted(daemon_socket)}")))'
        )
        rules.append(
            f"(allow network-bind (local unix-socket "
            f'(subpath "{quoted(worker_socket_dir)}")))'
        )
        rules.append(
            f"(allow network-outbound (remote unix-socket "
            f'(subpath "{quoted(worker_socket_dir)}")))'
        )
        rules.append(f'(allow file-write* (literal "{quoted(daemon_socket)}"))')
        lock_dir = Path(f"{daemon_socket}.lock")
        rules.append(
            f'(allow file-write* (literal "{quoted(lock_dir)}") '
            f'(subpath "{quoted(lock_dir)}"))'
        )
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


def shutdown_prime_daemon(
    executable: Path,
    daemon_socket: Path,
    profile: str,
    workspace: Path,
    environment: dict[str, str],
    home: Path,
    temp_dir: Path,
) -> dict[str, Any]:
    package_root = executable.resolve().parents[2]
    daemon_client = package_root / "dist" / "modes" / "daemon" / "daemon-client.js"
    daemon_launch = package_root / "dist" / "cli" / "daemon-launch.js"
    script = """
import { pathToFileURL } from "node:url";
const clientModule = await import(pathToFileURL(process.argv[1]).href);
const launchModule = await import(pathToFileURL(process.argv[2]).href);
const socketPath = process.argv[3];
const client = new clientModule.DaemonClient(socketPath);
await client.connect(3000);
await client.waitForHello(3000);
const response = await client.request({ type: "shutdown", force: true }, 10000);
client.close();
if (!response?.success) process.exit(2);
const stopped = await launchModule.shutdownDaemonAndWait(socketPath, 15000);
if (!stopped) process.exit(3);
"""
    shutdown_error = None
    try:
        result = subprocess.run(
            [
                "/usr/bin/sandbox-exec",
                "-p",
                profile,
                "/opt/homebrew/bin/node",
                "--input-type=module",
                "-e",
                script,
                str(daemon_client),
                str(daemon_launch),
                str(daemon_socket),
            ],
            cwd=workspace,
            env=environment,
            stdin=subprocess.DEVNULL,
            capture_output=True,
            text=True,
            timeout=35,
        )
        if result.returncode != 0:
            shutdown_error = (
                f"Targeted Prime daemon shutdown failed ({result.returncode}): "
                f"{result.stderr[-2000:]}"
            )
    except subprocess.TimeoutExpired:
        shutdown_error = "Targeted Prime daemon shutdown timed out after 35 seconds"

    process_rows = subprocess.run(
        ["ps", "-axo", "pid=,ppid=,command="],
        capture_output=True,
        text=True,
        check=True,
    ).stdout.splitlines()
    markers = (str(daemon_socket), str(home), str(temp_dir))
    process_table: dict[int, tuple[int, str]] = {}
    for row in process_rows:
        parts = row.strip().split(maxsplit=2)
        if len(parts) == 3:
            process_table[int(parts[0])] = (int(parts[1]), parts[2])
    forced_pids = {
        pid
        for pid, (_, command) in process_table.items()
        if any(marker in command for marker in markers)
    }
    if daemon_socket.exists():
        socket_owners = subprocess.run(
            ["/usr/sbin/lsof", "-t", "--", str(daemon_socket)],
            capture_output=True,
            text=True,
        )
        forced_pids.update(
            int(line)
            for line in socket_owners.stdout.splitlines()
            if line.strip().isdigit()
        )
    expanded = True
    while expanded:
        expanded = False
        for pid, (parent_pid, _) in process_table.items():
            if parent_pid in forced_pids and pid not in forced_pids:
                forced_pids.add(pid)
                expanded = True
    forced_pids = sorted(forced_pids)
    for pid in forced_pids:
        try:
            os.kill(pid, signal.SIGTERM)
        except ProcessLookupError:
            pass
    deadline = time.monotonic() + 5
    remaining = set(forced_pids)
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
    still_alive = []
    for pid in remaining:
        try:
            os.kill(pid, 0)
            still_alive.append(pid)
        except ProcessLookupError:
            pass
    if still_alive:
        raise RuntimeError(
            f"Prime daemon cleanup could not terminate PIDs: {still_alive}"
        )
    final_process_rows = subprocess.run(
        ["ps", "-axo", "pid=,command="],
        capture_output=True,
        text=True,
        check=True,
    ).stdout.splitlines()
    residual_pids = {
        int(row.strip().split(maxsplit=1)[0])
        for row in final_process_rows
        if any(marker in row for marker in markers)
    }
    if daemon_socket.exists():
        final_socket_owners = subprocess.run(
            ["/usr/sbin/lsof", "-t", "--", str(daemon_socket)],
            capture_output=True,
            text=True,
        )
        residual_pids.update(
            int(line)
            for line in final_socket_owners.stdout.splitlines()
            if line.strip().isdigit()
        )
    if residual_pids:
        raise RuntimeError(
            f"Prime daemon cleanup left or respawned PIDs: {sorted(residual_pids)}"
        )
    return {
        "targeted_shutdown": shutdown_error is None,
        "forced_descendant_pids": forced_pids,
        "shutdown_error": shutdown_error,
    }


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
    daemon_socket: Path | None = None
    if harness == "pi":
        config_dir = home / ".pi" / "agent"
        write_model_config(config_dir, proxy_port)
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
    elif harness == "prime":
        socket_id = hashlib.sha256(str(run_root).encode()).hexdigest()[:12]
        daemon_socket = Path(f"/private/tmp/prime-bench-{socket_id}.sock")
        daemon_socket.unlink(missing_ok=True)
        temp_dir = Path(f"/private/tmp/prime-tmp-{socket_id}")
        shutil.rmtree(temp_dir, ignore_errors=True)
        temp_dir.mkdir()
        config_dir = home / ".prime" / "agent"
        write_model_config(config_dir, proxy_port)
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
            "--daemon-socket",
            str(daemon_socket),
            "--no-session",
            "--no-extensions",
            "--no-skills",
            "--no-prompt-templates",
            "--no-context-files",
            "--cwd",
            str(workspace),
            "--",
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
        "PRIME_AGENT_CODING_AGENT_DIR": str(home / ".prime" / "agent"),
        "PI_OFFLINE": "1",
        "PI_TELEMETRY": "0",
        "PRIME_AGENT_KERNEL_PYTHON": str(tool_root / "prime-kernel" / "bin" / "python"),
        "PRIME_AGENT_INSTALL_UV": "0",
        "PYTHONDONTWRITEBYTECODE": "1",
    }
    profile = sandbox_profile(
        run_root, workspace, home, tool_root, temp_dir, proxy_port, daemon_socket
    )
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
    if daemon_socket is not None:
        prime_cleanup = shutdown_prime_daemon(
            executable, daemon_socket, profile, workspace, environment, home, temp_dir
        )
        daemon_socket.unlink(missing_ok=True)
        shutil.rmtree(Path(f"{daemon_socket}.lock"), ignore_errors=True)
        shutil.rmtree(temp_dir, ignore_errors=True)
    else:
        prime_cleanup = None
    return {
        "returncode": process.returncode,
        "timed_out": timed_out,
        "wall_seconds": elapsed,
        "stdout_bytes": len(stdout.encode()),
        "stderr_bytes": len(stderr.encode()),
        "stderr_tail": stderr[-2000:],
        "prime_cleanup": prime_cleanup,
    }


def grade_task(task_dir: Path, workspace: Path) -> dict[str, Any]:
    environment = dict(os.environ)
    environment["TASK_DIR"] = str(task_dir)
    environment["PYTHONDONTWRITEBYTECODE"] = "1"
    for cache_dir in workspace.rglob("__pycache__"):
        shutil.rmtree(cache_dir, ignore_errors=True)
    try:
        result = subprocess.run(
            ["/bin/bash", str(task_dir / "checker.sh")],
            cwd=workspace,
            env=environment,
            capture_output=True,
            text=True,
            timeout=180,
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
    grade = grade_task(task_dir, workspace)
    changes = workspace_changes(workspace)
    result = {
        "schema_version": RESULT_SCHEMA_VERSION,
        "run_id": run_id,
        "task": task,
        "task_sha256": sha256_tree(task_dir),
        "harness": harness,
        "trial": trial,
        "model": MODEL_ID,
        "thinking": THINKING_LEVEL,
        "timeout_seconds": timeout_seconds,
        "harness_result": harness_result,
        "proxy_totals": asdict(proxy.totals),
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
            canary_root, workspace, home, tool_root, temp_dir, 9, None
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


def build_schedule(tasks: tuple[str, ...], trials: int) -> list[tuple[int, str, str]]:
    schedule: list[tuple[int, str, str]] = []
    for trial in range(1, trials + 1):
        for index, task in enumerate(tasks):
            pi_first = (index + trial) % 2 == 1
            order = ("pi", "prime") if pi_first else ("prime", "pi")
            schedule.extend((trial, task, harness) for harness in order)
    return schedule


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser()
    parser.add_argument("--tasks-root", type=Path, required=True)
    parser.add_argument("--pi", type=Path, required=True)
    parser.add_argument("--prime", type=Path, required=True)
    parser.add_argument("--tool-root", type=Path, required=True)
    parser.add_argument("--run-base", type=Path, required=True)
    parser.add_argument("--tasks", default=",".join(DEFAULT_TASKS))
    parser.add_argument("--trials", type=int, default=2)
    parser.add_argument("--timeout-seconds", type=int, default=DEFAULT_TIMEOUT_SECONDS)
    parser.add_argument("--validate-only", action="store_true")
    parser.add_argument("--only-harness", choices=("pi", "prime"))
    parser.add_argument("--only-task")
    return parser.parse_args()


def main() -> None:
    args = parse_args()
    tasks = tuple(item.strip() for item in args.tasks.split(",") if item.strip())
    validate_hidden_grader_boundary(args.tasks_root, tasks, args.tool_root)
    validate_tasks(args.tasks_root, tasks)
    if args.validate_only:
        return
    args.run_base.mkdir(parents=True, exist_ok=True)
    api_key = load_api_key()
    session = admin_session(api_key)
    model = next(item for item in get_models(session) if item.get("id") == MODEL_ID)
    was_loaded = bool(model.get("loaded"))
    original_settings = configure_model(session)
    wait_omlx_idle(api_key)
    manifest = {
        "schema_version": RESULT_SCHEMA_VERSION,
        "started_at": time.strftime("%Y-%m-%dT%H:%M:%S%z"),
        "model": MODEL_ID,
        "model_settings": {
            "context_window": 98304,
            "max_tokens": 32768,
            "temperature": 0.6,
            "top_p": 0.95,
            "top_k": 20,
            "thinking": THINKING_LEVEL,
            "mtp_enabled": True,
            "mtp_num_draft_tokens": 3,
        },
        "tasks": list(tasks),
        "trials": args.trials,
        "timeout_seconds": args.timeout_seconds,
        "pi_version": subprocess.run(
            [str(args.pi), "--version"], capture_output=True, text=True, check=True
        ).stdout.strip(),
        "prime_version": subprocess.run(
            [str(args.prime), "--version"], capture_output=True, text=True, check=True
        ).stdout.strip(),
    }
    manifest_path = args.run_base / "manifest.json"
    if manifest_path.exists():
        existing_manifest = json.loads(manifest_path.read_text(encoding="utf-8"))
        existing_protocol = {
            key: value
            for key, value in existing_manifest.items()
            if key != "started_at"
        }
        current_protocol = {
            key: value for key, value in manifest.items() if key != "started_at"
        }
        if existing_protocol != current_protocol:
            raise RuntimeError("Resume protocol does not match the existing manifest")
    else:
        manifest_path.write_text(
            json.dumps(manifest, indent=2, sort_keys=True) + "\n", encoding="utf-8"
        )
    results_path = args.run_base / "results.jsonl"
    completed_run_ids: set[str] = set()
    if results_path.exists():
        completed_run_ids = {
            json.loads(line)["run_id"]
            for line in results_path.read_text(encoding="utf-8").splitlines()
            if line.strip()
        }
    try:
        for trial, task, harness in build_schedule(tasks, args.trials):
            if args.only_harness and harness != args.only_harness:
                continue
            if args.only_task and task != args.only_task:
                continue
            run_id = f"{trial:02d}-{task}-{harness}"
            if run_id in completed_run_ids:
                print(f"{run_id}: already complete; skipping", flush=True)
                continue
            executable = args.pi if harness == "pi" else args.prime
            run_cell(
                task=task,
                harness=harness,
                trial=trial,
                tasks_root=args.tasks_root,
                run_base=args.run_base,
                executable=executable,
                tool_root=args.tool_root,
                api_key=api_key,
                timeout_seconds=args.timeout_seconds,
            )
    finally:
        restore_model(session, original_settings, was_loaded, api_key)


if __name__ == "__main__":
    main()
