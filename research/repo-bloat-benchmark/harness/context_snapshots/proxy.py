"""API-boundary recording proxy (design.md §6.2, tap 1 — PRIMARY).

A local HTTP relay the agent's model traffic is routed through via a base-URL
override (e.g. ``OPENAI_BASE_URL=http://127.0.0.1:<port>/v1``). For every
request it archives the byte-exact request body (the composed context window),
the response body, and provider-reported ``usage``, then forwards the response
to the client unchanged.

Design properties:

- **Agent-agnostic and fork-free.** Works with any CLI that honors a base-URL
  override; the agent binary is never modified.
- **Complete by construction** when the run environment locks network egress
  to the proxy (design §8.1.1): every model request is captured or it never
  happened.
- **Byte-exact.** The archived request body is the exact bytes received; the
  sha256 in the snapshot record lets a third party verify fidelity.

Known limitation (documented in design §6.2): streamed (SSE) responses are
buffered and relayed after completion rather than streamed through. This
preserves capture fidelity and response content but serializes streaming
latency into ``wall_clock_seconds`` (a secondary metric). True pass-through
streaming is a follow-up.
"""

from __future__ import annotations

import hashlib
import json
import threading
import time
import urllib.error
import urllib.request
from http.server import BaseHTTPRequestHandler, ThreadingHTTPServer
from pathlib import Path
from typing import Any

from .schema import SnapshotRecord

# Hop-by-hop headers that must not be forwarded either direction.
_HOP_BY_HOP = {
    "connection",
    "keep-alive",
    "proxy-authenticate",
    "proxy-authorization",
    "te",
    "trailers",
    "transfer-encoding",
    "upgrade",
    "host",
    "content-length",
}

# Tool names whose invocation counts as an *edit* for the first-edit boundary
# (design §6.2). Checked case-insensitively; substring fallbacks catch
# provider-specific variants like ``apply_patch_call``.
DEFAULT_EDIT_TOOL_NAMES = frozenset(
    {"apply_patch", "edit", "edit_file", "write_file", "create_file", "str_replace_editor"}
)
_EDIT_SUBSTRINGS = ("patch", "edit", "write_file")


def _sha256(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def _extract_usage(obj: dict[str, Any]) -> tuple[int | None, int | None, int | None]:
    """Pull (input, output, total) tokens from a usage dict of either API shape."""
    usage = obj.get("usage") or {}
    if not isinstance(usage, dict):
        return None, None, None
    input_tokens = usage.get("input_tokens", usage.get("prompt_tokens"))
    output_tokens = usage.get("output_tokens", usage.get("completion_tokens"))
    total = usage.get("total_tokens")
    if total is None and input_tokens is not None and output_tokens is not None:
        total = input_tokens + output_tokens
    return input_tokens, output_tokens, total


def _extract_tool_calls(obj: dict[str, Any]) -> list[str]:
    """Collect tool-call names from a chat-completions or Responses-API body."""
    names: list[str] = []
    # Chat Completions: choices[].message.tool_calls[].function.name
    for choice in obj.get("choices") or []:
        message = (choice or {}).get("message") or {}
        for call in message.get("tool_calls") or []:
            name = ((call or {}).get("function") or {}).get("name")
            if name:
                names.append(str(name))
    # Responses API: output[] items typed *_call
    for item in obj.get("output") or []:
        if not isinstance(item, dict):
            continue
        item_type = str(item.get("type", ""))
        if item_type.endswith("_call"):
            names.append(str(item.get("name") or item_type))
    return names


def _parse_sse_events(body: bytes) -> list[dict[str, Any]]:
    """Best-effort parse of ``data:`` JSON payloads from an SSE body."""
    events: list[dict[str, Any]] = []
    for raw_line in body.decode("utf-8", errors="replace").splitlines():
        line = raw_line.strip()
        if not line.startswith("data:"):
            continue
        data = line[len("data:"):].strip()
        if not data or data == "[DONE]":
            continue
        try:
            parsed = json.loads(data)
        except json.JSONDecodeError:
            continue
        if isinstance(parsed, dict):
            events.append(parsed)
    return events


def _analyze_response_body(body: bytes, content_type: str) -> dict[str, Any]:
    """Extract usage/tool-call facts from a JSON or SSE response body."""
    result: dict[str, Any] = {
        "input_tokens": None,
        "output_tokens": None,
        "total_tokens": None,
        "tool_call_names": [],
        "streamed": False,
    }
    candidates: list[dict[str, Any]] = []
    if "text/event-stream" in content_type:
        result["streamed"] = True
        for event in _parse_sse_events(body):
            candidates.append(event)
            # Responses API terminal event nests the response object.
            nested = event.get("response")
            if isinstance(nested, dict):
                candidates.append(nested)
    else:
        try:
            parsed = json.loads(body.decode("utf-8"))
            if isinstance(parsed, dict):
                candidates.append(parsed)
        except (json.JSONDecodeError, UnicodeDecodeError):
            pass
    for obj in candidates:
        input_tokens, output_tokens, total = _extract_usage(obj)
        if input_tokens is not None or output_tokens is not None:
            result["input_tokens"] = input_tokens
            result["output_tokens"] = output_tokens
            result["total_tokens"] = total
        for name in _extract_tool_calls(obj):
            if name not in result["tool_call_names"]:
                result["tool_call_names"].append(name)
    return result


def is_edit_tool(name: str, edit_tool_names: frozenset[str] = DEFAULT_EDIT_TOOL_NAMES) -> bool:
    lowered = name.lower()
    if lowered in edit_tool_names:
        return True
    return any(sub in lowered for sub in _EDIT_SUBSTRINGS)


class RecordingProxy:
    """Recording relay between an agent CLI and its model provider.

    Usage::

        proxy = RecordingProxy(
            upstream_base_url="https://api.openai.com",
            archive_dir="reports/run-123",
            run_id="run-123",
        )
        base_url = proxy.start()      # export OPENAI_BASE_URL=f"{base_url}/v1"
        ...  # run the agent
        proxy.stop()
        proxy.records                 # list[SnapshotRecord], ordinal-ordered
    """

    def __init__(
        self,
        upstream_base_url: str,
        archive_dir: str | Path,
        run_id: str,
        host: str = "127.0.0.1",
        port: int = 0,
        edit_tool_names: frozenset[str] = DEFAULT_EDIT_TOOL_NAMES,
        forward_timeout: float = 600.0,
    ) -> None:
        self.upstream_base_url = upstream_base_url.rstrip("/")
        self.archive_dir = Path(archive_dir)
        self.payload_dir = self.archive_dir / "payloads"
        self.run_id = run_id
        self.host = host
        self.port = port
        self.edit_tool_names = edit_tool_names
        self.forward_timeout = forward_timeout
        self.records: list[SnapshotRecord] = []
        self._lock = threading.Lock()
        self._ordinal = 0
        self._server: ThreadingHTTPServer | None = None
        self._thread: threading.Thread | None = None
        self._snapshot_file: Path = self.archive_dir / "context_snapshots.jsonl"

    # -- lifecycle ---------------------------------------------------------

    def start(self) -> str:
        """Start serving; returns the proxy base URL (no trailing slash)."""
        self.payload_dir.mkdir(parents=True, exist_ok=True)
        proxy = self

        class Handler(BaseHTTPRequestHandler):
            protocol_version = "HTTP/1.1"

            def log_message(self, *args: Any) -> None:  # silence stderr
                pass

            def do_POST(self) -> None:  # noqa: N802 (stdlib naming)
                proxy._handle(self, record=True)

            def do_GET(self) -> None:  # noqa: N802
                proxy._handle(self, record=False)

        self._server = ThreadingHTTPServer((self.host, self.port), Handler)
        self.port = self._server.server_address[1]
        self._thread = threading.Thread(target=self._server.serve_forever, daemon=True)
        self._thread.start()
        return f"http://{self.host}:{self.port}"

    def stop(self) -> None:
        if self._server is not None:
            self._server.shutdown()
            self._server.server_close()
            self._server = None
        if self._thread is not None:
            self._thread.join(timeout=5)
            self._thread = None

    # -- request handling ----------------------------------------------------

    def _next_ordinal(self) -> int:
        with self._lock:
            self._ordinal += 1
            return self._ordinal

    def _append_record(self, record: SnapshotRecord) -> None:
        with self._lock:
            self.records.append(record)
            self.archive_dir.mkdir(parents=True, exist_ok=True)
            with self._snapshot_file.open("a", encoding="utf-8") as fh:
                fh.write(record.to_json() + "\n")

    def _forward(
        self, method: str, path: str, headers: dict[str, str], body: bytes | None
    ) -> tuple[int, dict[str, str], bytes]:
        url = self.upstream_base_url + path
        out_headers = {k: v for k, v in headers.items() if k.lower() not in _HOP_BY_HOP}
        request = urllib.request.Request(url, data=body, headers=out_headers, method=method)
        try:
            with urllib.request.urlopen(request, timeout=self.forward_timeout) as resp:
                resp_body = resp.read()
                resp_headers = {k: v for k, v in resp.headers.items()}
                return resp.status, resp_headers, resp_body
        except urllib.error.HTTPError as exc:
            return exc.code, dict(exc.headers or {}), exc.read()
        except (urllib.error.URLError, OSError) as exc:
            message = json.dumps({"error": {"message": f"proxy forward failed: {exc}"}})
            return 502, {"Content-Type": "application/json"}, message.encode("utf-8")

    def _handle(self, handler: BaseHTTPRequestHandler, record: bool) -> None:
        received_at = time.time()
        length = int(handler.headers.get("Content-Length") or 0)
        body = handler.rfile.read(length) if length else b""
        headers = {k: v for k, v in handler.headers.items()}

        status, resp_headers, resp_body = self._forward(
            handler.command, handler.path, headers, body or None
        )

        if record and body:
            self._record_exchange(handler.path, received_at, body, status, resp_headers, resp_body)

        handler.send_response(status)
        content_type = resp_headers.get("Content-Type", "application/json")
        handler.send_header("Content-Type", content_type)
        handler.send_header("Content-Length", str(len(resp_body)))
        handler.send_header("Connection", "close")
        handler.end_headers()
        handler.wfile.write(resp_body)

    def _record_exchange(
        self,
        path: str,
        received_at: float,
        body: bytes,
        status: int,
        resp_headers: dict[str, str],
        resp_body: bytes,
    ) -> None:
        ordinal = self._next_ordinal()
        request_name = f"{ordinal:05d}.request.json"
        response_name = f"{ordinal:05d}.response.body"
        (self.payload_dir / request_name).write_bytes(body)
        (self.payload_dir / response_name).write_bytes(resp_body)

        model: str | None = None
        message_count: int | None = None
        try:
            payload = json.loads(body.decode("utf-8"))
            if isinstance(payload, dict):
                model = payload.get("model")
                messages = payload.get("messages", payload.get("input"))
                if isinstance(messages, list):
                    message_count = len(messages)
        except (json.JSONDecodeError, UnicodeDecodeError):
            pass

        analysis = _analyze_response_body(
            resp_body, resp_headers.get("Content-Type", "")
        )
        tool_names = analysis["tool_call_names"]
        self._append_record(
            SnapshotRecord(
                run_id=self.run_id,
                ordinal=ordinal,
                timestamp=received_at,
                endpoint=path,
                request_sha256=_sha256(body),
                payload_path=f"payloads/{request_name}",
                response_path=f"payloads/{response_name}",
                status_code=status,
                model=model,
                input_tokens=analysis["input_tokens"],
                output_tokens=analysis["output_tokens"],
                total_tokens=analysis["total_tokens"],
                message_count=message_count,
                request_bytes=len(body),
                response_bytes=len(resp_body),
                tool_call_names=tool_names,
                edit_tool_call=any(is_edit_tool(n, self.edit_tool_names) for n in tool_names),
                streamed=analysis["streamed"],
            )
        )
