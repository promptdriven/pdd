"""End-to-end tests for the recording proxy against a scripted upstream.

These are the automated core of the §6.6 calibration gate's proxy-fidelity
assertions: byte-exact archiving, usage capture, ordinal indexing, edit
detection, and transparent forwarding.
"""

import hashlib
import json
import threading
import urllib.error
import urllib.request
from http.server import BaseHTTPRequestHandler, ThreadingHTTPServer

import pytest

from harness.context_snapshots.proxy import RecordingProxy, is_edit_tool
from harness.context_snapshots.schema import read_snapshots


class ScriptedUpstream:
    """Minimal fake model API returning queued responses."""

    def __init__(self):
        self.responses = []
        self.received = []
        self._server = None
        self._thread = None
        self.base_url = None

    def queue(self, body: dict, content_type: str = "application/json"):
        self.responses.append((json.dumps(body).encode(), content_type))

    def queue_raw(self, body: bytes, content_type: str):
        self.responses.append((body, content_type))

    def start(self):
        upstream = self

        class Handler(BaseHTTPRequestHandler):
            protocol_version = "HTTP/1.1"

            def log_message(self, *args):
                pass

            def do_POST(self):
                length = int(self.headers.get("Content-Length") or 0)
                upstream.received.append(self.rfile.read(length))
                body, content_type = upstream.responses.pop(0)
                self.send_response(200)
                self.send_header("Content-Type", content_type)
                self.send_header("Content-Length", str(len(body)))
                self.end_headers()
                self.wfile.write(body)

        self._server = ThreadingHTTPServer(("127.0.0.1", 0), Handler)
        self.base_url = f"http://127.0.0.1:{self._server.server_address[1]}"
        self._thread = threading.Thread(target=self._server.serve_forever, daemon=True)
        self._thread.start()
        return self.base_url

    def stop(self):
        self._server.shutdown()
        self._server.server_close()
        self._thread.join(timeout=5)


CHAT_RESPONSE_READ = {
    "id": "chatcmpl-1",
    "model": "gpt-test",
    "choices": [
        {
            "message": {
                "role": "assistant",
                "tool_calls": [{"function": {"name": "read_file"}}],
            }
        }
    ],
    "usage": {"prompt_tokens": 1000, "completion_tokens": 50, "total_tokens": 1050},
}

CHAT_RESPONSE_EDIT = {
    "id": "chatcmpl-2",
    "model": "gpt-test",
    "choices": [
        {
            "message": {
                "role": "assistant",
                "tool_calls": [{"function": {"name": "apply_patch"}}],
            }
        }
    ],
    "usage": {"prompt_tokens": 2400, "completion_tokens": 80, "total_tokens": 2480},
}


@pytest.fixture()
def upstream():
    server = ScriptedUpstream()
    server.start()
    yield server
    server.stop()


@pytest.fixture()
def proxy(upstream, tmp_path):
    recording_proxy = RecordingProxy(
        upstream_base_url=upstream.base_url,
        archive_dir=tmp_path / "run",
        run_id="test-run",
    )
    recording_proxy.start()
    yield recording_proxy
    recording_proxy.stop()


def _post(base_url: str, path: str, payload: dict) -> dict:
    body = json.dumps(payload).encode()
    request = urllib.request.Request(
        f"{base_url}{path}",
        data=body,
        headers={"Content-Type": "application/json", "Authorization": "Bearer test"},
        method="POST",
    )
    with urllib.request.urlopen(request, timeout=10) as resp:
        return json.loads(resp.read())


def test_forwards_and_records_in_order(upstream, proxy, tmp_path):
    upstream.queue(CHAT_RESPONSE_READ)
    upstream.queue(CHAT_RESPONSE_EDIT)
    base = f"http://127.0.0.1:{proxy.port}"

    first_payload = {"model": "gpt-test", "messages": [{"role": "user", "content": "find bug"}]}
    second_payload = {
        "model": "gpt-test",
        "messages": [
            {"role": "user", "content": "find bug"},
            {"role": "tool", "content": "def slice_page(): ..."},
        ],
    }
    first_response = _post(base, "/v1/chat/completions", first_payload)
    second_response = _post(base, "/v1/chat/completions", second_payload)

    # Forwarding is transparent: the client sees the upstream body verbatim.
    assert first_response == CHAT_RESPONSE_READ
    assert second_response == CHAT_RESPONSE_EDIT
    # Upstream saw the exact client bytes.
    assert json.loads(upstream.received[0]) == first_payload

    assert [r.ordinal for r in proxy.records] == [1, 2]
    first, second = proxy.records
    assert first.input_tokens == 1000
    assert second.input_tokens == 2400
    assert first.message_count == 1
    assert second.message_count == 2
    assert first.tool_call_names == ["read_file"]
    assert not first.edit_tool_call
    assert second.edit_tool_call  # apply_patch ⇒ first-edit boundary marker


def test_payloads_archived_byte_exact(upstream, proxy, tmp_path):
    upstream.queue(CHAT_RESPONSE_READ)
    base = f"http://127.0.0.1:{proxy.port}"
    payload = {"model": "gpt-test", "messages": [{"role": "user", "content": "x" * 100}]}
    _post(base, "/v1/chat/completions", payload)

    record = proxy.records[0]
    archived = (proxy.archive_dir / record.payload_path).read_bytes()
    assert hashlib.sha256(archived).hexdigest() == record.request_sha256
    assert json.loads(archived) == payload


def test_snapshot_jsonl_round_trip(upstream, proxy):
    upstream.queue(CHAT_RESPONSE_READ)
    base = f"http://127.0.0.1:{proxy.port}"
    _post(base, "/v1/chat/completions", {"model": "gpt-test", "messages": []})

    reloaded = list(read_snapshots(proxy.archive_dir / "context_snapshots.jsonl"))
    assert len(reloaded) == 1
    assert reloaded[0].run_id == "test-run"
    assert reloaded[0].input_tokens == 1000


def test_responses_api_sse_usage_extracted(upstream, proxy):
    completed = {
        "type": "response.completed",
        "response": {
            "usage": {"input_tokens": 3210, "output_tokens": 99, "total_tokens": 3309},
            "output": [{"type": "function_call", "name": "shell"}],
        },
    }
    sse_body = (
        b'data: {"type": "response.output_text.delta", "delta": "hi"}\n\n'
        + b"data: " + json.dumps(completed).encode() + b"\n\n"
        + b"data: [DONE]\n\n"
    )
    upstream.queue_raw(sse_body, "text/event-stream")
    base = f"http://127.0.0.1:{proxy.port}"
    body = json.dumps({"model": "gpt-test", "input": [{"role": "user", "content": "go"}]}).encode()
    request = urllib.request.Request(
        f"{base}/v1/responses", data=body,
        headers={"Content-Type": "application/json"}, method="POST",
    )
    with urllib.request.urlopen(request, timeout=10) as resp:
        relayed = resp.read()

    assert relayed == sse_body  # SSE body relayed intact (buffered)
    record = proxy.records[0]
    assert record.streamed
    assert record.input_tokens == 3210
    assert record.tool_call_names == ["shell"]
    assert record.message_count == 1


def test_upstream_failure_becomes_502_and_is_recorded(tmp_path):
    recording_proxy = RecordingProxy(
        upstream_base_url="http://127.0.0.1:1",  # nothing listens here
        archive_dir=tmp_path / "run",
        run_id="down",
        forward_timeout=2,
    )
    base = recording_proxy.start()
    try:
        body = json.dumps({"model": "m", "messages": []}).encode()
        request = urllib.request.Request(
            f"{base}/v1/chat/completions", data=body,
            headers={"Content-Type": "application/json"}, method="POST",
        )
        try:
            urllib.request.urlopen(request, timeout=10)
            status = 200
        except urllib.error.HTTPError as exc:
            status = exc.code
        assert status == 502
        assert recording_proxy.records[0].status_code == 502
    finally:
        recording_proxy.stop()


def test_healthcheck_is_served_locally_and_not_recorded(upstream, proxy):
    request = urllib.request.Request(
        f"http://127.0.0.1:{proxy.port}/__rb_health__",
        method="GET",
    )
    with urllib.request.urlopen(request, timeout=10) as response:
        assert response.status == 204
        assert response.read() == b""
    assert proxy.records == []


def test_edit_tool_name_matching():
    assert is_edit_tool("apply_patch")
    assert is_edit_tool("apply_patch_call")
    assert is_edit_tool("str_replace_editor")
    assert is_edit_tool("Edit")
    assert not is_edit_tool("read_file")
    assert not is_edit_tool("shell")
